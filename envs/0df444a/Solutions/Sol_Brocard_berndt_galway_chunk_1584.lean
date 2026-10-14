-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1584
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:42:11.742728+00:00
-- url     : https://prove2.me/submissions/d1159afd-9d1b-4ef8-9517-99a0c11b1e0f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 284712230 ≤ n < 284892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 284713480 1250 284712230 284712257
    0x1090c080103021504030506280b13320105031002070b01030807020a17010f0e01150902090414250311040510030e10020c06010807050a0e040c05092d060a06 69
    0x4c0650340210f904c08102d41c400e1038100e040c903031500c069030382804000c5020508000a00140e001f00340d284800a002003e2813004030315960040c0140e02031348108410450401300102010480710400c25040340c203289069452b00d42414500070078001882052441172298a00049400f031055045a40113030000d5101d07400c030300002d1200301c000d60002030700b88540395113201c02e9501900030f0f101900043c0c004104407280480c5035801c1c1c4010a0841ca00e52102c4002400100d2041c1d010341a2118050400503c01d0000c15010f46ca2030b0064484050041c900200e07540480128882c0322041d8030186014400340d2119003424100d400340c0d0043d10310400c0c0c1018101503051180c0d1018203800101000c8406072641082a00d00950002140800d140030741f40002c50700a10001e5820110354003c0c280110442c506010417200074030140c130841e0b0004d05407800052950321200540d0145403042040509041072000c203112812901c0503c0c2011620001008141e5a8180550741100c030542007841100d06030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 284714730 1250 284713480 284713519
    0x3060c1106151f05130306140f0c0d091a0c13080304030804030809042901020d0302030f13020a030803040326270a0b0903070308061e0f0616150501090c08010302 71
    0x1403505c022003074009008008240074058110b030b03160384903070a2401c0b419100ca03c0d41110011045801c0c2c0c20810081008001927030850384200f24007405070018840a44800309504490308041e0b401c80d00f07000000c106000c0881c501c1703208500802014000790301d89403860f42d40c600340e4011072101405a40340440c2913461a12036800a02c0320103d2140b41c262170b000ca600d01c00d104040310002c0301d8018494201c030170001d24042e2088a006803000d041d07030320142d6a02241042c039103d00d100120380240c02c0180000c0044c0e01403000e907000780d1003030f107803c01441c0d01203540700360060b000c1201000396601c88060002c041c0111015820036a809508039042190294102c0c4c40c28200490040c22a0400790400c5040000400600002c0c5c0c030030391760400591912020040090001140109240c10b540c03864032203458401c0c61803503802006041e503402d089400702c01c10f12403000120700365002840700c54480a2011544201809888103100c101301e02d104510000340032010500009026298510f0190042280d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 284715980 1250 284714730 284714737
    0x6040e010906090501270f0f081813060e0601030510081207021c05100203091c050a1211090607050319090f060c0b0f070903060c1106151f05 62
    0x105802844860038624080340104050a0280c90651034861502007444809020140d0307110504d5011610690f0340c2c465560100c0051400c445050071001c1200000300000d000d8a04140d03080340752402070782c0302028003e01e15036407200151b405250100a2007101c5800e0b0f03e841d0027010a00e000511980c8000c1401601580c6400120240c411010700c6002da80f074007401011000d10035940c0d1840c032000c6822815512a003540010a02d80210319020080425130703000c0c5901c14885000c490030074908070a0f001c0d016004280f01c0d0001100010113802c1542c20060403000c0d5510f04108100e070510203011180c80b0f001c3d008d80340341b04000c00140141404030400985101d0000904270440b51104020054201603c40c0b080300c041c5083d401000580c0c600030707803196042c103412440106540d5900032212500781c000a04000520110150100c041155881101c440b1401a11200d8000c052030b0400340c0f034070500905c80e0014400518450516494004580e0320303102c0d000d010b0380c0e0a0041ca20040d2050300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 284717230 1250 284715980 284716001
    0x51305040e0304061407020603040f030909150312020c010f030c140d0207050d0207030b04030503130c0f060306090e0715260406050a02070b04020108070203090a0905070e100e01080604 81
    0x141032401c40c1071032810100052085605640f103420100da207080c501c5405014546019500800900004001c1884500d50f001a1031291500010403a2510006001ca40420000c0058011054400e004000c03a0310140040e4013030900041c504040088002050014041001420580c44414024905d400380c001c845101d28800182e50301c8031201490b84000f500003500a54a40c4108510101e0b41c0780041486801c0d65000300351150f00d81e030385840c103540700ea0001c1c091400078084240004041038407a0f40203806172000440c07910100d440c103080101070ba10642c0281e42182d24120920403140d400161040454141007100000c2c00c00c40301c804d580465010304440c0d244a1064500c4081403005042d1b68400c0e032249504000e142c403031000d80c0040380204440144543d2503440030501560169640503800b08045c8122071900380310101107015411a40d1051038410384810602c01c2c000d82016003400d100c0c2c0d0580f00b40f2100c0000341c10003080036030011901410b200100001c10990340781d54001d1940f40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 284718480 1250 284717230 284717239
    0x30a05070614040b0309250807050108060a180e0c01110c09070207081b09010b090d0213060801090302030304020a060c030903170d141e092d0d0f0f0302070b07051305 73
    0x74178010301b860b0344810b010880610194082012003a4401c103c02c503400c103890080c00100911070400c801500c0403080904460b920010701000055030701c00c00038075100002450940402c0d600e42d22800310b850080d0716940c603418083c4001c410490410005201d4104000c2100c0b240072545403080160300b009a560420851800b82d28000c0319003040101071700300050800d49501d00d281e0303030355105022240100107000368400030082245000d0b203400b03a0400c03d02080c1e0140000c21640e20703c40e060031a42c18180807005a0070120800007986400141d0600510050811480243c0c950340c00800c0001c0502004120304021008804813184010a460714581101c44c20000c1c4282c00e40c0200817884115240012251501841003000da025403102d4050b540d81d4000701110841d005040c200604151a0b207003940e55607001d018144002085907065508031030315007078030151036684014890a0070309402c6081c140100281000686080700066002e41c16180c00b544400c0201c2a448524240d5401203910 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 284719730 1250 284718480 284718487
    0x501031a070e0d02040c09050a12020906060301050306181213091538130f15020d080711120903010b0f0a030816060501030b070e030a05070614040b 65
    0x400c4488140c858128489803240302065461240407030701d60720440764480d0004200500d0303200500b410703048110b0218141c10204046a2144041003030b205082d880448690410181c00095050642c0060b8000100380d0f070440c955810100803c0d42c901018180c0d440d00c901c0543c420882510600444c2410340c4108901aa030710b1400701d030006100f041c0c1c012500e01c90700d80180e1a140e44446801e5008403500d9030034940c000d158590301c19980e0320200c401c09a0310b00000d4054100c07404404c0003090000b2140550917541802c0040414000550381c0003140e40e04003650020700125000640030703c5205451800304d2960307031145000c0320810103017558480c8521030348000304001da47c01d2015090544c0d0070340c020400c00200310308228501c1807004089407c8000a402400401c52083c01480a640541c4031344648803070070358405c001c40d0f109910a951403c02007042c407040c02d6000842d0750005004500a00d0004110b8599503101d5100340f14034800c3c01600c03410710385500b5154040da0001d00d0305076219505c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 284720980 1250 284719730 284719733
    0x4030302150f0403020607030c11030f12090312010909060603150501061407020105182106040606050a03080307120f0c20161811030a0c080108060c07030e06090301050103 75
    0x69610781440228012500440000c04820411081a00c2150983c2c0100300c55102c80c1400d03001080040c601c0005c014a4000361080c912080000301201e9181c5d02d6455a610101c95a07003481000103001e8441c80e401c100f05000700b12451131844c4d07064441100300040c001d003079031a0100060403113600082007a00744504482c3c090721140e00c40e034102d407416150400095824504503240c0c1c0320700a070081c0424000d200b2950040342200d032030b86100d003018241250950166080c01070081c04004245280da12010402003003060314002c8000070101500c3c0310070315070f05690724800786020040121081112503c0503070161036007030700300010b00d50f109102003004089516005001250451038003400107051000c107000c4400c000740c05480c17507185c94001110503050031031003513401c4d80030039000410b41d03100c0c0c03102044a1340c20700056024130341120b40001c921020890240003400d05a00c8524640c0100c000c22442d0a80c4800b101c124561501c0d03c0e41c601c89d18500050084d005005245030035600c1c2400110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 284722230 1250 284720980 284720983
    0x51c0501150b03150418110406060e03030f0c01060b0c07030302370204091b05090f091c020309060f0c2a060904090b0112021e03070b090d33060e012904030302 70
    0x11f4400409540030720015894030810b40380c03469800c4c0e00c02d825a000300405103403000d0500142250100500010a541d030f03486030021616000a66030240c180c01c01c060400c1059010409100320340704240c903105da000c031440ca10401c090f04280713002c04220800c031801c8085644650007000d55a0384510200e2002880b6820005080418003945000380d9090020402003030520f06409d206207455801002007000ea071003101031214064607980158801840843d400b503640070060700610f8659651540c4600c20020700600d0100030303001c20395090140030301c00c1c01c0940120b004269440c4007074a0040e65903006401050040500d40c50241a2061000010600720944010707219060b000320764440240040b038042c00001998a401994150b008842c00c014601e000000740c200a10010107807581209079841d6000c10510058001154104c0b002080d021a11031004220b000598030004004080c1450840b440610042c0100b041c2802e544068203010311003e000b0f5070300390780031001040e11245d40e8500039 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 284723480 1250 284722230 284722253
    0x807030507171e04030239040b12191e0f17090a0803030412092714040303060e011203050d020306060f07060605130c0f08040c051c0501150b03150418 66
    0x43e00c0c48403001a0000c7d40008076005006c58000402c002c0710342c0500c0701c0c208002483ea03401c4d180e400841ca1494480408000d00c800c005148025102030802201450b1418400744030804040d80e200f0035103400d1010400c402130942605602030340c00c00c0c4800300400d28050a024a4601d0340d8440b240303200c04551100e0200c040c6000d00e100c1c5c28010101c28030180140d541d004540a000c0940305200300c1c620fa0042440b40c001c2d1280c0708480005190841c3d40e80b000c641a104a50030b0b030200740c4604041205c6106403641c02d004208650f8192148141c0341e40c01030061203441901003c841c4c012000c1031980c1d5900007211405484414074603a90b182d00d141001c09003105200c5c1c1c0c0d02ca030380740c1500180c0c806014007411070740c01156034400112180400064030485009401611106410070004c55540ca41c9200c900c045000e603140c00014050a241042c00c0d502005007464600343c10010800c181c80418050300d81019501c00401104200f03007000c2401000c40c8440040303240304088100c0188024a0310300c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 284724730 1250 284723480 284723503
    0xa081006080d020a1515030b01140f03031c05060f030708060a0b0307031718040e1b060a211b1d04060503071412010204060509010807030507171e040302 67
    0x648800b04141070007a6101c3e08140c8000d002c20440c1429500080203990003a182141034151030b03603031240caa407034080006209801410f05c40d1042824041c851900c94128040043c0071001549002540e281a003140301c00f48260020a545442c04207586507280034003e1501c95024044614140d80d41c400e1556502c0705485801d140c900d00101401036082c04684c80c0103417608224000f690005017015900c2035802019120309401c1030b0300c1c844450b6692401210b00410416006040d44860286540f1520100c3c80110f84504801c00001c071a1a801074010100344c0d840e1801d070030b5140da03c0504180980700d6101c00280060003a0b445201e50354100319030000019a41d034150829884001c240700803940140156541075202c6d0170b08100a4240380c010b02c942ca20040c0401c91075484140c912802d9803c01d410030000319a01080118284d64031030300195010407540350501040c01e0502c00a000c5101410303000400500366000500f030a4080c40c01d20ba05030003000b0626070289401d0030020b4030303008142c48 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 284725980 1250 284724730 284724733
    0x705040c030c080c0c151f180c110a080a050715140906070206150a030510060e060904150510030f0308060112020c030301290301090b10031a0904020a08100608 70
    0x7242c1081140c03015507016000e030344014101c4601094094400b41740007050407c80c1b41d140c2e60305003091000c4050507001031030400704650316225403100fa00203540c0c2002d1041c04101040102281c2d005000461400654002609a50354480000103c42601c036000001c1c05402c02c11382a900c0c802c13810382c0300300e18441456068032500d84500c0a41600d44100b034620100681c080004038112503040200c140668500410f40d1030070a540784da50350304244061515545c5207907204420400e0001207840706903c10412206070b50300c0e180a90343e440b07040032650581030443d66900001880c5010f000c04c48006180c00c088100c01141803481e0080c911101203c0d040d0000d2031064904101350203034002c1e9001405420080c60450307080a100f00380c0b09100d10740c1c20006400ca8802d658004070818000d40c0079114411010810758001414040c1240b00c0784103a4042604d0401d0030800a1a80203058002407802c0320303120500d850750b000041211600ea04020040d00071000031040906e4541e01ca1000c40c0c58510 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 284727230 1250 284725980 284725997
    0x120a0309060f05190917010506031207080a08060f0d0b0a0b040e0d0809101e0e070509060607060b030105090d110d0c0b04030302040f0303120b0a0f05060c0705040c030c 74
    0x858800d00d100c0c104202040007886080138070062020481e4400100d0724205000941d26007411524100d0880d50304042d035900c1040c49007504091011030045003843c1d08843c505003060b500d81c1800c1c440c00704903000f000b034060040390150707840d041c005c40d000400502800464040d400d04410166040e40c2c42d244403480c0c400c04000700d0900703000b601d40d00400e00d4003506041d54122016a4580801031284009014050010204207040d100f4080312284507440405022100348030403046440c0c42e01c142003140e101003020002e9a903a450150b51240d4142c034015180c0789107181c0f040c042c010201c803550789942800c00700031540e00001010f640995040d42c8040d0604008840365031551078012008000882030380c4072502252a101c4a5604507100303140062509640b828250044541c540040f000221040c00d5094010414010040c1560781150350071040391030540b2441c49803059104240c001c00c1d000c01d1681c9000018041300d002824054018081c41c020110300400514002104501280c0c044c2c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 284728480 1250 284727230 284727239
    0x7110f04090c30110a0e010f05010507050a0b07050306150301080a03080c07061503020907051602010e06070b010909060c090e06012307061a0607080d020901030b120a0309 75
    0x6000d07802005420a214040490400c420116078040101c40b00d07984034840100560750120154a000059024840444d00c9850030410003148049075400717003490104a00c0180010700700c94011604540003402c20079518991172500505000c0441c45c00b400754103024017003004503500a00210b01c42e000444000c8558804c280c884100b50100380902c0c41c003a0301c16002078000901405205412108d040241414912140d58920944840700004603800410090070400c500348801c0b250b0304103815090142c1405200038408115090360000681044034907501012181c95000c1202d07283c81c0c1050302e400c0c0541c0c4030400c0401401c418081110007c0c80d0000503114548552a84010303180b40100c3c88400343c54040044401182290381c1d140c00300c071b4495580000040b450003c0c4040b0788650310101e01020007200b020402c2c100f241d1014090402000340c0c0700050f50039421100881c0d02c000006032598101e4004030014a0540c25064000010f1040d01136842800121600342a100f80c0d42d0540b2142c88 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 284729730 1250 284728480 284728489
    0x7090501031e050402011107060207090b010807080402130f0f0501080c04020f030c0f130806070e040b010e1908010603050a0c051e101101020d0b121501062307110f 72
    0x851580200340c6400958459815005422464103d0700503d01f21103100d2061820b9828a00759500c10800340e8010354040040660600139104030b03910900704100d0515011201401d01040280001c2c0b00c0d144180d42c10000c0c60080d404454031008180b0100141944914900001d01081c0504081842400c445105502d814001c55610387e030648492070071a1a000070310119500049803c0090f00000e000b00c084003044011400001e0841a00030401c9050001014200c207038900d85443c00b940c10587d0058031039811011003a4a598192209c60b54000c84840161062070b40d500503800b25400c0c108c00105100c0001807102e040c80c0156103074506250703104100919100400e00c0010042c1c0c80905030341e510b160035120090b056555041c4a105203000d80e54207400c980c88107000f004520b179111003440250a081503045000b1002e00020070000c1d0380c1d0401c4668074801403044408008100d403001012800f0040d000d4880b110102c0035549420f024588000800c981048050288522803500080c502c2d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 284730980 1250 284729730 284729741
    0x3031407031d0a0503090d0302010b09070e1e0a1a040302030714012705041d012405030f03120403090b0a020318030d09060e15070506040204050112030f0e0d080c060709050103 77
    0x138858015440c1c030204600340103030074180e83d20550942d5a07a410800b002d454032600c0301c1c0700b130140f03559510340c0c01c80d460304010994100302e1582d90070341040101c940c03d03500e450001030705071892940c0c038149014070124807030803e20540d0002501409060000601c003e05202c01d907510170002d0b01d5800394481e420111580c0c032580c881c1020700340b40b0350741d80411441c1410383c40094090020303801e90074064103c0709524251007103500b002c15491034441c903035007080b200380b1743c0130003d40307011000340c415180d52100c090b580303005004045e11200d20b0000480c0405028903208802480c000d003845440301d522038400307512130300070f0310442c0c1403002410445900e43c500851064031202c0e55403518403c86040079411128400c078650083e41110b003844841e00c0008820000d13282d207920400c000c0181d0302c1d09105000503120103a1140318104551084500001e07088400c4000c0e170080c51404c254002618400a02c04c0300c1d03041c4000d841d2038000036003560301620106074a0b1003040b05484100c80c0da5500d0b40110129030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 284732230 1250 284730980 284730983
    0x902150a022503021908030c0f070f030803010b131505070c0f05090f0901020c0a050c040e030a050d0504080f120604060f08071406040305070605041d190903031407031d0a 75
    0x800e18005000602c3d00d43d05e07420800291010b820652a116a802460741c0d21582203480664800059007102e8001003081354081c0c4103214201032410302e1542c43d01d107240011302a900d000b0030049203458400002c0320440c0002e102c1010600c5404000c030402030090f078404401602c100d200020302140130384980704a0750840f040a401e28026507114100e0000200d0081c00c0d1802c0e1755000c0007552a03d0204000d4041c6a41c001d1000d0721003504500304000c01c8070b4261458042d140c00030300c80d820600350020140d4110460480b4007140d241e48500d08007400380f254809c0e00c00c18a00102d404810940300c007203074603c24082607808024613900c91344001c06030001d51040204a60100b002400301c0ca0f842e01c03c0c1c030302086010700030300d0908d51a40c4c0d403641441c40790f80000c0e0004001003020800c401000c0d1040c0d800008213460010141003401d110484c2889203484025141e46034580720080510a070302c6516229181c00d415801428045001070291122a40728103240701c80705040c08980700d020070680c0156 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 284733480 1250 284732230 284732293
    0x60e0306040213020c01291f050703050a11060c0903010e0a02060f07110a08010203160c020d0209070c0614161107090507050f040f1503150e06040902150a02 69
    0x2241456610103548107a5080174030307540701c008801c0500108428401c50004403040f41c000000c00300b0604c400d401e0622107803506032161403107004045400000300d44041c0d4040c6811583c0f00c400100613100310380811400915072080310100a140d0607075601070035610604500a118603124041e1243e0f480c0c0c202440607601000400107216000020030041c4041882240550306e4101d180c0006040708405d9400b940f00c40e5000020028185481a0822807608050524030310352041d85e0040703405006a158024000d420708404212440d0084840e41106603120000b031106080b5013041e1800108140c404507089408404003a4400f4003031000c0c0340c626403c440080250340e00d407210f1000601006011601442030410450015160040c001c0010381040d241d0000c1030792800603682502c51052446070209440c201c900d80c004144102d140e000ca412a01c0400ea86032180c00000c1c2c010300c00b43c140294000d043c0c86085e5500750301d00d0041e0804444540a4900703203144003220f4440e00c050364110740402e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 284734730 1250 284733480 284733499
    0xe0a060e030f01090f020f010903050316080409020a02070f050f060304080306040e0a050705010f260a0e0a030305011e08070303030207170301080c03070602030a0e28030c060e03060402 81
    0x90920a040500395200010121015110051109800c45469500903074865010000f4141941803c441030a001c02003807902054540c81c1da1542901ca010f00f186050f1128a0324426500340400076003504d0242c001404119501d03601e24002a60300c4295218410307503044035200010f1945000c20780d4402d01c84020305081e01d503640340d0f581c5210b25803004142a80c801c0e0f503407440c0621500704100815205104100400c0840c0c20700d0005854100000440740400004818a05000440300c01c550545000f01007a8003054a4000814010b001c000102d04407a20501211909042d0b040c0c01007412602e910480c0168017424102c103000c0f00f0000d000f96001940184010070000388a0781c01440d0150081c1c04281098101a8030300055610130b9000d2200c0c1d41c03000c5400b95440c07500303112200082a1038001545010090340c80a810070503c140c2042c410407440d08556610391444883c82d80a04070406818211030300c0386480e14803100c00d4042c2d00002407200000b155542400101640601d030014400b114 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 284735980 1250 284734730 284734739
    0xa0c0b192a02030109060507090e0c030106050a0c02040b06030717060d02011e0e06030406020d0b030a0203061b040504020316110c010215190f02031e150607081b01090c060e0a 77
    0x11540c800d60704980643da1000c035007011a140b441002d0250840d585d038003045a20f0800000321010010b030001030491010801000707465005003c444000449007010015080304d400003a000b08041e030207803900300100204022a4031b51021520030300342420f5207541042e0301d8400500c02d90391100e103c000d020034000c002e00303568840d42840043c031903015442c6c501480500180440c00c0c5401c00c1d6811240b00740c0200b40881940c5550040790070001c810f8005200c0c3c2d1a1a1f0006a510103020304a040115803140d41504041d5091085030701800018105564038141200380195031501d2503160340008181140008241402280c000c1c05004160700070f105031500d011140481d200c0151a60308803880298458101c41841d002d410b220b50881d10b00182c407442c0c4404da00c480700d10400310170801c4201040403c0f4044070700c008160a00b800c243d40300d503100d100b940f4124450b8400c1c1121030000007064042002180b6054108400c003a1040d01e58040181d922902a55100c10b414903032a40310440c44000d01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 284737230 1250 284735980 284736047
    0xc290726010f0620030d3c020a09080115051206090703060506010504170c01030f090213020306060906130f05180a05100f0303031505150a030903020a0c0b19 69
    0x74200c028015501d015003e41341c0c84d0919503440524201c0350039440701218088102144075110903403c078280c90300d50b0000103101541d518058050074480c56907001c10352955580c4500b101c1303405001c003c0000c00060862030742c0350400810606c121031003081802e14000081e0030104200f80103000c024000c010300346c1585d40314400b800d030003003110341080001d010000d5420030804007020915000d00151030810701d0400014103440c013116800e0211410000b00f4001038890910b200d0034503c2c42400107031a0b0b02d842c000950341e8410113001e51b50121021920074508e4104c088445c08840d401c02100481950718810f008000e04401395113280401d00000044150381290041323a0b0107101060b8084580351a111a800229640e07001507001a9564042d100c20031119040c038009001c04440d00c0750403084242150078180700d017148103070030940c99652060030076000b0000c00c028550f0002c00015120781b81d08203841607411418a028059031000141000640640b0004040ca02e44e0700d02070b41c81480276034851 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 284738480 1250 284737230 284737247
    0xc0e0d121403011214060114120109020d050d0e150403060b03070e0702010212060402090616030302070c030f1203051b09030a0501060e06100504060c290726010f06 72
    0x4418400c850900c840e103468200c0066020b864500340900071240c0345d0030941c080c461000c86510081e44903800502031070007800c0706041c9044080f0703207003c2c41c0c15001d1903103030140c001c0c0c000007500000c1901a000820401003016070700800c075595203510412100d400c1045c0080c06002d81c1602c00400c000a00c0400e0b42a04001981c1c3e0000d4202c801d55991948ac0c6c509414048841c440140d501248000d103008400e240550041401c56055082102400000e10b0728815811102e000d8110048400d08040c01b81d0140c7d84059040300860690300d9603400d044100c400b0401c011100c80c0445000c1d818801c3c02407140c1c0780220a5948610b88804041006c11720170381c4800b40300742c0e0600c94080e401001a0090066801400498000720b4440c00c0940a0017100050b10fa0341c030062150510062202a038010000345240c0c2e081041e940c040030309602c1c442c00c3c003140100c0d10010888000100405540c000e1050020f0380b825080c6080f00c0c1001456100710907c0c00c4c0180c2d4034420540304200000c84c49400702 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 284739730 1250 284738480 284738513
    0x40b040207050a050c0415050603161b0c060306060320090414090a02030c03070b030a02030a02390a08090d2102210301181e0603060605040c0e0d 64
    0x1072808425464003454078020000c00c88907580720310080c0c015030419000b1b0080524404092502c41410580090f0300360100800346000640e001c05100207c911440104642400354811400301100d03d040010040c0c1e0b40303000e018042030801e0300000b925031092180c1142d0f160b11b000292140d001ea0ba04501041d0f01c41232039103a2007916030b00c0c07540d4400d04031820f06016040820091003005c80920606d414440e244104074030a4118900c1000449600e20403240d003c1d072002c00c0141c0d40c0c6c0d10000301d1802800717641030b4034024140d108600b01c0c18040c402040d1520341000c002440c4030b071800c0700040c0d42d00d0b00003040040c603c0c0d2052001003080e0a00107842003800e441044480305d00300300b150341e4420344142800300f000141c0c0080c507804103418905080032001000d0802c5145158100f81c0000241b040840401e0010b65449102055082e0308400018045081140911040da92820100d0142c0300783d004007031260f0318007002c400e441e41c06481202504013015090001c8400f687c1c54140340304901440c0b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 284740980 1250 284739730 284739739
    0x2040609020408070504050c030702060109050403140c010f150b0a0509040f2a090f0618030b010b0702011403270c100302280e060c011e090201020f010902060306040b 73
    0x102290240d00c90014201a182950090204134904400c1200359003000c0c02605d44800100144991141e0100f40f56054071784604010510352281d1408036070030070214643c003c2d00080891007202a001c1900040382c0c9a44d621014410301a2518022515001a03c9200003a000800c0303030200050203900508071041c4c008100180b008249541e003815a5038003030080e40341c1e142e011400c1034501c3d4021240084501c651504640d01824140400285d1b1068010642848022031811030181d00c2914180003a6030f02c000414003550752030703250040395085001c0417804901c40c45202691211240c00342d070302c201543c401c851040d4000584135001006800d030300d40101d028209440c101e589a10009018000060b030700140d131081080810031654841140006c40b50f0419802c0040c00e81c0c0c401600b07444200304940741681c0e5440d020b540fa004200d8469200319003400b0090040105825902c81c01c882ca0003a004d4480f000003d250041c00ca4007030440c002d5000d80c080c0042420b40c2003d0344940400c1c00081c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 284742230 1250 284740980 284740991
    0xb121f021309020a0f050c060c0705100e07080709110901031503080307021f0203040209040b0702010e01091a010b041a07020d05061302100309030215040507030803070c0b0c090607020d0204 83
    0x200c60360300107030303908031510721500010b04082051784660040e004280714505141000c00250308540c9a900c0038106468483c0081402411300030103000b000c0a20301e0104040085440c10035407191500c010344100300141c0281c0c540051284038500400f0504a02081050b19000048006400a00200d1680a4014602200031002400361002140201d2441d0000c10351110541c2c851103001c1e00107600038075414014824040140c90b154440781e0010760242d2003100b5940c076450104d004115000e1080619820710801030107004a02c030340d440d17055161203240c134910f80c0c8031003c6568620481c0b003161008510207800310141d0042201030014688002c1140f400304e038098868528001090341c1c00e080e900d814180722411860110703040d1044841d08e05040c080e4469540303029459001030745c404140b8074500000101004000e1000c03030040d5601c442d005441c2c0c00d00c070754010b103840d14001085480c4260100400c041c1098801504c183c501d004000764038080e031950a0000c03028440108982003a100d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 284743480 1250 284742230 284742247
    0x60a180803010f05090a110a030902040219030b030115050d0807080f03011502010e010513020108060301060b04030506041115092202030106020a0302100507140a02031908010303030b121f02 83
    0x40c0000c500900a004900c2c100038200410804015006450300d02e840d440c1940c19842c1c00b03807980035035070142d80354100010241051700104019102e80c091032800c180d0503040e18082945c042d80b0612801d00d068000300020318222030204107414003401101d80c0498907040d4000050101c00040ca50944203200ca9410011312400c0c60a01ea0002c3e00078020441191061003035a036824070420701280d10103002400303181080148400c2d5107031810000307410442c0c08000101e258600b504420014900b0f00c176956a207958078140503484140540b011210424400840d503964588141000b00c03a011072910240303000020010841203031042c0c205d040c0c014070381d6540c00b0003031a2141f014600820550700a4070980202c0c0c1340003400c04484400c040c41543c605020320103119170000d00280c21606000001f5940d5414090691a40c000c4a007080010b6940f05042c1340200c0c1c2c401c2d84241201c0c0f00383c034203200c100c5092042100b6500c10703400c1240240e004641040c00700d61030007c0d03801d41c65040300d001032422400c0e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 284744730 1250 284743480 284743493
    0xa11040303080103020102060a060b040b0f2502210705010309030e210f0120070f05010603030c140a0f08090a050910060e010815010311090904060c03051602060a18 72
    0x603030058000c105880c004005550701405142c0d481100c82508210303103400c041200320940910300800003c0140442d4000d030032040501287c01c0c0004a01d8903002d11304144942540301029501d040f805008030404001d0060304050000d103042403081d02400415003400011001880106000c0e0100001e240d0030b1021512a03030099984031a01c1c658203042d2005503c0c99500d00006040d29065503032511151700e03880a445210818010401030019a0f620040d0403c07400c0780e0080407001c3c08651078042e00008254000e106445114441d540c586460203961000c1615901418000352a0804010302c0f04002011a0000c0c40b900d000100044a9a606c460120310881000c036500c07090411040005c0c4045e030f412492007644e01d5024640440285040520b4003c6540d03800440c60603d9120765401c1516884281076072203a21003e07150788254501410414054100d000d4408003080c07900340860111205400514038a202e15002040380ea103552a10f00000d102100c41e44801c1d42810501c80001040c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 284745980 1250 284744730 284744737
    0x60a020a09031a06010e0604061b02060c1b010f0e01051e0d0609053408040602040527010920031305120406030e0613030e0a080d020d090b12010302090a11 68
    0xc8621a40010b0720b42140094421050141d0187c03264000b40010807000e9803210001301c05204030f100d008001440c61000c43d074140a0031181403a80c0c040e844511803540545250740c034401d2426600d820084120303540a503020b0315131801c0c0340e0004000700160281c61080302d1420a4010262103a580381c11a410341c1a0100c444540000d120240c4a1003401180707070750101240400180304140c602d05c1c100d4600100c0c014200c1d04540c03000e00850500003400e0107800c0c1e0645000b04809400c1c1c9841004030a0500c1d00c00c0a043d103070218404c500c000200b14003902d4402c42d411540e03801000349244201a490400c0c42d000200031401c1071140640780c10001d10244490440c80340800809500c0314144030025065641c0a4844078107a4002c20805c4900341e0078a8440e2036440c0c0508008410381d100c00e0104040740d206803c0340000703202e50f02031003840c10b5001072002c11121080d0354000c1d00c980c0302c3c0f004190600c282080c81d40e030420503a005202501e080100c080c0c100ca1010030015000e240c81d04500d07176540 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 284747230 1250 284745980 284746013
    0xb0301060c210507120507061406090a0c0e210304030804051806030a11030c2e02010204050f27041b060e0d0b060a0306020f091011060a020a0903 64
    0xc1039244050700b04007020403903002400d04085800e680c2c00e85040020414080c888002e004030b400c812602d10360380c1c0148101c0d218240c020000b8400004501b10f035010b0403200351221070146846400040000740d0512440e60001003698505000d40c8606081103440700401e01045501c240360380c5c801c000c1c4541040104029442007107a035843d18541002c206404d00c0c040c03461070848000d1410456075a80100e540d100fa1640016a0049104d041002c245400c0420000d140c0140070070310300c0348205050301c115200301420f0a001c1c00704064111000c074241c0c0180d00ca0503400c410b070860080b0303c500c0c6ca5046c01c00a0f81104680c417580d03603950240711071802411f45054864104598103800d028203c1408907019005500f00160b03141c0802c0040358201c1e1480d040501182644d0340400e0084d6154952030000b150840815901e50800213030115136030388103e0900e4444c000c8801980360007801008032401000c003060240c015681c0f00048800030b94881540311081186040000c0300084070141801c0000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 284748480 1250 284747230 284747237
    0xb031b0c0703030f020d05090d0c0305060708150307060e0d050c10180f1206050a0f020a05250206040e130210050d060506031501051b0604050a11150a180b030106 71
    0x12869410081d050805070404c0000319041720700c1041009400100719501c00030243c405116014580c1815141d105950f00001e1440c001c00c400e010b070360390b44909917038054026007070301075150b41d10101016603404892103000c0114214841a803007034601080e80d034180d43c0c040c0054a2606e00c96500183c20f03000e00d03640740c00c08100044000e80c0249a841c0540d8054000d680481801d1030900b2513540e403040780924003d001c01e88038030010354030300f030b041d00164004400c040003503450f01100031010b0b11070380002c1110b0504191031303040c411030b05100e00719560580b44c028052529040c20407900b075496480040100841032020b01452005031694000720340c4041259603600d8440804c2c8201909545140d0b0015124140900070310861260040154501e01da090800d80ea4814180e00d80b540c0400d038000c504829401214108000d00c8800300d66007041034490030280481e0030580080140b20703600891502c40c1580b091040c04c0810303000350302d640c0100d01e100d0720100300540e03607084110607507000f604041d001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 284749730 1250 284748480 284748493
    0x1011071212060b040b0d1d011a0f0f01171b030a0f0e0109030f0302070203070b0f030f01080f060a0e1f06170a0206030a02070804030f0f03080c0a02070b031b0c 70
    0x40000d02d1046101400d2481583c925040c90446041c0d03450280100d5419007982d07030010310898003500705000f604030640700b00a000d100900c00a074400348a0003218140100c80c2050400000c0c5070000c00d140d0040d50586596001502050400110306401070020705503890050508545404400245208403045880070440c0200074003858180c894150080040da8140310103100044d1f00407455001031805c40ca001a2910014000a40760504962040801c2100000c402c03002ca1210342c015485641040401e01545c0d03620000c50760b0350381031811003440d02d4000e6404100f40e404a41c03c40980b4400410441d1204500b07104100300d44080a0030001502d95200820028075030344402e0704040f010007001900001126030041601c80c40700906035107174030f176000a503002080207150079180516006401040c1e042218541007a04085144040e004a001e650000715080c0005048030440699580034040c450708d400c00c0303051107804c041c2a4941003c1c2094003908005211030113402c0c441c08c02c134000d000e03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 284750980 1250 284749730 284749757
    0x60f03110706090206041a07060b03011506051e041d070912021017070c02010206100b030a0c050705100608011401080312040201050c0d270f06050306131103060103060b040810110712 80
    0x8a41211000d075010f339041076120700102d03c000000008403031aa0800c0c42c2d84104800b00404203450a09010740d2000e00860003048400c8840204410302850000494171500c60f41c4c400e0354110854880c0e40460210b007002a00141003d9410310550403843c105030b40400038012800701500340c100c510500103074406902c1400d40da0f0401040b9007000340f1203450080f140c00c0c8030883c0c6a80c40000d004082843d01c40c20080d0800d841001180e4019402009440c580c440c0d01405602810240c8203c0d802503007405a51488034003614004ca0480b4664801075140c1442d0002803840102c004000383d061141c28854009000001e02519000d1581a0780f8042540396800490398034101042141010080168040c8002c907420034240044e034906007490b070303140e0351102d001a110014804500c280b050400c0c0b040506024040055030280400b40c03802d221807070700c5480c44140390080b03100d80c900a030b0240f5a8404205556803101d000010320903961032a010040c0c60310280000c40000c00070005099095886 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 284752230 1250 284750980 284750993
    0x9161e0f03111f050d0203060a21141207111914011101050402030c150d06150f39020901031a0f100b0d0222060f03110706090206041a07 60
    0x580c83c50780c410000d0030b0200205402026800f452000a0404d9400000b1070041e5444c40300d860000c040c1000000d250100705a035504039400072072000c5840940301c480440c1943c07070118242030f140a51900e907d040228036100d00300c4808000307102e282c00c09203c004801490000451000151814103804048114281c00040400d423105070565001d134035280a00005a40c085003003411044202c2e1340b80f03009040e5401c00c002c0c41c0700703107030010308113900d80a40080d46840c03031400421600820740320040e10194154050b102100744800700e28446031a0082440300f48040a0702c0b6085c0340303001003d0b49915040d58046003400c40d0a8009540c81d0181018444d50252451202d96224003450700d525200e0a0010140a01c0d0285007e80000c4910205080d6041c800980c1031340d10542e12035111540c2802d4a4810041c945824025080040d03141204285400e00134040e607031038541d00304941450404541c07900f50062608110032a03120b041044000360445202e100342581d00076040c082951508245000f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 284753480 1250 284752230 284752249
    0x3110106090e0f19020d0201051908060f0607030f03050c0d02040e01030516080a0809041e09020a050102010903080a0c090b040e0109050f060102060a09021201180b09161e0f0311 78
    0x10074082d44400c40d89520320340c034a1a40341480354103031b0f1148450190391005035218010711a003800002e1801e0000119030358420b50321800781c0e40a682c3d24440d8401901805814454090082c000c40c01e06074840800a00c682d20aa600c076251007059810081442914030a90f8059401059080b80c0c11005000307000b01480024406040b00441a041d94908881285c569140d410041d01e000340200d000c80441d1580c0c0c005100b8408444510510450314455034002000401400d9000d00c5d81240e0224295005210f080411038154070b461580396141021500581448600241007080003580055480349181c0500081d00d01e48080300030320b605201c4e20404aa00040138264000514000d20441e81d802159254100e0080700c00851100b1a42c004140c035541c2010740c1c068a0341c6404150060040d52084508505100c0c10140c0d066407550702c040350f43d60455100061241401d0074040245500f03104601c0382d541c11169500122a5035003081c0805009968030542d07e0301c03005400044c0d245802c2501 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 284754730 1250 284753480 284753503
    0xd0308010305070f180203070e04050103054b07030b1023090103021903084b0c0f0d030e100903020c040e10060611160311060703110106090e 62
    0x1c4592080c07802500117120f09500703100b40c0305c03540d0000104400b58400e240008500d24064018002544e40b0b19101d5600c0300300c22001315404403011801241500d4010b13010340c0744003141d40d1941040420600141c4445040f00c2d074500c5512481200100150390304030403502c5045100b040d09421468805503100c84001603030170440003006140180250703507940c60b40381e042d02e4054480381d04000c00511500f140da210340d00054444500480c290f41b409814180309825858503605541e480341c2c00d40304482d4804030a6114454800e1402402502110083c002c0c1101070003140403a144c50700c040803030f2403e0420f54001c280010342c80b00c48500242d64100b06003445482c000c0010021004a528001d450703107807114032140308035140c02600610b80d6007080608070020300700200b08000d0355101d0018288810500e90720155000700e008000b2030459a00203001225002001c4111102c0a1301c1049026449200c3c1241404440316213070141c501c003482a4005070485c0000000d413840c0c8804c841d840d09100420 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 284755980 1250 284754730 284754749
    0x309070e0c0403060203090a0609060e1006210f0b07030b010f020d09060503090322030212070b0405040c031d060105030f0f0a060c0e0d03080a0b0402191d0d030801030507 75
    0xa02403000c41c81411202229000b41c40140c498469200d19404c00c90041d002800c054107210340310080c0100e40d40501081107101088800901c1c0402030181a90140e100f004031004c001005c4c80041851001d29080c042e00c10b01001c000701103595112035446405862420001b0b503540030100195800551441d4219450300003440315100441c0000e062603070034000d050030000044042680b40d0410030035114a10f0450410003695880101c02030045859031006a01c20300d110780b801e405512000c1094030030b9483c00c8040a00c1c0a040c201444050706051003000101131b510003c0103101c02c0c8410210311007103050741c043c26241d450310302014509510410129030351740090150a801c0d450014801040e26840800030401c44a9540203a0300301d0303030544441d600114020302c10010154810307041417007081c61040402101c0c401034148002c82c000c04c02134103a0020300c8401508080e0040c145141e102444400f9050130b0b100c1c0001150b01c1c8a4034007400c0703003c07446d51070040c0104402840400007800f10b050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 284757230 1250 284755980 284756009
    0x10605090d0f0311100b0a0b0915070c1205010504020f0105091014040905071e022d010902040612060f090201050f0a020f2d07030201050414010e09040602030907 71
    0xd00188012054090040401103500c0114081501841a119811012009455400d40d840301c448000c0d1800e440091f20a508001e4045500031880c421360300e54031f0f0060801e0740c007444d054040c2100c40e0301201c410348610360740f0b00300007501003c0304003100907441c4500008074280c1072620601c1180070fa0105010305000c0d00307120005ca2501d500c00c40808e110f8007460214040701040380036007981e10568120360340d00c5060204000390250803409600080c000d044940190100403a01261141c1803804d843e5840346100716400603540c5544620b0061745800d0340009504000796000504852041e800307040c0d22100c504466050120510510340641844c006c03e00000c0c4c004c0d0700090007845000d90b03443c00c5000c0422450b069501c00c02072059480b00d04000c540720010580002122070183c0c1401c041c040c07010641e420741a0301c0200d11035080b00d80c1070311041c2c103040c24280b0700d4603811200c103032072410020300014070344031690350403001402240982c40050760383c1821a151401c0110982140100000f80f0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 284758480 1250 284757230 284757247
    0xc0a06112e0207061e060e090604030203190e090f07030b030120031317090901060512281409070501020f0307020d020f030a03020f160815040503040e0c030906010605 73
    0xe0400509070089070001030f038640c1d5030b00c3c000004141201e81c0c2c14801035180840740c2c1c864000d900281c1500d0341418007001c3c036034a030b160261b500c480c1110002d005800a02214102c03c1003100d04610054243c1815070780c00316100c1c00700b09000b00031280f110100084809101c0c3c131039054415401091020380c024020090b0340340c500706d401601d0b00402142e5100004c0010701440741e0240001c941903010804a0000c0320740e2445881c0b6070041c000e0607104405800001411500130700803200240c190240034429959240c0da4035141c225629a8241011583c5401e549020701b0380c07003003404194820320f1442e094200304443c14501480c41d002181503502c81e1030302400c03002000090354200381d81143e02d5a2041001c1c07002c80c2a04402da0500d0303415228a80e00d00c4200b5401040c600c41600c02e00c4220340351001c0e40005003400c0c07550342c840c2c0782c0c4a410020ba0750100c14803001c005c0d039019001d50103e919140c3c6c0e48420781d5149404442d10302c03007402701000f4030095100a100f9140140020304d016410103940 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 284759730 1250 284758480 284758543
    0x1e01051008131410020901030f0504110907050c1e070b09061b0a0c0e0405010c020c13020d24060e030105040c0b0903070503010f090b0c0301031a090c0a0611 69
    0x1030015a80640b802c10018200702004081030340d407803503103030540300001040703201c90000c1c0d003100440f140800c6c1041c02c902c01500c1184120791040b5003020104120154540900101c5540a040b1500300b0804200d000f515100400022040300e07000c001c5258009180c208041c03c002c0160048810400704101500803170742e513401076560380e03000c200400300c80100ca401c1031791600115820042c0403410010001032005201d20b280d41c450b90069000380b004036201030b005c90300e80c000d1381c3d1082d6101504048044100016a000c0c0141c1030500d82d0014488420070700e002041c100e620413100802e49419001e01c0070360b910030076004494000384c0081c0709034100341e6180d00c52500359018034a0150000b01700205603580410030400240070140c004c2000c60003003008000600b02c0110182c5100100002040d810000003080360704032904501d009001d010304640c00d4615400c0644131255030b1045030320ba8007056407a5040b0000408a58031000743c1c0ca03c1c00f4600b5824803610740f411000c3c2507034130021030744cc0d41c61 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 284760980 1250 284759730 284759747
    0xc19051504080d050f0d05010609210b01060f170108060603070b03060328150b040623010f020f0706050d0609020a1205061c060203040b06120c011b0503031e010510 72
    0x10f9814800c0e107610449407808003602a075030800241500301070001400d241c0200c0740c5401d42d9500403802401400c44942d59036034010308000100440410740c0101310031071241040381e09120031460300316080c2d19401010324452101fa00300080d1a0040704c03c0c00350b50324080056600400c0103654560452074100700080e141d40c0f05e4844d10541000e0014040410200c0141c00d00c2c0465000300d500c1a101c00c4030840f00010602c0002d01802245011070114aa0301001710644030801107a4080034004580c1d0011581501300a42d0803055100740382c4404400c5200b4400350014181da03550350354480e589448201c6c280c502c5588034503030300c0740304000710755007142c1c41340080e1005030307001c20041403503225000400d103c55281e0344405003281903031503620100882900114001c90044000d401c8035201c03a4104000754078500d1048082c1c2e07020515480040d40075210780d40f00c1740410440d000d0103c2c601c0c0c841e6411588211006050103285c80301c100c03000c4e1000d1903094054841501d0503000341b44da020003c1c10204 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 284762230 1250 284760980 284761003
    0x30b15101409060d0510050103060504060509040609020d050307060905100905030d05040302031e07020306070216090f0f020d02031f050d11030307120c050606150a050901020c1905150408 82
    0x107a001500d5800390b120041110100480034a04000d03030b281c00c008884500300d990040c035000904020001075649040c2c026901030f55001402000c1d10346559503000c006204c242c0c800c0341c2244800d015040412020700207071102d14003400300820b81070140c1c0707019800c0c0038008441410251510110801040001041d5040c1599002001400d62070380d080036481c40c02000c1d0001e070f9098104208112480041000c1c2c15860310a400f122480d403691401aa00c80144544615211641110070401c0c2e442a401148485020b0280001d0314000d610359031b01030340d014a1085046680000600c01d40c210300b82c40e0441a0502c01c020b0002d03a0f802d001c0000d00e004421400541a0110050007404a690038011a6011680008882000c400020014000100e820011f842d940101c00c000780c0942823903000c081e100c1090440c0c142c030702441800d091760f4541040324921b04503c24040b00c0b1501cbd0721101d494400c403180d6002d001d926586403100304607a50500751010403030300070700b40010042c0100002d084800e1a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 284763480 1250 284762230 284762267
    0x5030718030210050a03050a0e030319060306020a05090f0f0603130203011d2d0703120e0a0305070906050102160501030e030706090309050f0301090f030305061504030b1510 76
    0x2032051800c0d010360030164001a50240540003601c4460340c102000b40021881501e0910256941216110031501e901c2a0f00d001030f0810800100307002502c0d422847c0c0c1078000400042c2d9540c881d20b81c842240c010025920214900290321886803600394141006005c0490360660040b03000d00102d00d030303404040e203030340c6d03840e01c1d4003040c0011590290081d407222100b03481d001c4900440945019a11020800144c40b0b00c55020f14640303d0b0309014140b948180326080044c0400c9155a0b038042c2d040000740480c0b8201315907c41800e0031a603a2160300801140900c000b0120f241c202000c90080398a144d1296065504c40d200186410f240c4080c601d08545003424000b8554100100c59800c51180c4480140310924099000307081540110320303401500e006856000e030008000c8141401c84108201c090013850f022203090001901c20b41101760300040c0500650b02c01c800618100c8900d402a070012901846104204001074840c1e98240c2c2101c041110b401d50500303e00d0f40054034500c081c10062400307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 284764730 1250 284763480 284763497
    0x2b020918040f1e020312220602030304080d06080f0c040f06140f01030b030609010212070905131a04020406051903051902160b0403020f060105030303160813020306010b070c0f0303050307 82
    0x10341000c28144100741360041c0980e03080d04201906030440303a02c441503440c0c08040510712080e01c40e24101000041c1d0b2543e80045113161142c2e00c8015641e0000074800c41c1180d00e0f0480840c452000740101c03070042c1ca12100415165480e282000281c0f4003900890382060b1030f1040c2085074004000e4403c130b14880646015415050040048000d400d280105c55014411a401e00488100550060024030b03078095405185440b660400c60f404001d907c40c0c140c1c460189111240822311607446040c1d207a0a400b4655140701c5440c02003002c2e42c01540c80200890800310f42c40005000c4400542c03082c00c26071400f0407052500c40e400c0006100390001e500900da80c040340394584103080113180454541c001c99441c9040c542441c0095491940ea145442280214030000845090000aa0740201580d17000d400a20120f80c01c1250a810000e2884007071944151002c40940c0781441558080d043c07507000203a5440c09810240800586641708160210240c0d50400c00700e68084181c2c0c3c1c006c2d0191619202 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 284765980 1250 284764730 284764763
    0x2003090109061d0603071205070509010c0308070309050706050a1701030f0b070210140121031b08070f0614160f030504080d0606020102180a030203060c2b020918040f 73
    0x41d60f0346401041c0c2d03000380001050000c51a08200565510640b102c01070101c0e5032034030f41c111054001c41c11070a0100f8040b1108400082c095500342d644940f56240004c1d21100580f6414030f01755060384004041800060000c103d160300408151304850320380c002242c154550707515000c0c49040e80101a2030368240c103000c100c20398820f210003001886044001c1c0040e203000300d004185910280f10b00102d0415481e801e0070490340d664030b400700c00e6805071101c8609016160104138a00728001c1e080b118a80d0420903000001d00041c0b0301001140640d0b00045d18201048000e00c4040d000740c042d2000d41160300c103003115141d1041c11450101864070740880e03103403140d00d400b0b2814040c0c03c843d0388410b805c1030701c0810302d29415070103440f1080149542000c22107641c0140100541907000c060f4041d000b03100000c1e562102400186294038180c0b61041c10403c01e43c00b11312409290511310710b451500001c08202610b80400442c50700c0b622810b5511032400c07c0d58404484e4011143c0052001d040340f0316808 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 284767230 1250 284765980 284766017
    0x60f0108070917100b0409030806120c04020310030302060f10060e0a05041a040605010e030a060209030a050f010e0c0109080d0320070b0109060e0601050d0b0604050a06200309010906 80
    0x400801c40c0544980f0005100f001e104e8441e038441228000702480d10b03841200038a0b00b0b026038490b0580580b10a4042e44801013480054400e601c00d8203000d114644541889856074402107110340311a26481002e6415403500038140384001e854500c54000c60790078405070300185900c40b4219507035424141c01038002240030880328141c950000754018504185c03442c9a5840388801d0f0a143c604076400c003c000d44071401921042c5981401a405d5402480391800041e01540200440d9000038121080329a09565592034030300d551740c08000694407a42e00b034503002000c0040c18031800f003d00341102810304001c2071071741d0350907450b0119040544409405041e03102110109601082c03601d1915602ca1441c100b4015800c401e00c40c0b080b820385080e01c00601c005990800c1c6010301d0050392560b10701350021207450050607400107450741c032090030000040c4036520101e00c403009048540b12041040280d1840701708242c07054164103603a070820005502907a900206490940356103040050182e2102ca0000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 284768480 1250 284767230 284767247
    0x3150c0e03100c020118050609070906061209022b11011407060b13110a1202070203030f210a1d01050f011a0c010e01060312030905150a15060e04060905060f010807 72
    0x1011b07502c98100314000d205020501a100e502c0400440740155514851b0104513000c610078080029403840f040118403006400100c02e581c0014203808501f1064041da411803e1580841160080342d000e09100700500351884600040d400d007488001094012080c52131803284d000020003280d610310302001150344041031240c00b24051441009100f01803c501c2c0c5081c1d2000892001189a02c002098802c0c0030303000321030700540e010b0007441c105400008040000d41081c1c000d02901c0c000030f101c0e003001102035040144652011301700413503044124491007005070503010070ba065a0341440c0400400b08500c200d40790444540c0d0242c0d41d42d180074030400c10302600910200204d103500b0000340070013015054111a0540f40a40b0000c01010100703402901207a000181c01090380d000a907540800d0500a148154000c3c2e80c13003004101221040007030400005140c0101d4082101c4100aa1030703030170588100030213400c1b000360402890500c0000600c0c00c00c0c12941c0d031810001004000340010748a0010b1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 284769730 1250 284768480 284768501
    0xc12140a1101020f03042420010b0109140901030b1302040203040b0601023315030109050106092003010302151204080403060c051602240403150c0e03100c0201 70
    0x40d036032480c00624154416a007181c166a0061142c01d1a816100402000315400c55990291a81440300350321100c02002c480c50711b0318428040c40701e200421441c0500c0e80c0131205000440006184e0300c0510014200103c20380002c500301e031030503103d00306680b81c1840d01419250000314035206596031030300309401e62844410081d00b0a0001c4244820401813011284c080c440980940b400d21760b443c8904130951441e540700c00b00c0a400e201c0743d07103684602c2d40480ca40244600e03035001c4808011001107400c1d10707090402103c0d00d079941c1d441000094018400c01c2c0703900110725240500710200f0900b82d00745020602002e4031075a540b089485981450208442c449503900301080ba591815080004041d00140300580f405410000142c3c000c80c81941254407404d0130085140742da0b0026000d0110207000300d81d500502e042004101400c680007400580000e51040c21210241d021030408003040c5c488540f01001032081c00399001c401540c010070420380b0444500c2c000140d03d0743c050f80481c050f0030003840 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 284770980 1250 284769730 284769733
    0xc0d050c0d050708070e0f1f2d0506040501050a05090607020306070c05010b0105280c080c07031e02090f0405160b0702040b010228230a120c0c1214 65
    0x10304000308600803c0c0581250341d00b10960741031944e0746c620300b481000100c0700303036034a0706108002402e2200c1d848032401c0c90340c54081c080d101c40b03900c80e0b0381082280401c8504030042e001c51071110440100740b40c1d5107005080b0503078006040034075010000c1c0c494098511824207102001c11031219907229281901d001c140c0080c229102d40c00c102c000540400410b5134207680650920310707001d01c0ca50050003100c00b240c403080e0b9040e104032075503a10304800020792590b000400c0071840545002c40d03071000180ca411400e0201401e4001c2c59407500e6940554030b1b102544c0301d4204503645802603a11240a80c5d4401048902e0303107101d41d078524205081ca5200c01985007000c140781c0c00845c0c5200143c020b89120391080e141000585078141c01640d46154100390340d00c00e8040b1500c000b0300040d0000004601074468072011011707a101c082405052a040c900c03c1c50658070900c021002c0c00001018004d41001c942080b0491000580396121100301c1809032142210341051400f042009240d07003090390303511000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 284772230 1250 284770980 284770999
    0x1e011403011e05160302090a05060d020d1401050a050a0e0a022a010b04050604020c0c010f0c02370b07030c0c0e04061d07050303120424050106031d0c0d050c 69
    0x80c0b44000a000039a1003005140b442007000395a14024402c5030300785140104940a041c3c50301c4100010750303010761004801640c0910000c41540c166000c0d8100d05c00c402079840c20710b0341c145414410000490762103103102e448032201c00c100d14518031642980150204502595520254503841c44003185200740c01c00c298601c480515034200194003200006d18121010b010715200d060810081c0d00585d0f1f110a1036402000e200d4403103600030348204008191380c0c208940c908185400160b42c0180c103102404001192521158440c2040e6460f2212100c0721f0380113100032400c00420031094042c10600070300348241110060148841904494020a11600c2d481840d150038985200940007240346048088207040b0050351402003c80d4110684001500440c20010142d00d80d1002e19006070094690001407600102540164100f440107440c40010200d4907516056006045400c03111041c2030303507189031040d000842004a008072120340300300c440c03141801ca83c5c105141800500c109041d403204611 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 284773480 1250 284772230 284772281
    0x52212030905130e06070315050303040603091b081b0a0b0a0c1109190207020f0303120f0604090c03030f0311040f03060609050112021203070203060f0901051e01140301 74
    0x300c03070180c0e4429282c494041605038100300a580655110041c2600004006050140b00b6800b140e0115407280ea042c900b196200702083c155401504107800198413040e103842401929250294805503000b1004d40403803600b686141c0722104c045e00200201c1100d120520581c1d140742141700944203e0082d9965130340c19441c0a4a0111070500c100c0d00c100c040300319801c3c0c910b4082080362140700100400d100c0d1900c0041100020744c013201b82280d0000410b6181402c948003000a0b25203038440860200c07080c10316a10495909400526442c80785081451a500080c5080c1d00e02c0d049030341c10709116031050007100c2c040d00034102282d069074454202003000104000700c50760003800c89011343ca04120080d180c00283c8143c9500f4010f12400c50001e1903a00c005007081e004074000e001c80c0781d0a03242050700c130b680041c1c103041e019500c41000284c10410b00c003450070300707104168101c2075110880f100044200c0309521520014890044500009005021180ca0079040a446880c0d403c405a10a4800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 284774730 1250 284773480 284773487
    0x70209060a030b042a090e0c01090810020c0a0503070b0f090d050a0507231e0c060304030c030203040e012309070e090901110309010e0d050315060304031b111f05221203 74
    0x741d0b01d2141c0c092188c0ca40d400c0c400d5000b0702c4044183c1e030410028100d04600d02c0c074400f029504c410750307034a1544103640c04140410010f0000e00b10b038900c10443ca410906001030704011a85001d8034101d8180c208000b145030300c503088130440701e4a0455007041c6840341c1072820000140d02d00c850307148101d0703140380782100c80703c20005c2402c55031400120001e00c1301142d20411142e54040e8844c0c240e0304550100003140210f0301032003200d410340b4402d1040320f18080d125010300034841003e91080a103030f80c20304855590040c802c203607000c881005403000c07a034600d0412001071540c0c450100c4103015030713556808501c0e2181e0a410902d50a0b1040500c0c83c1d8070700340302100c1c90013403264032450003440c043d699811100302d01c505c0480b4090a103000c2e01088006100c0200403a56001400480610412802c008101500480141d00b064000c00007001004d59030400d202c40002507800418501045404042d022500007050391440e0595035800b0702c000c102c03030907880700c17541c3e80f50400c03541003031a04880e84c2055070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 284775980 1250 284774730 284774741
    0x3010e0703030f03020909150a0f0810060b0f0a031113060503100f0501020d0809031c09050d2109020409050114070306080d0f08070c060c0302070209060a030b042a09 73
    0x10070ba031070789100407402c00e013101240140b0b40c83c1030303010208001085260b141c00315000c1c468003004100000565541c04155034408996000946580041c0244000d400306441403c0003455118000f5141c40000d0b08003100381d00c100d40ca4032040c90750300c00e480e03448080a00c080d03e41c000c410141280101d525404050580c2e08112141540c1c2c0e41e6850010425a1003603d84c4d10440308107070020503500310500010b652091006000030400c0c0300506c64070461402507020491440d00c00000013a91980c181070681c24158441607150612018030010710450459402d000d4001005400c0081c00c00c44038400030340034007032300c0001400c03540c03d010040c0d1240e806400e400b0b000e42da068034100301071551000c039103480e001e04042150109a9900546000368000c0c032905030720100c2c03443d09043d81410786d603908089070070040b00303000000e17400300d0b1070070440c10082c290940060040b50740340400c40ca1691400203486000700010180740b240c00459002c000d17410600c44003ca0781c4a5a481c1305620340a4070002400c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 284777230 1250 284775980 284775983
    0x90504020f040e06040c020a03080702160e0103020315190903090504051806070e0609010c0614040b0a15030f0206070510060b030f01140a090b030a15020a0f02030a0504030b1503010e0703 82
    0x8104000301e84e2a2a051041130072104983d00504507090341c54400340c0340715400902a000b94064032001403031040070100c81201030204010f203111194190700505107003030091107010284402c24030038050580706030482c40d4241000c03010041034001c0e01d46030454207507805500098000c0d08000500c1b0f2520042c1c58071140031194081102c08580d26240c045a52950200b07180350880c0d010400114a541b14612010800340a00350201c2e05c01407203c05140200b00c02c170f40c01e40d080100d4130107000b0310301d107139006214000c161440c05549150840d02c1e80152560100d0000384188000503001080100c240217540d1103422404c070811603643d60b844012001e500c112800703194500003000200d18034001d4103120b03070b0303408016200300260350620b0401d400402e40d0903d03c0307a141c8600701b00c0000141701d44a003c942483c0c00880562182d40100c0040c2418404007511000c0d5041440744000c00c0e64054140c2d070413250005040383d46511101404000c585841c2c50840d055420004980c0380030400055580449 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 284778480 1250 284777230 284777249
    0x4060806010e150603150402031803122707170c030a05030d0c0311070605041104020705071e030206031b1b2514090402060c030c06070207060503160c03090504020f04 73
    0x583c2d60303802c0003480e2100702c030030320000120141c20805a041c950701455210140344003072401e024034188203034556008060b503004000c800000300001d61300ca8514020031f00b03405030707d1075103140e50401056494110398018503031a44d030f1400910084d4001000441e82c40030014064030000504c60900039100d5209142c0303400d800c2d0505044003001d6100c2c0c403462034000c1221801604240c3c281d0f070307224050b003000f610540b0030310725040c1c045020341e640744018540ca512410040c4040e40c9000c80b0055807803140b40483c100c4460380b040c20000768407888110b036804000314010401034503258045049038001d1502d032452240380c0844034941c0b8500020081e00900305508030401e910181c48203200c03d182103002e40e0080c0c141c01e071000e400b00e0074800300d241d070494401040359040c13429003d821480c42d017100000280c650300c80010301880c2601809044041c22443c9009407031445e18058030f44e4038481d0380340d0030303010094040704400034940b240701000064000100159a60101d40101d401c09401c41d005140c8030703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 284779730 1250 284778480 284778511
    0xc17070e0c040f090e0f16090506090f130606030b190e0106080d110703061401050112090218041505070503060f01030905070317040312080118020702030c0f04060806010e 75
    0x40c142094604803552000240c4103142490807040181c105204529070520440e203146100310b03000d10000888103000654080d1f000d240680f01003d40700090410350003424280180000c40d12064115a800f10010a840401c00c0b00303450444000d248039400a0702d80e8003100d061040c41c80d0f82d503804e885d24030203141080c80380000c0240d03941d08803411842652400d5200110f4411460f004541404403c040c04040e40c0840703589448080544100085603144900e107940148001d41c2c0120305503080c40500d200800420300e803540400c3c10b50f104c0001c12070818034284005001c10001c0d4410203002c0b40f6528040c03219080c001c0002d04540c0040c2c2c0e03071030b1203201c60144884c5070303503c40d20954100ca900940100040c51454441d038048811105010003070641c10000030000c035842201c51000d029481c1e4035a02558500140c1900302c0c03510070100a8200e004000d02c402596000804401c1c090003140c01280e081e8141c0000360007000710b40d01038200743c00390303400020300b5007a4101d6280c4120000c0f43c1c213416 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 284780980 1250 284779730 284779741
    0x308030a0b0a0801182904081201150813060216030804021203120c090a051e040501050a05030d1d0d060e0c0d23011d01021b0d0e06070c17070e 63
    0xe9030905d001c03101440807064015030101d0810101c54102c028018080c0303410340b4240d262000301d100b084030155100d03840090b150200000940045004144076a25041130940014004200240260103d10cc00d45a1400da030180b2995504540f20700052010350200d5020314640500000070444081c0e10074080700e60403000b802d0000c4215601c181c07800d554554156186026040301e50004c0d921a03070005034074440400c507074683c00d0f1645101c0d034402c1544140c440740381c000c0105444058000394020880e41c1c908001c5520005500c05140c41107050a80400e50701281c40210720a00340c02c59544841c0c042c15500a00c02d85500889c1c6003940d01e01502d1024108905020201548003c0101881c5410592041460029450700c804512050021034080325641c40303284890403400a82ccc8440c3d500140c200d14562502c102803c407442110068000d2681c41c5001400304020301c22920301500340064602d040088c0407007030001401c0e440290303d002340c3c0c00480141d0350f442d050240700da442104c10003180 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 284782230 1250 284780980 284780983
    0x3030e15070c080315100507050705042a1202030c0c011404020105120417040320220207080403020310020318010e0601060c05100507030510050a030804030f020a0308030a0b0a08 78
    0x1071140781192108036009407503a03103a244507480102503c2440440000583c503d5a84801c2c41591136440e9441c252582080d09015040ca2a95407100d4850b91504420010100441d1602564004a012000c0007a51103d9050351800011014140c3d00391000040081580c1482c02924200070200c00070013920148004000c080076065402a0104605014613000c0e42c02c40785405031b20500c210720401080c0696007146903132b40c005420490301910000e031490000800c000303444841e1102260b8440b2005440c12410610b01d280359440c0c4009500055400180104001181c005650180c01c64201d85003450000c070094205403050101d42d100008410b10021301400340c40801001c3c1c002900c000d0740380145c00c4d51040b01820085806000311800e0000c0c122441c0311389485800300361404102450604030000b000f1030b482e000184a44400607090000c02d40c01020740c0c0540e50b0010b0054100152030000540500d01d0390710042102c02c0000810001425641200c0000e1900b0790b840c910300c070340380c09226 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 284783480 1250 284782230 284782273
    0xc0f08030906040531090b070519050307180909060c0908060705091c0605010501140f1c020c0f010b091012030e010509120c18060102061602031603030e 67
    0x50740d01141c140014040c1703282c14002d4402003554564904030200345010110402d01031018031095145c2c0d0760484005004d15004010341c1300e5402d2070800c0c90903059420702c0c4070803188030840303404015001c00090340c840d000c2c8a0380b042d409084101c801031541d55000040283c158158201c41482c141008100390900802030394050343c46c108041d140540e500c10048420b900480c2e10309920030341017107254144034580008000c62500030301e004540380d03040c980050324103445800c1400b40440100103a16030200400c0594040150a4066400034008054184040d000c1e070104100c003802111410380141c1d40540c481d0072303000016959020f442c1d8078000a9515050240b0403258003800b0303103010740002481003003105100350050404504114421012071075070030760107443c01012360003401e001521303282c001d8014400c01c4986440c1011403030043c1c0001d4482c400548a140e142020250784c440c3d5600038401e440700f25240000c0858032010b10708008000e440410000906030184051a6002007401c000e01c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 284784730 1250 284783480 284783497
    0x603020a020703060b01050702120a020103111305010c050a14030c060108070f0e0a1d0f1c14030702010621121d01110708070b07030f0903230f07030c0f0803 69
    0xb500040d071840d1280e4015003d4220300a04000d800c01603580140e55001e41e645014031440000c200c4082c461001500329440c40c50f44c90b04e10b0074103200b022180d00c4041104000d9030030a182c44e110b610094503000c1d00d08620903d00802400702c500101010040c0080908843c000b6a01124542c0e640d80256a0325034405018180c2d5421103680c040c02a1426410119042903c644001403c01d43c2e0448040d49100b8207102c10840d504070110210340b091041001c81e4403180070740702c090200f035080344021f020709500707110388031010f00003200240d1024002e42c80341c4d004294002200034584e0103240c800400d00e5070440c084400000750101d2480c581d00c500e040c0e880f000004140c0d8003410303862100644080750381c003a0444492081c1640843e2141c4c040c40b0200040c02c020305100c0c3c5982d0180340c0a410b60500d02020303c20000f001c4c4d001c2000c00c3c142002184003510720a0403120b01081c446890f800c003544a03000400b184550f180010404c40b40102d083c00b125a0075109030140ca0701c070004103840b4441c1062 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 284785980 1250 284784730 284784733
    0x6010804030305070e1906140f2a010905150106080912030a0b0619271a0c060403090911040b0f09010c0f061a040c0503150f03070810060603020a02 65
    0x9800a402503000700d4000b282c40c2040801182c035200042c0010000711b20402d411429107108001c9190421069030107074104507190303030800b807007546406900e005510801c044903c8086a007502c0c182c030741c614450341d5031001c0e0090040d9140c90070a190781d00010015074003010b0150000091051081e00750714007401d60b100c0580350340b240e0004000e41c90b40004d00001d66040e590130524125581d03500082040240380056000c0e03070a0184005403410307006e50b0031802d07002c09401080c1e100e40012030f80101992044000f941000b000314a84648a00070911001c442e84070704421300003850340200320a400c4031040c04041c0903216181c92021114011032148241c480030503c110000840c22901410b555003041c07500a80b0143ca03500d544030106220b1005071011a581c5031012814000306030600c2545009882c284070710745400000400520000304001e070440e5035010000701c50303500c0f443d20f0300c17805074010f040f11302c1f082d2101440c546485070400c00385181858040c0010703640e4024029110108000d40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 284787230 1250 284785980 284785997
    0x219021008070e060a1d1f080415020424090f051c06060e090f030a051209120a02010b2b240501030c0311010801231503040303090203150601 62
    0x240305480c1036102505000c14451002030100c01512041d014002c15503180d41d850003a92414480f40d80d518609804190040030030355220b05805920f044484062035403442c0031000341e0fa807070509114007804106000c11741d5000042c0081c5494251344150341560030100302e0880d8000c82d0401340c4200b10544616030a04503000410815858900c0101c143c0d100c418440481444441d82c03071404407103451300104491403103d41880248030041020620107240b000c011480c0640009010380b607402400b0321600f0104402c800645c00080c00e10100340c26883c1400c000e0344a0581d100f004c3e010705641942107001d40c0050311811902101c00d280300501c0d20b0301107a1070ba2640b403903496107800641000304040c9002d0740c0c0c0c2d0072800c038003182d4411507000f18000e10300c0c3e00a481c00c1d4a45803004036241c8422504001c1800014405440c0c5015a0300c1c050311940407510040028601113809046c814580308a4450084100018181c141e000050b1081c400c0b0155105034100f85d00c500091002904c4060004a500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 284788480 1250 284787230 284787259
    0x50a05010810110702040e07030c23090a18032318040510080d090501080f0f01090216020d11031207030e010c020d0807060617010204050f0402070602210106021902 72
    0x5601c0100540301c00e1400034a00513041e00818151484102d600a1075803043c030b800c1060000c0aa00c04014014400210032403c0384020140c1c1e5a001900d0a03900c104910700102c1c41070081f9911010380f100381d4020200d2200e0642c2406454030001403489001070310910b454803008200720040301c0402d000c0411010040900740244401480d0080521071240c5000b80041180c10381040664000c0b6581d40d0b4080c0d14a0600300018806000a40070500e4501e2072414001c4a010b141a00781c10344084440040e11507408500fa0000b98868200203034120f030f10740c133043c4140059034400e900d0b200d4050741120028070384640c051001d4031a442c0045d000031030014003441603600c610402d40300c042c0000e0413840c0c030891540f20410243d00468044a01d6030361800100314140040d0011100300802000841c202450b04000c00d111240e030b58401441164000350200410030103506445488403a61440c0501001d04140c01d4030043d0207008071b001511900040c8503820046204000c01580d015000005c041c051 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 284789730 1250 284788480 284788513
    0x30b0a020d2004031a01030b18071503020d06080303040309060c0f02060a05120921070c0f0b041e030201140703090510050909130308040b100305011e050a050108 71
    0x40c0c072016400649910049500401216030941d01e040d50541d1280d880e451864060603007a440800303140300812070801000425001546142e0000b04c003401e1040c0d400c425402c490901d25560441410f00c000e40414409443c0d15501408074141c0c0000100b1660b516403204903642e0108940003800540c0030182441280d1141590000c11403041f020120300301466400210345400000000d4006880440d450307040b0525455801d8006140c4806030a52010900114152270b450721206240f8020018405041040740702c0030400400f40100c4500e003403a1541061042e50f889031003a02000b00100701c2c418859903840002a080702c0e4140c44101d80354240060704101600048130603020301140d0384000521743c803011601100790103a580c44070341d2400e008080000907038014107441c4900e011071024900103900070b0b80a58000e50060b08004455403a111902c13804201500010b003203500f00340d10000040c00400c00c5001300b10000708280002d0b521140300c8003c44900344210480303607005000f6141304580 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 284790980 1250 284789730 284789737
    0xf1d0f0319021006091a0a0f0b07030c0506100e01090c0914010203130e0118051b161a01030b06060901020c011202040306060b0c1c08010501030c0908061e10030b0a02 73
    0x8840c010f40c1d102c5520385050004941103544280c003500d80340c255000814448154640c0711002c00c59980084030f0520540ca0303491003450007810f00c030a030001140c40038180201c074009000e55000301100c84915040100d1180e040b01071165100110b0900004aa049a1402000501c507120786e6844142d6181417101400890500f081c18158001008520460581a5002c001074084101114910752400c1d020f1861880300040c0c800e0f5152401f0700b0310040c00e549442c0c01440001c8ae2501c60b84680d001400b019004600711802480f28001c05000c00800d0220030a031350403a8020840105107503941ca0500c04240710720500140140c0250140c51840e41c010419601c1c0341080d0007005041030b890317594240458010b90046001c1c0760010402d0311504100300000340441098003a40400120030b000054a03035001809154189912040d100e41d481e4440c0921708000e0442c082215002e0600c0c440000c80303403100140c6503c090070804000749800c03a006901c8402c0341d40c800d4000c0861f80d51809610000e42 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 284792230 1250 284790980 284791027
    0x30a24020d0f0b0f03010209010c02040207020f0303160302060f0408220506210702010b0a140d0803160e03120a030e0f0304060908150408030105100c060f1d0f03 71
    0x660038040c041001c01240b0070100700c04465000000c0041e40d0304100254510340510700b6220340c0c01003042c20380990740328014446841e4162000f585071070f1144005644c00089a00d02030301880b011621070600e9a030600030022450007038085c0d0380c0d2611010020300c0c074040203c4000e0401da000304000620010755a100060203400640045800e0751540b0000c2e120798084140030300300c80c2f0811900038a0750000d525803500405203000800030300c03568501207018281c240c8961545000c8400c0302210f19202c5003104500c4642c011420341c0e5030718003c02840600309110030250001904590040168180000d8031929452034000312800d1090030038085000c1d0800500c3c42441c0e000750451791b20030280410141002d44840d8039000000b9041601543c60a02c0200101c00f400000c0700500002c55a4101100c0c15a117096544010043c107040b0195a01c5018143c000c5c1528170b4821540c0811256078014464554403000316000c444603000110355415001b00b40780e602d40c00030030040c8801d0707010712480c044e0103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 284793480 1250 284792230 284792303
    0x60c01060305011a01080f160c06060306060608040614010302061b0c0d051e0a03050a11010b1e0f01020c06180d0807030207090e030a120203071103040f03050c030a 72
    0x60703126650b0a09598003c4110711a0780203100d15221030751303004003501e40e008059a00c02c812514000700d00403221505110301c4001d0280780b550100c10701c44240c02c058042d60700000140203640d542e94005006a00072203054074028030300780c5103081c0104030450441c101c4e074005210900f4019940815091040c460801c1890b0b4404ca9400f80b4030398643c00b1301011032500400c09010105121030381c3c00004051003081d03003100d8002d10580c800107a0030500b40e5000c1480c1c3c0c500700d120340c18410729981c0101803a000e40e540c4420707800382140341d8000d030643d1103941500542e5910a2201a4401a41d442407100b10840e81304030140485000300c02c1d50300800c2c00d2058000c140705464401a02e44802a6014000560060300618018004000203020700940c0302042030046d031920f00d506c50002c0892810019005c612a00003021900c0a882041645ea1210040c41600e40c3c85940e0b0318101c000184911046032240114961394072141b6000c61904200e68009103102d94181300c200d5441ca16084418800140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 284794730 1250 284793480 284793491
    0x903030904061211010809030436060602011506080103060c02030702130501241e09090e031e030f01090b010c0f142b030e031b060a060503010c0806060c01 68
    0x9650301d6000e070301e004060700803240021480a042102402c03540300c1440d814010100280000399800004403022240484034410032006407406100c0310030070355100007a016010311355444000030a503002c50b0440c0c580384c00130040c0e515a510710000703019482c407034030002c07484003001080801d0716604000c6c5a58042d00c1928a0005a40d0001e00385060b030340b44c01204d4643d518010300c42403000407800800130034581e2a140a8401d0048002e156118400c00b1018001c0e10b040c40c4a0598060145800540300c0d000050201d0414150b406581e44c1101d1078070f41030301528482c80e0115020180c00c0b07900038007640c09981401e0382040800c8010f048068111410004e400c0e0703203900801d0758281d002054500c60035140304414401d440107860724004a42d4542600c40802c6101d0808603212802c51242806040c00b01c2c0405101640700d045000711140e03881401014180c50101c00c20100ba00c03840303036200c410100030441d141d07800c0c5401c03115024500004074002d01d011860034038108019100c1c0d0132920002252 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 284795980 1250 284794730 284794747
    0x1b1214101205070f0e01031103150c0c0c0a091509050c07021012050f150f030622080c030a2307020108190c05042c0f0601021608070f0603050f040206090303 69
    0x2401c2a03c0c2e000c41176503090080140204243c2603510101d08200f240140005c0200401c10301a80402034401c5030800130024100b040800140301c0710f030001c0b60050414864654800c1d80704060300710241441c09081d4886004150142640f00c0c0c07a0087ea040700b134039403c0024a074288000d54800c803820380240071103c404040801304078002c4030710400720103242407000d00300060f0740c4000016411500e4411f156100c0410683e44000a607160700100d810403c46c41842d10701000c40c00746a0f052009072200350000394030440500000020300b2259031907601c0c031128640303964a02d810a0b0072801c0320071681c0010048003000d50f01c070b03038011034000701d0f500701400c00c41c4000c50000d001c88a481000d078000c90008202005220307144200c1c040e0031121403100041120703404c5108210317840010003c03141c1c103007010042074030350348204981c52100d01c5280c2d130b4030350180e01c904e030080daa0000c0784590000c2480685000c01d0040c800d000d0030707000d03d40c0f03101095210380303540e8200401074000d2481c503500340c4814009600f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 284797230 1250 284795980 284795999
    0x150c0f0f04091a010e1e060403050f0606030c0a12080901050c0d080103050706030b15070812040501050f0a09051518070308180402040e0c030a1b121410120507 70
    0x14402e40d140002c00c8040850b01100350b11450300128148000b14402da051034484c0441069040200d103440031425202d100041d12a010b035400240036445501400d075a004e80001e0f83c18004ea508404468036101c1100030058088842c2c09155041e0780b000040d080001d1060f0045d104d0480141461801c00341114405850541003440c01400500800c004000b4800e05112000140c80603140034013140d440741c404039213240d4030032000071001e050010382c1c0800e116018080c3c400c4004644007205860400c1d0602c01c0c0641750950750714440c009090b010a248480341e2049441e00e5500402900204007a68444003920100501001d14401d01d4100c0482c114000e012030809903200b00d00e4680c0720b000d1010010319010044402602813881008184044400c0c25419036101d2401e8000540d25602c0040190251601040c0c01c280e004007484d0042c8410380002409400302e494a90400c203c0300c060030032220540045d1401d00410b40b4400003803055001d0b204000c242c0070b00407021103020903551840c04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 284798480 1250 284797230 284797237
    0xe1503040b0411060f09060d02070c0b04030309060806130b010212040b0d1506090e070e030102030406050124080c090102010e03161506140607050a021003051602150c0f0f 75
    0x448108030701c042000308220180010748021001502c00c6070501495900501c524416001458810721011910044010240e01225136a5a00140c070250244c3d4401c10314000350094042140800c4030139401048040c032600c1c0355807152000811252620452846020062000105290450051036170000c0e16050300d40c02040103000e0010015502c0460006c50740445007400ca000382410b010050410043c4d40c000c940d04243c8115051110351610341800070340701040d0703c03810590194000b10400082c043d05501070381c100d4200031010390390301c144d50a0402600d0305407a00d00000c0780c51203011980708001c4034003800c04084d041c000068100040c03107025166030851004189581c3c140f050410422031040040007200044160920070103041c00540c9a204400c1840580102d0022460b0741c20301504100c102d6840f90090140030b40c41d13250500c0200584811940c504898502c508030009540c80060180c1c3d1402520080407401d8640035001409940080c202440003141840071404007402a0b004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 284799730 1250 284798480 284798483
    0x40326210c0c061906062607020a141005131a092802010905010212251208040c081f05071709060601030507031404020d030909020a0509090f01080a030e150304 70
    0x1840c0300c80d1103022131003e581440d0005c504000c01941d03803244000036501c4001e0003500c017a03482d030520303030301d000b01246082c1d40000c0140040f505d800319440c8040c0049400354200d64031400610041d0b4441045114805000307100400c84034541d0b0075008607144030000700c0d410441400c1a903001c0a01460309860030140c1c0c8000c0d0642c42c00841040b000c5603004800c0c4001000280094401109a1104e500b401c0c0107543d0000759030101204183d5041100380707099488581d102000e91450070a05000500690040f04d00f2105403c44a4000c1203d001c0021402ca05403000c42110014521a024a201800e0003070145014001c901422140800c200e0005620405818008140901c3d1140005060301c0c0c000e040c54050610b400700c0080d80c64411100294040d070152852854003003d0f103000c03111042c0a0348002e004a202165245000780d102c1c00030030035400203d07020032840c2c46204c8650030103030080c4214646a03104846500000e8010215041072000040020b51260141d40e03411119074400c850 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 284800980 1250 284799730 284799751
    0x11a0d09240b03010b040c0207140312040e0f150307270e150f01050a0605130806090102070606090b030c01080c0d060b0c0f07060f120b0402040326210c0c06 69
    0x20000b42e43c1030921a601505804880c02d100070000500f0194803982d85000d440001c0c0c0c2c1d41044a145030f2001c010a60281d40c0d03020009948030b43d103004d03400000a0951325640442c8100c0003042c000301004a6640503608011701911a6a2411100156840070740c003444041c0c10840c0c890341100ca0003441142c1490320905d01034a80d040d1520304030354480000401c050800e0580da00144055100c0604000584000307007040d40e624042c4101d0800301020641c40104544079100400c48448410740140c03041da0320601d002e01100703888000e44401c0d40c1040da4220340690002341e0341da450f503201304205600300043d10a9140742030705062040c0e080d0740c0260020107000100250680792000100030b9030243c28a084054520300cad050007401091000005121002c1022240786000c0700f10340d0703620070015801c004004641e90380d0380b454410078461102c0019600800034141082189400204440411240111080120b100d06200030310794030003d8280c1c0001d11007804030005a001c01c0125a000388014207 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 284802230 1250 284800980 284800991
    0x3106030c020d0801080607030b04020c1c0e06030c03070c03091a07020a0b0319020c07081e0105090f101d100f0e03040303140711060a05040e011a0d0924 67
    0x10380191810200000300c004102c02d5900401c4203440c0070610079002a035074a4086a001451000980030340a899954101c0340510b0483c1c80313084003c6040c4144080c181d0b15070f2a40504404100034a0340021550340c41d40c440204000f40106200300b03680000ba520034200002004e40b1070980c101081c1001c07180d491400c600203102030944c5001341404e001801c001400500d145066a0103076128265458400c03900e5402044d400300c40714091003558081c0501408407403401c280111109010811050044c0c015482e1101203440c4842c00314480b50f81d24002c4004000d040c02410003500100b03441c0641c20041a0b540480c0d5500b500c081c080542c51000c6000f021891003190502002250010f040084941c0c1c020001000000e401501003082400700004d003940364002814180d050808030007100d41e1141c00081d210305000e03003090280c030030358409041440141ea00c56003041c201ca582a414009422424403503100c07641c0d19904210170710b6100d8a86ca109403c18030f028003d01a20300c4902881da0b40c2c40f030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 284803480 1250 284802230 284802251
    0x20a030b041a040b1902040503100f020c0a030903060b01020102130b070c0e011202010906080714180901032018010b07030e0402030c250206040e100816050321310603 73
    0xa8544012030f140605d04500c1c151030b0000107030b41c0d59440710300d0011081d143c1104070300f0301303040d40e0681d0700e51360f040000d03101800c91525005000e552140011228145000c440d8102c9510510079115030347d02d1903010308059418a04a480240c0040208880c0004080004106010084811030080103a040c0043c10085039100141c148001c0780c114404000d440c074200310744503a0000d408040101c55208281d981d010340c03208182d001c2c44c11103090b078020381201c0001003000740c415050301405103100b0b002c487e1400a503003000090850b2159090720744400a005100e82e050650051001c0742c86801c05501000510003c0303003d90300103c40b101d406010216540c605800d08480c00071418070b004000e00030f90a1a070f070000304540101c0c01018510190f0100003800300300c0044c7c00001402800007200d08141a2000303030440e00743c0c18041c09d03020b802001040c02d202070071031111400d0800c050000a00f080d001019444205104603016400d682001080d02d488101105401001d03001c50758001c035020124 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 284804730 1250 284803480 284803501
    0x30603050609010908090f0d02181f0e1503030d05040b060406061701141212090f0306042109121a010608010f0302061e0d06051309020a030b041a040b 66
    0x70802c2d00b50380d0400049000284681e81104c0d50b800e4101da40482c0c1c81100c1d8081507100c0d00c1d000000b03402c03200d440e2a0701e40f1260700d10300e0184910100003e0350030341c8a4220101c08413031034074420004c0c0218841c011850541e910742d041d10000d940130302100e040540c50b0711058283c59040e01c06507034100300c800900030581032501801000d48054208490402e8800f0010101c515052003409580030703002c40200c0c0300395501102d02c0c0c1820314110444180100c07140d505a0345510010040e40309100c0074040c61800d084c089001480f070b0b5004030340030351445209241d0a00c041c0101d11740408101402d14080b0320510b0200c0e580c0801030041c205006184a1405410307030400040c5c100d80c0500c0480001004a5072964a0401c1580d5064940e943c880e04885520190380c14401d000d11500305000c241c40000f000c0503448042110401c032007403100c0583d114558421109080000f0350044600441400403812000c035103a000b91003060300d0660b40d5144246610b070504181c804075080740220051185180c03c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 284805980 1250 284804730 284804743
    0x6040f0f0e0c01020c0a12030c0b07030b03010b09010501020d080405011514040f050609131b03030f03050106030b130504050f0a0c060305010602030a0906030506030f0714011202040302220b030102070303060305 92
    0xc203000400c5c90405280003c1d090700e1240c422512910402e400a0302010f02c6a0fa6020a0550000e041182802c1020019000d0030550000d02d010751b1920b6041140c510342403084604890042c2c018000340071541c80b04480030b1000070015100c56495902280168101d010314900500c1e004170540012268038040200b0781e10740c4c0180e0030703c01d4244000c0c80690758900703034540d81010341e00745d0311400359a0520704020300356404400001009c442010010038160404465540000c00f50b4040001ea80c0314801542101d10340a031a64010700f03141a486042243c0d0f034003840e0000d018004444429603c280d04501c0c040c14800106d561040c1e00320100450f07070301400307042d001d046640051801c101c0d105d03500412850f8a44504800c0548447c00b08580c4d03241403110340c5501216100342c2d0640341c1c41c0c1044580400d0043e2010b400503101400c50604c6050a00c01c0d10107480d4001c0c8800b01d600c0b21100288050702c00e80c0300200d16142d58440b6440245e500344000d00e0080d00c00e0320003049541c9942000d03410920f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 284807230 1250 284805980 284806003
    0xa090c0605120108030316081306060b0910020f100c0507060c0e120303091c17010b1c050112020f19140405060405070e010f230d0506150d0506040f0f0e 67
    0x1030081c01808540b00811f6403503034a1910516080b040c5035255100c00100450301000030301001e00e841d10110b500d03090078008005010058805407514450404126541d800c0440d054060390800c8620b40b82c0203070070b40c00003811850103140050911406807601d80032621911401e10105540c0040e00201d410801480844d20f101c80001d18154030342300b24000d454890310140c0c403101350005804850b809000d2110f030b050b86445049030024540c2c50318500c1509a01c42c00100101600994807082204201d004041c141c402420b115000803c4580c2484030b403121400c4965032145615040301c42c02c1d2030360580b0320002c0282084c1b0150804060f402d00089500142c1100e004606003001c2001d4180c00c1141c1d100420380c2842d041003190303581070040314284407034543c0100e00351240d40c0c034110f107481c3c5801511254107150020003268449c20100800130002c0100c42e2100d00c028445601d000710700354420350f8020710103800800c03590020104030048440b028006200b065884c40041081d000400c046002d0f030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 284808480 1250 284807230 284807233
    0x403020301110f1206120312070905150405090c040e040302151003080304020910050402070809030f0307020132070602070b060f030a020f15070b010e060a18050a090c0605120108 78
    0x400c000d01c3c01c24510900c0510704143c6020f001150301622446e03820010485d840e02a02e856854401c51000d0f5048161140c02c0050002d04011a880c03a040f960b8140c00c0120740d84d094581071400b0b0500540d014010b02214403410107200000f19201d0b070410f001c2c0304600c41d6020b010404020a81c5803211400030303100d0391191000c4402803001840c2e01088a40294045072680c90783e03905c5003481c0030400c080307401c090f130000d00228000f020042c2c03503405484640310407401e4a49000c210b0000a030389004014020340010550313030907001d10b6102040c0240301424070044103001123000b200b000055900001040312859400146d03001400311301164241c02c141d08a501d0307840c103100d842c00640d4a0b203041002910546088110510568a502c6064020714455541d0780e21445c0234280060043c20910030b01d0f0006803950300040013468a54080419502011000310500605075407100c028a0020600e803003082d9241801004100c0d801020070041c081c907070b9190b81e107401c015507100720140c043e4000c0a45 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 284809730 1250 284808480 284808487
    0x30d110f04090b030a05012f0c03091201090807120f181707030b0f091b01020714010c021801050415080c01030209012010140708010e130c0803040302030111 69
    0x303100c1a90212021900c5240000c1480c001100000c2c1c200b00c034185000301258604940d121180d0701519a0400034840c809103420302d502c00c0e900082091150b000016003d410400085a461800c04d4a18008410705000001c0640c4a0390ba1840da0794400b00d41035a20000ca440040b148552102c091801c0b013400389440c1808140c170071040440c180441c0501c00c001411000c1031030b401103041100000441c1c00401c014001e0425040d074103504003080e07481507141c0c02048000d0540300210540a1000c0f60107900030b0a10345e01d4058072140c200400304c019410007001e03034002005039950440030130942040d503800b0510765140204200c11244504502080e80c0130118081010b0600400c0800840380207080150b5030301d4104c030040f1107844184060307003d89031084030203a084a000190f58030f8640b40825041051006e44095040403400843e01c1350001a803130401484060100981c0135040710450021184c0503920759500150b50445400000c0b00780c0c8041010001c1d03241c24000e00c4010017200d40117030315 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 284810980 1250 284809730 284809747
    0xf0402210607030c171006170106080f1503011e0c140d0b01091502071a090f040c030b0604030f11060a0f050703090e0a0207150b0a030f050106031202030d11 69
    0x722124001e04010615590710003004c1c40600560303042e400d842c601c1c542d01245107003000c95240780300c04e1401084009600d07002c0302c00502d00580280c506072520f43c0c40c0e9100a590340301d01c0c8079110100400c0140ca0400c400111000c03610240948076840d5254030041e9000e400c0c0003032480480301d40a002808003c041d034001103501850f41c0c1201c000c0074080030003180441c2642c1c01603640070711551207002c20800408000d40707020703404581c0c2000d98004010710364111a040008412a002e0108104c1d44252682c0a00c0c02601d071070740c0525545051414049019142c01c0009101c9030000d60041c1c80490214601000300050b0b4080b00000100172200d0724200450382d04001c0c1052044034100e030038030a0000d08030042c90302952640340101400d080d20a46450301c000038501135040300303804403403078180c100301c000b00046c1c1800f621a08003c003800c0034041e81d1a507154010441001c01c01520f195503122004008504003801c5140d040d241d031340045070b40301c0b4500b448008407050600a880719090900c100b01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 284812230 1250 284810980 284810983
    0x60909060b031219030216052409010902011715060c0304081e0309010c0804050405040c08010c020c0f220204090b120102040e010e180607080105030d0314040b0c0d050f040221 77
    0x1804c02c1094600181c41e030100f100c22480454140501414070b00c2005a0700c00401f207007a10340304031040c03080c40303428032519221845400d940040c100280480c00400b5008900e062204a203580640e180ba110b484112400700803c0b056440842d9510103500000350034050158100411070150200d5618402446110175803652a40581c46406041181d4003881d01c0c2881118400d4502078040200200510700b85454aa113a5001074800d0100d00c0d400c00c640444c15500100341d0104422010308072200e655440c1041040d90540000c601603885401d03040d070300004140d4405000074046801002a41c0b0b4001801c000032280403500c01803090303004110600211440900150450f42050b0b103034aa980c66441c201c0b55401280c0407469080e1113000100b040042d48010883d0480e0026000e644004041c03c10440a582d0100011061a80c1d250041340000b200c060203581d1144151420a003842180c141460039242c05079038008c3c0c2c10030710368244001c0d46031043c800101d01e825500c400071300c1c400c11078019 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 284813480 1250 284812230 284812267
    0x10e010503040b06040e0a050d0815010c20060f0d0204030506010b13030609080705010513210207180b0a0306060f0b030601020607031d0111070b01060212040b07020103060909060b0312 81
    0x80b801143c4500d02201000000c00007c0189a030210545a4807a28040010032100c0125101c0c80401c8a0a40701c10303655005255040039550401c1018220f0400c80244034001071141540c540c014808001d4000b00340c41080203804c1c161010031015035100d245062540ca06141a0003030000e2a070704001034120305d80c21100036800c4980c08200072403001c4035810802d0381c600a60502900b154200740800070f102049006480c00e55228860904088220003500b00203905009100c03005a44951410b001804109240d074403140d486640c042040394150000c02d40e0f0424a84c030032900355171504410301502581c20701030405000020303411425441d2030b00000f550b0707810140030a020b065543e55840900070140e018020716181010084c171003500f5800e28100168042d541c1615181007510020940034800b064109800700c155400c030f4103040c06c010340801c907507110500c22814540d86240001e02c83c0c0840c060004c0e00341c084c0c80002812440300c2c0074142480e0a40140c85440c807030401c40b890101124a401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 284814730 1250 284813480 284813491
    0x702011b0809030906120a0c030c05091504080106081020070f020103060302060c0307140c0f0603070306030c0902032502070b0c010f09050609070f080604020402220f05010e010503040b 81
    0x1d0300381a21410003650840c42002c450075040309000031440403602040b41014000c011408041002c50003243c01101119940c28a8a00161041115540303030301e04007a00c0c1d030020f000c000f010303850140e49510150850711150f000f1000e5400040412414201ca03201c0c12050f0403e03610b140d10100c100c160300040710312031104020300d5000e02940e0442564403a40c4060003440d070240149a07a021402009075580e0802c4004888860820b031070b5501901c80851401e0a0348005411084400c1940c003c104080d00010200750815540303100c004040341c511401c1000400c5008001a603c0c14590b00203081c415052001f0011000d40c2c108201e1b03490382c009844400c80b450040d00e41d1301c2c1c54075550824050500c030b034a08200c00d410018048188000402da050103201d021044540c0301d0b568004680b400d5546125a4025400c80e40001f4058106030b0000c21452004041c0703e041e20304d100603d02c1400301540c202441850201c0b2040c451540c00c21400320107480c090a040341185015a641400080000d04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 284815980 1250 284814730 284814737
    0x909020a0203090d080315060405030a1e06050a06030327150507060603080307030b12030403081315080a360206070804120b130b151909090b0702011b 66
    0x210303050518424800d90300103030002400301d40048182c1c02c1418840c2c1080d00c080c42d03590302c0009500260b107040da013154112100034024021020f09521140c00004142c20919120f284e20a00c4800090716841624440e01c0080000100d843c1142001807581c0400c8205140a0200d8038410f103480c0e02689080c81224112364070300d0105c0c400c41c03804030307a503000382e2400900141c00e10340c010080014410142d0311902007907400308866801d050401c0709c0542c4040c000c22060700200300610204400e1030041c52501d0b0311030703584680d042d510320610340c01d02c0c090741c500b40020b41d1071030502080042038010701c8803020240107075400400c1e501c014498400d0303040080c0710f024001d800040f4119140d200994400d03a40161480da02c641d43d454030018070005d501c004440c21031a140000c1d5048502140da0051160400001d0000d07035922042000e009145c01d030307619030014032004064a2000c2800902028100301e61020030320919501d402000b42c200604a0019641814500c00614203500401181c141286c035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 284817230 1250 284815980 284815987
    0x50906010e0d14014101032009010603020c0105060937051003060c081b070f0b0712140603120f1201030f050d0e06091203040504091109070f090902 65
    0x180400c02840301603a40b00300c40d402e080108170480c01e5510550340801181100c0b1509680384512198050160810000c008560b0001031010600004a1202c0c80c4c4101c460520741c0d002c04800103401c4134003680550700081c0c002030b1114a418003070003651740010094a07512160300746aa04e0420403001c9a01e00610078600488810650a040010b00c0681e45c02040800141c10700c0b8140c007046000c1400705440c0705040c610740c00302440c801c2134110b01c40d00d00d111010629102080910348654007030641500c1c203054628541000c240e40104060107004252560301600505507141010340f8030084203250444041000c0100981300440d521341201c811140791560340e41c40007900c800354081e0808031001c030100c1f440003104218804886207212030003541110310640201c00100c44444651010079046841885681c01509106900550048114050741d041c01d49500220302200d0008005a074980c1405080d1705050800e0100c1c0754000a10389000c1880001c0440013810b039410600c51a05d4031903000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 284818480 1250 284817230 284817233
    0x150406030c140a0807020f0d050409050612070b0d06050906030c041d0f031308010c020a0809040b060711210c0609010c0f0516090b1c050102040b1201080106050906010e0d 75
    0x1503082c1102028100d841c540c03144480750001300600f900302c648030094032517010051101000060085140c6005544070b030714281c03c050031480940300c0544601d0300041d000001804211081c0729090260001420140c1c6492203094040240c5030341e81e0020707002e14589402c1c0842c541b0040344d801620b04099402162142080c002480000181244080f02d805003007211298120080003d000340780750403a0201ca410303100c44500f07080710a5051400096805401d2400c00a104080503107900400200000345031040b03807010138103a9103c00c008540304441110308078207501e0441c04940c00000300f111000103002004441c280d403007036202e08151089402013039041c11603101d50320342e0b40c1c02d540c080040584c90f240c41c68075682ea05d1030b5692824141181400100d41d10b03400c2c1c41210040c00004004000001448081008188030079406440654003084082019400c040c003c210b0981c46554400843d07252000560840e105600703c588075603844002d001c50f0741c0c1d0145240703916010803610200380e40c886 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 284819730 1250 284818480 284818487
    0x206071403040306020c010506122d150103020a0609080706120b0604030311061b04030209091e031908041106090d060c050408060c0703050301061803150b0f150406030c 74
    0x644030615120000e000300400c8502d401400c40b0070341c51402400591510070800c540001807121224245d802040400c844404100700442403070020306814280d20391141241c7d041201c0001701c80502000705004204605002d540600203112a1904000450401195a48402d01445590204071060140003414203050788868001d6500410070744d03503155a45800b422540d089030480140d0b005070000120340c10250440d8105c0000e0000006186c5425a402c2088520002d031160000d881341c41020300c28150f260014440b41108900115111100e1b400003140400f9401c5034442003041003414000001d04860f80080300000c1220300a48441d850070218240c05136680000c0c00e034505140c4500c2101ba0008001c02c00e580c078903000c2c2c849660300c0380c105542610500c030b00200050b43c104010454107204200114810b130310503001c0f0002e69074031b8841c1010034031859051b040d03a9a41e40082c0040e8030b82091114014102612070700d08950241a5140280c015881002c0c245520348001e07948440c407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 284820980 1250 284819730 284819753
    0x50a0504050a060906030b030606210102090405010e0103120e0d080a300f0605060d05040519060501060809160e070e04060305030702012601090c0e030d020129090103020607 76
    0x28080c1606030010380e100c8004260140d10b200e58404a03240182ca031f030705c1d41400705509100b203c2c0640701c81c0d501d011000441507c40c02c13001302812155428441d0000c140e449010b00c42c000c1c00004d41030035180d411401c201c0550b51100ada0301d0180a2413002c90551a220b4060f003610407a0031103401620b03441ca0400603954840b150301c0d019141460f41604142800545610560514009500700200042560a0001c45205002c2c40758042414842c0307050ba00120340080d540107203d102a10011900030400e0b0f68107560b6030901700d8140391903200502100341d00014151703100301050003d00610755030064000e4040c0d010300541c44003480080c0041d403103074040c1840c40841c0901400c1000716544c0c1e030030020303102d8100030f000301d00080b582c04200e01020a10541156001203141204045900e05400785c001404540044820b01c181d401d80751201c3d0b542840007000c130316100d400202d031090f0300307a5840b644c1c08000e6510040400c0411107542c51130300d60f85086410759505558013956011981001c2d0541032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 284822230 1250 284820980 284820989
    0x403060203070305090c010e0102030304061107051002280512040c0b270f0a0902030405010603060c02061803032701060b0a05210118051302060301140319050607050a0504 75
    0x140004107101d601c0b0380c1070780140c0c881e40c900006d450b40c146801c801180c000024a1125005078030510102d0041140c0782c2c09052104d620103005864020340741e441c14100b40440040c0c83d9403650120b071096007070080a0321700000d5140e140b00c4d43c40c105071411024000740100e00d90000341c00c80c582c00003800c1000300c02d01103002c0d24540440303580720348032074940e8107500e00480168095007000c1e80068205090400b0103c114a00c01041c84c1d001e2402d0540c884020340008205a440d5900c23020b00002048640c8146e49100751a5800382c101480d02004c1c0d08500b00200011000b02d900800800070300456054401e001c607440302c10f80300800980c9598260140205400032507880400080700c1200d10b41001c020302e4101c0d18440e9800d580d03d0080c04007048903409100c0d10000042c088600c0f03803600391a50010f90b010340f84047e1119161015004900d054000b40c1101a40500114424903546420824485446804403140f40070050540c1c480f511950301911860500c00040381603d0818020002e440151 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 284823480 1250 284822230 284822243
    0x30c020f0601081e0105060109060c050307020d0609051605060f090f1003021b0607020a0f0510050c090a0b0f071202210d0605120c0f0612040b0106030c05070c0605070204020403 78
    0x1035071241c104640742c006540044c1a9801c484070740e07003250704060003010310905058440c1c140715850454140d92a42a608040302c0d103000400140d0300603500d11540084882c010280000c1c0d4441034030b410391a040214100034032088080100300481d5a0315001c603101d81452001c02c41d2034038800c60200f640d00205042041d4004031070862141110780c103502900124050701461719445840300180f0361594800d0b1040390058002d42400008030300ea00b4201e00c0924465002c4910703986d81c15030505c0440f0800d4440c02d000d40d4002034400c8041c0b070a22001c00c040c200200109140200440b0f1150003481000c0004040b00c801c02d000048282c000e101100228180a00e201050320350349856620b40d44c420175581c841580b40c03150110345d07402c00031000902d15280b88005c1461404c1e600800c40300e04510600503034481002c001e0207581d01140780015010b00e2040c42250159414230b600501620644030010003001000d001d0300001c2200c0d012755100b00c0e689805e08075900c02160020901034419904040c146 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 284824730 1250 284823480 284823493
    0xb0f030609010506010e010f050a0305040809091302010305090c010804120212031911040305100b0604090f021c0504080301090b01120903020f06010501110c06030901021318050a021306030c020f 85
    0x400e07606400c018442c0000b41d0301e540d0840105070043d52540080141d4900007102440845070950282c0d000b250024060b28880d81002c13007031400190441d4007201e0088002c10040000d204650b00342c00707100e801c001c059020702105803040b8002440050000e0000d001ea071040046414080c1c000e2085000f15581d1070900ba64030314111034030040901c400090f11002074944207035040710142c12000d0f141a81d60020103444028041d20361800603000300448031394884803c100010707100d42d0f5840f4070ba0500c13210100158403417611559030404080040810421941010708100c001080c04e8105c078150340d001c1e84001606c0080c00012586540c006541c15145c0d440c1c07400c84406c0c59000140c0a071441d4085084800710b0fa02c44d801140c40701c494032260041c0f54810800600e551910401441d40030040d000010b0411020b1160010980c05682c0114040c4000d070240c4038984e981d41c000c056120030480d00c154500302d041031950303001007010b20074282013607030342c10540c07240074400d002e515236006001c801c5444 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 284825980 1250 284824730 284824741
    0xc0f090a0f0605031614030c090a1e060e0a0506043c230105030a0b010e040606032c0604020405040f050d050c010f0501120305070212190309080606030a060b0f0306 72
    0x154421780302542c149402030440c41c000c4c0c1c031404201c40103020a682c51400c503103d84d12203000c140c1051030f1080d40320a0030b40c4040761070748481100420a05607032402c244c0d514a0705001402c0c00700a441c8880c0654452501400035443e028204c50866003403044c20148032000304103692011442d0350301e20792003403950300141c3e000401070000c10064035a40e001c02100340fa48181d0074910640c141c075040e03010072820f00005481030565449202d4140040c140b49281c02d60343c40c0050101c0c1c1c038a8004102080c1d50b01c3c40841203190030344140807003035100d011f0041c1c08150804c0313071682c400d00140028407642c1c075080045e0400c80c4517804c5004e0f036540401161607082a290010b0030f20341201c0343c078004644c60140c0b94020401c4600569040f140381030b0010111640d151002c1761700341c0c81003000783e80108207418480c848141c20081e200181240b486c01c1144480c0a1400811034100d544c02401654440d005009080d6404600c24001075440180003c07008840c0010844408003440300b9035160082208100703 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 284827230 1250 284825980 284825987
    0xc120c0405151606110903060f100509040b0406021608070b010812040b0f0a020f0f070311120c0f040f090605010302130212010e090325050d0203030c0f090a0f06 71
    0x81a0740040307031041420300c1c894038495481d00552500c5910710428401503c049985a8043c800a0101455541c54056150046440c00600f918028525185041002918404000e41c000609012154500e013130a054960090201e4054005006d443e0700145a02ca50600440010103a5a00040c030300d450710224201441e20780307824801c0036014051942c0954960a045089a0940d48800303207003400c0810022241049410400340700e0150b1140c49900c401d851001c001110042244500800d0f0144c00c42c90300103c10b0780111034150051084820058600c107020480c485c2030b10044d240b52121502c03040009000e4024504a0070a040c60920340206020064000c06e050b00e000f51200c0140106108058007207201d00b101c912403142100c001031080800c3c1880351a080891174044a050170800701c1024803000160f540c135152152814652810008144058840b00c142c0d400510305602c1c02a034401b500b44900c1507141840000000ca005d029610241060050300c3c2d5030384621400c0781c0302e10014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 284828480 1250 284827230 284827237
    0x31c0e0d050609010c020c0a0902070204060906240f17130c1d010b1e030c0c060a060e0a060e0105010e37090b1c05010b04090803060406080120030c120c 67
    0xf481c2e500704070f0340311070060000482a594420207070404000b1031818680300000c0d00402c3c002c0b0703802603c0b5400014149080d005010160440000084510390344240243d054010511081d0500c900b032580942c002c1e401248800440381031004000c516903480c866420a8010400c0050051001080204e061100c803d40880e8900242c69a05d0040c0d0702d07000309105078003c4018600444449140184680514501954000d040044c11605060a0012843c180802180c1d42a40c0715a41e080400000c480d45d804242c010000e040b0400c111810071a00e44240d010500402b4188800205040780700d031210720fa5100d001c200201045050203000800021a40310a003028000b001d03005d401007607004052181983c0c040c0014400a0903110b951080038440300240000c1c2c942d956640909400c40d10b440c0640c43c0240e202c0c1980c10345c0e03071608000700401c5a10b50b07045440940c0c54050b00f09501940e000000b00304c0403e005a098496a450700803903103a10480c41412251b603051011702c04101d9215028 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 284829730 1250 284828480 284828491
    0xc0f0d1e050615030405030403030f0513030503120601210b06090a0e060f060a020c01030b120102160c08070612021b07030b0405120903101508010c170114031c0e0d0506 74
    0x2048039803d0458819481c1c2c00195009056074200f00400c00010f030264020700b0300080182002c034288165503a528411034000d40c0240c5107500700103014080322111806007542f240003428000045040c500c421082c04c031075100203001140c0c1c0c4000c001c00a80e90390013690b41e4440000c1080500c0c40e01e49602e608140d200345c0d90140914140600600c0f0340c507004003682c115007a26802005802402801107024010342d1544540000c071000501440314001e0004180d00a40521401d91400c0d07a0700d4200708115540d40020590382000c08140f20f041e6004019192040d01010056111210014444040c03400401100140d200c1c1a5002040081e0012a00d1189004ea42680e85030010310081c00500e21400c04860f501d600003c407011381c9040340e94481c0d24095400c4c111a82d1094884650300d08680b919902c40300854480190507c1c4502d8440781d0074050220741607411000f260540c040b0380d482d010001404080c1994220200d110ba201d1040044030100041c0804503504081c248151541c109850 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 284830980 1250 284829730 284829739
    0x2101050102010939140a06090803040b07060212010303080a0e030a0c140a050d0914060405032a04020f07050c0d030806011409040608160e0c0f0d1e0506 67
    0x88560040c45030003200c6030031000001007002c41107041600c0c4802c01000040b6150b1400c8450494402210180060007040711182071040c0d0080410422051a034008010845032004c10f03c520b07100441502c044130140480c031a02c9004a181031800382c001c4040528480001e00000418554403151030f034050002c4a008105000843c08119202c0c0b08001040e0702041c90300300b0381d42c0000c40100d845400090717003030150354041d03203030365219030030400040c0d600800603052000c18040c2f8006400e007043d540008450080c40c1c20315040109440d41e10ba44020050078015490100d482c4600300c41c0700e611000010004c5554030310081e000030142d0080ca01c20349a500c80c8052141141c1001c0c1000780307405405840c0c4540554406004603541030064041111092003440001165211030081c10302a150101c042c002182131180c0800e43e00b00380d81c3c42541c2d9650402c0501c0360304421102181c85109420949030398800307070302c07500d2000b500748600303411910340c10b600c910800034000340d000c9802000c0841d0f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 284832230 1250 284830980 284831047
    0x5010203070917030a050c010f06080d091d010b09011b05030421020108010504020c1e030924071e0b1e01080304030503030a180803010b04030312051e0403030f02 71
    0x4401d42100c41c107182c443c40b180e03402000102280c60156025140050540c80042820700003480b501c07058800c3c507030042010341d11038007128025640040c281e001030550000350f0f204441038004001d0354114103100b80c001914000500c542c03240d10905c11183d40340c0800304010005000340c83e10b1036990b8007920811804200c0307209100c0003561900c4802401540594408032903900340406c102c000e40c401100e02c0040d11074001032544400c81030341d901049072140c601441d2120070700c4081c8565007440321080303070481080450614021a0344410380d010340750407003000e21021104c1070650440000040b4090184d000c1c0c0c004004840010148144107043c01c11001003080c0d0303030344800d02c1e0750307018600000380660010701c0081c80b20910b60b40004901c0101c09051800315140d40c95480390747d402030f08110f100c50000034062040c541c020134413031070251103200b00b00030520342050845a001c4034034520b05000030040d00400d017418460340203a1100c2145100442d91007201001e0f6851141400181420308820314 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 284833480 1250 284832230 284832239
    0x60901091a120106020303091903120b01030f09110f0a031e1b12060b03060912090a03060509100e0a0f020118080f07080c1c0b0a060b07110315160f03020d09050102030709 75
    0x12000c040190315444044240b0003000bc510080c20b8283d81ca81d0402da5240043c0c0d451035054022025424001c0150280d40b041c980280f200c900e004841242c09006007000810000d582e10103100d041034080d4081c44000e8000703140000b000940050003001c101d00d490008070f14603146203076142a40f8404d0b4010043c0100740c0d000d02d511414102c62000054008400212096549500402c489400103050240241c1c8962301d140c1141d00c00e444180450740700801c1022038801511402074103080c00001810340c89416a0386c5c5400c283c030f19a00a0401c00c12210044c03c06003840701040240c414541507507a1a5261003c0c0e90340c03221a03110707540262089583d01540783c1403941d40c01f6a851015180001fa0004544a01003040e402420800b60f4a0360713010005400c12200c4054143c051150240310140c0100404040c5800c0e6a0903032060001031500a010312200c3c0d034040102c40354401d0500710000021284142c00a02601d00201030746820000003404014040d80110711880980c0c070f40104c1e450b00c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 284834730 1250 284833480 284833513
    0x409051806010e070e010201020912030702120303010f03150905330112060c02031201030b010306050106110c01031a0a030f061b120f0609020d05010801050105060901091a12010602030309 82
    0x30f100c0c55500c0700c4041c010600c0c0034404ca607032000c11281800050304d450b1404d40482c20221544e120a1181d0f00003191410851900d0030351007154480c804011829541000d0440320901d186100c0101001f1548119a0b03040105070805072103540c11506882400c4541c0a0b42010102d6058100d40c0c140c0310394070400407002411031814180e030f80741e1a88054002440cad17900c030010220b0540d00b40035880203002c12038404016120040c00395204107102c000c80c2d4550719200f000e81798113802c20030901c40e41d07140c503690ba00780009191042942c24600481c6c0c15910b09212428162403481e0036812002e072541c08810b0001d0307100301d0311081e88100410000714104a107061429a407403010712001400388400301540f5541c98001c0414000324120001e412a0b5521703640307049a000504070306a00b41c43c0d000401507105c0a204e91801040e00f901e141385000d691500007480c80c0d02501680c40800c04001d01141d00ca802132086e00c0440451481181445d40c40d140f010303549400807115000c10348102d4004549a81c02c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 284835980 1250 284834730 284834743
    0x1902040b010921020613091b03090503030f042102010207020306060114031311040903030c0e0f062a032a120d0b03101a0f090402030a12021204090518 66
    0x684100765110044030000e07050400721100f40c02e0f688094140942c1d860721400744840c100810308401d00050240152040030341d800070300780c403400030300d0f281c41c1d270000218802000722079100303146220349106a525480e14148507900041c480c800c0900c0ca040c0c10010940550041101c2802201116079503541c803401101c40080b230044c0009203607801e0000c6610a0000e0440d0740d6654460050646032420000124085803584141a0000382d250b940301483c1075003008070300080140c00e84040103143c5443d00400d08602c0361903000c4400c075404404d98084110030601041c1a81c8005084c3e90b82e0348003903264441c0c0e80450407000307041d51401002071050b0800010304234441403904410359080c0040c11030220001e01c40004602d415029807039190f80040b401e4898001c8080c40004078110f4100c141c4188000510051403050264144d042804003699000440c82d0300d40c5e51016071000c40348108a8100d00341102002c01424217040418003040b04406500310701d109040c6182e2110f544da68600c00395a0300d14 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 284837230 1250 284835980 284835989
    0x90e0d08011e03080c010b091611011103011a0705010903080609100608062107060906020c0904020a0b0f04180209010f030212040605091e0f0c100212070f02031902040b0109 76
    0x101c100c42d00f00000f41201c4081d2a181e03040f0f0000080a000328408100d0394541100e007250980d040501000040d5009400c82c000e107202c110003008407845103100303c07509201c1800b403100d5510030303403020240d42c400c00310807124419403000c000d005601d090314010b4403001064560a100c0c1d040940050858054208020101c03002c0b030761120082e03150407061050f00501e18000c04c2800d43d10380c01c000007081d02001507000400d0385a40c2c0000b41450420003d0510085504d001c0c85142c0e075209120141e40c9404151083c0c4040b040d1603030741d988070b6041c000814410b035030121510f0061990b080c0c010700720650107405a44e0080e200c00c0401c54001e00101c4c120720079006e025030074402203804540401e5080d0300055001e20074078101c441d8100600180d4000c0041141100c5541c0d00c103200410403a0021b02032082111000d540caa20b100b40390001c0651185810302e0b1401080e5000b24020051101810300300344590303000b03400d4400c0392200144001c1421074a100a9000d0340c10801110400d5121356588800c46 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 284838480 1250 284837230 284837279
    0x6120212031306140705060f0405060a090f0209070504150c05060106140d0b060409150504060b041211010905060c24150405040212191104090c0e10090e0d0801 70
    0x25040c21804e071200e482c0c42c8076400110000f4050407002441c1001454002c40f81013010311458641481c200c2d1400c5d10003010500442d050207903442c0007036040901c003200c1030743c1203a00a503241c0d20040216034901455001559040100092890098110307191444140c0501c046c0c4455a880b0041a240300f2084109208065010803c03420301c0b0132694080b045580c40242014903243e07072a142c140c00e030381c5c03d5a001000948012010807440c0f400780300303440017000c04904c01802c0600d0440352806101c1d030144003a021040d030203650702560384204141c2c0064480100202e44070ba08074038400c1d07500c910009076280c584d014403501245621850444921540c9280030741c8001000d1007061101800b80600107c2e040407801d01d111f00000020302401c3c0c5540d0360300d00011103003c3c00742020b012050b03080c03082c50700407031800704440d02180c0340b419000255080ea800b416000e0f1600c14241540c80b459902c14400300349020f420b1122140003003041d0341ea4807423a0340c0e00c0e415030b6291030070300c2c03500400c0f071341081c1c1036 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 284839730 1250 284838480 284838517
    0x702070e310506100503060a0606080712090209100603050703050105030c01050c011103010b03040b0c030903040311060d0518010c17060919060f0510110c0f0a090612021203 76
    0x103855204039507500100300400401e0401d0503690b1114506007040c0d03600400c0c0c0c0da0801c418840360404000301c0358818411a01400028030341503000d4081c0001030107403001c12001440e64000e111aa820281d66131768003030700b007000c070707283c80440781790b0410043c020100064100000708a229109000e040d0507540000d003d05419601d01d801500d05901005001d455552541f50665541811601641c028031420b490140e41c0e181a1a00d2080c3c9440140320241800040c4240039401c90004141c0e800d0700d078404214011507032047c0014110340906115480310f5410300041100036404035581201c0c1c04240c40003400000000035040e00d40c0302000c0d0fa000c54400716a00060b00501d0003400c440c0d003003a021b002c686c1182110390700071016600e0541000440d400941000c201074140010307212100b901f070b880c10010700c4858007080c589411850030014032a200045c07011000395100c00d60800101544a420040503030b035100c80c000300c01c042507002c0c0c0c4515448030241072514808011220450000c4440e00c2a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 284840980 1250 284839730 284839771
    0x10603050a0b090702071707080708071707140409020117040303060611120d0f060302100e0102071d0402010c230c10030e03120a09140c0a0902181c060908030702070e 73
    0xa191440100c00c4400e0312408e4400144040c0501a841c05042c2c41e0002d08811400c101650540c20305090b540d002e00e40c4129003c11074581c40003111500c9420882e00800c1010080c00122000701035210340342c1c285040c0d4400d0100309505035100c4404c03034426031501c03591528148421a15413803044040500341c1010000c0c0c4030760030581c1c0c2c0305c0103070803c3c03401001074801d407032f500031031074030149a82c2c44000315280003100229980c040000000808404600c148401c0445501102042c40580003c1c148803140041c0d4041290801d2b200b040e10305089004030148842400c21503035a11034001e0b05d402a00003800e107181244c8a40204603142144c24015460842144011030204000400111100d17950b0300040300024841852403581a4541c0300030806101c900702048040c0c0700c581e1142c080c0310b1040141d611201000384550f40703140701c11260111400c10b08075580348100c0112000501191810854804201603c805180100035a9003210140c80d03c80b10b0b07140800e0815185807085a031a0020b215 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 284842230 1250 284840980 284840999
    0xc082703011a010c0c0b0c06070e0d02010e010e0d06020f070c05040b0d0201180305060708090d0c0b010603022109030c0f010608120a0507050d0e1002010b090f0c12010603050a0b09070207 82
    0x42c0c054800c03a160781d0b8150341c41a2011b22600a0700286007250030810a200e0601c3c0e11102404140c0c00407240052044450741c00680794400d2050340c181804000b80890050b07985c0c0605454100c1d4010030190758400c0961a0150642e0200d070040351041c001c041c0104071400c1502c00d41c1041080608003c07511203098005542c0500b0303a0b0807020b1440310369030011000500521003030340101103a413258091810841c060324103041c582c0d0f29000c200096810841c01251801d51200c0c11a16241001a5289400d900101d0060b0400074144e00d401c10034001c0c040c40400000c010a060020341c4d007501c0c44006d222034514243c0b0180d1255060a5000c0242d00413a042044000c000110790f5080040c502003040d9107250800350381c45900740c0410888403000c030340c50804500e81c5040c8a114402000b0b00030380e0400203074500902400400ca80d61100b80019000c18081049501a40014514003055030f0340d540020050601100d07100a42814010a04003508044030070501800c09500030300140c50402d103209 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 284843480 1250 284842230 284842247
    0xb04050906031c03090209012103050c01090203070f0e241507050d0306080d0207030305250b0a050a060e0106080f0c190203130f061e0c082703011a01 66
    0x1c6505003e0a18842c041440d140c107003101c41c80b041c3d01c0118003654140104002c0282c140e2100340704a1110400003c08060600d01e196429850300304552648400e20001c0c3c010105042c00035014841e42402140c141507401200301245c01003040c000c402d558025446035410742001c125403051200880c04aa1858007500b04100188003000300e605114950310380724a00034000c014400801c4c0d41d01010300c0b034040cac02d00010030380540c02c0c0001c1034001d2a50b5401003032407140b03e600c1c0f44a01243d26252a20f03140c020b061441245c1c0040d0450301c103090000d802d03001010160b035001903482c6042000120010b6040000741290040e80f1840040c0d074403460381040c1d00310010030302801c3d90010020700d41300c44d0512101e9000d8401545c019a25140da03120040b04c01c44254101c80d54000803114100482e581c00b002e40a0070344c20010000c000001055401d032480200181d00030000c40e40070a1001542e000b100c0d0181c0060915821034000450b05d609041c00c0300c0745003424846400c2802c0742d0701c0b0f81d940074031f07581c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 284844730 1250 284843480 284843491
    0x1d101211070510110d060e06032506080613060e0108190f020108040312020d02040501020f03190c0302100f020d0b090403050306190302040603080703110c09280c0201021e040b040509 80
    0x70245045d15001c22401100c00b80d03000f031540202c0d16014810b40e0305040054001c280c4614900c00b4102d0b41100d80310a2202e407511480700bc0001c0710703001a000303444424401c0b055040040d028045c494803108040002d581c04d0084070814801d43c0f0b080801203013080c880b06a0140c110900f01030040751500110b41092000740254140a140b4a4dc000010514030050428040a80e0300607151810100024180030348c142546695600a005c50340c2522414400587e2941050408040700e030194038041e401d000b03541c24540314180c5440503100852070541c00508444180000c20401003104004004c001c850546010f40043e0701800058540d04081101450521005032640074003540c0350b0025041d9015038008940e00d4102160b07480825811100b100600030400300503111000880c80800c062a100405081e00701c4c1c8400c1412181c40c0c0364000140720300e44452403d100801b03003c84007038042d6008800362085104200c2039000e40c8540c500a0b1004d40c4c01810003549054644003c101c42100040c12 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 284845980 1250 284844730 284844761
    0x31b07031511071a0118050f0703090201140309160e0f07030b0a0e09030a090e0f04020f0406050d140d020f0a080a090e190b01030b030a031d101211070510 68
    0x30076004540c0010040200c9044d015540e21190305000c245038040a01c9507000350003900700700038030480c110840c1010b54000380d5458001002c12860004840c8100c1c18640c51540c01d034000700f40102440041880714070701d2042c0c080401150758039407601c03076030810441b043e02d864201e04010034510741c0b01c0d0b0424000424001e00c4084403640710b41d4940740c40002510400b90360b500000f402401940c010202e02c0c0100480e104450561410b6074070300e0010316005000034440d40c0d601c0c00034146644e80340e00206c090040a0404010445180b80400e200c0d40d21021402c040c0c07040e150761071111480090340104a030300700f2000e8180c8030754076a00d20301141c10600320001446070114021074520203c000ba1480785685206403400c0d0030072018208200c526910302d075410181440110b48068a0002d82104101e6140c0303008200300c12168280d01041d62040005580300d0020394981ca44d00f0390003001c081030610f00c01c004000040400795049030500c16400020129000241c0801121340320754084580c05004e01f0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 284847230 1250 284845980 284845987
    0x40212070510110601060c021f0504150305150307050d0f050a080c0619020a05120402030c030607210605101812031e02060705030c07020406090509031b07031511 71
    0x800190b402c42e01007555400040716151090511402048000d0050040d8284002045440d80201d0b0a40d1001c0502d201004503803445100309c0b2744550200c0d802070103420b00c261000c14000500401a000607a41e0f20221042d105040e01c2d17034500412603a08485000703003031501810499403000300341c502e801001d41d0a8040e51844102050449004001c1c0410050140900740b03070002642e86840e01d9000c40300f070b5151050181030900c1c0e0308801201c1e5484e10500c1c2d108a80c4d44e0b81d01c0024900300d0071080240d058021502031000442d00001d0a1121040d4450305090311024003900c681101c185116199010740180028061a4080e0701201c0d422194100d50400442d1110030314414202040c00480000d0b40c40300800840c015509980340f1000118809000d00c1d00700064018624000a00904040341c0e00013125011591a50b002c2c500030300c41c20209102c039182ca051010713100d410607200d09015a038800812000f5920200303200081e42d5020500408503002146107500810404205400c940800c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 284848480 1250 284847230 284847239
    0x406030f11030a06031e120c0213061412030906041502070f03030f091d0a0e0102071709150703050337090510110415020a020901030503040302090f060904021207 71
    0x110002c600c1603100340000305a40b4510f180c003070091003840680303801840e803250410b0006950006080e11003c541d01d8140d4034001c443c00010380c1e480242110103800e51514000148284060403070281c000c00455040150381c034012600e585901c581d07030015030301003020017040c845882e9403445070300303000910301c101c0c1d0500f0b8032a03600b255048103a4000380e0100d201d07815a051810b5204400002619010604801c1d024801003007200402002d0254007460741c4803011000c40807000d5040e1400907410611040c8c400120400c15455a030200090501480c200e540c825910754454086401d0713203034980d07600b0b0320355615841410403034401d0460f265040c41140c402201c6407401403624450388409503c00080c00b15151506500e0710303420000300c207612030a0466a82010200c20141e030229103180403501160000001f08a090803403c54001354064104000803003404030001c090030030741b03100b40e80360300c0d25417610908044030180c03c49805078060314000c0010010f0402640d00840030348050300b140c0c51151103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 284849730 1250 284848480 284848511
    0xa020d09080d24080c01140c0102040b09030c1005070b0406110415030e06150d050c03160303020607020a0b010915090c0e0306060d050706180f06090e0f0603030406030f 74
    0x101102c40300c0d03100c03040c81c55003103070350140244201440c00e08a8900e0740b6000c04a51586003612003030703043c004212115259040c070781007102c0c0c03071401e240001c42d62a1740319008145180c01500d00e19000341b044054202203420f24003514051003000361100d81c1000d507035a585800c0c0a00003482250f169884036410910800400050005840c0126981201c0e03072030200d0080450350751a100425a51041d402d0242c034840b40c6003042240241680c0e40150322105044c0790f40750000d0190502e4052040101c0c2403145810f2800c00c1c0d05880c481e60a86030562100c01d400ca0b610380308070700302820703184103440100400c200d581d010160490f06107880005a0340e5a551030070413590070b00101c0c00402c640f000401e0a1b403405005041e8000c104840b4002e1a07038558442e00d540307081d103000d00420b001200301105214401c3c4240e1000411035280d00b01c8025469100041c80444c1c141304005081c1915008901c0c100194103505101c0c01000d0011400c0c185804400c0340030b041034426011000d5038640040380718618 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 284850980 1250 284849730 284849737
    0x60f01082a03011a010806040b010e1c0b0c0403050706020304062a050a06020903151306020c07080d03090b0c03061f0e0a090516110a120905030a0506090111040803030a020d0908 78
    0x2c04550600c4d401400800260a8120082c91203104514101c4508140d80c0c1002000f1026841921840a42c07010032528221251090302b0140c9060b41c11402c001000c3d51000092042d24800d6060311400f55403000c040c2c0e030b280590f0180c1030115035840f86000c0c031542101d003d0408074038904103004510392240c480c5818403840640a4840c180c0000d0301010a04040000c409000c94280c2c0c1090b01e0b2800d00c88649014401200052145800040c2000980000c00c0150050090071054540c02103c13100054000c1072007200c01c5400210200004640e4401101528031541001d01414020000c0415104801c100400c610090245980d104009602c81c1000030b13025003160f082c0081c142c1407414400c01340000c0d000c400d40030002c104070344070144140030508104156004074903100214201d88250381c800c2d000e4100a802d0301c1050808001d0020000d86103001e0380c901402045001e201d0200b0904510881c0502e40d5280c0c0204003085c103060240c2c0c000e1840c800030031000607900201d13559801c429030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 284852230 1250 284850980 284851001
    0xb070509131d010e12040b092101090302010c080c1912020a030e070e011805091c0c02010305420a0303050301031104050f01030201110f100905060f01082a0301 70
    0x42d65618203a0110409100700108a102070001304000c40c2c160190309002d10940c05030701c205070004580040c46894607078001c0c844038018500c1c0c40b010410040314a00034600b918096005600704103840f01c0c074500500141d4041c0081704102407070b08800c06070200c0e01c020380f044001e0401c00c80c00344c0001619440e101074848641d59503004154140f440040600d0b1005642001078007810603401007100e40032500702d68002e10100d020104160f41e83c405880d0a001c43d40303200952010132105110425540a0203007828140700741c03800c200da13469079440b083c00c030b11907920340c40443c451034294900a03100c0c141d10302c0e0440c0c88065207a07080b401008040b5680410541c01240861400720042c0208507506040030360201e016034003080fa5103419094491500d206110207030500213a960704c944102400d010032501c50b0079020882d0402402002044018a0b011074152a640286d2010905110520800c02d040390a118003c21921200d020b24070300307072000215003110019031055617400329203081c040e44036082c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 284853480 1250 284852230 284852261
    0x2131107050106080d05031b0c1b040f05012d0b040608040c0905090a060c050d0509030a142701120606030c0801080c010f0f140d020717070b07050913 66
    0xc04152600a0940300160441d46264000314403500c0e18580c0103007070306c0d48119918042141c110300c0b00306c0c0ca1414490380b070f03000141340516400600b1403130302c0120703050300c0e84000e4074104440e904150b8800d0860b03000f8001c090704102000102c18003542000c0041504982601100c40050340c5c42400c004250301c10340c040c101240c032180402c014804000c0c00e42004290b00f101c00c2c040c0e40340c6801050780715400044003c1886649810150100c2d1252003600c500012001042105003801081c00d681c0c1d401518282c0c0001e0123910450060200c0402910b04001d079509a01c100c009917000341c40c82c82c5203050a000e040101100211041c1ca0140c0210300003040d540c1c4001a402040000003041e00308160800d502c6913110700340c0c00000303980c4081032501c5034a5901c0c100b18000808030045a03800c400943c050b0305070704013007101c8d146155580c1c010000e185c850303101640800c404503d815a075024141010b0075010194000441a900460007442e442c0303001005010400d40481161003152103070458118072 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 284854730 1250 284853480 284853487
    0x51305220305120403050c010504030e030f010b01050d0e15070305150a0303051813020c0102030f070e03030307080a02070c080a05070501051306110a0204020a12051608060904021311 80
    0x650510826a0000503800e00c214250203031a4a028200d44180c45500365141031120001d018076100d5020361360030912a078000d00032400c0c9814010003150105203c03070301c64016500362200000051041110785401078503070a08140c0d135400035000402e610402d0180034058140349501000360015528498a8107482c001103e0508859160700941e110200c9402890703a5441400881d8216040d01c5250004140312410700782c0f10340101d041c40001c4d41c0d165030141c0c0040f440c484200d0b4190040c522441510340d10341281e94541d00700b03c400740390100f55160942c000300042007035984599520b1f548401d14010140c40d2031442d1ba51003018901603130081c5207581001202404010040c0001c0340206024a042c81c188454a0b20340f086c83c02c0e1900c42e030f0003401200100e1401081041c4040000306400034001c5440790a0008080c00c512960350781b0140b181e01d0304001550b80704142000d4101800036030ba5004d40780d6900810310616000103041a64803400d01002440d080d040c5000b68280301103881c0c0c41684 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 284855980 1250 284854730 284854741
    0xa0f18091d07060503060d020402160203030d02040812031605030a0b0a090b040507030905100902130507030b0a080a0f0609110a03061b0509030d0f050c0d020303012102130203060a051305 82
    0xb4400b0703c0d04041c04100301041444030940d20f1a0901c400990126401079540d03030704000a0300c0c0240c400d40000d4140c0000725044207404c060f507010303004850724281a1011000c0c41c907003402d8288003c0342c1d01c00e540e298481266021074030a10146038460840100025000300d00c03000038640d010242d00c40c050a9407100b982500c141041d001b401d811008900703040c04100c10681d6125100c034080201083c0c0c443d6207040c001c0c00d643e205001100244409182007080c5e040c800ca000380900741400c1194012400d00200007112000090040318041c2c000d41e4004a105081c0c1d01c40d0094000c0c00c80030b484540103603161811981e922480ca1005521030003001454145102c0c0c980c00c586010b80d1100e05002041c40509895100440d0003d0f014840d8548400044103c2d24181d9507805a206030005a208203080c02e4007150b0008001d505a4508c0718401c2e03040da1480d03a610840c0301118100a4002c803da42180c0c0c0c45400a4019542060300140380c10300700c0761558003148003402110200d000c4652030781c05000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 284857230 1250 284855980 284855983
    0x120c050a08010c20191101090b0c061501050c010e010905300c01150f0e160509040c1b0605010306110a020a0312060f0b0309010f020a0f18091d 63
    0x1401030800e44028042d20416034000380030400140c0d940301e003542000d00d2414402d4001c0c8000c0118128444981104196a08103540030201c0c000482c0c2c04234110710008104612404103a50128821400a000700c0c1d481d02d065181a40701824070714103111090000700240402030240705400c03901c0780000200307184542130644c90541508002c0c3d500003d036144650825441c034241340501e034010001f1643d104202000c0500520704000100907441b00780ca800300300204c180b60a6001c0365400309440103e030720380c514944550203160f082c0c1404104100a406200d0809411013509881a414807070150402e403260f0110004a0b441c045034041d80c5c400041c420055240300d2030081046070b40c0741c43c0c206140c0c2c520103540c61004007405414011115480c0104120640105002e00350b51145180402d43c0c8240a00c0c850300144c51031000c40d401c2c100e070039111030024801d0d200314900325510300070561101c0030103031040180386807143e611007414a00410180f4007805414800101c2c90008480401003d1109 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 284858480 1250 284857230 284857249
    0x3030a060b040f06080603120c07060f020d08070c050c040e0304090e0a0b04021306030804030305030403030c1d0f13050f09190c050609040905011d0d09081c09120c05 73
    0x10150704010320040c060000e5001c50301054030850700b420106603c50b41c000078602908001c8001c100180054a14140800410104102c4200f600e95020f4505014400d0742c0fa103424036103000000e0b8a0000080c070080c413a51621407418016001c1c0d448054428011400f42c030070074000b0030b8403680005010400720403248101c4021101e094054074000905594204540328040c20192242c8031070035040100c01400e034800e00c02194441ea00540d10390340c0345030142181e001141c007540071074074003500080024044c024080d00e0100f10884034031900318010401039000c1841600617000171581c00d80c0a42d45906100b414002c040c0f03013461002d1031614118642c507203404500040c1c007400002c41d0000000e00054010070980300c003240d0b2a5211614640410000c4c0140c45010301150300300100160401c0c4104c0c6050100b408120a60f60f40103043c0702d040d510912144103039940da900000f003500d21301d01d12402c00c841005861920b041900c0e0343c0c048922007620b40f060251180d40250004000c07030316044a06 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 284859730 1250 284858480 284858489
    0x6031b290d0b4f0510171f090b040215090a031a060105040612051b13091a0a050f0a03050607051903050108100e240405010501060c050a110f100203030a06 68
    0x803280e182d100c0e202504007420f083c0000c034a01c00c1d01c500110300c4150500020b14040e1507203c48210083c8110459143c1d03600c51102a00c1416600201070442c1c9042401100c4c80b07580c1003000351880d07440c3c81e42030080b46420070b101801260070a001030031180d9110002d100040d400382c140310145016141114190307400c0540041c3c1406010441003040c0f0f600101c0a16500e05850000901d0780c0d1003d000501c41c001c00c1d810712228100c000364055042d40c06039120010b6400e0402c08016640b1404c82020620030907800302c47c1d1001d603040c1300700314034a45020301c0303192a80d01810031130196580b40e403120b00c0c18000f1386840010520208409090400d40c0c058107082c80c01e14078040c410b5525052115403100b00b040d40000c1d1190b219030240c4180501041908020317900b84080a42c00c2c1b241b107400b0750703400005075402c9501e54207000001881901c9002407484154102003e041c03031200580d1241c28030440782d80078070b401c0010703451402c003541e42da40040300f5030f11940c1e0082c5980e40b410300c14100841c0d4140c0c11 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 284860980 1250 284859730 284859829
    0x50a1d010905061309050703060c0809010e01020405011409121e12070c03080702120d0c0507080a1a04170711012c0d0606050406031b290d0b 62
    0x2000060354404403501c54180c01444c0009101415043c0070342407002c036401c050308640c2000040c82c001076001040030b1181d40c155008200d55141034000d036090744118070456000841c60117001d440d6000c2c02c001000544401812056800d000899090400c003030045100c0c4000c0e010000c02c2540c4005001c001d40a40307016004038903028056440d100611460700003d0881500410341000b1904c13541c407000141b00012040701c51806007035030000c000301c2000340126881c4c0076002d00024000030007d5404c080c5580300302d000a000300c01c5d0040c0890b4031002002540c0d0803607040708981400101c1d0005000281c080d10b101c0c20054800380002d81106001003403440d04e003001e02e010020194428106c4110400c0c2124030b0070105005041003009020760b5008654018034003480001006507140404a01c02c01d01070b070a08080f6076805416140749000c903a00a8464640c2d0b0703910b2403c0030500002c0c005810802c100160024004002c140072400646031043d014111411596903200052039508411b556081c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 284862230 1250 284860980 284860991
    0x90203190c0e0402030115091a03161a0f12010306240605090109030605131a150d020402071209030606081f020c0f0d0f0e120c0f0109050a1d0109 64
    0x751a2129120300b48180d080308500e00c0d0100741156401e41100340b00c0c00718a01c02c10007803500c1e0301d1244000c10f5003001c84510005008403e142d00d05000c02c990392003014240b0360304400d901c5d1407200b90000f86000d00c1103004040400c000141c5c0152000500403140007442c10040c0ca40c19450f1150485441a090008a170480414030600c18140840602518250b140107900c4441400060350600d4180d040104200d00b0041080341004001c068105c2c1507000e0f030700c0e4a40d040d05105038244019001e82e0040300469142e506030b601400d20090300380710980b005e04010314108003903c0d26104480e81103100c50008007405410000d000840c003032140682040b1001d040d40307034170000058030b1403640d20f14103002e4207230080340114040301d081c00360701c80403441e0710700303540c00001000c01c001c2603160104d08003c081030490b4a07588841c1000d8442110603410400140b02c4080664100205440188030890400a2031600420715444164150004050100500c204401403203c0b907012200c05801000d0010709c0c2c06c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 284863480 1250 284862230 284862233
    0xd0c050c03030a0b010509040f091a04050a12021513021302030112061d0102031e090712060906060f090605011119080318161518060f0509040f09020319 67
    0x100482c1e0f0851044503002840c202070741c006860900818440c0c5038418034021a03907925084540190000c00d01c42c0220302036120210f82843d40005c0d080d0f4010b0002da0110109000041401d00c07086030104142c0116000400c44000d2091150021940c1e46215450080344008501703041e810a0b458490b002c0055041d581003411010008880e40130241030340b602e40c0300c0c0c080c0101011501d030151000c000c0007590b6903d001400e44517480707001c0105150020310f140004500100201d440416100746c0c04070340070362003041e41b501d1020384401c2c50141c5d4416912080003e00b048800c000000405000380c02240041c90301001400c81c003141c887c0e0800d243c01188180c140104a000e55541e410760000c4050b44a84441c0780228101281400c2c014403885920a405031010702201413004640d410032050a01e03224800701201c00705000092202c0220800f00184205c0c1e00941c0da0041c4140746140c51420510200f000a00b80e81140c1501c180066031158003405505081c080240c040921812000107501d69 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 284864730 1250 284863480 284863483
    0xa122a081c0209060301080102250203062d040302100c0825020f010609050a0605030c1302250b0411011d190b03041110030e0a060e03090303040b0d0c050c 68
    0x140c900480300562a4031000749640350303940c191400c00c000502540d4896844070283ea000390b00024211508203105803a820b0b002c5950710b036003c010355000d0080c7c0074648626841901c0e00b0f0118581004096110940142807c0380b145181d1040e402903004001a04450180004031418181c0b441c0400c4009020007454200850550210078180c44600c4421070322030320308031b082c81d45044407a201c550030400e0004094a40c1d8011501412181104000d669900c1c0304055441c0c880e4060b26401071aa0842c112046102c0d9015009190386410034103d5020380c0300d102c500c47c40c40c44c1c0c0c00b1aa10f950a5042c0001c3c0701d03480511100c004030a0070400c0808a401e4441d02c0002440051640f00d203141c10841d9075041c1e010513091000340840d11980d07460341400e11307158400d42c0707290764203e0080031100c044100c00e901c80d000300342c852003000f405405110402e031110130150605079401c0c082d61001300032820760341d1000c100801c0241240ca0505482d00720001c10300040e14070118a040801000b4455000c1040c3c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 284865980 1250 284864730 284864737
    0x606031514091e07020d020717060f1b1606050f060109030f0302030412110f060f0f07020a080a0b07020d02070e0c03090c15070605130503040312020a122a08 69
    0x80b1480801580c03056120405490f40e0406031907100c4070502070003d86500090318420f016000d4080d168504c0d00c9840f042002a1140c2242526038008000b0034092843c0d503604540100d90301d071041c0002425668070000c030740e00540040700b000428402c0d030400e001652040d1504401e081d00100d42d142010310008000c88004c2c0005010710044140312030806008004130340c001d00d1040004031801c0c04602704140d0500c4002c03e190300826034001e0510310303460114111031071002d0100411307090202d03054052500b50000b0340226085140c00301c000c21800c20801070040c4280c440c01f2100300c00e10b45640300034100040c8044407410355124003c14400c00c03d4254020f03074000203510350140c9994a4410840c40c106004250380d070001d080100308070000c0c1801d40109183c0f0300880c401c0c0030a03110851201e400d004003281c041e18680043c0002e000049280004200117651403040f980019140d80710380305009610446a00032484041d402c03107903050421004500720b02600d030007483c010480c1c0c40300511480b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 284867230 1250 284865980 284866019
    0x6050402090102030f0d020c070b12090609100b0303040305101b0309110904021809062a0406050708071509060b03030c0a0b061503041a06031b0904060906090606060315 74
    0x1602046c1c4014515855054804c031114000c210742e4001d545040110381c50340a148911402204400058080380c4001f90b100d000d20080390003404e0012a4005060040050b1109580d050000300300000120b8400c0052070300203503024400168a0405062000854812100794014182411182804140101d034034000700e890035240007176030799124400a2040c1200400040300d210542d414440424000a601c51141c6140340b8020407807480344445468000b000600c0d04483c0904001c01d000d15480b0740040d1038030300c6c400d4000b281024025614414424003403011010b00175a2105440e0a21880e0b0041c0c0304504010382c0514609500c1c11003d41c0c5801d411040038214036019404100c045d16004d100302d0141171004c00c2c0544a05203858081241b9011400040420f14901e0118081d0324021034004441001d02d005000d042082401b44000300c10001d01c1640c00d07a070b1b61011103010600750700507021810320800000500034144440601180c0034015030542020702c0c401c0a00c03104c0f04d449007420448 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 284868480 1250 284867230 284867257
    0x203060f0319030e0a09020c0a0302100603080405040e0f060114040b01140904090302030c010e01020c06070206010b0307120902060d020306100503090a06050606090a17070909150c120e030a030605040209010203 92
    0x40413200042041200b0342e501134040a4400600f030740390300030041009444c0c2c502c40d90035101d43c810000c00200507544180400340005004200030000c81c0384c540e11031200d10006400b070302c1103504500c426904059090b4003510b507030b00403044524042c2c0b030688039a8050303aa0900f44100003001d414454000b601880c0441c1e80201d60f600e95a6007418000c1003984c819014801c020f0250729540462103001c1e40181ea030241c0715124910105a0041c000304080c0d058403840702989040d6540e04600312100341c814400e50b00081c4e42c03801c40b03102503140c103401441c01d55100c41d400342c1e40c2d0400c0d90a00c8039884844260a041140c14000d1011f04040403c010100c41c3c0c029101150320307241d440028903030b4440d030704141c3d5000311034a9000075085a1500036114078070840301622031440ea5029240f055034202d5800401070012032a2034000c4c03082c00c0d403150304200b2661800c654210704c61003296003280c0301c1404c9004143d03c08100b1104150b07050151001404d41a81c00b54103101000300040e550303002ea6410803106 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 284869730 1250 284868480 284868497
    0x609050c0f070f02040c0302040e060a270e030703080117060103021c03050912060601021504020a0614070609030e100314010303030c051e1b01050f19060e0a0203060f031903 76
    0x501c00e10280f02810681c000700100458100031a010b0001d5120341b140380007503c54040001c099141544a500850320031550404541c3c418040000d04000c1c600c042e214400c1e600e1000387d008480801c043e0070340500c6916180c1495041c6200d00d44c21105e400000074440e07000c0c400510050b1192402403c6000c80300050801c004102c2c07800f5100e030b000300340071503402c81c0000704041e03210100082c0f224051002a020703642d42901181e81d010000000300c402075000310310008100583d40c401d442280c90310048040260405180d0342d100e206445101c0c0b010b800040e11815040c3c103511340034400502030320040c1420060414002d04128000d20144009010700d0741c0c42d102a0750380350007041203070013400c0c0600c070310181c0d11002d800c1c0c1501500a2100c81e20362007060320092a60840501c41d00f4011880d02805a0340395403564240c1e01c640d001a40000c46240d2900300c00100020f40d1a00d041c002d00032200c002da01c0380782400c00c1c4031419568011840c400da221500040c00103030708035a0000c81d00c1d014a08a9503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 284870980 1250 284869730 284869733
    0x110103181101031a06031302040b0108040305090d080412230703171e12040b0a060b0d0f0f0903110606240f120a140f270a14100609050c0f07 62
    0x3074141343c00c00313500000c0000401200c1980d61301c0032841284220f1b0300b0403404164800454102404032001400700e1810400540141f0b020405030a0003440348802034a480e4840c105195254441d00044502220f01018480c0c4061000002d2444045010041150615688403256000035541501190650001d043d00041c042c1c1c9005214510185208694440c500c001c142c60441e801c035021341c1c901450b000840c8003541140550300031580c020b0349990038404003000074401064103041c2014056a5680303c8020310340240501c800d441d000f6150b0f041c540400c00126404c15600401003840384000c151904030841c0114a030303074203082c050f5114a4680c420900782c1c0d00e0510500805100318030400007080414803980d040f5100030103440c1c840918a807030300302850500740020744180c80031541c0401c4074a60402c80342403484800300450219501550580c841c1311211070704003494800b03034115104500d281000e50086400400401d0030402040c43c044030380c21402d019034030301d10b5000c2000086840 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 284872230 1250 284870980 284871011
    0xb0f01121404080c0c060708090f01031d011e0902091311090a1e0e100b0f0603040c0e0f06030627100c200c040203100f0311010318110103 61
    0xc1d03100e81d4092141410700741805002034001c00785030419841004c0d0035241c182071801c1a140480d501c84c1c04a41000301c0e02c000c00080c40044c004407410160b03174001501e000c10514102e13a00144d011000000d924005201e4074602c032940700b051095540c148083e402c0141c880c00c80180c2d114941032040d149c424407604e85540344140401d40340b5840080d090034099001d03903641c07005503202180d003000d4403114200301345078007921400018280c20340c21101c0c51702c01000041e0009542c2c160000c00d40d0302b101c20007000045140d001950141d0f940d040810f014000540180078641e00000000b403c040589000400640d441900070440b46515000c041c0540140c8030003103d81c003000e9900c0003900c1d08580c0702c1e900500200180b87c1d5802c0003485808100781440640881c1c8440700354108003400310b4450709000c3c000a580003400e02443d11004400c00a8029030290220b00a0b41c8185038020040605070001000d072164000300104c04420450803070300091108541d900801e0742070074080707100212440c088 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 284873480 1250 284872230 284872241
    0x60e0109020c0f1b0906011b17070503071a0f010807030f1502030f070f230c0a080313020f090105010c0f050c1908011103090a030e06091806130b0f0112 67
    0x50f101ca1045407411140b9119502c60400700d80411303200d440c443c2d83c4540045481501403075801c4011014141e01c90007040152790080300c554081c182052174141719035680c0d4616482a481524015060000309046400132030b94150030054048581e0002d50421081c10f4541900703210080c8107a01d400c8000080003942038a182c400c5440c458110749a10348144c0221000900300e828400280300924801481030081803000204014901c0d584c0600080000c604015402000c900d0202e10401d541c410008011038000c5110308483c0500c0d542c1e00941d48107125031088280e11040c4a20b0200006020a99100d940e01c482d498003c0005002d001d59818114148a059404190007500c020540140e00f0f0387c00c254070044400d080000c000c0341a4018481386680401e64000140342c10426905010a11880d00d81542050041c102498111100b0000d0308017142144080c0750420b4031400c005240c5042d4007a888100d2220300306016000030b2500149040c80d241e02c426040c00419105100001050b9024 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 284874730 1250 284873480 284873503
    0xa09050405060601110607091e05040207080d050109020913020901030b03030301140108060f0325082d0d0503010909050a050d05131e06030903020f010507120f060e0109020c 76
    0x10419800d241c24190b403036903001c486013408101d41010b00403c0c8540090b00c1d40c8101b00655600b6130341d1b401d007450800c22140d0240103964102c00004046801d41d180e100502005120705092a81d0310748000e41542503c41c140d0202042d41c5c03040c03014100d940c45010503904c410402c5400141da40751800d006800604641c1007458045c40044000304100b0b007040f00c4595a0102620707410019a1040c0c20010441c010a400d2074240d04408d581810820151144491440091801a50103601c40d94003d140807000358031154100051845002031891821440035000250f001801c100b2358103140241c1035210601c102c890117a079801e044c00610406001c45548154814259a6400b440381c0009003550080c1507402c0150b040b201001a05d8110711500d21040c0c0c4986040c1850036152510642c020b11024500350190301455100400d4180c081c41075511498141d11841c02d25960021010100c44000c200a04400d14050090058100410905044400b54a030140c6e4603d000d80310f550030058409031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 284875980 1250 284874730 284874749
    0xd140d0903020c010e0a051311070f0b070e01110d0809100207112b030f12240b0903071205010e070308030f0a0203010e060d0201020705220e07050312090a 68
    0x150101007541c041201500c3e00390980c1e4242002c0364a00c2003006601c001d118080d8461381010358018040b0031a001307403d058207000e042034241129611040e00e6088290303070450b4141510703000c00c45600c0c0c12902414a400e82807910401c035414040701c0540e984c294500541c14030203800005008880108540048621118025510f6000c2d40c0f40c0949280409605e981c412200000d1440c0c1101000078002e4030001e107050000400c074543c0d1019641c49000c200c1d1b89003041706200c8400000079143c002c0d40740120300311b4030311543c500c400c84260800520030b80041d410ba00b4108410440e071ba81c0051488117842c0000b02184064802c1d10704540180764404d0008103030300461500000344007a00340075500c05d150200f0129000c2c5e80d4403070b00400300d1100f409040c84403000c0c040460001d04000b80700307000701d42c07041c0100c0321920345807000658a0b148070f04543c411000900042d42c10114070b40a040c120645000c0244440c50034400040d07120000b40400d410030303050208500c00250340c0e1400e5800200900407 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 284877230 1250 284875980 284875991
    0xb10150207360902011403011202030c03010506181e0f18030702062d1c14100b031b0703050909130809120109080f19050703020d140d 59
    0x10006900c4801500c03500c070009031007214035160752100322071000d5003008055044441d01d202c20308160041c1507111090f410400e080c421040300c0d4154500460203004030606100104919104241ca4861758880180c000d90500090160b141c940c0d007002c016921402020b030b881d55a4280520144c03100805400103030700821000c0c0011401064141d41c006c400750043c0411210003c41c1040d0740e44184900290800010800340d0a00703810340f490902ca00040b90071100c1c000c1d118003040784194005580f01c250105d009030780760381b520a441c410342c0c4812900442c2040c842c64140559040354a0a100d01682d18500100080d0b800c540d046000c070a24000804164445505081c0140b0790f40200300d20f1070045800b03102043d007a001d58001000c0d15540503401e0303450b081c0b2030740034481440100504180c0350b64858540740c0004403118003801071407115190560321120000036644000b01c8807140602031003000c02605000c26400310f0215403800642c02c0015003031040840f008020f1242c80f9440000c00d1920 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 284878480 1250 284877230 284877269
    0x14030c0715020d0518060439030c0501030e0f0705040e03040305011e0c05120402010e010c050307061b0801060503040303021803030a0f030b0f0d060b1c05070503010c080903070b10 79
    0x10f40c007070382c002c404402001c0c20005c11081c00c0e550b112001e03076006d00720903100d02ca00011000110418070050540c0c4040c600220007405540302504000e80048881e000120420310480d6410312400800b00c00c11002440300c42903c075041074a91401d801518000ca07160764141410b0b000420440e4015a4000000c000704458104110040050405020380181c20300c8079a403400362041040e682c126461407110079090312698011340d01c013900d1212141c184040820544042181800375001050042c4804582568203000d458032166880a80b01c0500012100600c100340d449000e8a9000360f241c2001a690904d000c1440020800209802c0e032600c00042c4801c1c0c50b9510085443d90354215450030301680f80d4210400030302c0c0421941050b000006076215001151240c0c2181030342039000340c1000e80c00340142107002c090080b81003040da1241d02c2002c01b0030590800341308050810801c0d1901d606103050110780180caa1140410140107891700e003000c2803521150317084950091000e80942417880c80702 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 284879730 1250 284878480 284878507
    0x50c04061b022b15091101182102030c0a060203030406050411040219030b1c0303021b0303010602030a080609010b0708070606090e012403030c0b090109060c1e14030c071502 76
    0x204001c0302c2c081210b420b0312004e0400c0f17000d03d8041942c0504002503050301c00300115100b105503100c2d17201484405000280102000c814006251310042c01d85454032841d005041c0303000c2c40b20083c0c80c0207414402080044c540d010096941040d0700582c0422a600c50303003844400c2c00d980c0362425070311500c0012480c2d40791811140107c04480356890030301c040a4003100300000c0c0401c0030f9150702c80c4c00d00500004006480b1381d0092204c0b42060001f0890116402d100500d550400d1b0009000760b440040c5130020355400019580e0300003011034910b281ca604054003807800d8011480700911302100414440c08200644e00100c0250031900c2c0200700c0400700710800c44c040c0010362001c080041e2500400221082c80c0c0c02100b0a907074040d1104100d550403a52446815000100301c1c040d035550312102440028028011088450304030303600c03141c2000c1401b200240a0400c0c0070b00f5400e0046410a0484180010003925030082051384550b0300c40819092a0001d1100340d1074401d0094400140c6e4900c0688 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 284880980 1250 284879730 284879809
    0x3020418050f10080d030c092102031c0203040b07061e06050a060201270f0b0106030c11030c1b03010b040608060906060612160509100210050c04061b02 67
    0xd002070034010075103c07241001040510b03406007201d07030341050b244031070307842c0c080e4001080d600710764903250b0f1140e0fa40c0c03000c00d502141d44a444800001400342c210042d4642045994240e035001c140010a102d03000c007010f50380303110b1840758041070304020a8070020301020340c0c0700100d030000702d11744000e46404402c2142d00504130360141c24031480f00c154001c41c000b44148a185101001184440b8501c0382c4030109010480342541c0458040450070300e1113000850304041c0034000e007000d032004204048443d030040d01140c0440441102d0382e009000c0000d0101c0c0007d0030000321240c0c0180b00041c0c111040c0032a001d05850b203940d6420908100000841010010700d0510443c0a03505540e030640740c50040020303d10415a503118196041c0b000b041202c01088000304501c0791600f44141f40208030380216058280c0749100c1009604006003a040c0e02c410341c0a641d5109220702c20303170f0b440d0609011014240c07544802100304041c80c01c40d1079000b1911681d24003200d000300381d4143d115040c6a560320700707148034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 284882230 1250 284880980 284880991
    0x60108150f012006161115040212030c0d0201051b0d20070f060f0203010608010b0d06050d0b0603121e0f04170d03060b0f070f03021e070e1003030e09070302041805 72
    0x20701e0f140705905184584680c1845505c0900640074060450030300e807c0c1da0801500c260f900c084548810000040c00304011720190749100040c25901c2c0080d00060700710b410042c06120010502ca40150244100c1d0084421602c24040005a4011004030010802c11440041e5103201c20014080b02800b0703c03011810f8200d445200207014208180502c48243e020a1040c1c401050803d4018414a004500900407102e141500084c1c146c0c0d684002402c1c554a0060540da540c041e002840158241801410308a90525143c0e0b4138240342d138078801c020086100001807001030041400303c00c045e117040880f0014564007074040c42c030355100811991900d002c0941003001ca440d00400084000d46c0c4001d9503a0703c48102c003640c3c18003450307440e24101007003a000214114020702c2c0031500c0d182d183d0309000c2100b0084c00d00508155041003408000500058400244201066010000246c2c0220040c1c1e01040a644259294590141c1a40a40119005288000e59007a000b40c05003038141e01c094803c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 284883480 1250 284882230 284882251
    0x1b030c090f0905120705011a1f0c020d030815030604030e060a110f01060806090a02030304171609020415140904110d0603112d0f0d0803180105060108150f012006 71
    0x76008c8096003180034501c6403109801214034181c00c81c100080d00c00082115405040c202221400740e4005003071500780740d0003200422001010301804142242d04080c0741d80301900101102d003042d031000380046c007618103071a20912001801c1d140c0c0354070034290040203100000c11110f0146009540501801840c010f4100303520a1500103100c0b080c001528044894024016600d854109860034012111040941040b84140c44004080072107018041e002410720840041c4c4843c1486022903212110302080c10811800d000c40b415004103440031104014401c40e400607440f01000c18040030b9014020384121202e24081001003031043d188000030b0194812079641104a1348003561881250080304c8030781e9884900d240d091a2b03414100003a0f0310446001f0b1124404030707a15030326106075a0003203c40341041600b80301006040c1d60240900c58200300242170880315440c0906104d2071700c000505910b48601000e0403a0306c0c0a034044c40700c0c501560350440100608407000c2c6003859076983e080d65041e010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 284884730 1250 284883480 284883491
    0x3031c0f0e0703030801050d11060a090302010306060e0f0d0309030807030302090907091d060a05060c010b04051506031302041503030c0c0905011805090312040b01031b030c090f090512070501 84
    0x6908041448019603070304d81c440f0b015a07401d060500c1034000c1d548030200c8030282e0245081c1429622003014003000119a600c1c2d502d264214030005060710450fa06c1038003409030313143c0381c1d580d190b4944d01240c88901041e01d10300b94542d42801c04a0f10340701706900c040c002c036600154090a0503455001010b6072941620061580c0d1110b180c221041445881401d1880418840311a04681810fa11030b400000061205085980b1480004c41c25480341c1e0080b10142e550f1661118103080034002d4580c8000c10400000b80101e0320004a00c25100c0209142e0894580c450190110756071a8003058101311300c160011881034036403601800005581d6001d5801e01c148031400103e001181c0903007816245d940c040825440d01c07414401c4068100a031840c06140014400b0003140150000c070389102d1400340d80c80a6465265091000e00721411000040b016180d41c5030902c042a8203140180c100c48020f00009100030944165400070811002c00a16a0103040d0344c410752110350402805400b80a00300030000b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 284885980 1250 284884730 284884751
    0x206040b0c0120070b060102010e0303100f0b18013902010201141014150c250317031305010608030d0c030209090411011710030606060804051b03031c0f 67
    0x69082c008900400c415004015020010741c0103160250031001c1800041805c0c070ac20381e0780a00310382080307400109003c0341401c1040400b40e80703440c02e030080c5450030007a4030305070a4003055000358018140b1a8103200c0d1210329028440c0c142940300501018600c3c0c03001e84980020321031741200211890aa00560030014968011000080344502406445185100f070f907144c101121103003008842002d42c8000c14040e4500640000310040c08070020510183c070b0f500c582000c0c4a5603d100a22100191003001181400020f2102014488401c0c09990340340d120b59560810703511070f07440800d000380a9420450002100340002000e840c01540e580e40602c40c1100c40c440c128207d008221841c1cad80004040c0100c0d020849851030402004010f1400c000100521280030360030f400195817126080350001c03810018411903200e140041c003810310f0401013a0805446440d90b400c0069912170030f100e60764000c010190b0b4108100c0b40f01c0300d060707a8004605020306c003917031009241111400340c1050038144101c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 284887230 1250 284885980 284886011
    0x51801050901200a0b04050106060201060b1306180b0a0e0406063b0a060f08060405071706040612050303041b0302060f030c0d0509370204020c0106030206040b0c01 72
    0x1070030407106075140140045140e0b6541ca0350501c0407610040b0380540071401011403076210b042842035010314000f00d403039460584001c0c215450b44c0d100104810050000398461995018114101c504600e4071440e405240088080400c002d41e1050030507440010b004012a074020194020410781203034104030b130ba9562041565900078001c00604202c0110000340000c03180a030803010038002445e5070014010b40c1c840400c0a0703207007a0700702d400030038141600400056070041c0ea1650150301501c050083e0b0501c2d40c00944100c1c00d1515044001c440304000a60540340c42d4400c100600c10002c100707000c0004c509241c0d44a0b841a1415594201c911101d030034441d0b000018003080f294003404030340c588010390380c0e29800743d000036003610030404080201d0200d61041340078641c010b0345d10751b000d48a90083d028030708034190b40010112584050310062040309590b0600255403c13a0151009030b6281f080080d03003801844140c000075440750300804d01150380403500c4c0150214034850f00080281d007445801700c8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 284888480 1250 284887230 284887237
    0x1505010f0e0411070b01080601030b090a0f03030c022e05010902071e0606050a171b010f11010207200111030f030a0e0c10030e010f061409041b030305180105 69
    0x1021803a02000c2044905207039000880030f0300321004660803c0308030f0f500d600b818802030f0712401c0c0551103900140700f4010700400c450340001d20340000701600103156a4844400e60102c002601b81541c1e0f1800c100b00d40d0090001c44c2c554607030b50072220700240644032030418000c20070400040f058607060020a038803406108480f030f815008503803001040e000b2400c0d010310200180084494984591002440e81c6407520003602810b40140310386401c05170840326514041307416501c03000044810404020b266082038036a000c0c00c641d4034007102c9184040541501900c84c04c4c1c401011012900c80f000e191009403d0060103542c02662200403240c1424445540e80c000d810a646810004001080c0141c01c08e80c09690b00b28041015224070000c2100041c0480d101107401002194440440b172021400a2041691403484d0715801c100702802c055100711115106007c56004000141c01305d024000c10100c0e10039850f02ca00603040c400d540782d2400800300d400590281c002d036080e25541c10460360084c401d8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 284889730 1250 284888480 284888507
    0x60510080c0d080319020a02071802031303200f06010501110601030c0b070c090e01050601030b0406060206061e09010609051003020c030d1a060a050705101407051e0c01150501 77
    0x38115814066100c0c24070f00d030710140031401d190620214102a044090000c0d11450101e070300a080400e142c41c50a4100815090580c0804d5204108010014803602d00e803410068051134003042c00f07054054201140090207510400d14400d881c802000b5a40000380503050300c00a0344ca0610f440070084003651344a4080c080103101c140040d000307010b00c8210101a2012500074403140c103010745d071020198107c543c1d106100e0301740e0751103c08001d00e80d60140207162643d001501e08000061404000945409004d4101e9100b005038810000c8641c9041e0426058000006d200400a580d1a50041d021405078401c440c003035400420f10b21030140c0248280d5608881d10000f8510782181c1c0345c4644018024006813182e180e01070440c8440584030306000e0700b0400400d0300c40d02d6907810300b4180341e442c0101302c52010a403d0f080418502c0f400b41f00002c43c2e500840741e800c280d0f0321220b0882c00003000045503003450205140201ba5061461015000b960554103c0758200c03151035103d03001104c032140206103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 284890980 1250 284889730 284889739
    0x1e06020c0c0103290f0603191515050702040207020907050d1811101107090207060e030301030c0b0322030e0f03070b0f070825120903020a151704060510080c 69
    0x18690f44481191040d811440c04c000d10402c0025507141c001246a0030079280b00721480003038400e1001608032441400034210800041e807800170300c1e00c00042030815017502c402c0100000800c0650841d15560140c1c0d51042c0d000300742028a01e803040c80103025401c8280030a10f220300788049000400c81e03420090030300c140c02200c01110b8410401c14000a4806084c0c00b000f0040e42a0f0103c03964002400700e43c001c2c00284102598031030726400c0c200150341e140b050408a5810030401000046c108003015812551042c01140e101d41e6160080031810142d4046400315492518940b020558000e5030006040c6003205c401000c1c401d070303070249691030b2801d0181f5410f040007040820300444804000c1c009203446546500c1c9090840b517081c07214411142001c50071403203824400400c01414420340c0c95994a40d1a004801900d5030f000120140b900c5c1c81802002200640380c903681501c6808400c01003ca06101440103080616143c00140000c440980103119072038008650b081010440c40e01d40d01c00140b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 284892086 1106 284890980 284891021
    0x30c02030f0c190f090903021024120c0608061c0b07022a06071109040317090f060a050601030e07080105070305010b03040f0f1e06020c0c0103 63
    0x4081d44260408400d051020044040304d03801120740459010413802c925080c241d040145c882c00403210682800d8040c032202020900452100c0c1d0107030f00000c51550341d40049800701014000040440012a80802c1a0342c446c101032508800010004c0244100031441c401e100c4103e52422a00b8102002c204440c0a805114000d00810030305100030b103040c02c24410003040a60942040e01c1400045480e0301445061420600e942002030003d0300c0303031708103401c0c05003420b01d11b0407010118200c21000030b100c110000c241200400a50301c0100416101c00d5a11005803a0007800241010f0b40c40c2d18203904ca4a003044004e00a05c14140000307480e060164004003030b0342050300314401020007002440300050303201025108071608a0241010040c080c5410b00065030100040012114a6880c0b0f02c148000340d4000d200400130482110301007000c00005405481c0c2e00b00350a5006020030 = true := by decide +kernel

theorem cover : BRFrame.Cov 284712230 284892086 := by
  have h0 := BRFrame.cov_init 284712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 284712230 ≤ n) (h2 : n < 284892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
