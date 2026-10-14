-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1219
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:49:53.262018+00:00
-- url     : https://prove2.me/submissions/979439bf-f529-4e96-85ce-eda5ba49105d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 219064748 ≤ n < 219244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 219065998 1250 219064748 219064777
    0xd0201020c010305061c0b01082b1b061a03071a0913110d0207050d0c051b0114040806010906120305040608130209010b2802151302041b0e040203040c0b 67
    0x110290306e40102d0b01c0c0d000041c0e50140421006000241d400c000d0b01c040070000d42568101d03e0042c00366284035582e0140c2c000b00b080001c03d032099042001030600103038160480010407001a0b40c021031000d12904203034050080c01225800111507024640421140c8003035600c09140c41c5c1088100204c2c114104004540d1603507580c00345550702004400340070084101c90006030f03140d403241800da01c0c1c03007955200d45041100d102c0081001840c017003801c8802c1458403007442c04003419034005032515503000019864401021400203032100c40003a286040382c0701c40c00304100c12a1a0b000060340c801440401030701088040000300f1801c0d01c03d140450b40300008150280d219091540002c05071402070748000c0c002c54011a000044940507088401e00000481c600c4a2114442c40040c1d00d4800600701070b0311032a5002d00103413101c004241a00540c950080c0108035040d410038080d025203030030411510004011200300116805c1c50b02c00c6900071134109401a940c0c915042e1501d500340e02040c486100c14 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 219067248 1250 219065998 219066019
    0xd0e040212070206040506100f0501030c23041d040b040b090309040f1d0708071e12050601150e06070b06060706090c170a080d020307140403060b010e0d0201020c01030506 75
    0x100501d1031601808041d4058451414a41049450400c0190403c09002040c0104016042c0d6440000301150820708020460ba104442d007038482824421410210300d900359180c07458041ca940090080d51030110208043c003420038065034491108407001454a10b4000101d00030038918440b040d44541980116413600c1664400305094511190301585441d880b0301080c0c00505800c00142e91b8034060034020030905107000211581c03030700380d8480d0100800d4024031203412603007074400c000d0241040d0b0034481d002c3ea22502d07004cc0c0d03440d800d00c6802e15690581c14811882e0b84074590139460740f41c0043c1702c5410003003140c544510020014045660040f010061040084d28900403000e505000e14030400282c2e01c0c045c500c18803251151100308071600300303480944c00920302100b07507200710a030b100c030060b02c90340c800000380d400d01e651507991050203070045030000800c54a0b4122a03604642a40c030184404a41d005000c44084601c00083c00368000c0c0010048651095014a60141005120390b444 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 219068498 1250 219067248 219067267
    0xb033315041805100605211b0103150b1e070c0315021b011d0109020a21331b0309020a0b0706050f060603070c0f0206070c0e04050c010806030d0e0402 66
    0x81580f202c4c09204099200e0b182080750386882c500303038803140780448103003210751300e81c0d914017500d8070441c02c0f00521000d03400076056502d0744a940700c1d200c00400c0848003240d0740e4a419800103182c0103d031036031400301c101201c42180141e2034419110000e501a4074440c2440c00c580e80c0d200043c2c200075551013841c4d0300341300c0d1080c414011a00030845214403000040c444041c0304800201340760902004103642e0401c4079841c01602c50748203240c11100c054100303820b21502d0560a60345d4030fa05102c05802840c0030410003551003c400e0812110000c42442000e00c2d5244000840680705508900e04958401c1701c041040e03a4065008864590300c01000e000b40035483d003880603207540001d10150b908640d104200044000c1944100c0d4010300100d64042c2589840c0100070422031039064010200c141c8500b03a24115161013003500c21080c2d010760302c0410141c44621050441108032816a1140701d41e40d8500b05c1540a000160b00601d03015020b01500c40c801141900c4030f030b54500301c240d0410f0313003000541038 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 219069748 1250 219068498 219068503
    0x30506070807140406030b031501060c0609020355060c0c080d021c020c030a0c17210a0c05031f090e031309020301060e040f0b033315041805 62
    0x64205c50310f0024204991005040c5040d1040309245416a0140c0042c410a9041450801810751000340402c5480c40740c4042400c0134600105a40307101c1d43d003142c2001080d100e2807400d019815141400c030900c13000011100c0f480316113a003c1041c038a00f40c0b000c0400319032075400c0b00850b00038a082c030b410344591a580c0c2c032180f94080001079164607404100407100d003000b02000c1082d2014050f00750300b848140d0000340e0710782c41144000000e205603d904c3c00704226030342047c240190110912691200a08001400d071021408254042c40303a10340009980100315118088080500f0303a030341811559080c1907041d181e11460248841a03140703540014220080b80507182c0001c098130091510b940c520042e1910b45085608580f00541c01031005211a641c0964000e4103020704503008110701180d883c0c11401443d5854174603030540038000025420400409503041a40b40320780c83c04002c41c84050103130600c0035080d00d018120140802c200003892034280c0243c1c0fa038183e05240c841c03420040c0da80d803030b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 219070998 1250 219069748 219069757
    0x11106040602041502060c09010503100e0c07030905190905060f12030a1b030804080f0c03130312090f0b0a020715031b030c02060417041d15010903050607080714 71
    0x340c5032900043c051000602880f84602104200d000405540c20b1030000450301e80280740320141048030210001d004406800205002044440c40411403410680400c985660101105a001c1303010340c0400909404c2615640250000046030030581c18105403085000d031001900c81c55028540400060480e13452015000c01801080021661a80e004402802c80080d44140603590301460341e514000c00d0300103d10980c01580440ca141e42c441d130104090b0102c1c0190b8641100512002c40d071107040c4003200b001c05040c1c80c0660350074070000007080d10442d50f15280b80a0080c84650710300e030421910341d2480243c01c14201d5401074820b03058590b0050320f100c10488582c41c00194550340c020707882d4400c0d030481811103501c80c50188809041460080d54030400508010301428000d00d541c2c0380e003500071041e500030b81800d04160003805050550704c001070710f05440702d90300d03502c81d84e080303510381c0d805010360b4422258040058034450703891030f40031b84580c6401000b01c001e04c4840000250100c140f4001403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 219072248 1250 219070998 219071003
    0xc080408030f0414030c03030a1a060307050a180e040605061207031e321b09060f12100e06010f060507110a0b07330b0402070b01031a0708040f1101110604 68
    0x107542341d140506204050382d5a4000c003072a4003d040811150b281c554004a03035201e90b003030402950700c0c10307071000488000442544518103078001840100303e080e0402e000c580102d005134028092515441e040015643d00115030620329802680304000191281620b403800742640407080400076140c0d102d001c500c045d200031070380701c15150100b05032407440c1d107504440303005403048020012201c0f0044004160042180f82912070b011683c0040c006030341c0c440034002c5681c0058082d0f004c0b41d124030344a9594030903048658902c03508105071480c12180004881c0d0403120b030b040c1040c0022740b4004040d5429803003410300b030729074010b0114a501152500b100c80304c0100004107020303540d850141050303a08130580014100f0300075031107010900114030440035040e24003901000090010940c1000030001d00c00d03110002c09103c04d40000005005911400d222464600c8564402c999604401202d8604080360003d0a000d1803048120114114800320340f410340047c1400844030000705076051510000f01c03000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 219073498 1250 219072248 219072253
    0x216050d0801060f02030703030506120d05040602211210030506010b1801030207030e09130501240b030c1206040603050307050604050f01060506031b120c0903010c080408030f0414030c 81
    0x400e84640e50001d809801850945804001e20003c100001d40b01c2c41429406010591100c010480f0355a031402c0c0a0540c0345080100c07400c00012120107010364005106840150040f140b145d0340c0310301414402d43c06414900c08480c40e10a0031440061140303c041c0c241200c00c14101000f000140b0f0801c09203000e4144001c1040d120a40c000e8659100060001c0c5141014014055800040d070091108550420106c440c0e0f042d80d40c43d00540e216604464001801560a040d9000c0c070078210118060380d5602850000089280c40f0300411680388800d5440510720030040105400300501000d038140c100c10b00901c089509503072a2a0300745142c0014500b5075194104100780070800008024080c50140b065000780950361803c00010a00c1c0801001d181c2022007044c514501c3c0074252049032442e50000c1040c0d185801c2003090010303a90407217480d5038081c0d840c2003a0140030b00d0003190f51620407039102031001d00c1d55031840c4480304440c1c00640111200e011000c0180e90800741030000d0800c16004600 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 219074748 1250 219073498 219073513
    0x105012f160e0a0b060c030904050a110d06050a050405100b130b190305150a0302040e010207050106030503040810140114040902061c1103070206071b0b040b010303020610060e040e01021605 83
    0x3c0001c200c5101128642c400d6004000790781e0420000700c10390349440303000c4400003026681e80c2540c0002c0d00ba40036424000150002d54840e2925050340710b07605403141070b900f40041580710710130310040740d6003610081c021840205080001005480c001e11000441d03041044600350b40c0c00412000b60481180c1140340d20b00300a503460015454031a4551001200039000401c7c070700e0343d0100da035068842c0000b034050b5840c1c8908510304a000d40440d18090fa010000b00320f100e40d80c3c1007540e00c03500f0034080e0711024000c00b200d03111480074078000d41c1105402288590050791800c0f24076541c3c1001d02c0c011540003170311400f03504050ba88080250200c0700c4c01002c502d210343e82c00015030003101c454044150a0200a0003400b101550000d2400c1d800320040c1418641d45103050300309040c6540685008160041400c1004100180c88900b076040f24440e800b2281d103511480b0a4414440c02c5005401c0050071000030b00d411440e041d00995121030402e000103241854140d132005031010790090540300c6511a20 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 219075998 1250 219074748 219074761
    0x325030e091513140a0f0209120307020108090c010e01080604090c140f04060b03060f03030408010e01020d0c0c030c3c03260604050402040609020c0a030201050105012f160e 76
    0xc400f5242e200d10001c0810100f19005404800007001401060310603030784402c10400900c2e154100d44c3e0012000741008a1501c4503484182d83e030b40040c100301c2c0040c4400c00070882c3c00600281c81e1080c0003050311908240200f0740011074001500601075a4402e440b89140030100d4042c5888402604600003030003d90700c4010300b070044001040c042e06c0d00843c030b0441c1c10400c4003a880152600820204c2c2c884814501c044c00092450203180c00030600c55190041c1001c070302c42d05500801c1d1081030003605126503010034030207548080074000c0c060081000700150344000741c41e41544102e0038541880c1c004148030a18450b00c41420710440c40c06548032080050818140c2000c2000c030b040b990003110383c0c1d00001c080c2145450010142142d4012525600483c0440d40e43c0d400600c0602150030045455a00c2411080d81d103422000741a8090b51900c8004211540300340140b00101e411411444c1c800041c6850080440140447d165594020403040300d541c450914188401840a181112014200362 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 219077248 1250 219075998 219076009
    0x13020102061b0904020708040e0a02030609010b0901051206011b0b060909280c050d0809090601090803070201080a0e030a090915150c0515160305090325030e0915 71
    0x1401c408030300004403456003491090001114283c5400f51030150301e460241ca0000c07064082d54000c5100c080e2400e08000d5031800b580d000e184508402c94035202d003660780c0d100d0002c1600c42c103801240001c204010840304030b00ca01c03c0240d0404010b151585215904503460820300b401c0c2242214a444207a00748009c1c0d2802c444c03060741110020010b02848211191411707264a017207039900c071800141c0c20300e0405000300e0100b010010440a881c05c1c4034402246088001640300c02c0707040d40f1503580c14003c10120b5210700c20f05001c6e02d491200841c40c101494006441c0c0842c01041086000e80b204240484400180701500f4545800d46034080c00e40c1c102030f5020151400079402d1802103010402c204070941e0100c2074240c1d81407090500d0f00000b020703030502e98104900c1400208006907204c05000340c210900a12544520300d903a020085034541c4801a9100d100f0303d0440c071403295641d91920600048180d4109682c0d10030300704640e8200320240881e8a07007100b191500601400c0344860348071401c02 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 219078498 1250 219077248 219077251
    0xe120102070201180e070c03030e03030f0a0c03090201020c1e0607060b0117090c04050405160f080c180f090316030306030204180b0703110408070b03060a0509040b01030b040201171302010206 84
    0x13401800c80a5003000b20720049001c00502d20802c2000c40d25208084c035000740e0203540d406108100b642c0e40ca140c1070b54491000201603603d601c0192a05010008461081c03045483c01a8140d0103001086140010031032000e03c0011404445d030118034416145a882000400c0c030703103103d0030001c80c502c0c0c03d40c40054080c8250145880310694840c0030040d44200114041606030411a0001196112801c0c124070340100610031240c004040c58001c901608000001d804440086003101e40313101d4050140b00402c03580c103d020290150b2400840e01c03c651480701d40d5405600d0340112801e005007007221030801c82c502441940466550082032040d81405d009010000400031001040d001d41c81c1d4030403600030b8004000104056449241e907202051300d0302240c0c0140b0070807048844c40340d00c0d0031038500241c0c025184c00c0c0c428003000c01c002806040002c0100d10a0750440d034017840d1a86192101c1d400d10000074001c0341004a49894107402400a40702d00d0b0041d81114002c4156541e18400a89802030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 219079748 1250 219078498 219078527
    0x304091d0712060507050d050403020604060c050c0726030301120c050609010c0b0a0b0607061a01020a03020d030b060403080c030c0606010e030d0c051002270105040b0301030201030c0e120102070201 87
    0x9000030b00c0421003401c48000000e0344400c00080c59034904400315654095182d40000460800d41480280769000420342d001d50702400003080701101011003034440c0c5c441c0d40d1085d011500301c00c8041000300c0300c1c2602c00c1601e07100030310000403221350b04c0ca4046c1154000d0700400000c00700e4420308418442c001030802702500e802c0c0c840d50300c0e0400450020b0b044050005005007540e4201c0c0004a12100c59000b0304a1403d000d400c43e0344070b1045150541c042d00620120080c000401c01203040a0b62000607240c90643d09074014201042912408030b001c2e104810402d504407004000020004580400420340c4010703440c0510344130900039107024180b050181041e07040150100041030599000314403142510381605000035069007601e0040e041c02c9804100c40a043d00c040b400d49035046a200600d0151401c02d68030240c0c0280010066036103008501414403c070074180010700055000303074803203081c1814608144003d00c00c80400500110950940c156840e500443c06008650f00000d1641c0e1100307 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 219080998 1250 219079748 219079753
    0x1a0406030e150f0402030a02030d03020a030e0111120901062111030106030305040b0d0e0d1e0f0c1707020a08010b10030902031504140a0303140a052403010e0304091d 73
    0x100da41c402d031400d8440948051400c18034000840c04551341044046a010340c040d003510310200315824090001d4200c41c0e10200440d080807012542844e040c803031a41940005100b50381419000f8042d41400701c0c0080c07008015660b40d0001140030003480c80d641d24882888030706915000042e1038200a84151180b03914001ea06111050000a0b00b15050b641a1450020720a44540c401000c100c0641070244142c5800e00601595000855200001c02000941d60007038130345201141000b1145d03800020940c0c2c0004a142c4481c10014000511007061000804281810504a600041e03220b02169000c0d62850b0f564040381d00300344c20400c2018000d00590705041064204907004682c62300c0006501e6500225070000080400408003001441850418201d884d80b11113441c001e4014001207140c004d40f041c0d5100040c5210010f4003d0520170040c41803061000b00c01480744450040861001a6240d501da42d020b1400542c2040948010f242020011030000341da90080c5200c4004440d8002c4580c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 219082248 1250 219080998 219081013
    0x1606020c030a110a0906090204050306011d1f032306011a0706020c0313031202070902071214040510020304050913030f0c15050a0e120301052202041a0406030e 70
    0x381c0d00800c0c2880100e40040482190580e001c0014103600b4041e00941c0700e1529005021401a0407a406442503800507001c607000c507601c0343c524188050504020512548280000800c0c40f460308400280a150038041945802d850344d407540124081130349440c82c00452202c130080c003c407040246a00520100e054034400e2090310044928500c10300c1c00c00707040503400043d400d2030400100111824006d00b08002d050b425240d14080042d0300b490303541c900045c410780b040403a4580c0d061003110f161076407115445d101c00340100700a40d0711034050066800c000c0000d200014440d140d502900c0c0e66a05650f0185582d03178145000c111450fa00a070104403e120b214915200094010b9540c1e0340d030881d2410f003c03400e44154642254030846504d52100c20343d0400c1c060102000142c2c200740d0051844000380c0f059180c1c0f080c44070340306010074400c041d405152010904c10b0300202606000030040110405880e107602e80d142c00d00e5034140f010741c400d082407000604022181c0d00d4818040d45488201c081d0004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 219083498 1250 219082248 219082273
    0x203150705190306060f0507170703170105060306010518120607030902040e0604030206010605030a0605181509090d030905010902191802030903040b0c0a0209070206190b060d0908040306050405160602 88
    0xf103946e0304981009202d00001c0c2403090003c80052140e03008090401144c1c6e034010342c600100b40307184c1200c1800e08150250004192480d0034400e49206400680d602401e001b04400200b55100c525186a034100d5600c20155400c10002d010040c400d1980d514046880c40c0c0b20b00c1070108460303000312060b50302d030880c40500c00003960100301d8a0440c1c0c41403070010780b2502c030f1003d041d00034030b100e5010581c00b49102101f011329201e803c1d200c030b200351211000d03004c002e80d50070240302015100300c2c1c60700740d29001800543d0146009a0160410070f0081000140e150169800710b00e11a10741d541000241803003100c02c01c00940c00d002d10201c0508c3d090030950440c02c041c440680e803801940070700b4005501c04a00201d01000411104080d141c0041050b01c00d0300b00114041d403941d006980da05007480c0300443c0d10441c8a4180640315a03940041c1040d860078103941e030a1002401440c5080341e80d40320400c0000040744040c09080d0066000d10003506955008da802c3c0340c406d03042e540c4541c05642252182511 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 219084748 1250 219083498 219083507
    0x90e10090f0602030417070b0f010602061009020c0705130614010c0c0306090f0f06060e09070608010302040c20070503060601091d1f0801090c050d08070f020315070519030606 77
    0x740550302080140e1242c4503807624a441c4101d07802c80d603d03040d202150725400d0040781142d0b03034001d01200104500343d07629000c00326155441103465000040444504001d10005a0b0040c401c0704065400e45821a40303400000b1000440b002c2c0c04a8100e8450700c09203c0890f200b0300e02d40704ea040909001c203d4040300c2c0c6c0c40303a5081c80740380300240591f0341e00c1d04440107106075014003000e0355500890301044101e5070b01c0c2c01c01c0200824002c808a0102d480000381d0780071000607078034080c2d43c95620b5059840e80380d0f41c01c000203000c0d1004113008210340058400640d12802e00f01030745000048c00035207900d5083c00c052514001000784440c2c1004154003040000440c0c01112040d00c080c01c40c0310340183c0e9203611511185003141110400a55440c4500142655043d0f100640e817a120f118400241940c9100704050316240b8038014100941c10408000060543e0340405585407014054510040da41446035904860860701e14001c24000108070f82c0700c860100929400b40200e040070812103040140003003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 219085998 1250 219084748 219084773
    0xf0d060605040c02032107091404021c0e070f08071a0403081308160b0403060b1206070f0813030905091e13030314160309061d0d090b090f0409020415090e1009 70
    0x292741c60501e0a5845403a1110307011110340201d41c1c40c00c58805901040200028406008460300501407194040782480c0c04003410012500030b0002006620f0800d20200a00c8004c5465031400b103004010020004050101504180c40c0120708040f209140180d10f0741029004145a070100d080c14200740150021034055405482c2c01c9040003400c2d401010100781051450000d400061041804008a06510803c454110801036072078540b1529a100715141c1000200001808620000c000348820300340105a03030381c840580801c4881c001a2088080c41d0060240c1c0d03000c1c07522260800941c10300d509405816102d40300032002e10a1b91900904800d51071200c0038461003010b40780d01c0e0040500080350003116030f10021001c441e401041291100341d449030390b182c1000120396035003c00211030302c0080035110000f0000d0801e05c0006500b0742000000c004101c0b0480e401130b034982c0310f800441044603030100500300b009070000361070009002043c94912510004c8030484d0905600304000b4484400e500b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 219087248 1250 219085998 219086009
    0x3120c0c1505070b0a201207080712091a07020a05100b040906020c070503010b0a08070e042901090612081c1118041401050f0d060605040c0203210709 66
    0x101e0059520000469192090b904007409081d0076101340041c25407660b000c113406541c28011071110303034449800300031140552204140f108200c0000126083e00902410342e0110307103460311451070000f9080d440f0403900340160a507030402010b0400000c075089508020303081003040c0010409000036031340e1140e542c0454106086e0f215113a042c03400e4251143e0708a1208268403900554179291862042581d4041510030a440781d0b09210296250342001009802078501502c042c02001c2d08000b1003c14201018004507103200014240c000c8450323038001001c42c2c280080070b250006500d0607801206807036031a0042d0308204d5085126400260000040702c40c810180d64040240380400c2c03454100030701152400c0c0108000c00907010000d1503900c0d41c24440040100d4040040980750394080000010034001d49400550300c423010030036480c00310710b80d0550740e118060100b100d039141c00100e015960360708d081c0005a480441c4030600107422400c3c03505021200362030412203241c0b414001780400403d1049 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 219088498 1250 219087248 219087269
    0x10801030f03140f0a0e090f22081603021b011103090d0c030506010b21060a0509060427050105090d02030712021203010b040e16050315010e090408030103120c0c 71
    0x3244860a03015200441410585503889068000000d07250a142807405486080010009548c081d141300c20940580e007031b03801280b4102d01c1c03080388200b00c10a0b807205451151003071000c01262440d035050954001d210780d000e44402801803000c1100b0840f2513740c0c0c0d0600c100c801c5404502d120000c03c1d00c0c1c0c82441254007030030003425420000301e0703070220741c201804070700075480081020200f8100505413121800410130400880306000f0b24030900a0320950380c41503481c8000c100c2032404104440c0c0160f0020000155051400d450709010594115065103040404d940c07030080c40002e01c100366102c00c03654003138641c1d2410640000c1d121701c11180020280b01d044210342030310600c00c10030504144080c0d10119602c0d61201003040d10b9030800d201d20180b022034000042c203070003102c0480300503d428a4850718110307128844003424108010760024104030707056002c04c40d569911881c0900940c058070440381d40f941141081e2915140084198050000c0100020f000601c001440390440e07248040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 219089748 1250 219088498 219088517
    0x70c0b160509030f030a090801090506010510120903021c0305060906100504090c0e0a080309011715030703060b0a080a030203120a29100c0c09270818010801030f03 72
    0x30546a0303015140c01c1c00d4240c80b440001c040c1c11000080100101040d907240c265015540380e80150030703100103100007001c58000000400c40c0b41030807102c010a030101410301682d610504c2c030180f0204c1c0c1e542c50701980141e00400041c01c0b00c243c0071003040d8000d022440c1c18025441d060002c01d44040c00601414051800c4890044629208806541c0a45085802403110002002005000c1d205210107544181001100099260f20000031640b14080c180c548140040c495150750302035500c0104001c5004030072500ea864648d8090001c50042d621038040092075040290a119401d4002e810880441d4401c42000001c2034000058a2840c26280a940911340e50030405401400b803443c48558841c89204069018000159142d00e400c10240da442204070344030031003290a4000e141015000d4009614140b02d00c1c0d20681103da00b00460100503205829040c102c01c0100c1d00c0842d064034603d001080e401c901d40851202c032071a80c1001d180c52452941141c403803900031302a8100040500c0002607 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 219090998 1250 219089748 219089791
    0x601030209030303100807121509050102091305100b090109030b1918051c050d09020411070312060503010209010e0d0c0b0a110106080d021c090f030c0509070c0b 71
    0x804036088890060140c0344c0303a04104450300e0080010303015040460182280100d121810011045140c030b4100a81315500ca0b418024100201030b00101900c3d070f0f54003086054260b84030765900045001c0c42071800111441c090080c001421555048038202e00c900b0000b03d9003030781c3d2198000e01601e4000444a40340d0700c480a58611010746038551160807820300b107280f10741b924603a0407402d03000c1c0078070199520720507501c255100b248403006501001c42c0c014052a41034202590146540c00d1000d040040c09005c10014428180c00044003200002c400c00b110725040f04040c0914001007070103400950910407590001303060502002a42409480026241400d100042c007c44d0000d007040603800d03598040740036000301003040344002c1110942c00d06100140e010000284112103804a40c090302603941903030010610b0810000c4814100704860700c0c081030054518408000a600c04c4032402c0c8114680014004c101e81e0040c810b80504c42e100f4150408250004941c0c1e51107024040180c4030312000b031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 219092248 1250 219090998 219091001
    0x203040513022502100804030921150518070518090c040e0c01021615050708040f09091202191103100207050606030c060a051206130903020109030e0f0603010509060103 74
    0xc40e41048140c030815001000761881603c5141624004e54444c801420250401d5402c0c500560f00180050744085040002c20310444038003400c249152480c95480f0703034039242c5154043c08200c889150a41d103000b400110900c0c0c800140e480c08a000107485041c0c648000201061400000b8030a000d00350f00019000c01c00501c0b00c0300c00c81c41d0041080050041d035100d03082d59032403001e10840c054403401c4003160803e041403a90808070703404c0311260121126441e208039429086110101c1d0100c3d81484041002008840d181c00601030910000480e0503544c10029417200101c22854159040200300140c80305909050b5110181c02003c400c951070115408a032800003060010a001031001c5103040411a020500600540b022011199507000035005c010040c840c4c8141007010a40c01c0003e00c0b99540d0a500441c0d0044004103044400e480d0404144269151200101c0041c3d40d50021101095003001c00002c14282c2520a11208080b55002c10501e100602546218200c01d00002d44242e129 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 219093498 1250 219092248 219092257
    0x303130c05030616030605030102070c050f0d0c0e040c0b0f071202030c010216050f010219030e191a010f0b0f090301060506070f030905010c02010e040e0a0203011b02100606020304051302 82
    0x20381240c0940c9400000420090780303401e07013000068140400040c05260500907540c0064108804820082c64202000503001c407110355181c211400350921000700700d03550860002007803c1411050246440e2520071480c404035048079901d0a0113100c0b204c4040703d0202602d030420f9100011400640e0728410591450280e03880d400c03042d40c0001040409a8940d1842c40b11130fa01c90301c04c8603c030480100016090313004007003900c050240d02505140d600b41c842e8019100045500c3e040d217249417211441d00002d450a070f00c05482000d00b4407150f11524141900d00d81c010b008064030480c0aa080401c01402c1e846600c00a040100003c5164035655500390300050050500900351a0740d00c0542c41c041c814521121400c0e8080398943d280081c840d400350783c040d4912a416911a080c0c0c00d00402004014240c1d6820b8418500c540c18086005031002d100306829001e900802c40014039204800a10308064400510311890900a04121041d00081a10240c990490b5140485102c03240d292009004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 219094748 1250 219093498 219093509
    0x2010809070e1017010516050711030303240a05090106050a03060e090d02071208071401090203100e071403120318010603030507060605041b050a1403041a01050d050303130c 76
    0x1c080d01409101404982e550f070441d00d10248150fa400c1d43d4082041c02c8400486590803182d0020081c4241c56200e00028034103144100020404040c440d0702191070b641046400b20100100c01e42d9100b1550310b5a03241107403840c0d08469811041d401c000c0072034041030381031144001b844004140d000c969802074201c0b002070844050304461030300c1c044e405240d450340e0000c120400340c0500070700444c88010300300b64101240e400c40e60040c601850755645a4030124030440c03c214555a441805005075028414181c014032008804140c81e04c0300341c1c840f0308001560b801494011211010140117440100e0100060304910304880c0d03c0760340e052a509003600d01145040a1540b07401e002100700758020001c0d040303c0340a40d500b08107460720b55091200300c03101076014401c0c0051010f0f60300011886032000340541380d05440d000342140141184529036410a690403a0310108010f0408800011100010b0043c10110f035107440c0c40b4a42e89501c0c2e103a1201170040c06400c1041c1c000340040c8406800254014030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 219095998 1250 219094748 219094769
    0x4050d030f0605090c09150f0702010c0c05040f0524090606160c120614010b160c090e0a020f01050f0703440a02040807060c02130c0908010b010215040201080907 71
    0x1806142d0241d69501154072035205606900c03047d03c55a00c0c83c001e450490a8000060f464203415400640c3c11444a64049816008104011a95446500524902c841d030503c8c042001e0900380348020110344040f1004501e42006100c01000303544039102550860000c2d01c00fa5aa8030b02140600900c442c6508007400000080320001032400c19070b003009446500034441000754099568403082805000e10944a402c1020300040c846002041220000c0d544500c54001d0700b5039807520100c099401d6007080740e400c0d801c011841c0d019030910403280351404070246031603071518070310384c5011090b0702400e54064208110007401d880300c045140c0c0324a0364040090f1000e01e810038203020700010a807200884a007152034500100d55503100703d000351810b840740310016064030b6080520440780300c5010074040e0f038040e0b546040074030f410141d445640070b0010203a0f07651408038100b500550a4031840c2d0032560465110010250a404045440343d4005d542460400702544070400e080f0316080480d040a0503a5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 219097248 1250 219095998 219096001
    0x2040f0b070605070f0c02120f06010b040303080c0403020a271d010e070b0414040609020a0503010501090f03020307120602070c0906060e04111602031203090a060b030604050d030f060509 82
    0x2038610310060850749108110600c00395031607000840c4d10254507121074012500d003105540051030b10801e6030350802e0f0355404503141c17901d061704403d180c18820707030041c40c0c003141c001401d109040c0d102e0026980200080b000500e0b09146070b010034502905486035120840418010259403036605100d04011009a03105004505d401207205021400001302e1420302c0d0302e810009107251002041c4e04044840c0f41c40c1d03540c1000d14203520942a10000b11805511507031f5103002048188252003c1c00140005079102c60b1207606090015115027419007180100c1c0200882c10001650009100026510f000d1040446c4490394542030001c0c3c0144e00004000107034501c000324440c0c0e0594083e070304860381992951045010b11081c0700c229003c070140750041032400c000303a44800d0b443e20004001203201404460611300790800200d499041514082180c0d080801000b05000e003a01603caa12482100031b002c240c1044e035030f02e6235140c04642d040c02c2810740300c640120041415900000040c81d01400203801d6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 219098498 1250 219097248 219097259
    0xf03030b090a14070302030907080601080f15090a02060904062c0a0207030215090a0f0b06040c091d1005150c0f210d110408011d0f0c040f02040f 64
    0x94404482618041c81c24080020280b08050140d0035a8882500b41c5091984403000e0440207507200070030030400ea200c1c1c04000500f0740f1080054600030f08290000c0e0100c00c201094803400c1002140e00700f500a5000700a200401e000031621000069048440d20798510640303011070003030324084d8440c1003509002188000040241c100c10252101c80302004503150b500d0340340381802c81c0961400035005074494032040d244002070645464011140c4011500034000c503654820400d45002d404448440c200d4040c4059070810b4094441604128184014103d0a001c01d1030341b0000b50240014900b221000800c41c0341c8404184140584005440a09880085c2042100c0e40d4080c1c0780806d000d1240240c0240005000704062080c0d0300300303080d042403080c0296500c1d45c0759084051400c410030781d02d484011400380013a0003800102101d030008a9409590300c4000f00c50541c007103040748643c0220b0007c4030b003044042002002804211000203580c00503982d004020b001d107802c4004141d031300050100c0c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 219099748 1250 219098498 219098501
    0x90109090311120f090d02100f020d0203040303050f090109090e01140c03010503070b031509040c0501080a1a040e07030204020706090b0907080c010509030f070308041a04140409050a0f0303 83
    0x114103020351221490181c02c800074a070340700c40d0240c0844440c0020301901004580020003410621401009000d524000343c000aa49191001d41c46010407100441400002e03010b1000540384149400518109403039034601600c20301c1030103141c041c16000000d210320390341e0064214802502c40c0d4842041005121002a40200881540350600d912a41c00140b02070100c0411a81610000b4014011080ca0074803a0011500081c0015009000480390034040342c48000c00240f261380101440104a441c200014100b1600070308028500b9003485001150145070601020700c02c01c050b940000c142055241e11403c0c5001a08029441800040d00100b44551604140066801041c9207180c603241c00020943e50348543c03086038034540255a49400d6580108050600c40f4005416140c14003818482c01341800b146030812600b0602c042000c2c80902c1c282000c00c0c0a410407041054607140c184100f108007001411040340c82151500384c65030400c0400c0c06003055140d40300003141c0402645190180 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 219100998 1250 219099748 219099761
    0x8071e1b0b0705030f070302070e0f0613020909040311030405040e01060509060316051302091c03020d03021614011409031c0908030a0906021b0c0a0801061503051005090109 76
    0x31901420160301145008681044403165940000110b14184110000d0b44850300415800d074207500030340b80c5c00200c40d124010fa2611441103004242da1600d458020000c3c92240c2e02800c40d0000c0c410711081d015030f240c0c18035403a0007540504007100c400580001952035482580c100755009030414650a101070015044101070714000c071855941540c52409050769031642030301d54001010b40c81420040c3e42802c4d1100d00301810310810251070b2441081c08203003007001541c40120315208500c004018154140080042c19030949001c1d4074000301e1800014100c9004480034112440c901288182900b00754407070600501d8000c4094164940a6503494580d00101000e68094000c20400c40301c048a0784240d04031958003103241421074071030b075641d2402003000f0343d030849961b0ba00300010103020f01c113a10079031039800200000300321580b410701c01d21184085950100c44c0e681e046c180c0a106100d0004004050480d0910380003880c0d9071075404142550007150b00c101c2c0c0104542c0004079501c610b0f40c0046 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 219102248 1250 219100998 219101033
    0x402130c05090907050f071104060b040b030f010902040807030308060d0c120302150f0708041425050a03030503071206050414091b03030405012106090506210a08071e 73
    0x80465691800c4c142ca072845a00d10804a02404000940001d0f00004060102e480007a10010385641c0740c1e5560003240d0720913082030703070f207404040200710810390164001d81c09054680000e5050a1a0145055407103007035000003801e00c210600000d005488042c200380c03034aa000280000c24650b10b10000c0c0305050750f0b0009070014001d100d009490422040100360290101c0d07810802c00380d460b008206c07000d5002500844040d240d40803600c0b40c428040000340c000308403070b81c8101140c0d81c5e50b40c0110310f415800d41c4524014141410108040798200c0c0c1981c4c3c0c002240d0a03d40541200704421400a190b950029503000d4a400039984100380c100700110702c2140c00c4000c4038440c0042d60200c41c00642d4841005c0c0d81984200000e10465101e2244524224148400d8641c01403420b103400d41562038907003080c2c00e0b1607a10010400f0503d03158146240b100030303518403000a141a1170303aa40e161400014040d00302c03d000200e00c01040612261080c0040c0d400c1440076200c0c2080c50040032100100c81c40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 219103498 1250 219102248 219102259
    0x1205010314060a020316110309030a152d11040b0a030b090f04020a0314031308030c0114070c0f02210105060109051005030105040c090b19030c0c1a0402130c0509 71
    0x701c401d00c062003224006d40007201c82214088000c5811a01e41521141e1003006000500c59500b25403000c100707008030603208884129001c02005a050100c0d114903c54600030a0000c4281d4941200b1200b51810310112210118121003440c142c2c404510690b8001c1c1c80c82000060066259540b40d402648100e400311101e0303071345440d801201c8000071000e4401a41c0260000301c10030016208a071130b852920403c105990070804546001c6100400715800350500e6000020301901d004428440c00c194001800403541c542e0400c000000c000300342c5543c004024007282c182c81c01c203555448404081c03483c0e0446d511001003001c404140c0c060002981e095001c41d500203400f04003807405022446200c00a42c0d1601e085030f283c44100700103813581d6a41c42050149100000c65201041c6004202502da040e01c00d003c52480b0946c000c0840701d44803410400c11441d0030000c400140f51034041d044442e00c406a1141c540c03101e00005420b0500010810001d502d000c8043c0040c3d6004405420382039000c690 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 219104748 1250 219103498 219103501
    0x3040c050108040809091b070b040215040f0603021303080a170603010c0c0f020402070501090b01030c0b0910390b060a0308070b15060f041e0503120a120501031406 72
    0x549402a043d50010044101841000007a043c55617400d0360083c21070640d4004110020442d604d96403001d43d050300e00e400114208420f50600340d886481c1c54030001c00f0141b61924003500d02c02c0c0800300e800384034201500045e69640000c04507620300051078000d50619a1000390380e0028084121140c1001450115000014124941803054480002407500d032900510015960040032007081c050032688590700740300701400300d0802d21901ca03400b840754a881a05504600346030f081803180d503001000102e030170032420100c0d8603807003800a12080281041c4594010340040021402c1c1101400c0c0c88039080c000389000200c15881c44a40c0d40b078001d0360401810740760342c02480300d009007500016007444070400c035541c0021890040c031944004600300c50fa1303002c0c03100310009682da070044408040401c00450148103d010548000d40d6a00b1506000b455007480c14000c6030312402210980c0c00000c1021902d0000d01e800385d02545141800d40204100341e46c1c580c9080b20b150714091841804900c1440b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 219105998 1250 219104748 219104759
    0xe0702060703150506090109030b0a0c110d170603030d0c0e19050303040326040e160e0108010504020d0f020d020d0510060c060f0207140f1606082202030a050303040c 73
    0x101d018401880010f100d048141003100340086039110380c2005040014051002011400d452087ca01840c3d9154001c40c46803e048401030004101018003601f0fa00071200705903501d45c110480c401400e60300c0340c580341da5985201c00a41180640f504801195060885413202c1c154000c1b17800340100412184082e581281c00344040901010b401200c0d01948104828804644d407098104511204401d0030541003420199501c25900070780e004851341766015080c00b44035030a42000301c012482e180750000400c0d9242c1c0000b031440c00184a914010717940004c040c103040c04c0c03d400540840355000c00545d03582c505002000300a61100007400665407410f0b0100714580c4c00e0303400c0c1c903040f1070141d91549421126521008001c2484c021401c0d4142da003000b5680000b5861070741c0150480610340078019030705030020000d003852998101c9035203d00300c0000622203039402103000c0360400d13000b0401c40b010132401c042d42890307510594006076040c07203000c0011017000f900100841c8224400c4e0152564599200f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 219107248 1250 219105998 219106001
    0x80f030403080d1808130612020306090a0e0304051c060c020c030a12020709060905061509100525080409110310030b130b09070303080f06180403020a05070e0702060703 74
    0x1404010207140041000f0324406001da0048858611200c10b000e1540321140e8415040368042c11400803000c450100c10030200d1b41005086000c503005140640c07445c9003031b40c002114080c1c002c0070760803810341e03441405031125400c00940d4045c01004d000e420043c004154103c14000c09440225195420928401c00051000c101c50000510140c0101704011031683d45c520b03402c410b034040100b144540d040000707a00840d401100006d1460034000034003814100203014403031111007801e250446d010407000c0303c0d81e1250a00051001c146140c4035895014000ba2060302c40309901030045024002c43e404814001017200034001c60b5404402000256018102000c40780000c07074010b003044406200410103d0160080e00f80c1c05681e12400c45484203456940310301c2d80800350355080240d4040351051080640061a4603042482180301d01c10529040c40000c1e10100321458a0400b4003260010600300760080140070841c0b070340b000503541080d882d5000e061255000703c85810042c4110303004540500c2c042e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 219108498 1250 219107248 219107257
    0x20c06160206040f0501110a0302180d08030a1a0a030308060a081519020c060705090307050a0b030c0a02031209010902010305072f1f0905010b0108090c010813060207030207080f03 79
    0xa4002d05a5a070311a110040c8108058509490a54903098100b000d01c08400003854098051f4800503100c0c0c081c140d451400010b69419280102010410310b00440c9901080d00d50003070f00c80c603000c02e0f85003c103940d00d807105100d440403541002403d9000b204040e04414014070696091781e41c0640207548410041d41c0b0024805040c80800d82c150100e1500d81d400344410b2010106950050301e0300c00b0707030049249840000c4408070b0025002003100b56082c07506004040040034100c801008480c01c0c290f9030103552102900300c0020040014a401d203c4e4000c1c0103176600350b05d010204810134a403007021140617011100040380040d10304000540c20f2401103500300e8102040181310511186080502c0440c280814020030207403040c0800d0ba0030310805440c080003a907025000119000301503150107400e40d400c0b00302442c1840076140c10888068000103100448030002d10388148680c42c1c0c900c070043c0e0308040450140181d0f0001a800c03081c0b6800040d40701c1100c1c00202150b1074480d882c202d0319200d014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 219109748 1250 219108498 219108541
    0x40b03070311040302120a0605010b0c03180118030b0603010f05040f020915060a02010603050d140708090612040b040507060f17090f2b1b0201030504060e010c0201020c06 75
    0x10510110344040c0c0300b50b0140c0820100545214585600c9400060104d10f81c15211200c0764050041d19041041d64040c083c010700b4107100c0c0e941060300410b4040e0f164000e02c142c81c0742560103190b0040c4aa0711520b100940002600f0030381091903264242051888000c582c170a00a41c00d000011013041c006105040c4a140c0040e80a207a52009500b00080604060580300401224000103915561118000c1c003d01809400008455185180c03ca0400c01b9500304a01400310202c01c2003084600e030011224003951102c0e02568411680001035101e0103000090765078030041c0c100b04400c0042cac0780c0172070340030b54024030859001650b00d03941256140040300e038a00c00982041014915071604050464100101e41d054641c840c00d9032070360500e0417101c40c50201c0e08542c110040f00b05003241c0b46104e01601c032036151075241c070720041401352186141e40c1c03002410140da40300000d061091a40c41402a17044100081c41025403040000f4040c0d00030000300c040d140030300740105e0984140c103500d103d170081 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 219110998 1250 219109748 219109769
    0x6180b2a070302092706090a11030c03071215060b04090e0c1c0314030a06060f0c12140d06060e011b0c0308091f2a0c09020307020a0203030301030b040b060604 70
    0x160382c4105c0c030181071a40107403001406549172010485c6001408020b04c0380307031560010a500c174071605009001142400c021402030708000801c5c8441e490214003242500c40e03042246036050308c58039000e841885040980511540341c54004290044034100603c101e4000c0760b401d003e058a00f0010075203407281c61410540c024403c1640c94003e0a02014544240b406810100040c0600154403092540200c07507009840d940c2d203905002007600611080035013481449c00c04206651696003900340700400785060140002400072800480320203003120382c8001019000c0c092180d4941c0094101781c5c031620842c1c082268901c0c034140c601c8079004c4060f480342d00706451201103455919035011591018000903046901c040c51400480b4964020600803140e966075004040803c03144c0004a00030140c0b2540d40c01c0c2440104400703e64407020780420340e10b00200c0140e407502c9211060340303800c0182d00000d415000200000042c03100e0ba070b9401d403085002d080800e006070789a5040081c1403069006913030211 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 219112248 1250 219110998 219111001
    0x10030c02070510170103060516091a031003140a14030705030702040504020d02061303030e0d0b0a0c02032109060105030d021504031202030406020304061a0a06180b2a07030209 77
    0x5103052030f402030f41d481c114202803025588103444000700300001d81007600c40701d48481c20b2014010b4804246003000300030b854001c0b8007600382501c419007191200c030045582c0d84c0100c0443c0031a01000074140085d50300968000e81c00d40342d0581203441d180c1d07281d001e032840c40641d4440c40c10030b1008011101c190b584900554a44100c550811000345800b0708282e80042d50540c400d40146c03145030080c0704185450600c0d0014501d186002400c040c04046014003c485004040e0005010803920a420034154180070030342c1d00c50003500301c2ca1800f80b103450540040d40036800d04200d035003010501d8080c0075401e055580ca0303a02c88090540e101248115200168400c3d0340109082c6000005140c000e8882d2420400c03151110364000300360b80065900780c801d1580002400308208092042c6030351000920b41a0700303503031007d20010307a054a8038407511003801408403401802e0309100800c4405040e8200d00141c0b610944142c87d041c02c11200700001004005001c80310b82104005150401c40e0f600030030841d0755 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 219113498 1250 219112248 219112259
    0x14090d0c0314090a06020703061a1507031e09051c052d0a110f0f030c040b0f09070206070f020109080a050c1005010602160f0e040212160605040510030c0207 69
    0x940340d00840031401c40b500380b10076a4560707221410f8200624817036008142c0356080d0304042d001ca8040100c40180c00c480e549010505494006072544048003241105882b180c1d24102584c500c4008514907a4403000796030005c0900f5000b01104050b03410035600042038907200c00100703803440080b04001c1e180b42d001110241188000d0440a442041d0160742420150b4a44881c141b400c0c1002c07004031140345404240064600b0107002501120300308490002c00741c005030300841d440c2e0050074011400b42ea00d48030300400c55120f044c6e009101c7d14001d40008202e140c0010002e4031038000340c80c142c002401c0c0a645004892050064402403500069010f140443d0208141d0700d59004200c00c0d045070040401c000648002489250300801154025200712590304000d160748950541020741402060102030050703007000107826031310035810744e40c641403030102c02a007616200988404031410f4450340c20104020350301801800c11100301f03a440002040c2450010303800c0d41c0001608400590042074200007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 219114748 1250 219113498 219113507
    0x1008070b0d2a0906030c08070903020111120c0609012406030b011202071a09120706050606071b060311090d03210c0e030706020106050607060203150d030314090d0c03 73
    0x498140030000c0c074400500601c0c000e480b5844500c00e40000c81c80c440303810010190940180c40c0c101d5010301d4005998a4864009805c5011600001e8100100744006a610203820000800320580c4104981d45404450044030396444080751003600035424030750720590700da0126a022408078018541880701c2e5003040ca04034000c2c080d1440c04c0341044903a154000888103148009c000160240014071615145000680401d040150070300129610807840d201540d000c210580c0c40c016445540450592078035130004007139024114014100c540da0300c40400c6074071604e480d46001c81c1c145440c00e202c824564103040d002400b0749008142c01203104001030700000c0c0705558100d0350f14400c807811603201c400039040c2c00894800e0041c04020031894000203c0618007002800018034243c0300a001d032604043c0811854043d80b880103007a95004008143c0c840d0f180305070000d10368000341528050840504008018010b5000440e10b56440c2002150000002082d41c00a01c229a01c50342910201035400700c6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 219115998 1250 219114748 219114761
    0x61418010f031b0b071b050603010f030803090c040e10060f03020d030c06151403070e250c02030d090314060c0406180f15080c0a020a0201120b0405010b031008070b0d 73
    0x1e0f242401c001d804251504200041e00c2003500800700e21390158001d159107051807415400161190383c040c80100410415003400505481e44001000d0b04ca444101d001841c080007001c01d10341c802d0070404e101c4642100054804026444404d0600a4940d41c8021a40d01c55280c00065001840c01e0405800302b0300600342d800380b0a200d0200000c4040664000c0110701d0101e07003280a8018036030074100602e01d0200220030240081c1d4854016038241000c0544496107442ca0304100e0000340d148990a6502804800203101d401609860342202041c200030800344543c082228020b171140641c82c1c40310030000301c03c0c0c819107000507218036180c1003040c1030303c11071040902008506404040840d407822003402c020003c0c0080e0300ba2000420803494042c011070b00c02040d11452000c240b0414401541c000703000170030f0540a0a12314001015001c2210103041c28524060304030307080c10000941c0d2a0b07038000a41c480d0003050b4030b042606840c1c0c10b900ea220104d80c0304a01c1c02085c284205149000e8540c0100c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 219117248 1250 219115998 219116033
    0x24030d0804030509040906020405030d18060c02030a170a0324050603060f031002030609060105070b0c031914041415011701091509060b040c0c06050910061418010f03 73
    0x244d0401c070034400040d040e100101030441d00e0a401140c02c00007030134200003a02110303102c2c1c1429070f5800034030051003000c0c0d6800c0c461303c020050203051040540d2401c0c0919044181c00840201302c41c0080503020185034051403120001a103010b402c074150180241c6002605c086c580c210b100070b103240004119040c0c0014004a07402404101074a0403030303500300103075842480e40a01c003580302d18160007003140142000f8580741c14000300300580700000300c4400c0e00c298040551215640c036910354440c100300c07000710498040803140c80c2840c41e40d50080e2841c406440b680c0b08034030b0358418541207010103444094403103c0c0fa00903014803005014100d0603040036650040011300001c0c10700450b4079201e441404180307141c0301181e61138581c0e0007805128010250f92910558080c8440211030034000e04d665003503a40680010350780d03030110304009014440c0f000705440d82c0c2c1c0c01f8400507481d0030303580c0c010094007200c1c940304025103200f84402d42482c84055049030700c0640405038840c91601ca00c00c89060300d00a1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 219118498 1250 219117248 219117257
    0x3106050a0605040e070f06080103051f0213120b060a06090909081905030106030b0301020909010506071506181406060415050c07030c080c031c0509040b03060f24030d080403 76
    0x402c16450343d2041045040d0703408014034400303103400f103c10f0300e07480d86822041c01c1140700c90050002c51400204400b101040030304400600303211080c40c00080c0034864030802c0c0e4090340c1ca00064403440d108040d40840e40207404240ba6500e0301d8081041c07038000f07841071300003040820008008501040d0700004446020702c0201349045801003418004640a40600300801c1012005101e0242e151007500580c10099000718940240f180000f480d110f4140315681c405d0100203908410040388800b030303402d45c9200300000c1c01599121110294000f00100142401c80d141078015103803100c1d8845040c0c041c01c400307096649441e00f00044001c0c100c18150f910343c28000d0801c20700104a004205100055000d503040c108540c1c01c00b509982007019601c2c81c05d2283e4031406043c005070320303200c0069040c20010304005070b0744c0ea200408a40640490700d40a5410b0080303034204102035100058003845005450740c40222b02240c45a03030207412040310260354041c1d00241c03071680020300a14100350014000d003807 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 219119748 1250 219118498 219118511
    0x714030312010603060e07020f1c18062a0b040f0203070f0b13060503070914210c01030c0c03080406020a030b0603250521070c08030903033106050a 65
    0x40e40036101c03000380d01120002e90b481004004184403640d015800043c64070103804410183d0b4a682d0359a44142140c1104454004820740c42c2070288542c007000038640c6202c45002c503503444000d450855115100000c07038011442035600c1c1d658520560311250b61004206d58141c49a480f0b0700c035405807201080ba014450844049022240c4922030b0b4010304009007100e60f20740801c080c000e00b150762a03000c402401410b00c140002503420656040c00e480c5c448082100e0300000000090306002d1060604403118a580c10f07500e03003420082034101d80300d14203881c18007d40d114683c0450b514030513141c014001071203210100300000d42c04c0e00204581c2040d4030b8085115100c05e00040c0e83c543c0103581101188038103100482050040b1001c0c51440722140c14841c0c00e01010391200745140101141d0580742c0d0100000040c40725008520700c0d91455045446952649842074683c1d54950003600d140d002028628014101c80d46c1c04020b02042040340d01c0c0e44103500e801903071064003914010301070350056510781c403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 219120998 1250 219119748 219119767
    0x5060307141c060b0607120f031a090405070f0603050a06082d160602030901081b2b0207140601050a03030c0b070c02150406030b040504021809030f070606080105150307140303 77
    0x580381b1203000e0b00c003180104c5040240640303445180100d4209060522071902042c5145001c0401e080405407000c2d0f040395580e2a01e40d00f810286c0d0854411801c10001c04103210f40e1550002d0710035291541c0400000d134a0303481c0c10b81ea80002c250140c6401500c04096030030801c0c0e01058000b0003000c0b10441c1c0056146149081a40226030090b000581c00820004415a403114081c0c1e040410221700720000d40034981000100d00c00e80c0d1201e40c00345500300008080143c6c42c0441c0c0203e6200a404640350140c0c1c0c42c04c201c2082d80d2805188642c410000003080600d420014242100c0e1b0540340c14201c034649e1b80c0d400010120040c8036000340841d034050080540c5030940080e0601c1c03060410f181d03480f810004c2c05070844114280c1c15005a10709410000140c0f00d01981c40b0301d5aa00250003552070740c0ea45000c502d180704440c019040400042040000c100481d0044c005894001f0001e02c0142d80c0e62060156010905003250b41c5a440340c8001c1050300d50650303403005445805410f881c60300b1400e8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 219122248 1250 219120998 219121009
    0xb0a0c050307030c110d030e060f0408011103010f0605040e041403070501050115021e030304030c140d12050f060d02040e030f07050d090e1618050d050105060307141c060b 75
    0x2c00503800701c1d01002c4981d041004415040e0900b60040b6060f00c001d1010b91001060420310345e0440303026150004070070450f498504103560082c4070240091007018950700c0500f440b90001c2c4684a07502e2011308000c075034140203805890070b4031701c206a0140280e50320f407105481064115000030060208000b5003022400a010700b5001c2c1c4400301400200e000410b100134545150720003200d24100e21001c29156a91000c401c507900f0540601c0e0282c6000b5290074001c400c204010320902c054070403003618240280e0810b0041d0000d030098041040556208000c400751181e048401e2a4040341414a00c0014070306a801441a0034440d02101d0400103000306201455020f034909550540c002860b140e01a540440300e1005002132080240040c01c10307a11131269518003000d232909120014000e8903260f050f1821003001440300030021071510f04a81002d600801d01a01c50314060700a0940104181c030094400501030300010788603c20090010130030b0b8490b070803440c03401c40703d060303c8400d9801c881d581d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 219123498 1250 219122248 219122257
    0x5210403020a0b0c1303021003140f01030b0f0c0d15080d1e0906080a0b03331f0e060f060408031801080c040909170c0d0e0406030b010b0a0c0503 64
    0x1c1d00106901082030a00c40d5a00e00700a09007900710404022a10310030400302c440000300ca605a800c0c0d0500c5a07190420380103483c0641041c1095441c4804025000103d1410181201e02400482c440303a01c411040d103940050486080341140410845030200c1300641e4410b00c2040c10300b6429001080d190492603040040e8600400d0000b00348401c0b100001840688550307002d006420014110b40c40d240c0041c2c05d0000007040b0031f4001c0e82d0344105186540341404101190010080943c03500d61074401003003a801c600c0181c59402c40c2100000444040d00e4201d0080413042c510304800680345800034030201c0d60130051080c0e80042c0d2200c000480d545034840544060a140400f55031180741000500c8084440c15104034104880e01003408848840d100c212000e4a91f401ca01050f80d80d4981440c004c5201c9100300d043c00d00c06e00103640030340c8650120b0300c00e001510641c1c075801e00300710140420007510790070302010f441400c0100c010012414120002c00d842980d9040480e00c406c60394641c642150030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 219124748 1250 219123498 219123503
    0x7030c0801090203010b0603161b0602270a0b0d020d0609050108030901020d0513050d05010e0d09050103110909072003071208010902070b0105040b060c190506060a06020607052104 79
    0x440e02d585204600d028007403143c20b00390a5407a2802e620340403020000c56409481000d043c041d8000c0c0d101c000c042e40c80301071031460780c00090942d80c40c00303000507083d030540b0b0034010918001041c004a510340d141400f41d5100311000007054a0405204800c013800039441041c0b80074443d41e40d140d0005070f10300e0328002e05008010360800f446e12003084000190406100c0d00e420020403104210f0710307000da004400b02400783c0e0029500c414400700d40c0d02e002e82c010007042c0f1440660784900c5144403600e991200350300f426101e080c0c0c0d0038416020b41c1c2240949a019910b03040381c1c8a100480024080c1d40704900c540e001000707a0341e011100710524100719042d40d00071901566406034074581c240c0c855810048071801098108011031800c0c6003a01c0d20480844180078a82c403d0381ca400440e00340da5503501c260341003105030b00295410400d0049082105459001c8111118011800024240e180c80c240600480fa8107802800296840354000c42d410b6001c61603443d013040040015203034204010042611461 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 219125998 1250 219124748 219124751
    0x20c04061d0105042715110c190305041e0305070902070510020a0e09090106031a010305031e221811030a0902220213141302160602070f03081f06080907030c0801 71
    0x707800c0010b00d003030312947c039076140c680c840400c11039162201c0002c5078450002c1360f0900b2243c14031140307400c440034811640011903014454803c0e60b07403914140100c0c0304991041c0d084138403042e910500d17a0240d02503000080c105802503035002642c4045900200541c2e402403030701c003000310303400f4000a1950200ba103540c81244e560714018005c0041c112101740844041030f0310f4940543c5155610b6569204400b90480b41551140c00441280c66907015129213083d4443c00f80c5030007041c5603031203503421914403c00780c0c00030042d884440c00d03c0c00da02c40c1508103004941000e10715a100c400101c09450350b02d201f01c1e0014003081082c07030703c440c0803581e01142d15441000903a4545603291100c1040000b900924041c0c561758030b50320720750340d00c02201500f000c0c04104056254490900c8880c2158444135015000034000518041042002e819905000380300b03442e0980c0b29258240180450412180c0070101030306840002d10203030740601c02d40e5501110150440310955260703518903112040d0380d8001c5125a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 219127248 1250 219125998 219126023
    0x904020f090f160309080a031505040614030c0607110613080102070b04110111030415020c0d03030219050309030901050304050f01090308011802070b060603060109080607020c04061d01050427 84
    0x803031011004a10f024140f6081c00386a8243d02d48225512501e48290241071b614081d18600e040890b01c6e02c0010480180104500d903511114403441412181034070748a80106103003180149000d000f40ca1145401420304081c040f481c0341441142c0d80a08400461444590000200c40301c00740014150680b00700f0b0080441d091074903080b0b0b00c03050344049440c148428008034a034000f01c0081a00e08807a0446101e80c0410f8aa0798141c0c140201c01440036044075440900310241901a0005e20074482d80811243c200e1180480844031800f0560301c0c1d02c019001040801c4003903104001442e0418060390903a40340e50300320346040d070845440321411000300d5140401000102c03001c28884509081c170440c15450700c04140c2d60080c0451008040742d110f14804004100d4a0f445000c0c56805440c4420466105003459000a90f4903d8003402007403186080840104100000040e400b036240721400707914840382d082000b0480501025040c1702000c1c40241c0450154800b665007048609000303241d680440c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 219128498 1250 219127248 219127261
    0xc030c0506042f030607180f030c06020606010f050405240d0606140a0909052203110601050609031009023f0c1e0307090c0305060a06030c0903020904020f090f 70
    0x6100f0249945554070788808070508180d1408180d00c1e80c440d40f103180104440d0003e2440c50504021b80e041107407044c1d0001c50100801c1805a2030000ba03540b41c0e02150032542d02c2e42d004507200f08030b2208480c0000c1040c401000181040111130b00007003028580e9060725110140810350be0f4000d10003111201303454520401c06103030001100e04ea04810418003134600303c081d0760081d201c0311561060980b816500c0300000d00d041c101e114124005000507266a06010f054113005201400803c42d4021034010800000f0f02d62800008455601c40d01034041d20508200b8071940000300131905084c0e0300b08400004840c91034038030803000721490b541205819044d414203103c855106881886140c000e502001c1710380919901e01c820460030600074620487c0c0f0340d0f800e20100303060040c2c07030703100b01c20321414000d004140c5074250f08213034441c92040e5a90449250323100341c100d0585441040c81800300701640003d0016040940815502c43c1c00600850940100e00c00484c4214100f103804900441c10714091182 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 219129748 1250 219128498 219128543
    0x20406050621041509030207080c030706090b0c0c12030a02010b0f2b0206040e160f05160503042d0f03020a051c021e100201050c09010c030c050604 65
    0x2801007550100e0030a621803000107800c034004080c81c082c0c0084074002808105043c500d8422103c0c0080041c001454207240c007030360703800701d600030b5081500500c8211516424002100360848220355161203215140c0100b041c030399401010b180c040b0b03004a806160140c0c980001c0c08002015000080da40c036003580394000d00311078002c3c0110b4403502040c0f021180e83d0f940d403003040c03200d43c0d1000a4691611441c5112244617048014000d40205020a0010307407649a82102403003051408002c004c20030002404903010740c4107050b0500403e40034807560010404101030501240d210360100d916045e1901c92400800000c000c0750911020104007241c1c24289030b0180200400041514015050a6500040080d209401001e01883e00100c2800d051000c08108400c0790b5000b810342c030b1850340d0000000159258005a46002d50b161150b4009034910501c65644030341a4444001e090403604070046403500303144074040d810021050402d0000c540280400d6002c3c601c030329000381661044a40d41603 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 219130998 1250 219129748 219129761
    0x90d020f042d0b0904050c102303070e06090a03060e1501090203010602010606091802030a18050105070f0c0b0118090803010602100f060602060a090507150302130f0830070f0204 78
    0x41c003d82c490300a0000081b070006a84000141c201c4a80c0c2d200c121b960740440e0403046803510704403040c211400c90b40241d01250011070080794a69140d900703d8240d803090194600c2a10f0610743c1140c01000c01300081440c682c402c00350280314a00341e6849906a000f8941c003a482a04011107143c1d00000400101c2e0f02449010010301e042d060a0a5240c502000d00480900303040080d10035035000000200b01c0040341e03000788400e80410b038a450603502c0a0800a00034007048583d03001090543c035040401074007407000c1140d95540400202e43c0c903800d002c020301c410010b10111030f143c151500c207070380c001070300140165001c3c003a41d45c000c040e15480c0100c89816180c08030100186246016021312003603601084169002802c0c650208000126180251034801680d010340080940c44a0a424903503140e002001c2c0364200d900e01c006a5a00d80001d03651080c2188150b007415800151600030480f2195103044207103108621008110a410b000b4010f10f40c04424112000000700c002d000442c5054800c0700c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 219132248 1250 219130998 219131021
    0x60e090c06042304060909060b09090d2a030215011e090504021207060e09060307060f080c2b050708091f0b0301020703050702031002090d020f042d 65
    0x40c100610050041800341c4070b00d0140700c0120707080d580356441d402080c00300c07040c00c01006070003080116614078200300106200002151010b0601410318040d207041c06030b1038000d0203c2400b40014104d50b1005a41c02d182c021160880c0c014444500e440102010300400c09490103500988800e072189880e000340003e05030407039650b0305c45072250f80d40b0070a002d800d41c0b010b40d17495450004e07080d22540000352844031500d1040500b8131a101e00401c8241d8091402c03005008103a50311680c0b500d80c40c042546400a902610000418070003100c0c3d0000d119403103254105900340c0e010791030030544040402c408a180001e900000b0046a0045e0302c0300c955100d030f07550080c3c09107441452414105446600e4001540c0008806c4d4012402c0b01d1251040d98404507000301e00500031940c0b290140350282540c1c000c50010b0b07205c0e028a4102da16600c1383e0f0300860f09045d80080142d6091411781e4204400014030350002908150355800c502c055034640181149441d1204c0200d100f0a40b101d8521025903020301d801 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 219133498 1250 219132248 219132253
    0x50103080903120a09030f050f0a080c0106060507171308030a0f0f0201201b01020c0c011e0e130e060f04060e0a0c03080a11030313050601060302030f3403060e09 71
    0x71a0b105070390140301701c0256030340400600319920007420024600b41c44000710700040e00612051074200040c0c0001840d840560750001d01c0850355822068496009808015244203e8040740038249082d010081141c6003c1e45000b03642c45450b54900c0e0b00c3c50704518034400108084100425110341c022005506144c0e551009011841d02c2906041000c40030a00c211489500450003901c2448940c1c600004130000000854540513000a042d95030201608074501007085c103030000806080b0050780c204079084030340701c020410400314240714030158000b12401d015595440c3d1110f8010092040c58028002cac1240b8a1103401c250a00c10104d40010103442d54580c01040343c0c0000030400d1150200b220741042181e038071548052015605a010b100d40d500c002e010000811040e2a6204408440c16000302c0483d0226030f00e440c400d80491200b5100b5564a506c00000940c030042c24000e814041d0340e0280c01c0102c40d0000a20013010001000107840200e91a02401d02070448078000c11035010615100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 219134748 1250 219133498 219133507
    0x20c0f1905070b03060f01030c0327351c05092401060c030c02030a0b01030b090d0302040b19030603051006080615010c0212010e070e041a04080a0318020405010308090312 75
    0x2021400c1b14a440380c141601c40c0000c031009806648002d298540030407a02c05070101d0104600206c0749842d008803580400345030341c0409018040b400c2d074018012a4445010315001107246003040e04940e14a1410264410160712040703110300907140500c0714400180f01c80042c900e070110944078803d0455800005031001007090303546c00f100b208585501400d140b81801c482c3d0002c64100800440d010300203903a540d0001042104501d1103a00c0b49002209590489910820482c264440c41c803800c0c0a0500500ca1406c03500750315090100e4a40c0c107420001801d983d80e80d569810440185c01d0b5105140e580c1508010014050120715070003201022415942c9007500300107001210100e0700a40a80704000244407a00401d40c056901c540501b82112401a981d40d81e040380c600c401c45040304c9003020200f01c1402d00d110716101c54003d9901440d01810440b00fa5000c400800d20f1108921b204a418040000036840d80d102701c40c06903004005c1b00344e407084042c041c075180603800220010031120802 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 219135998 1250 219134748 219134761
    0xa050a09020102061b071a1602010203100608130605070e01020c0909030a030e030714011a040c0807081519090e070b0403020f0a0b030708090c030c090a020c0f1905070b03 75
    0x7182c4da030003960100d80b8400404031415525141c0180d000c01414280713012107442c0c5107500c24010038400d5102d22080c41018480003001c074283d000599811240e00c4580e802800054003c8001d00d17803080030041c0b6503421030050348a46c01a20000d03100c04010030068201142c1c1541d061080901d25601603032002024101f21030320664074810455040201984c5907541041c244060007100c031840d81004914600380c00d05040301c1d00800000760007450060821401400a080c940205141c600c0b25841d42d4680d507803008410b07290b807080100602c1001c4072468001400d6a10410b4030411140c8400324040b850303080400f013900f180d40c500904111036220740010420240f25504a800740d0742c0c103951600a103100d501c00304000031101c0e0045110305202004000d05582e203d500c3c80c0c8525a01002c4030340421050b418035440d05030b129080c5400214400000b001d036070031340e0014074010544170100d403400300340010a1400c0c1580742c40d499076500410b40c142e00c180102017091002030b06d0240c0e420341c0f9501340392 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 219137248 1250 219135998 219136003
    0x1505030c060a090b07060905060403020705040f0b0108060f2106060907020729130b1e21151818010605060d09020d06020d0f06080a020a0303110307060609050a050a09020102 76
    0x1131085642c10031000074007000f003000780e400003404c00303600c0001c58071702e81001d24020351139201c1400741d680aa481e00d1580c90b42d805450181082403003040e1984046a12018180f094858614803616017061030700c80d50314031282c1d000c200021038a0060001d0000790400100b0000c8960700580000110741c0300139014021068941e01160fa000748201844d00704540000c111011401480a01480c076080c2141c0040d051072484000c1c5000c00559449545a9040c03020203c0c0c1c03800307508020a03842001c0c1a101450914110b11140c001c50f5030818440c9841e00000040c4481c00e01e000f0041111071500b0030300c01142c0c1f1070150100d861a03003400a0120f1030804020071840d0280c0c2001c01d0728281c862446606644072035003a01d025682100d0305660303600d5010103a0f8090f2421b655070000c1c20f031a00c0d4001070700100104030300300e405a00812241b9030701d20b1078508071804d4014000c0c5810b5030000b005a0030000f2064841c2d04000c4c0792131900481d0328034007001d1031021200c0062401081609140c00040141e130302 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 219138498 1250 219137248 219137267
    0x4090e1203010806070f020a0501020a0509012c04240618080607022113030606080d0801031502070206160c051f080a180602070b0907170627011505030c060a 69
    0x4920b400102e01d002c8130400c83c40c111400d080944554400650800365551000051440e6071003a01d80c03160340e108460140103c030818111700054404c614301c0c50041841d1030780201154a6019a011980000000c545848000c03140d000c48003103180c030304a200780f035020850304174018000d800190200703103010030029488040002018005c01c43d103815020703a039031041040d21200304075034048100c0603841c1d10f050401007000b40126a018480c82000704030151050900d0b90582c0d40c4500001107040e460700b03030300000e50410341b400c1340c0c0520b0500c02e2b003c1c040c0500100300c049038090220b8011440c540400e00c0881600c42c10744542022103460040340c050b03082a10190402c10000b0001400d40c002d80743d1540c10382e03041a006108a0002415901b441410040746006108007401c1e82c000302da54030850007412000d0314081095402000009800079130369112110124101304c108540558100320440c02c640035035028030202c0d4600c4004ec402ea0800f00a80341c0c0c0c0702005d940e07861820000c403070040d0010743c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 219139748 1250 219138498 219138511
    0xa050a080a0f060e0d0f082202040908160f02090f1e042307080f01061206020a051b06041a06010207031b081c0f0e0d080a031104090e1203010806 64
    0x81e102c0c00392003000150f9111101d58090036055440c10802040006c03c0b829070f40640d1070014005d90041504480524501c5100089842c410a5500d800d1f03800d002c090600600700360303a40c8e81c060117942002d9180105480e540e42c450b1403812085207070f901c1080007241010701002e04c0309890204000601107040d5080b401a01b0b4040c1c0d000c1c0c00d546071f24211188100c40b500c1309c2122002e08816110010380015800c0680e0f040005803000f00e40d2044016088460521030b6090200106200c034010882d140d0040800c40418509107140070303201407104010840e040082846580003c4c100410f01a003aa040c1011b403659a4840e0094200980000d550b00b01d180000b07000903c40820103000017440c50802401005210305076070030b621540c01078240d12061003100c00085503009401e0321109105000710701c0d455200400d4100011a10b07101c41e102c617003180034418245543c480101c402e4030030400281004000080300490b09164031000c044c10300484461103004640240700600a0a4000c180d40e5030240 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 219140998 1250 219139748 219139763
    0x1030e01060504110c0c0f0a060c110409110102100506090c091212030403020d090302010207030b06040b220f1104090e24010302101707080a020408100603020a050a080a 74
    0x224408180e005041039488941d101d4541460074012591040c040d0103210004825a42a00e6042051140c001c001038a40e40c2d101954201c107100c014003641000903040e00414039241401d40240201e01164203020003078a02c03810048041410f983e04000950303482040394014080d600388000071804d8460b024100007241400070554a4440d00c81c204425400700d0610101c031a034420720718000c5201c0e4400d0350305070014000c44655460300b80c00307514000101d070f5043e4000d01c0c00d20b144d030700c40d03514620380500150b40c4544c9031205420141d0340c17004003601626240030b65041d001144008001250640c1000b1882c09082002c40000c142c03c01040d20102c50141d040483d903d9500e0758024140000e501c019441e902d107440301588a4411209074a0507a8801d4415642010f5212401d0340c030b945a480c1c0901ca141c030120002040e080c404c01645400c0030481c0c00140c01c00f603d5010490401c04103001007440f81d580c4220800661030001c4002c0020401540e041d0052400c041c861078642022410140100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 219142248 1250 219140998 219141011
    0x120513150c140912060c0405040c0f02060f0601031b0207060206090d0c060207030203090d080306040b12100903020304080106090f0b0a050108040f1b0311040515031b150a02030703020712110103 85
    0x540314001004d002c1e112070700c1034612030710307107034078016599001401170901407071410704d04010141c080c00f010000c8112a0300100201d0b61040709134204204003d1041d03041507181c0b00790840c03080541080000700c41ca0741d00900581828000000d04c0c2c82001020740289034004821140d00a4001c0081a40c21303410480140e0b031030302c03241826451445901122900302c035000e5901d03001c1c07250400243d03000389000c440c01d00c00310340102c08000b80100d00c2c007829071540c2c100b80c0c0c02030300280040c0d11407401c281c480e005581c00d04d581c0740489401c540055207d4400c01c2c4e1a6024140802040d100380000028225503035010746c5e081c140002e1000f04000c06c020b080d002030f1401e0310207000c2240c1807081c2c150344011004581c5c0340c481c54503454119407001120300881c00c06001c0b400c03030440080000f07041c000c05002820010341c50007680c0f0700c1c1030b106c40449400100340d82c6080260041c0c07000a000c400c440d50029552480c0b01e20b4003d107000141c3c0d0090b0030340c0342d42c840084005104051307102401c1c11709180c0400c02 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 219143498 1250 219142248 219142267
    0x60601120207060b0925030c050f0a110105090f061602030a0f0905130915091509031101021b062d0a021201061805040209090a050403120513150c14 65
    0x28035130080c01607881480781d010084504203000740180c000d01d18041c800d1185240c0201903046d03482041d503040201d0018401a003142c40078a000d0011484245040d140c801d064460150840b107050b90b520300740c3d400c0540a40400d00701040701c141c2040881030030044962810070000d4890040525030401c20000500515020b485075241e44083c00d401800310349040c00b0074100b10010000040c048038556034101240c41409e4040c440c0241140e005600040075006880c884c000030074075030702c085040c000c2d08038080c138641c0400d1000d81310b03c0c40625054085040802c03609450b0000003407400d04040303507002c1e02e181c05040f070a0a001881201000351100c50b129564103002034080d840c803100620200800000d03a281e0311022102002c0c00c2c5110b8400c0e02a10f45051000343d102d00090a50001c0244001c507820140039408541d00078041c0c9003440c990824081101c094800a480c084610484100d811050020607540c000012680842c10441c0254041c0c0252108400110401201001080c090744 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 219144748 1250 219143498 219143501
    0x3070203120307020a0c09090c061d15041806031707110904150f0c031109010206060d061e0221010302030a02090703060b0c030d0e0304050303220509160e0306060112020706 76
    0x30417551020700d05620701c0d1510403800003015480300070790344403025680000e09180904548a81001c4420f803050000b440c3c401801010f4603030004614940d04100000100b4514a0301c2e00ca20148103100007080152950070301c0a055007244518240003401001064001807034030402000c401402d03516800e00e559241000d05545c0c0d9640c4046003801c0c01d000f55800d407049154041d000c0769910392801c000d03c0261030500302044c05100c1d60030b40560301410106103646002c0e620220707468416074010039951042030f190f807c0f40c081d0180b00c5034460740104031410071440c0c5079080d440d100704560b203490080d0314540009948410803100603000340c0089012501180c401d42100300030745203c0b256940c4e40c4034840d0a05070b4940c00200c03001c50080c508000d5540c501000304c01c8804a400040003141003080c4036806840d00c1503052100c0906984c01c100000d09500c411841521803034a081c841660110180d02c003a08030100b81c4081c40c4a40c01030001c100303103a0707004505400c0c0e04140410050310b8208030f10b081320 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 219145998 1250 219144748 219144763
    0x609270203010603060c0e030d0906091a13060809060c030f0103120e06041e08030301030b010512010e160e0603010507050d181e020102160b092b0602030907080307020312030702 78
    0xb400c031404c0070006c0c180340360000c4504007040303019012034215824003a0211924140382c06034500242c4503d4040003000d200800404040007500c1d035080c902210f60400c0c80d0706208130362040000c00e031154204482c0760014000b00d41c3c0216110700301c518514240500c0200710005000080c250354070744401c41c01e4a441089022001040036122580d200d80720140300c5109260000000240000440701141d000400710a480c1203992005050443e6401d01d030402c8201121040710719407565842d007640349840000c2109600d11420b00c106140320508242d00240b14000041200d8080c1c0c0c10306060100256100c0c0480c2c80c4c000c82003000003007030000c074034100803c080c072400003510b031140d0074400c102e0002e22103a4410a00d0300c00d0302100c1c459459140f0b0b03e2015156031150b034500d201e00b40f02100060900d0401c1342803c017031003890740c000098281c1d80d202c00e0394103089088d00c290703a01004001c80c1c90010001d00000d812090011404c2c00056800640d032a0700361500851000f0003c40881d9000b0300030040e48 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 219147248 1250 219145998 219146003
    0xc060c1b0b0306030705041e1805151603090506011503020408060a020a030509070608041b03061506020709020c07050d06060305060421030606050d201c0609270203010603 75
    0x4845a60341c40d000e800d940050322050b11901400d080001c2d41d01d07040c401d1031070900040c009a8080780342e07140584020a006030b4840a503840301c118001c00224140a8100c8080c021818680182000b1006000080c203030141da500345450804c0020218000284990448194a10f0400203034144801107019020b543d00640c61403003541d0a0005002440e00a0a84201640c0e010002c6640b60011195a03141e54031a410201c0e244402041c04200c007071020f01011034103502c1e400d41c0f56a40360343d00c004a07410b51400c0382035044a078406000d140c2d0306000340401400070b21810750501081e00f04203901d5000d2072060350700c115000181d5a0822000707401ca100210f0b00b00b82507854510785030800e00d00000a541903448004851004840124068400c0c2400d4440a80d2043d06198204c40000001c04400400380510510011003a409100040081803601c40c1d0208405880020f90703120b01c251042070f04a5001030b41032590800d05140e5410f0700103e002c9107600c800c08825014004070340189410b4202 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 219148498 1250 219147248 219147293
    0xb04060e0313080f06150a171903031401080105010803090906120a0c0306140c0904050907082e060b07080706110a0e030c0a0b0d0b150c0109031403040c060c 69
    0x7825800418080d00c3c013440319090359043d91340c0410300d021494000d2110342e40208911401d1040b44a015070000060a541044402c0d04804005080251000f13900031800291142454810790342070b0a155401071070301000a2000d075040c05911626400b0342d40540b40242221400101240e407081000040f410075131043e1406003d031070809079148200343c08161091400e102d400d448800804001c42d102d2482044a030b4144003d0f401000060302d400b42a28446114050340411880000d01800740d2404844414264409500c140d04a041582c4186140081e1070040d04000326000c035812904590307400ba0440780e17540d0540c80c259000380580b000c042d0079400c0100d0410b4040d90441e01e4094005421022214070040407020040b1100341c80c010000e0001c81070291100d0383c100ca0f0049606400000c02c1c110820550041c1c000c842c0d04606403114a80e910380b00c84006140d04400c081d80161070fa90452031641c0303010740b0350091030105440380b442088000c4105100344010170642100e8610f00408 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 219149748 1250 219148498 219148537
    0x9131b180315050106260c0304080d0c1d060306030c060c070e0a050a0b0910030209061c060507111603080f0c010218030f0304031104020f0405090c0703021204030b04060e03 76
    0x442e103004003403d0103410003241e43c0080c0c5400006a501c0752618501c45050384c030809039103242c44900301d608064001c503046032083c021103001400d103000e0300303110500f182c0d87e4414840903020a0882c40510750400d82c05041d080007032003800c0e103012410060071070040d82c0582d5580b10550215241805a9209d070030803101c0c540c20311144070b80b5900600d01405103058240580d11034141045003804051300d1340c030046102c0c00300402c010300303040d403485500034001411880c406030020444070b129440008119900c561340e504100c00e0719000100080c007041c0d0760000b0026110040500001070f191404040c01000c00400c042c462050082e04844203083c007032009644420b00700d21521412401c2c249041d00c203006820441648143c00010342d0200ca03044a040f0010b00004002c0c44000e6020031401e480460b4200404240d81d1a4405040e016546402031555940031740e041c000c0c10700d1503204800941d00f90401040020402032194140c105030130040000d0340e16001e000c1c0350700c5c5215421014140041414 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 219150998 1250 219149748 219149783
    0xf011b0b04110a0810050a0b031f05090316030309020a17030a030c02061006050c0c061b01150e0f0703060e071106010b0726130b09131b1803 62
    0xd81203400756204034203082c4a8600b40041201c0080a03000d1314203540d0000e00c030008070b100c0f5500320a40010302d00b000016041003041c0407900b003410005910041900071a244608500d4074490307198040c0005024604050074444118000b41e0188409004c054541c0380c0c000541d0750b5140041c0007403200c80d2038400750989804465403250040444000441d2400d00c035103900710700100c1c0191080750050f4490304094184001a10281c03c012410307440d501c43d101c50081c031500c03050018001d40c03801150813140450444130150a40b148400003200d04035041c003082101203010344c2c1d01c641007044004d01210329038855008500400329544040300d461185000c2c000c0c0107811480001107000fa003c160380b030503070300e820340640c251141d01d6005116821008000c6520102c403600d81034082903100000f454400e01c1140030026000540103105400c5001800e246249881030384022008243c00051140d0080307800407c40c01041000f0035401c2c0a001245d01c1050b00d18121100e0140d40d200c088007030340a080c1c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 219152248 1250 219150998 219151013
    0x409030f18090501091e093801080601150309050304051203070c0e0702070e01030c061412010b1903050609040803100b0309030d140f0411010e040c020115050604030f020f011b 77
    0x1224030200c031140c41c01900c142900600400c10700b00d0b0000e25040d818625501c00550310790236401400404001ca2460803441c0c440c090b0524024601240280070f2941000025440302d00c58a01c0407090518080011000813008004d071b4003160303411140c1c81424404004443d08510a4003801081d5a4246c4c00100c0d00e401c0025031a0b00400143e400c03121541e4541c4c3c440203036041c3c00c0c000505100ca01d0201080014814080305000900d000324a0782001011503810340302040a030041702c55400c1c080341070380b20440c2400714008100024a02444542401d41c04208040740113000680811000000200c10b50642010080200514008035541b4580420410307102e80126030900c000c1c5081404042d000050440d000c1e0003007501c059071300b061703860755030300c42ca0942c6182c1a4203040c4800d8880b01c0941e55a14403c0554504a680011414404110800780f60800c650051881000180300500c0400c4204a54007852603058401c020b1030741041c030040e070f80140c0015410844540005004c000c20891 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 219153498 1250 219152248 219152261
    0x60f01081207020d021f030f0b09130221060a232406040e01030b011202100e03070b030a05090106050a081f020904050103050a0308060d020f220c02070e060409030f1809050109 77
    0x111f940400c83d13195405592015034850404a0368405141c50110350b107041c020406122182c4000d24590850305556406c00040c0c3d03d0b80c3c00041a41c00001c100010b0b044d050203001c1d040070702c4c40055046502440310740d0007070950207015280002c203003000444140b44480d422106500c801005a13483e156180c0c3d04054203c0240400c0710842211800041c00d48100d800d40e40ca8183d000b400c070541490207503400c4407400145046603034144100140040c08000d0880214010703101c41902081619203034142c5801e44015921803400380e008000200141c1c840070660303030700c801809409000b10450300a11100680507840303401c1d03401132a1100000821074000340060740c0303d2180d01d80101e40d036920810004003e0070a1400f941103001003800035010300e407031300119549003501c0c080e00340d600312090511000c0310054105030015a0101c54203020343d941d01c4001c1d07503010384100c07002c0c031185202e0b5a0051100c0c444007000d8062051501c1801d28450085400c03102030718501e1000c020720341c0c0d1030b071058014161 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 219154748 1250 219153498 219153559
    0xb030403200a110f01020601030206030406090206030403030b0f090106020c010c031112070b0a0507120c02030705010905070501090f0b073807140304120e0f04090b01030302060f01081207020d02 85
    0x110b0503104070303a8281342440e0f0713440c24130507005001c41d60320f546c00303000540d0b0009000303d940c0e44c1e440070180010780d1514040c50040e40030750380020302c0d07110010600c608088401c1140340f0031001c2d03400400c00c5550009001240050038a425004294189030035643d0001d0707540b1640b02c5000f140e00d146001c5d0001009040c4850065543e107015445d0f40d8408412500d0583ea040c001030943c1080c41101d4145070000345200c030061048901c0c03c0050784556085900fa260700f29002d4103c01c10030001742d0790240c2e01c000038142c0c1003610000d051404038100058803c8510090130001150641540d5440711180901c203d80e440104540e16865503010241c450710441d1400007043d80b007140d401c0115203500903244102d03442407061aa20f0f000501c1600c0c0740b110100142c0e4404610488004252a0343c002d0b9182148240b01c8260a541103150203030030140e004040d80040c01c209c00c0100010003000078104064000303226513560b50103030750021940d10140030a0181d00303c52070201603c0380c058230000320800480c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 219155998 1250 219154748 219154763
    0x6010e010c0f080a0315080d050a05070b07120b12190c0302090703020301150c02061b1204030609110319031d101d04150e0a0e0d02340b030403200a 65
    0x141090780307400d8860824040d03247c565104020720200c1d0350282008051010341c03428004e0601c1c8140e5a603101c0514106e07100300000364005c074241d49292481c0204000d03c0380440d00342000c00e8510303090a907286c0d03041111070741001030145008140b0035141c81c11005580c0240601c40c5600d0105000b50180d4000c2c0300f15944000704d01c0030b03c10031500c100304070344080303500408251502d03441141900c6024014503000d1440d00980c40f4608880b02c0c0080104000d40c421000443c180069083c43d4007440c806032240c0740039800102e04000505100c83c260031010368181490400c40140008818001150080054006080050882d0400d41000f048032a000d201032400240c0d00844081c0b0054070744907940321030070414111051010500d1261407640c07061286070001640c4e0700da058040d1800b00c03204d00780302c050f0304035221702d4900c030080c0240c80190100d64140c01d0040d10301c0c4001036030740d211244108001007401101007010113124032000e800806281d4a88600030340744149154495940c08021110b84 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 219157248 1250 219155998 219156011
    0x8090d2102120901210609360807030302041805060405130302060109020c0f0709021207030504020a090b19060908070807081e10060b04050405010b090906010e010c0f080a03 76
    0x1e2000410740c000c200c10902041c10006401d0054686030f0350b00010708840c0380f501c14040c0032846280300d82d0000f00031800c4086544600001c0852484c2040b502010301c03c0212807a800390135044e4586400c51b1644900c8043d40d45141c4d0400310001e001e5904943c0082d4030031410300c815856290030183c0039400071030302005507071140c03036042d0500300b03440e040200581c0120340100480c44150f40503141d5000c820342034a050102c844607640c102800340e00071020030f40e0301151840020140d41152070748003000782000c000e641007070340000301c1203e000d04c03070b084909840c1c00c184109078944030b10045604007038041c0360403880d0f2a060301502081d054081d2030268414404001907103a0001203c50458204c40050925498100c1040542504405600c035051084200c001c40c800341c1840740000034072224040d55203403410a4100002d071507040c0d010b01c14600061095640a80d06c0d811510740049003401d25541981e1131800589850401120103055a03181201180038406143c005144100050f681081103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 219158498 1250 219157248 219157313
    0x5072003090102060411030f190506280b01030f021204140102120628060e032a0f011b08030f0f01030b01120c171b030118060908090d 59
    0xc0e40103005403580141d0000c00420081001c0c110b090b0a00700f00902540e0140c28401385551803c3d40c49040b02ea90340071260001c400780281440341d650004081003014001c0ca00840034684a0290307425010030590b61448800703182da000340e010000100710035800f5500e82c2c24025054402d204115415074100d4001c40449407441c5043c821101010200128003045407955000d01094801e00609240e9180d03581000302d101d040100c26002c0102160780e6050304480d03132803040c141403c144100749443c43da842e00e8001140700360000c20206480041d1240c801c50f1010b00c0040342c107088000049616680e81c81c9061040c000310100a601c11007000d0f02400e120385541e40c480700384600034032014003070040c0c20005101e460860b80ca880b00c0d0502a00080e00c4441c1c40e00e0045032000340340117280065034040800b22004120400c848849030310100c008010260809000751483d0441c610000d09090313640307240c80204043c2c84162480b50601034070003410220240740001c2c10074040203400c8600700901549429 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 219159748 1250 219158498 219158503
    0x20c15010b0d09050708120301060e0904030507030e0d020406090e060609010b04120f02130b030f0111190309050601080c12060415090201050705010908130608010807030807080c01050720 82
    0x480c0c116101451906600070700c010003c3c006000c00303c0795405800c20014002400300035a081c408008079540d03560307514001014103250b03145c20503923004150032001c110201c1e42001c00c0c0d8200e25010300340402c01d00058000940740e1540050020340c4103240c5071300821519a035a000700b0401083d0b02c12607604d91581002c1000c0312409100340c82410404001c00d124205002140e00d811900c1822121140192980090070001c0031031080324156a0340c51030985940303802c204400301a00396400811404189802090700351146e1226000c10144a02440b1102c5100384d1045144035049005e0380c08035611114035548a426440407940310b4055a60303040413244020541c41d0085034000c2c40310a1851041c40d01c01d014100750300e000e0703041c020188500c101160702806110000c510880c10f043c1d13030708402030384140c010700e0380e0b0400b40070807443e1070060055007070000d5800241d07030f0805140c5482e0116440c002e10b15101398078002209500380b2007441001a0807907040c4100c101d100051080503410000d5556 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 219160998 1250 219159748 219159751
    0x3060902070f0609030212030a1b030212010627081e03040e040605060d02061603020f0c0117040219090204050f0906060a0c111503060f01080103031707180306020c15 73
    0x4240c0c0c00440b0700400050300300d43c04184141d00c240150f0710114202c0411700c0ca0f03500102c1c4e01078081e5881313030500d4100031041c0c800f140180800c1d040460070b080d0599a5543d280505000e4081400b00b13a01809501c0000c1a40e1035031024002e66610b0a0641c44d03080c07050b2502030540c1c0070305011802c0d00701078048030310100c00c0e1800c1d070300036035009611076a89845042c040c11000e400280c206850f031178002c000d0381f184401828040540b040202c900c1000b1314000346007404520b0950303259002968003000c1a83e000c540c900c00c0003407003e40081c0d0b91b1214000a100740c1c00d1504000c440010081001801e00c40c660094404c90303a00701c5803a082125a40300344a081d242c11200c0c2580a00d04002469549009603440c50085000b5000002100c011802103412036650011900d180503010080004601d0305070320500d04e90001b841c1803045945035a402400c03402ca580300d03c808600820700010009441b906510b602326141030b0044a1440daa410508025400a90121050b001c0d0240d110000101485030a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 219162248 1250 219160998 219161003
    0x2090c0702030d050a03090c0e07021204080703080d0e0708060f0a06140402130305030d1a0604290702100806011d06030721020d062309061c0c090204060306090207 72
    0x1c0c0703015030800608903520742c010070a120071b00d030740c840b80d846c0407a49020008018000e44aa040198101010043e183c1403081c00490f8a1500402080c00644c0c0007140450840394000b2010351211100502e110107001c0403400105540720748600000d1961000800c0c50103581c201c12045007507111601e1007000e440701400760b0b00c4940d002110450702c50a165000b088100141001c03440010b841c2d580c1d1908540c820042c890305252078200c58120b46907010600c41c18641e08503001031400c0d01e02004d0b803500000d558404001d002c01c034007080040d01c000030120780142e640200013030821008907030082d04404054440701d0000700994940b42c05d5829022500b014480002d18190440c0d035034001c00c64401c080d200114042c04260805001c0c000b0490000d481180c41005c0003054107403c00f44030a4641c1d90701b09000381100740c6000305084645a4841d20b0340c12407016604800309841040840010b03141c04180286070300d844440c00a0300021641c00342c070540e0305a5a0502110b40d940704001c00782d01448001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 219163498 1250 219162248 219162253
    0x601260c09070c0f0b070909140408070f0c060815010c0c031101090e240a0324060e0f0f100b090402030a1d030a090501260a0e1002040302090c070203 66
    0x22100c592810000680d80241c003490720b2400b00382c880d03880e200340c00c0e007141040f10704001801c00d00400d00c0d00a07610801400d055001002000309002d0900241a0041c00c050174000e000141d900500004070010681e19400050341e050007951b03100700030003400d0704540d0080c06a000b0a4600990b61050f02039044058011102841090440d25030000a55052200740c0c107000d02800c000910815002c641c3e8071030f03c60031000403950800c0c541d50f5680e61146d00940c6105d00c0040d8000d00000720079000080041c3c484411080103807501d0781c030a10040c0700039042194109601c10802040e045c030851114490080004020066120752000c0c0c0a040810700580c4174050040c0046603c90925038042c50b800100780c1d40c0441c4990854070ba2030780704403001c43c00c0c0040340c00c00030715124140e4000184100800081c41c2808481441c8000c0070074003c0300150a004120401010035141800ba400c01c05003614000705641d035074000d10b8941d43c025440340c4002c0303008846210000320008014410740c2d802a4001e0003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 219164748 1250 219163498 219163513
    0x60f030c041109030d03090b010603020304030801140a0302060c0d1103030c070204020918130314030c030106030902010e031006030209090a1a09010603050a080406020f011a010513090e060126 84
    0x2000080c2241c01c0a45070100402c0c8820b04059500b0400f148005d50540c80004d812401403c12088501b01600031105060040090000207907000320203904469280b900880c00164800015980e107050b5130020754454000314198400c0c2d000406c840d40f851300305460b850500410300407400c3c0c03a404101e07004042801c0034080381c0003500b03064000f0003401c000245440c841c02c0074001c0050103140165030044420200c8440c4200300b542080d07510105000c140c0c0c20303c1c254078004045482e14032050080c80c0815840d03000e040210790240c0319501d001c9200a00307480e0054001e1200307100412142c4400c2e03106901d94030101c3c401c4c0c100840e070404465042020700118003410f0813101c056400107028218150350703c02e40040440d2003449580700d6180302d40701c844d66551134034200a1911019010034801030340740c03c0140d041d0502d00092059072100a081240d00c076106007107085503510507984642c035042d0402e10550365400340464114140d54800180e000c4425881c142181160038040c1c168081e6402080e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 219165998 1250 219164748 219164773
    0x160506040b09010504030f110907030e06010510051201090b01091e03030503090f01020c0c0a0510020606150c0303010315231b0415090608011202010206040b060a05121005060f03 78
    0x1d005011602e018105649056500d5484440240c0000b2007031b901c0c20201c003601149498441e0010790807001c249014462003141075145a01d41406205441c0b1641c2c0c40e44540078001d02500c20340b88410750140d01e503405507940d502800e001c0e108258040d80082c0d9000d8011480d444030342e1842000d4210880000805401c2d0303a003c2d0341552015000c2070003032186500340800008240014030307294015030040e05200c24050240084540c082c0c201510950351800d40d000c03036603400205283d00c40c004403100385c048803020f01018110722a021a28440e40000000407040c00500e1413584251392003400304002e05110300b00024071203100e010400c1c0ca4500320002180340368440c08115914030650b07402d01c41c6059503540e070441070742c0403525a440104811b00400c100c1141c203d88201d0041c40400090030741c8c1c2104d903000030f40f0b4200044c001002418480080b460f01d484021320321026040c0503140a0200c0604408141d5031600007030840700d82d9091000041310380c01c05240186031240c0103002061514080d8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 219167248 1250 219165998 219166019
    0x206010f0f1e05090103060213050f0f010807120603050f0f0106241b060905060702060118091a071d01020102040f03080309121306031b0e0913080f030916050604 71
    0x48900d10050b20411201150f0342d695a019140210b108400042c0d580c1d601c8160302540b20701d03691201d1311072015801d440c0c115480300c90014449060903c1c010542e0390310910181d48543c012094100218540400031041010026001041c4c00d02070044034030030382d1100040d600383c4656025840e4542d1840302c00709851110080302103c3d41003a400c12440b445001045070b81c54500d940025a609500c400c0d094017401801d0010341d40001c001d03c060b200543c180011002008a06a507000b451a604c2c1914000d1145002c440031030148080c2c1c0041e0207007002e0000a00b00d1044280320032500e402d04603072a11030b40c014400c036003c407001c95258201c1181f0316160340c00187c0004000490754050608004051044940104100071a0345182d070318030b0b401c00000604a0341501c1c3c906090040ca01c07002030510741c003e020006d411030110765201d0035503141d45200070300a00c540001841c1e01804607006600100160140d0b100b10340d0902155125000034921400000d51b500c02d80c2d070849010072007444500541c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 219168498 1250 219167248 219167279
    0x9321203041e08460806010c060b0406060c0c0e0112060c030e060403031b02071202090702070e1003060b03060f15060714070f0e0408030c0315061204030206010f0f 72
    0x41440605000d510006480c070441090004060418840b13140b2a6118511510524848001041200e80b5440440c0a4102c41001d810a4107000103114103000f0886550012030049101030014059640e94900107408a100c0c0001200d041280c600080740d80398220321130358104c0e420080d40380e0520141303071a148001d00d009104403042503100d4030400c101e81c0003004030724000c034030039a00028692041c0b001d000000109956180c02c41d00814000c21060f80c00c0d40301c260443d5012248a985510750400680c43d00d5840e0380315404000f03c0c0802c20800003009400030b002c0780e001b5034044c41b07002e1103602055181d030743c101d400c421034442000204540282070301200c07107003602c00340c465441c005c3ca5490790300c03000d8501811301400d58441c1c9018004418200070020040c0200400d4415504082c1d0343c182c0300c0d02000b01303014200c1c0b8010001500440f10000510b01400018041e01e90341c0200205403030074654126400e401500c80c007000018181b0065120400b1101e0b02d860340c0c09000c1c2011040a6602003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 219169748 1250 219168498 219168503
    0x100507030204120f0209100f090b0102160311040501050f030d0f110f16060806010504120c0b040902030405060f0907120206040b0f030702070b04031509321203041e 72
    0xd0038080440d0b0b00f40c409145508841c003c020180d69030000384100949a10018050b5070000d035013001c1000000e1030300704031000383c4240c108003251f28400040100e1801d1018460452410030120b40001480100180410940001d507000d2150703030380360f906019580c00390030f0113542c0680c03001c2400f4001a101d120107004044152030941840d40400100900c0d1825029203002240c00592044109801507000740000303049608005100380390420020b440b074002c610503615408503100c0042d0411400440c190054405200c10303170b032516142e0b070840000390403c0f50229028410140131603401c03640b101929200b221001c00401155050424002c00d004203000c0498101350b040c032000c01c0190300311000c0d120740d4412154040c1c607032801110007403034400b442d8082d5045180c00c20050020511060700d402056a82c000086a2a001071801240d080c180803003e0311140840111441801d0045210701104042d50301141c00b1182c00d01e1100c807841c40159801030280c80100b0300c01007070401c1c1d01d072003140550 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 219170998 1250 219169748 219169751
    0xd080913020414090f04050712030201020d0207082101050f1002010e0d0201051f1a091f02010e0d0503010b0403030e01022b11060709180216050607110d0210050703 72
    0x9a00350080142d80040d00034101c0d0030f454503901c070050308050204c650700040318542c010301c1e41007984505480d10100e000c0c81114501e05a10101414000d40458045011a4000319901d001c0c03401c24404039000703241810f00c03542d0b101c8400e205035082070055905075003006005041b09035104041240320021501008290754860005403001403090040d8902504143c00205913450309050460003550048070441080da20b08005021300880032109440721414401d00d0343e9100010000181000c0d010658402c82c10160f0b1264100942c0c103400c26804800100110703501e4110b149004e40d0540000d0080000104043c030080000c6803081080c52582241801511460501c26881442c000d500c212400707090309283d51042c01c855402112000e42000f0840646042e052140004100701900e00c00da0079a500e000c15042c09540040c3d0485041e0f0010380c0030151800c0d240d203071441e2a5002245c0640100303805404480284102203420301c3c0190207075000d8883d903056201c1000040902404100416 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 219172248 1250 219170998 219171019
    0xc1d0414160b16020901030c030620070f170313060e07060e06071a010b19050315090408090414010801150503030a0f05041211031c09030f0203010e060708190207020d0809 75
    0x607205c40f40018061801121807541c05030071820300c002940c680021585410182102c020800f0034850203940c1c4107607100901109041385814940c403607210107043c1000024000040c002001c0e004a10740d18041d201e80c1c03061229151000c00b032500c0700898816003020a070404820907107403400d40000e0190912400480240301d200801851010200740c000b200d640b03500180c101c030742e09180c058141015519241051852501c0b01003054a107802c42d00382c0b8007458210001c281005415010384038810f10150040000f00e030007040c00800d0340c1080c8140a095481c0c01030314000400c4c401a10010394002400a52034822302100031504215118007000400500780000306840e01a103500721345440c000d4121110b4060315108041c02c1605c1c0c0c00180301c8080481082040483d0083c1c0928222508000c04018032141400401c0c003410f800c40701d00d49540240020010000d400c050b42501558032800590030031a8828115001c030b1040c110043d600c0800014035400241c00c8a00500c1e01c00c40282240114 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 219173498 1250 219172248 219172253
    0x40605030330071d22020c010e010f02070209062425210c02090c0c0115031a0c0c0601050913060f0f0b0d0f0b040c1d0414160b16 57
    0x580082d02d80f0800561a18907400e203a000800d0203182030310089075480181700c00124071300d001c0b008001c41e17100001c0d008a68071907203000a50000c00000c0496000380070840741c1c244014000c4d4404401203100d50450000300c0e03000c0c03c103c1e85a65802c2e0400d82c610081c226500c02440c056000b10780041109940d40c20b901e88800b440152005009201d48850149003040c45141051129035403030000401003515111000b59440e0183e8580001604d80a1542c884c81c114109014001c149042c1c000401911fa001040051000ca503c0104083d0158840540c0b540c00e1003500074400c4920300d07145030f0b00160051055160040300944c2251115003415810000b5588480680d4408038035000e10b2952400300a4814001d03004950f000c600841e16a10f1898640c0d6a10a4880031a18080c0c040d00011001078100700b00b80c00703400b02500a4024400044808554030b16605c4401c440072202d5142058949441e030800281c20391180103850301c1e44001b182232101c41440394101d503804007a400140c000c500d01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 219174748 1250 219173498 219173587
    0x61204210201090308090c0d030311090405010f03020102010e030a09050405060a091a010206150a09090f08030906070e09012103141815040e0f0402030a061b0e0406050303 75
    0x2040c40c02500040f9030f86185060140c1410802401390440c2d07000404200d51507595400760990642e49410300003850690881044c54074041c481d13410303400518000020070072007105141c00044a100360300030301891031150843c80c0c17240100720001021940b82c0c60240103500e0950000c607400880a48101c483d5551030450105840343c5a1401e0504d07400c030b002405065a0601c0360070b80c0900480c6200e26480006400300d0120031051150303a0601d0717500e0a0f04400c01c40700d040192a0503400800301603c03420242d05007900c030381080c0da10002040c0c00c0107540d40c131410b1110340c0d00e04988144c2c44451161900096082c00660603880440401002d840c0c169070422200340a08048003158060314024208041401580045001c4030700500c00c003484108140400b03c46001e50014415913018030303a80701c42c4041381c500591f0010040c07100d410402c2181403146c00d0707404100328506640c0c41d400d4440301e0307209100c1129814094160550020071544600150844404000031130640d0243d032601400300c0e0101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 219175998 1250 219174748 219174803
    0x5040f0215031803130e0a0e030a0503100501031a040b0102010902060d1a03070e0c0c071d0a1506050301140a12050f07060206010b07030e1206250509061204 69
    0x200070304040180000c0101c50004206521007003401503140c00c1603000107031301081e07651203682c0604400340300007000074109810290440c281c190489444440703107000500260802c4509610280740498001280d41c841d001c0d240310744c0c000342003c0c00f0f100320b10b0007804041d290010146040d90f480d10405401602c403800140401c1b841040009a0032510348503058030712b42d86003140d9200341d000000510140420a10494100200c0c0541030f0360b814512050301d092005580c0300d60b51480c0010041c0030540f45116000740f02d0061010100f080350605c002103801a8154007954000590500060080d440c401e40e51071102d080081c00c007107e507a42d554500100707031103012007182c3c10780111080c041200d004101e2300002d44502e001425903581810484160340c0203d0001504200746159002c081da11079605111540c0c4420099a5292070040040c80e0119961450303400140d0082e21550210307441070040e034a00c2d5200400e81460040c0c209804e03014144050310a86100740c8107041c0e07075621039041c035001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 219177248 1250 219175998 219176029
    0x8040909260a030b04140718030b0108151321180801060e10030327033c0f06050a0b090f07200a0b04050712110a0801021c05040f02 58
    0x1181d542c1c610720001020f54006012440c0034a01700280e8001e80c0040e401c0040c0c0c454100d150504010540c90b6980f03243d9040c50744050102e150050000c5108007001c42d42942051821300c00d20300035114005040c500b94400307440038084038980b08a45034003601e0314446c058610414a40885640855800380e04590395a83c8011a1603551316410084103c2c821249944494110404044d5504d075842c054171a400050b4414000f252103403c1008440d0180b11400c0074582110f01b000360760814048003402c20480c40030600c0d10811620b10b002d5903e004516807091f850b400f40101d00050040da40301c0000d040003410302d01c0b600e03880e04500c0070903441d10060b09110718000000390b142341c1441b140c041c081803003400403010b032402c0c1030500f050f081000041c1d40c108641d02480d010036903500c5040480c14201182c00a007a03240c00c0781c00c4501030220882284000f0201194010802caa0b0f50081c1801c134801d41d8020050b4007003c2140c50743d890019445981d20a000303105400400190785d0000300100501840c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 219178498 1250 219177248 219177323
    0x150905030c060c42040228060509060f03040c062a0f030e1005040f0e06010c0201121503060207060e06070818070b040e010e0a020708040909 62
    0x401403450304000945403840203030354161400411070703030040e103a07103d43e5804481508400c01d04000022206450900d9181c28410341a440c912042c14203038000c400d0314281e1182d4081768040c50b4041340000c2c0c90041072805441c0183c040c0c40d181d4255071310740211540c1e5a00c0001800300440701d541801c0103500c503a00c5808001401824000c004c0c00341c11009048060002c1890341c885a0f81391a00074803500383e40c200640f0011075859140440d507d0002051080c3c02100d0941090300482c1c200c000781040c1c40d0418164914180c4424000039030b5001200c0301030001e010403030001d0241d4000e004825000380954008584000c0f81d0b40000103425242c2d204480c140c1d03001402400b840041c0c4200d00310708070b600300034100b02e052100004200c4c072000342c43c0c2c41039840e441c20b6450321200100905802000b0302080300307440e5542d07228900385401c02442141d000200c0c150000701851428402c40c1c8203140d0100000b414503090a1115005001c4800e044601d080c0003001704082079010311030000e07203441d100322 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 219179748 1250 219178498 219178517
    0xe0108060708070306050a0b09040207061b02010f0b0f060705030d0509031b060f040201050912010f0515011407080a030f020310031104060506030103060b0a150306030c05180412020715 81
    0x81c0b4140004140904252030700d00188546ea0340eaa280e0700403a005900c6140e19a200b01000600074841e83c1e03c018036441c900300850100354140090a4119242ca400070081c1e0940c1e014240b0581d540b01c5c0b03000740e210540c140380d140306280c00006002224040d9045906040c0c2901c1d034102141c1c4140ca0b00c891603400411041c42404031401c03151205012400600142c2c06e09121418a24001800003810300c540421400e000313449040c200c151501c0d27020024862034010342954001000140c820034000c044003200c0c00300030b50180044c1c240600ca001d11607883d041c080d40390705000c2e401c000081b1003055151806010900000e002850290841c4040c1d803052503e1480c20284c25a82443c20341d0240d414018101302c0c17640c4039000d4904481e0013071400300300d040c60a030004480c0300385070b0092400781ca03804a0441e6417550603800141503903c52019149a070f61034074100704901d0200342c040300301c07400703031100080000b1070240c002c541031221801180c0000c0c0e01c4411820352501c50010200015500e00d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 219180998 1250 219179748 219179761
    0x705030d0510092912011107020f0d020303041e05040c02031b0106062f010903050c07210f0507151809090804030b07050909160f02011418070e010806 66
    0x75000c00040c16421400c00c140c42115480c1c90210318101340c0146410a0b070000c580c100d450b80d041c00341180440700d00820000286c4200b04005410604013680143c0c0e2010f0312001a042c49aa52080e09400030011030506141200340c0d0f0390082070400030907142d444814000ba1036222400f4445005086401858803003034210f003108440201818200d44981c10b0450412010340c01c1144619443c0031600a001e0f1060000c10f10300d0410340c04880d400f1039610b40412034040c140c0c89005099410205000e480341300d03075034007160070407070324124910700501c48030610321130005200780603d42051b481034080e20a600d03510031040304568028402031012074041303860307915260b4081103040007501e202d40381041108003e07140c0c00303280d000303034000109400f900f01c02052000f406002640c1264100400702881850400c0c00c0d03080c041c1e010040c03040450302e40d08406250034018015100b10200c428031821082d07a480c0704034485042c4c10b085d03c1c1840d000b5084003003252440e410915000c6e00307401000385034900340300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 219182248 1250 219180998 219181021
    0x60a091512020a0504030b060406140d02010c0512070c06030e0303010b070618030f091706040204151505130e190c09050409050a0209060306102601020c0a05210f0307050705030d05 79
    0x90030244254172b4000c0603c10081e03402d81c003180003801034070101c600c0020b510043e5046041070308040d080c1d114607504003d0b2083c2c4540248002031040600848c46130b170b508020340a4075204401c0d0000d03a04280018080c0030015005440254003c3d0380200d410f440d0076030404590784071a6820340001c1c2d07003000c01040c01034000680e04000c1802d450740414403c0040e044030384410000d00700034400c0c0d458840e01130101d140904004060f02270b811400c9504495a040031b00342d94000103200c52581880c6500198010305820798038032580d24807015a1048401d50160801000c00f4440c280c14070602c0c2c900407541da21750788521904540301d00000e040001c2e02d0700401c10f40040c01001544240d00c10410800c20790550700440044400c10039054154051880101041404880c2c0b2617543e9880841c0500c0b0b4510001132101c0d10b03900510a80d0136007411030b150110410118008032035280005c20079524883c04090095078000c43c00e00d0800e08002c5c031035660780d0039503000e09611020070b07441e00d0a00042c41c500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 219183498 1250 219182248 219182251
    0x1c05090a02010c02191502030703030c030501060804020f1315080111032701090807051f0b0d02060c030906030405060406060b0a08061e03060c0406020c060a091512020a0504030b 78
    0x58200500c529161540000d2080211a00003405038003052201406102000c0300840500000102c000c81258240300c004d42e40c0d00891030503000242400800a41c5038064030419050381c46940e42c0108695a6070207000c0380746c03650007290740c01040406800005505502c03030700010940340e18152060914108081d03094650101a1440d01c1104000784102c1840d4001d0700c401c045013042d4140c2503c52000f55050040c1113400c800340444400207818420440c01140e000c0e0b07480305c468818407105828081b000b085940c000396003038015030540b0491015141010152003549840fa003243d203440c3c0c036480428000d40060b03504071820350000003404100445401203402406810b65054100010385e0320040030b441d0007509481c020507413800210701425401a023419420b901404468450400d81d2100c5411391003489400014092241880260300c6e00708111140742c1d04581c1c1b0041002d0134424403200304418000c011040c04450540081803000d1760000e00b40030041521140d8031146103080000b5071010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 219184748 1250 219183498 219183511
    0x3120509032d0f0331030f0b04020909060c040504110913020405030f011a1c0f030203040807050a0b031b0c070e010608180a080d091a04020a0f1401030c030b061c05 72
    0x10605c040342c0144001501404481c08a0499600b0b0202c00d000d100368220143d0405000101002c46040c1400741002d5214025031003a01c1c0c400030780d0b0700e81b008180c80300303404e48400501c0b1504010070051840c2680003443c0200c2c00585140c0782404400000e04421010910440840e801103010000da240030b02000840800c1c07000240302c400d08510b245204600480d00c1d141c420008589150543d02200e0307505000030b5444031411245006605000e5900e4000e482601614440c0950100e80c60405452034001c542c010000c0e581180c65000c080b03004010a1414607102800601c003c042c6148204142c8000749002c2030146199414030300002d203503400007400030407005401c040300380415800007031000041350081c2c0000e0f104d41031046c28501030031030140047d008540160952800d145030804403030055200b2656000e140c0d0b03a408451744000324902c02c40a0740f2945540c00c030b50f954000c0d0000c2010703200610300014045400700000702c0341e8100d802e0140350188804d0038150030240c40e116164010380d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 219185998 1250 219184748 219184753
    0x30d0e250b0316110307060b040507020304030f0f020d120c05010c050903190305090a08010501050a090c022a060403061a0f030703030e040e060f0a050c030103120509032d0f 76
    0x2030034180030a07040d100c05094120302d004046100d0318034500c15002c2c0110308064000343c0342ea9102c1c0f428540080e046292115116a1600c400f04002a0001080b9402c4960140c143d01c40c070429910340c3d1320b0302c86800c401039030000766054822000030458824000c10000740e4444820120f07144c00c046003103c00680313800042c002d04002024040d40d00096a503480005021aa030180c2c0c1c5d01c0c40c0032134aa00a80c1247c1d80c0001c0640004514202c040d0401810703100155598045640d866040401380c130802c003d102c001d40c000703114001c1d03126080c0c641d500c0c0a000c022180380c18141400082041a0b200340d205030b07203440c1d03524840c0c0c065402c2026103004d000b00072240d0840f040e26010021307481c0c1c0744902c00242401004035112910303841e2a000304500b598148103495482c5401140301c40c3c4601c04480b60001030b440e00c00002e03d50204201581d060340e0300010008511060000c007035072654404c100c3c0a5061107190444811714281c102100104288603081ca400c2030b800c14000c43c41c02141e0b207410381154 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 219187248 1250 219185998 219186073
    0x2120f010e250306090c2006010303050f0a03140a090501050601080106020303010b090f100908070b04270b0a060f300b120f01020306010806040911040c02030d0e 71
    0x50001219003890420420208182d001c0d4860103500a003d16401100110704120f401005241c00c0720401910180c0c40d12010707040b035444084151101402d02008002c6981880507001c0c810724030024000700e480700e040005020440c142e0f10306882004482ca404013644078003140782086001c1c080c85400c44000e007882003055042c41c80103526400b0501031008600e00108820601d51f40d01c2c0b00760b402c41c0e01c002e85651080038455070004c01c41d031428000c2491300c1c4141d180014603ca41002101c0071191201c0309002a030300c2da0550603801c1d1008103820f40b5500c0e101c00b1a0086039a0b42110034006181c80e80782e41c5403626507510042d2221000717280806014248107181c00f07840c2d82c0c00700c410840f2564070500285076882d010028803280c0c40d082840085101c1c4009140d610f080550085014250076294609540e56030700400c0140ca0020304004e01c0b043c900c095a502e142420340143c08441081e0050380d0034101c0101002049422040c804029503000f207c2818480c1d06d080c919151003401840c40340b508 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 219188498 1250 219187248 219187261
    0x4150b0306160807031808040f120818131e05130503070605091507170604020c03070b100b0a050405100201090b0f0a091208160815060c070902120f010e 67
    0x440c10112909115441c000982964444d0340046c1200d900c1181102c1c4800d06400d140800780c00c14040d8818001c2e10400100e10303145845c2c510010035a1004480e440e10800c486508240e01c03000300c10540110349070282102e0000c15002d150203821822031045000210a104542900c1015014030380b181011950000419000b104440c03156400000200380d03500c9079042c01d031800120040481c2a0b181100c00e220380d8591003884c841803204034074045003641d01e0325410841203100381058140d20742d0040210000244100e59001d41c050907000e082100300d40e0780e80c0082103950100030900b00103000002d061050780381209000e6000f0005200030014610166035424012202403c0a1001c0c043e24000030035404441e080026280c0e844800750100000da60005070042f036065840d5000c811019080a468a204028291058000940303140204203170505100345507229144214190084100219008140c0c1c002400d0310300c0406100e100c6440c0005103d0030442040e002000200171140a1120 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 219189748 1250 219188498 219188521
    0xd121409010912050a0203031216050909070f090302040f0917070507030215160c180e07060c030507020619140a092c04080d0f0204080d030b01020708010504150b0306 73
    0x151902140e03102403c60f8103081041c600909032800950620001441d0030000c18801c403c50300507400da03241c80140102c0746000780da1b207000700210960050821000945400e2040344c0c0309040c074619003400e0039580d03165004607040e1145401400d02c0240c0700c00100e01003200c1885d1b594420310340d94a00038149446699840d442d40c50902c006032007441d100303440c0341109420358201d450307040d1503803840d82c0540642d181c002d1700c960b494400c0c0c00d540b0003214080b06030002d40380600c00740b00000302c010f40441410150180c4080354038082c01d40030000e090080100580380d171002845290740a0385004500c00881c0c030010041c0c00e4041e949100d291080c050110302da82c21110010950b41c4403620340c0f04a126002694201d900c3c0c00040302c4900d00350070280024022030100402100c200c21809000c1800c0c024888020b034402c52055000b6903000c4820b6500c821310a500c40261030348140b040c0c03003043e0341d034990260a4880581d002d603241d150b00d0340c003103c03007800500c00e0b00084481603014001074681803446d00c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 219190998 1250 219189748 219189767
    0x7050a0504050c040f030c030b070503091e1002030108030d0c090f05010e12011a040c020c1c0311030f031603060b0d0e011b02060f10030510090606050d12140901 71
    0x80c0a2610b40740450b0a800341d0405960141914a030b070401210b0b92801c21107100701403444144c070803015150100c1c4400e8400d400b00c3c1d11404615005080d000c84c0b20018400700c540701840a191f500500b05040034242c002e00080d0b008081c0480255201d00c80d000b206000c45030b14064400c14400b030710004100701e0780071440550489400f400e0600502e103082c030100f06080e4910043c3c40e070729480e1441003005c4102c80070030920411801d440421001d0301c0c2100681c1d6500341c00084a5000030301c2001c484070308562001102c481c45c464901074400b0750b0304e04851481e54200d0f90b100c400b0441c0200c20080740101d840d1200001c4402890140401e40c581250500329208458900303204640f182c038010300c103510940090b2041003111030f020b0160040500000d4654106483da90704003d003010100310b13100203100b86141500d400c8000f4160b03040010306100e0040c40600412141d89403104400101e0340d880641c8809064004c80e460030f624501140d0081c400c0e040f041050040d040184000c2a40c0d90b4001c0041e07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 219192248 1250 219190998 219191009
    0xd0b0115081306111e0717030603150405010905030a02152d090109140d030f02030c030f090f0d0e010818031c0207060c0302070212030c1c030e0f07150207050a 70
    0xa0740b44040008503003180301c5c440c01c40403071076003510100f0f00100c402001801e080c3d00070031100c07000f80301600000c1c06070310094840c29899400402c048070302c01000094203402510171000001c0c0d00c3d2140e915241140c2220711540c002d80c0050103501c11618180328015404406035000104480703841c1d115046c0154071401c40b41d4230f020142d0006808404c00d41c0400f048d0380e000b400741c0b408240c540380e2641c1e96440900d120000281410101d20454019009030b9001d407000005c0076065981e92038401c003180400400805080c032840c81d004042034403d02003188021059559071603246003480024003c110041c01c2d1000524400589400c040c0c03010007550080c2c148820345441c40d050003642400a40070b49500544982c2c6403600c102015a0143d0003461203920923210b00c4a175411076004036440e4015904d801840d600080107d0100100c00c103160079140c1001d040028074a09030041d09450207240d00f40d480c20603484501c043c0076905031503c002c20042554801840f11904010105604001d1032062 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 219193498 1250 219192248 219192251
    0xd050a0c03020a060e0c0f030102040b0d0207082803050919030f0302120907170a08030402090414010518010501080106053d020a0c0b2106030102090d0b0115081306 72
    0xc0001c01d07109210030244503400c031009000d28807240709500c1d2510302600c43d440c45004103980b400010300301802078408903401905454100304982c07903403070003962040b1400c07241e5030b004000202100c078415482c00503800000301382d25100d2a4004020b001c649003d031134040c3e1503200388420610403010030401c03030210340d0501e004011040b4a04058000c2d000300e41c688486032824038200803000b14001404011502500c000ca40d000740d10b00c5085849410b11000503107600810030000f805810803180c540e4210b0f204415024545040540480c2120b038280c1d6200000c109a001011140e0400d000c2e590240c48442c5c0200810f901d408006450001000d080008049a03106c0442d6404440504a2424240e00104401001100b103000751580043c52007101d01014810012030008041c0382914aa03103004682d03065142d0204045c000c1108000b484c841d4107640800c501d803d140c913910403c2d01018880e102c501c1c22541803c1709405440c48142300030701041f02d15401c03c04000b080b0f01507105440c0c4c00c100c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 219194748 1250 219193498 219193517
    0x1021603081905190c050601060f0807080c0403020402030405010203100b130302010309260a1701152d0e030105090604030c022107060504081c120f14040809120d050a 73
    0x301618a4014589000104d00d000300010b22401d0300010f410302c0c1948580141c4c0e05a81c1c03501c0d415103111b8000c495150004880b1130010701220301440503aa0007400f106116401e1560f41c1e40058107983c0704031021162a500802440308000394000c025001d01240315096040151034103480744040750070304c1b029042603150a202010b03c407803000d120042135683d0315924451109002d0002a0303600c00c80e8403600280030315502e4200b034520140100e040e200840003070f04120800d0700301240c8200e09982c4009148100c1c60005206114551000100302030702d0316800c00101950303080508580d00101544210f070024000c200002e0390000090700c50a90464204140b43c11011040703168082610390141644100e40011501c03a4200014104036050401214506174004451800030030682d482c5101240450501a0301007450384c122a482400074500000c1010070700410088262054400b51001400007a03c0200c50170500d4611910344881c40051680506101008006124a610401c1041130380c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 219195998 1250 219194748 219194797
    0xe10090c020a051f0e01050a0603021206090c0d060e0601060305060a0e06030d050c0a080a050702040b031c030e0111040f060206060a030b160e030d030516110322030f0b0103020102160308 82
    0x9010510617030003100204072501c2d040ca0031200511083c0800d03032240b0403100100c40786d07403400603caa100740304030009041c00d00344201c00e000200c00940d6086510035103c01d00c280c11000200002c81c000c00d00f40d6008122401c2c03020031f200c850b40c80c4c3d8221045130408141000fa50352800100c0c070000301030a14000b0340d0340341c0d6003c5840c02c0080d03480c0c00910013030001400e0a10958440051f150b0380d40200e400300111075205d420140e803038649085a5a0314040601013000c054060340c0010030022200c400800c200c80512501d4085a109401c01418030055001c240086541088071903032017602615403000e01411500c0700c005c0d01d00014081421480b0307404100c101b00d44980c1004d01101e4000d01100c1c00ca05807048064050300c4212980740d017005910441030103203031081c14803501d00c00689018501e001107991102c1d1008040300130078406410744210010010340200e0113003222138001c240503070065040d48002420003149210641720f00044803002c0c404242d0040440708060948820b411031808400e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 219197248 1250 219195998 219196001
    0x2805030417010e0706021006050f011d0a0f030b0a060602010203060102030409020706090c0909060c0f1b05010e0d020a0605070203030c0a0503090a0c0f030201080612030301031403040e10090c020a051f 88
    0x3c100c001c1c082c05a0302c00010030742d030002040d002c0c010720790390148001a00c40d070602c8003205010021900041e030150b908101c3c0c940480401c034840310b0240010f0b02c002e443c0c41200e0842651607108642100d01030342084449203180c4500c0010744003030701c001c2d440c6003043d1000035a80c4c02180036840c245039002034940b04200c503da01078a0f000e54420350000e030741540c80141d000204074501c01a2081d500b0b124500a03c1803041c1070203a49c4652a07100c0d1215803800900541003c9201c05007104c5947da40d050386000c520741004070800c040203030350092814075020301d00141601c034003a18001c1554020720a00c40130340d014805036400000c04c2e182c000d44a81d1488845c034a0a1030b103890161450044103400320304210301d00c0000d002d40f8000c0c0ca48401d9529940148000303500039501c00c0000760030a00c0140000341c21681408002050101120308168603034444010100b0203980c04216404142d40130010500e440c040d442c90321b441130028080c4503105885180d11101040d01c0088518510b180c40c04004495 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 219198498 1250 219197248 219197261
    0x30a020409050f0108010b03010e1e010921020d080402030d0305070516210806060301050f010203071506170616080a0e03041514030405031204080f0309280503041701 73
    0x418400e02c901d003030000d080000f401c400e0207140704a5082043d24525410140183c503400c0208000a040700304101004d40c48000740c00001910039520f4158841c00301d0707004549541d1010b0307080c0300c0300743d01020814081d05e880204c5e81c4180910a10804010242e90b000c11040d100003624107010400340d030740344400c03100c46c0f0581020141c2c400000000c4000e0242026540c03107050710260703100406861b0042e0903550602e0403260f040c2d001034200b0060290f41040703035464a10220600407a82001ea50340d50303030140700032421850313a02107650f00c8081000c01c02d00c0b4400c0804560707a40c0a03018904020101c5020034200072602018040301c2000304030b030a0f40c981e21070b442c3da00c250401d803a02c481d2035804051040701d004011100245003c80714440070800c030300441c1d0180794000e00851902c1075800040741903a400900944050509020250150f52240c00a600c41c2c04500c003e4819194800040c400c1d103041c05a0745518081c039034181000045c0004119419602e6150804841000c0c0c100050f016040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 219199748 1250 219198498 219198509
    0x10b130806090a02120c030705040902181e06100f0e0a0f18050f011211010302070204050405010207140303150f0f03010e06092107020f0a08191b0515030a0204 70
    0x90801000300c02d0790003103120b0f21403620032100009086600056a0365807010030002c668580c010b400108003610381a8005d0a40c4d910282040350302d81d000c03000c0d09200c1203080390702051005101603192121408207014a500510440d548079a2a580690040c103810a49090405000c0b0710003692116a407045e05e620000c104180f07203252116180e030401150700b5800d000000d0b80f1801c1001050003208507010351816241c10980080103c400da4a440314894030722102d060602d542006820007684840c000c06c0c0c1304600420025a81d11280c1c60300ea64404a000c040c01441d40003403052010302003444180c29030b060710448101126040c81c1d03001032151244a2605685503182503100b5540c0c140108403188151030038800e0b0b4410703480c0c050aa5011000c40742c603000000c0347c1002060018138100502c201ca44202500b41c1021588900c0168581a400c1c20114030040600f200302c0108146140904004146030b040c0130f0f4803900d0100130400d45188600b00101d44c0c1d4005c000180d1000355036041d98009c15 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 219200998 1250 219199748 219199753
    0x70206090a08190507090606020c01180b2b1e15050904050105100b030c030a020f0706110c240112051f0b0111060f060103110d060f1706010b03010b1308 67
    0x820f02212090105459012110b42c041d4000c0020110498400d04080361145e80203809004101c5004507000e0303994101072040303c0c0101c0e4000c100a05000054010b64020352841e034948462280c025907080340c0c000d0700a21b058144181750350403201c0c40840b0801a0103c2402181c0c603da540c00050108400e60403c0d500444003100304801d00405400241c003440310740b502c000c122070701c8020450180c80201d4619004400801c041403013209594005d05d2291242c020a0b4284402d50340e5020a684500d81ca01000c01c90108140111a0060085000000030010200910003904007142080401403082445e92070148541e0b2090240034841003480d0400e0101c0c0110f03000d010011200180f1a5102c0f481c00100c150381c07414000030b00020800d02806400c1c9005905a56a00c0110058400c40c1c0707840303842d03c800703001c03105011901e0301554000c0c1c0b0581e1180b01d09a82054413080700102c1003c0e5460382d5902401c0100440325203181100e041d104802541e035903541e000e40708042032405550000c402071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 219202248 1250 219200998 219201013
    0x2071806090506060c06040b1312080a0b0105070317070309080f0301080d0804030206060409031b03030501080c040207020d03030b0f0a030b0a2f0d20030a060504020f070206090a08 79
    0x11069030302030419250305010400240c0c4074082030051a000d03005019040350301c0320020a021407206c10303101c0d6005903100d03180800d1071520790300d10062114104420b00429400790911050182a000b10a94540203281081c148429501c1c01044070100728070751041c800c07001010481691098203c1c1040700d42054845136a4007a51b034900c5a19032003449080b151b801800404135005104220040c05160140d00405181d180c0800b004020000810210207002440d071065850040e003440d41950346010f0340300002c0d03540c5883d0406003006481d86109108034410002d10b80140e4404000e04582d0b40c051030005851103c0c140400c0400c0b00203108150701c0801000d00204104024000c3e80c400e50b102d10041c0928811f6504911041c200503041e0f14014403003546688203220850080c2c594002c90640200e8514880310307400d42e000310035490a005e1001c0000170403410421901800005080640c2d08500c8c00c0c1901c0880d01c460301425900922a0034005050b600c0c41d80c40c1075856000d004d1520965841 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 219203498 1250 219202248 219202289
    0x30f030f0c07081c08070e06070813050913110d0503030f13080417010f0b03030d0f0216060c020f03041a03040201020c15041e050a0302010f110106080d120c0c020f010207 75
    0x10103a031000400d0005d503140000415091064907a0740e9001c02c00b8040360b08000c1c495036020150b410103402c00460200f100800034542d40e8400a07140101160407030131a140040d41002d2540c60348020005002c0d210344842c0c0f4000460000842e039108115100f80c1c0c1c25503c910074100881c6c40340318000703803813040041030102c0c1404411006105040826000b00140c07541d240740300c020740b151100310345e9060f00140040c07024920183c001d000a0400c1120040c541840700c00e1105150503030190503502030341c0d20740071710452940401001c110710710b00e0b03001542400d29111000e14402d885188142c0c110074048081001c59008000c000201d241c02080c40c02401005101407185070401d12407541c1101d66504180c40a21502110105840000c0e2142c0c02581c02c580040d174400d002c01e22940108011350034420364800e13003172150340701804501000d810601d4840400420f10000301408010f03040c82d08085036119508110600b8080c0c2d8140c6241d80080e9441c40183c2c1800000d40c40143d0000c082d490000760b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 219204748 1250 219203498 219203533
    0x80304020f1c150501050f1f030609050a0203090f1b041509051513020405011b08040308031003030f0807020a02010c0203101814070518090111120402040b030f030f0c0708 75
    0xd10300f480c0d1040120340c0e80c2d04100a45101c4a44540360003540c1019420420058040801c2200a4500300480d0701a03544650f0421544120b49241c0c80690100510000000511540d03201080300401080100702030682088501400854244a00c0d6165100b5038444503d5038088014403840c0420881441c00d103c0003113003440c807101d9071885046412800302c00715400d4802d031815120180c2d81c0e0100f201c012100d6402e1407070203002c02d46211000388000400181c1c41c2c0000d42c81841c40c031116102352031442c5800b5203810307190004081030109c1c8104105c1da0039400109503808a8091074400c3e0407000e1703400441d090026440c414404103051240841400c00e81213005070000b440352103150300c04080c03280c09070f486000078050342d98170a000f4489117440007181044180c00409100000810254850102c003060b4050020740302180c8a100401c015498280b0030803903158000d034007400005440d01c0407262244034410f5110210070001c04c007681000420005880541001800c0700c105034003403a84d149 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 219205998 1250 219204748 219204773
    0x1407030f080906010b0d2c151e0a0207150c03060e01050607031e0207090203010e0f061f05070515010f0315020a0207030f14071404110403080304020f1c 67
    0x4003140306040880c00031640012214102e40b055180075040c02488004000138001f0364100000320400580e082d80300340780390341c07900740c101030400e0090000c001d016424040b90000209180c1003103100c13600500c0c013031400300036159002c2007448005998400742e24103010300842191260348000d01c0c18030fa4a040c0d83d05580100c0990700004406020ba03039031102000498419118010002488a0f4600d04070903500c014030308500301d0b01d00640d40300030740b0344032840300b04c5e08242e008400d0880500c0910406035009000d4036005402910000707000d013841c00441b400c20a071006000208140001c0001c1806401d101d07641010148104c8442503594521401810702c1c1d0314001030320700c4c42c04604000440801403003190381440c196001340c6181451500d602014180e14a0169a0748000c12002803000700c09003c04006400086c8c00d51900d8031080d01444115401c4031003c0112010411040c40494500e000390390b80a40c0c107c91003140d040b482c1000c2184050b5081c121060724615444071000c010700c024621 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 219207248 1250 219205998 219206027
    0xb090105150303030907060e030703080304150605240901050903060109090201030c020a20010507080307030c090501050403110609030f0307060209041a090a050a18140709050103081801140703 84
    0xc01ea000251041688922050700e0014299008640800c5031758054200d41c042510010160341003d603503a00c2d141e405502c202ea0890341e5505503000144030350700c02c0c410b40014010555541a00941c4102c010403114100050440301080203da0054941e00c42d20807191003080c05025607019595034102c441c00307800c540701c04a020074185550258500d100240c40c40d44c0680107020110965440322607012030558480c980c1c1c2c1085410414040800d00b858019401141213950024030b0802e0640c0080c80f19516802040c10440c0400c41000814440d0800901103070f02254031650711007042d00001d00d0251410404611804042542c40c1804600c1e800350610140070754080c0400c0b18800d204000c3c19880400c2c40340e00443c0c01c0c010442c3d5440f541d004561000c00c0d440001020300424020003034820615404890f80140c0210041114400703022a05c001c0003202c2042c46594115078900c191402020481d1030f003c011051510000e0380300d001d68030750651508580c5940d580c0c1c01c2c20018000c0410001c103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 219208498 1250 219207248 219207271
    0x30305030a05070e060f0703020a0f03080601080108010507050906030c070512070c0e040b1305010b0a15140c1c09050d060212060306060f0f01180608090d03090302030a030c03090b090105 82
    0x20f081c0301c4c0138980345800010700900c4076242180030007100c1c810790080c0d20180c0861080031503a10006111000500080b4000c0d1100d8120303207824000100011303c1604450016410102813242080d0040c00761500440100c0d1416160765403140300c0c403aa40035184002d40184a00340902c07001000d40f0b030041107c01d00038041c025880743c8524003440040c0041e00d0080c01081c284001071032001900c0015030b0310034811000850001c2100000505280711034010300020601d0025195505800c0003941c024200c4105406090000e5550340b551540114060070781c2e01c8848800b8000168030a8081002403d0001c08024000c5024181500250040c00e205266440b0040c0407825074030f400500c5038441d440090240021074025014000347c80320107210f071414032a00c804a42450f046828940004c0c1c29180c0d81c000a40c900b07441c0c81860b200e40144903030181440c00c07a036240842d40c044101d4219100e80d050206d0107480d030401c120300a021405002c3c01140c20f50041c003a14003010b4002c80c0c01203101a4a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 219209748 1250 219208498 219208501
    0x5240a211401050108041407150327030e210601090e0109020d06022104080a091a0304122c011806080a0c0c02030604050102193204080106030305030a05 67
    0x1808800c9500307030781c0070201d0303001d140004029540c03244490b541d00611038824030807605020781c3e00303902d000090f800052540005d0000052002e903d4840e0100c0140024445031700703040304208009187c220b0807005000c11140201c1200c46407940180d0300580001407181c1c2000107500220306440f50000e0050414150030000e03420b001590500407078003201c0d001802110880b0407607682d04001e611461001d125040001c4030b030080c4071201051180300c5c074019214250356418050000f8800341450b0003100d10f58441800c0302c0280c008500940e60b0281d40305440c02e840c1c2030440c4094070118101e141c0210001e85c41c103510070392081c00000d4100f001c0b9080c2c80301c020800e040c0800d500c010500d80614000a12000d00061440c012604000342d49601406d000440081c950042414001c0840e400d8480740e4002407200c2400701181d52000c00c500d03252803c420341c4c0d4030650031f2441040680c10050f1110b05d101504407440081582218000d00340d0360001c00c4015a01e143c054025082191180d006519000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 219210998 1250 219209748 219209807
    0x102190207180603051027030801090b04050c0d0203070c0b0103030f03050c0a1d0609100c051b0f01050a1137030903032321090a050705240a 62
    0x916400d82c5e90110240000c0103000321008000e00a8100c4159525403070080c0c0c1110074400c2030b02e501d20314001d507542d004941c100f0525000781c400740200b007400b680c501002c01800390301042c00e56481504021000d40e0301e0322249411980c002e00030002600480d1010f000000709500b024a10342d1104560306d060149039520303c0041c000c1d0141e80701507804075851a48543c0e809074040f1407000311150041c22642050714078804a4584000101010082000d121109040c4a010845c40e00c1d004030100103200f160840d68007255800e00d0500f002c60600c0808030301011320030700038640510f0061001040b602d0740e0450b5940d24032005201043d1012600b003176a5001503d4003141c0c0c080c440c05405494694002c2c0c65940d0403a024039001c0000c050020000c1d6402c0d8a0881030001445200302d0042c2c842d819800d201404540302c00042d00c030820301c0e8064035600001480118504044400807945121080c465070f280380001498a580395104410000316980c1441d0000190740c0814080c1244a00100052 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 219212248 1250 219210998 219211001
    0xf01090302030c010e0a0b0c01023105010806040f051609060207030f081b060403020307060b0108100b0d0b03030c030406080106080106021f02071b030b060411030c0903010219020718 80
    0x3408080d4054000b801000300d035500403640c10304d2105002e0110f10103c1e559201041c01038005c401c11019503500010105210000c0c04852800c0d03000b01d4102c0c82c140540c0c488100302181d924441d0a05000d14040000c1d043c0d07549a00102034415803840c18401031a06000e502d0300382d205100f10001050800e0004180680b0000f084801c2c0c82d40b0441c80c1c16002100e883c5c0080e43e400036080b070310060344c0010040c4480d10080c08900c0c0070300e00c6a00190745a410915080086d51808810f40d81040504020803c03014507006011044542240340e8541e1001ca1850b00c10281c076000d94251f0301803100203003035009040000020000c80d1015610100c0300d90b210740048074801ca0030300c01c40300140d2199100d005a0404501c0040460020070401460f10f90107655401e00e40c5030140010b613468222090400034400c42d07003641580040125800c001005420035050050300001e04028004440841e40c40301549003541120300b444507105403e240e14030075410095503101603006807501c8481c484445040c1a405 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 219213498 1250 219212248 219212267
    0x31014150a08220c091802030a030203120f1501030e120a081012050a03030c09051f030c0908100506030c060c16051801140307090e0c1f050304030815030d0e0f01 71
    0x2400b9128003403a20000c400540408020341b039004500c1c401e56401668100404845180700750003464503901c4665400c0300540006110f50740c50f080c490f04014400c00340f1094083d00607001d0034001207550300c003044989072104030740500c42c2001c0c00007a10141a40c01005561043c50000c08080c0200d80f60003110820f0003020030002d007641c3c001c3c000540041c1c069045031000001c1c5180a8801c0b0381c0d501c00042c001c06000c01c0a0241040704000d0743d031610350500403620b201c0c82a05284072403501d403043d0141c2d5084006800d0340c03010340d5000403070329a5400348a1b00091080081002d0f4603000c05400c81601c2e05000c051080d038800e5068000122805c0c0606a44e03074402481c09100c40d56072808059260181c4403046a9031f00d80070705900454001c12a00c10b440407034885200070b0181c4801d03901802850503035018000c001c0c00c03100c62030300b07d5168044100c0350302903890b10b40000142c44422555410f0400c045180e6803501400c4d00c000e0391183c3c420804621404200d440c03a950140410064072100303071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 219214748 1250 219213498 219213503
    0x1c0e03040303090501050d0902100c110f090a0c03060506070c050a0e0c030f04050a0501050c0a02011103090d0e060408030a0c060b040e060408160204150503060c031014150a0822 78
    0x110f400e0304100540c002c602801d8640c0c485080450b11644a0340000d0b2303c00c1e0b40e20803250110b13614ac0e140c0707414440da200d02040b4100064032001d005a00d0303907000400c0c5800007014030f50aa6120a040d8584038843d070860f07001014094100f0707480741194540964141954005e81c1d0040c50460320024410252480d000d01400c2c0c40703201c81e0300d10388820141c410250700052042d1040c0c41070000007000180248a2603210b456064a400e46907060100d0083c250f0381c60810340510b900090040c081050000301c0c095450020302d0605814840458020407428041c540c40801c3c10700021400308405034000c65800002c0707200391070411404240340c0400c021200141c000b5447d60b40404009400100c2c050010100741100c01a00240003103141c1c00103041e241107000e107544103524800300700158141044040d42102182005504524202d1124400602988140e4155080e201e01c400c0d6140c485c04141d14111040e8808503035a00000040070f0100c9500b5a074201604200d0807a00070701c142514024030710960b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 219215998 1250 219214748 219214757
    0xf0316150f0219060c050705032106041a04020a03060e04050d0206071407120e1c0507080d05180604030209010b090a08031e07081908011403073005031c0e03040303 72
    0x41504c40200420320b201d4014103210042005101103401007000d021050400e540303510b040d40349100d0091b002c3c4001b9040d40c1c0103500f000c840c108001007039640400e8110341614016141c910782401200078003240e41c00000140510b40c00d0206200c070200b0710f101c6003480c070b408a440036140e00c041110085501d00207031981e00010700040c40018a400c200c0c2968501915008200d44040b600044407038100d010300d01003481e05804000104032040c8074841c010094000508411076003018040e06070b00c1844802c01e075440d11607240c0210b5035146ca05031409940c003e011360700b02d50303140c400c403001541c440e81d5031a00c00c00c1c8803100010005800404c0303d00308404041d1611003800404080025600700b640d00b1640500d050100d95862902110501c2070715072140d0b1140043e5140900380c6c1e44010b0703001c948a01a4015880900100002d401f41e100444500003100f00340d00413580000801042000d002402800001a0451406641b841d0b01a80d050800c0c0c04018542c1d6400d00d155984c802d6100080100e07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 219217248 1250 219215998 219216043
    0x105011407030e040509030702040509030a0804151404060204060206100b0a0f020a2907090305030912240613060e0a0e0307140a110607030e0f0316150f02 68
    0x14410181c42190b1003420048038803081e050015094131001c0f641802d45510119124055141c1402100c2c0c003e07403000d014500d04502140c00800f1204010809050071442c1c0c034242c0d20031590740e031003074101d64800080c0441c503043c103181840280d072007440fa40d030051203800041117462540042c0807049610904101d450081070002c1501d2130829001ea810950103840b01a0000c1203682da020060b00e0405510b5200040d841e1030038045240001d0000010091030f01402c0c00022400811202642801c030390704503808a07030464591500000c100d40707d8042040c02d6501424400381004540038210442c2c0001e2a6031b034030345404048030200c8c801c5d1072a201c0da43c008104c42640c40e5100309000600e00c010341c0e280c54220717212900c83c00d104a20310320540e405110b002043c07140305840b00f82510b108643e024504586920024590345480c03504038401c2c1540c40981c2c450340c6e810403102c001e03200340a0519621aa80f01b00b4101081807049078000820710b02d0301b0900034140302090000c0b030300034626428000d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 219218498 1250 219217248 219217277
    0x10f080f100b01020c13020409060602060c0a0509041d061006030e15061c0510060605040e0f06120d0201020c100219050c2404030210021c09050a080f0705010b0306010501 75
    0x2d07000c0d0000c2e050541c000c4004080083c0c0303070751900c1d0600a00110000d81d0b100d03e0130f10140203c488613449a81150404420b2003a61450101120082a13281c0307405500c814001c00014000c0800642d586802d080035000c405003c540410032910845181401802099a804d015405e0380c403484bd810b102604800c0e010b21582804003002c9400000252204055084403142c210201c2540541034a180d4403602508503482c40314040c60014025030f2909a0070107251140c1610f8441014104641e0817040c82d000405a0315403140003105603048904448148004c8100a4005e52080880340d01c1030064400303003150780215000300e4400c002d8040c004110308010070001c80305900211448151806524402d10b403040c100703900c0c8400c0c48800700003d0082d0420b0310f8083d203444942c00c0000302040c0103008019410014151444a220402901088103030641c90700302d003402e07101700000300800e20110f001045240000c020700380301c81c4100c00030041440e11008040d9224000d10440b40001c0521101140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 219219748 1250 219218498 219218501
    0xa08010612141213150e060a030c020a0203010c090906051e011103070803010e060102061303020d0c0309050402030c070c090b030705040c120603050c030d0302122206050c03010f080f10 81
    0x452004001583c2c10240909000c8000ba8004100941da0054461091001c000581c44131901c40b01682081148071062001142d0540140212102030665030a24100c80c40c0c0284100800b40b80d005000300700d232114201380681908010f000f50300c02c00e40b51400100396810001c2c0e50b2030071110241d01c0110018100d800454441d00c0c108a40d03590f501080c030034100000e0780d000245000e004030542d0950286441c0340020310349080180140301d402c1482c44400c012a0300492860400091450003040c41c642c03a00741580e1000d1503902064006100204010030111228042d041c0c10744107856001480c1e694000510a0ba84c5075075030b603070740354000c10703010822850564800f2481e800c4034200300412400e480d4200c0b0440e02660b109480e40d4100501c400c0c910f103000e000d151500017580c1802c60520a041400460404008041c040c03207011101c0c400c40781a00c44000309400d258441c1e000d1180e850051a4040550400c0c07090322400284d200010a52010114070f0455580a00000f4210031541011500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 219220998 1250 219219748 219219773
    0xb120309040b0a0e0c0301030303110304020a06030b0f03060108010501050306090f0d260708070809010c1d0d1403070201091d13110a080a021c020607060905030d0501030f020a08010612 81
    0x203034002440d40307000132580d070100142482098035540c1c980d01c039899030030b0240a84a80517920107050030208108401030340d4180508040d50308515000600a1010000c81c1110c41611002d503410b104510000807402015000349060311740c1981170f50310907190383d011190784900251125a00380c10180c14560310300c1c0b06442a104615140c4007442c2d41c1000181c007140b000038142d542c3d400040081d030400c0349280d046410380b5040b003400e000030004242003c0005000411640f0f1280f40130150307243d01c0d4000e40d41c850782d40c00c8580c1c000004080e9114800a081d50300c1c1d100401c102c2c080394811500040411544050201d495a0f4a503403603015540d04441d20048000d02d503007101e010141c5100d030110380c0c58440d1003001610b00e80f4010070040c0c041d40100110801103106200c4014140c1c448180181c542e0030684e544140e000304d0110390b0240a1130064210300841d102a101503140000000c00d10007100440120359000b03450200046440b0f06486007602c216005a0402c1c0c1070a4107000d0001d169521141d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 219222248 1250 219220998 219221021
    0x5101206150f09060e03030904021b060f040b10060518041b050d0501080a050a03081504090308010303200706050a1202030a0e100b130f1503150b12030904 68
    0x5101a1210a01484403000d1580d0740001007219540520240e0041900000707020703070341030500e144c01c2c549001a075a881000b6150b40580d0b0040340c44440c13005c131000741034040d0681e0001d0f00c4d441e1510150304080d941003100c0985003102c5610100e010840e4000c00700b0291902c2e039035650700c3c0c02c5958048201c003c5003074461a8000f9030321251580010641901c4880078002c690340d45558000c40c0c544031068540603005000e194114000300da0000b01c00140001c00a0340c5803d0501e881d07a00c15800c010340c003960010310fa81181c2003010f0001010b074821566410b07203110307407070b8241c10b01d041042d086554a40750b100d07020254421030042c401580030314003900b604c1005140c602c20714118100310070140d80050310010803954031f8002011207200140000c015104444004006640c00c40001400201c8100c454001c107540e20403c80340c4e0940e0640022100003440c500c210351b80f56881c5010014020070309004004541340001602c10340c0741101c1802d040e020b100c40154103250600741004001c0c03a142107003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 219223498 1250 219222248 219222251
    0x809010c0f12091707150806060d060f0302011b0308070509150d020304061404031d1201050403080712060e0103080307021504060c030605090103030c0b040303020c0307060b041104051012 82
    0x1070300c0050a203440d810120340e02d5550320342441d85090406a100c02c40860b03d1121900030381010b00942d03194019500c103280d42454460401c2e03c49202260280c441c4416810341d00742840c6011075002c840c40e031010200c82c401ea13102200781c6008030603200001510000180040d11100c00700f91414880d8020307018410009107880720805104082c2c49159000c10214144207401200f04030070b12446203d507403e690562407403001c051502d50380c020305030480e40b20408044509003101016a0b115008400030904c0608020403450400c0c0c1005042c0750000c54800300000c014070304141c0082d215000301401c0b2054a941401185d003166180801170308000c0030f001c214440c1034000010f54105119450040e03016000010302081000d44c006d050381c440d0740059001d0074038540104000ba81c040d920301d28240e003102e01e501242d01d691604401a114200c00d100e014800402e1242c14050a076110382c900200894007040300c0c0480320b13142c04990080344111984041e092241a2006000e02819025000072020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 219224748 1250 219223498 219223523
    0xa11010212040e1915031109070f0801060c05030405090406140109060f18020c0109080c060c090114180301050106050c0106050a0605191103070309090f1b050a0c020916080a090809010c 81
    0x103281c145c0300029841a594100c1c00d404001c1641441d00444e03812030800c0c036201001e01c0052034050140e110601c185170030000c0c0440d800003404002e100766400707010000c01140386802d01c1c6c11b090000d00380c14003007030032003903842303400000d4495061183d20226440c5c2480d40c01954900001003503c458800e800c182240c4d000c000c000342e541070a2045581d100d01c0360f04041e45540e100e20304a842d080004040c00101c450030094000380f03a030012164404410690b900a030b940c510140580e258405146000d50158203000010a01c0c50300000580a03041e00311008000150f82e07032041004400340c510850340856000c2020307003040c07502c100d02c4000400c01030070200551020902803511795030003650141e00056030410b00303001d0500c4a001300c0799006503007101442195011880020005640c0522a00703100000542d00c1c04d03540510152422a9001480381c9800c1c6400c0e100e428000071040c040300c00160600c0009880c0325102c1c854080441d400424032030030810820b0056450303100384c25081d10003144984 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 219225998 1250 219224748 219224771
    0x100c1b0f0f030206010303110c090c0a03020c0d1112040315050405070f09021213031215080105010b0a02070509040f0f060b030613020108070c1a060a080a11010212040e19 75
    0x501c0ea00c4480c841d038014003540d0714504000300744587d03030307080044250400e0600b00c3d0306d5500d282460703420441c0803240a50782c40680754150000d10440540c0480d85c0904191000c42d1034010700300c003050101c103000b5505001900000c007040c038482c81c08001c00244960b643c3d0090312001d07030302c1558028480c4041b5003166450740c04100c0181403d9110916a907000900c0401d2040525282a003000003403841c1d80201140340d80240c2420b0300e01c0740c2907024640e00c03504c0f00c5140b299515920010a02d6a008101c0355071504802c1d519940918070388805441500c000082c2402c5c001d480c90f1040e078118004c4c0350700c80c00c42c0c2c0e0342e48400305084809172481c40e115200c4440c2c0d9641031200c10300a40803107400c0307201520244005007401e00000e00c4542817004444208020840c201102000941099100b414030f03901c510010f0841280703500202c5607441420481c1d002c100031450340d005a24026022a0740118501c0b441c0c000034466400360407070406030030340440d100802a07050003070140c4160344003291203d00003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 219227248 1250 219225998 219226013
    0xd02061f1d01050f0907020d140d1e05180d0e040603081215040c02030a0305040c08030a090306050c040308070f230706120b06030708130206070311100c1b0f 69
    0x38078840c5510141800108154503111562641201d0305454a5441c0c0c034000d840691542d00001d020414060b940b0038180b03900c0024802c40304800d414102c10800840e00200c001613804100540d40c00e00751400005c00c0480b12122002c0500002c6140249000340c40c18a003203c3d08050b0f80300c030315086919410044005951140503100361201901e95145078600305800403091030442c89110300482c0303080134003669154044229a9100c0171f504011650351103501d09004009450745c440825404080341100b1019484600344040764021141442151079484600c480b51003a4030005003103540400c940700008038450782d000c903038070f004400310801e81c1900400c1e042100020303400e82c0d805030130199040c002150402d024490301032004008100150a034004903c16100140440d0180b00400c80002c1803c20320000c00e402144d8050142d075105d00d01c0d45005070051103800c020842c0c0c0d00a04000d0501d1f01d5461203001d800d1007040e03840701d0b4040c2e01d8507035880511a080303d040e24104007082c0c040c00400c001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 219228498 1250 219227248 219227279
    0xf0c05010612021e0901060e0d080a110f0c09040609210504060201180f06090206190804030305060d030207090e1e030706050c0403150513060c080103020a080d02061f 73
    0x81c00000d00010350910410403801240520804040704d5070100d1259070b22040e041d0746c19a0554101151000c1030080050f080103500c0c000200002000078200c2904c43d8000c2121003601a020102c4445500703480c641c035164031010541c10b81041c1000009000b00f0b082d504460b001601071005c0c04a02d480b106009038500061150600210b0320014081089c03c0d8244505420900f902c01c01c074480710041da0b43c121001390f90f80000781c0540c0c2c40d403001d101903566800440d5105428800c00c02c3e4035421010000e409007400f02c13400d8000c030f4540400105c29041500c40b1002055050740942040d07414101c1d0180205001e070b9a10001c3d202d000d00e03025407040c1d00104d00b0000782030440255101d116503c2c2c01c1d025100010b008100c1c1d014240420400a20314400003040e00d207010402041943c0c5c4c461502901c010042c030080c200e01e00f803490040c40755400860050680e4001c2c3c80c00c0000c1500c2d2050715503202c07105d0307140d00c0c0141d04c05000607909508001c030f4400b84402c170300c0030140c0d80c0303654054000c0300464 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 219229748 1250 219228498 219228509
    0x30309021807020706021506060d0222050319021f020c0307030c0906080c0105072d060b0a0504020901050403200a06120c02160905040f0b090304080c1f0f0c050106 72
    0x104000b80114160100041d1000304018401081185190781d07489200150223013071103002e44c00128200002d030a66805407404616139160700741000d80b00d41e21030800c0f9030300c6200700340c040e01a1640c1d44c24603100c2d0320003543c155500a4100341103030b400c01410035000014254081c04600401082c4070b03040d03030300f401401c000714040c0c601a043c590a0013001411128aa4444245a480000c0040b601d9070010150b41580d0f80104008032000540114104080c40c4010016060f502e0110448200800b80c0d0007000c1028059641e01045030301c82c014030003207210342e80200d0301003034041c40b04000240748050401c4105004244640c0c00c00c0b0200d02054040c092a00500302003610000c102d4210080ca100c2c0c440d192610b4401003103c219000f81141d0400b02078080d4420458540700084d050140035500c00d01180d5200d03000c03040714540501280d80b00d030424000c02d040c41c02140400102445c241241e004e1182c24400341c0d00306040d00c0802560200c04100021007480740300e04061010401c00e2081100809 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 219230998 1250 219229748 219229789
    0xb040209090c100525032003090301050a06181104050402070501020d090506090f030f0f09031c03061415091c060203041a01320a0e011e080a11060703030902 69
    0x14035001c03aa803184503501004100d080c40e0005d1078001b00f03038400132420b80321400e07080f80c040600349003000a05601c2001526078040d806c2405101c1c40c803d042d4000800c980b000c81031001e0301500911000e05a4506a0007211484400d00003442140381560003401d100303100d90001481c00c0341b0444528190b03040d02c4801d881ca82c11078420050304600520040b0303e510b00c41c002445ca010710000c503e11243c050110104d4203000086403200317003902c0801110245803030380d003039000399030030b500e9000ac026046600403061903500c21b048140c45414503055010044030b080094a040200035000d0206951101a000d8101212401c08a0100704c9904c000d40c010b9000b0184e00c0c035200c1c040d82a810360104181d2210103903240c2e0480b288002051075100001a222008050301c071908070074001801c40409800494980141c00b0001030307191030030a0300340c4000380701d14000d85140c0c1e5240790390354541c02e0041000d0b021401c81050102c01c1d10f0800c0060040e940b00c0d0a0000711040103801049222050000c3c0e1307031051 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 219232248 1250 219230998 219231007
    0x114030a0b0a050928060b1809010608070605040f2c040b0a0b0909030306040c02121b0105180a03080a0f0609022107020d110a1a1e040b040209090c1005 67
    0xa001c01e02c4100c0070804004102079021801d00241c0100f8000d21754080d040c581e40c0d031045440303030350b40c40360701c04e504400140301c2c044e50b0402010481c000e00131445054200d02c14001c0011f402d034007030b40a941c200d0f010405201151450f2243c5555140b0001d08812a00700031a441140f40340c407041e60702c074052405042c011015192081c1444110b82078004168866010b000401182600010849511010075640801c2c81e2401d141e0a91401d111080180407290f0003060042100341d80000310700c0034260f401c009201646406001d03505020700100d02c00d109420001d08080464060b48509802c1160b201c4001a540641c4c9480002c60b0100d030010382500f900003889080e100b03034a52200901c0346854034016094100807201030342c2c3e00341840c10781d02480210035420440c000103102a240b0b10340c01042524511031000b64075130103902d0032640d211581d03010007000750026000a42c0135103d81d0740000041c1064940d03030204501488001d02d412100d00c1850121303038183e250f511502041050303c4d00c886d0b845 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 219233498 1250 219232248 219232261
    0x30105071101060b0412231209010905060c070b0f0408010f020c01470301090302070305070e070215220c0501030e030c060c07080717030708010603020307080114030a0b0a05 76
    0x35200c0c1e5510268000b13130140400c1c0038800d801c100c0c024615500c41000861000a4003401c2c0310050741000300d0181e4026400d260340700401c02402044036520980c1d50004031911402080160b00a0944003291036228103000c0c404440e003880202001c0081001c030b18141030360b8817120f0f0300b9160107554030540d07a0f8000c100000c40d201c00f40a08810740f600141c15840d1046c00c1c52603600d1249a880b05035a0080c6801511494011a121806850b0002500900101c90107040c0a55106072502c011101846003600004150390641060350041410764080c2003e41d456410200c03080ca0060003010044c28028000829061021101100144543c415020240c60040090202c0d0350b808154021900208030f501c0401d0344c00f01e0125402030303050500c1030700c0d07034080c0c1800d150900a254008140440c80005001e801c02038a0285100303469950300c0c208560703241e1208805901040d40c461000c40c0b50a0018061800729109440103060043e013101c0605055444421007084e0130780d1040b4400380d464060005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 219234748 1250 219233498 219233501
    0x24091f0c031103030402240d1401140102030c0c0d1a0702010b100201020915030a14101404020405030a02010e06130b1b0a0201050d0908070212160906080a021e030105071101 76
    0x10340b0559001c1d6046150a4001c40c500d204210038180d0307142c903400c0c5a401c40450000503640d116041d070100700050111401000b140075400e0081003001000150601c155610000444e000e107054400075144960311f01c002e00181070140c100403525a0304a0b45a0461203006800840c03050031150700100b0070000000c14842103040b002c0301d4034116401040b446285889501d18506103903403d40e1041d980c1d641303016503100185902840480b003c20035006100c07a030904086901c098810a00010400b4103851081104a12691042641603082180b95101542c041c444c00b40b849040a8055461b1075040c0051012140c0e003a0840e102c04240482c80c0c0e440941e0900c1880000b8000030020050314200d90006007040c0612100300001c0340d285da22110800c890314007512540c65001d0181c00440481c0500d99403640c01c250402c1d80d80c0c00d5170000011b0f0600c458040c103401c0b1030261001e400c0942c220780038020034004000c050020012900da208031183c50034818079120341840e80c0e400741801c12106a4a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 219235998 1250 219234748 219234767
    0x11d0303040504020a0201021e21090109051204060e0108060a12030309050d0f0e03030301210c0510030501050f03011406040c09031205030702060906010602030a0c03020c040f06090b24091f0c03 85
    0x81d8003800503c0310ac149424881d03410095201c9010603042e0a548010000c1c1c00760005107402820b60103100d036240e13400c42280001e001603411ba40c68107100400c16800440c0c003820100c503180c0c0d06c1070b20080200802400d0199130320b1594003d140228802b4442d403105d40c41c0100c488070500020340204d00224503994041880030042401310080c6241d07514101078005180da038026901076082d910b0002c001080038000200004100150005040302c0540b00040d005020034070605002d081d03070707000c004114034040c0700b13240d1038110b14240100945c071480d0500005202400e0300209002c0c000038048046468008090301b081620381e01e640d900d01d0907480080c10080c014013804003d501800050006d07a401006517552a0420700e88001841323040d007401c0b480c242c80c4295150b0001e00e0184801d00483c0c0b04e8205205841040b0001d0200c04124002d015030a4000701c81040000d44005211417a1780e00c035001010007072001440308803050401c078591800c1454180205003c9100c03a1046003c06402c0030040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 219237248 1250 219235998 219236047
    0x32703040f1a03070f05040e0709050901060c031d0a0905010306230f0c0d020f0310050109050a031a040f05190510050c070f060f0e0c0a0b0306011d0303040504020a020102 75
    0x1030554611007040040b40340030141040703042c4180b1803804060346100e403069074010408021203a001c0c0c00e2181024180318164018180a112410000300f0503c2c000c0d403090404507816901d42c683d002034081b6a500240981c8041c82d8400004c110016044006014050195004460004040484075038000c4c260f4404c00882c10980805070800c050b0135102508540c0c0030015002c8150754466042507a8000d1142003001d0064000100038029850b50500400d1b0a41d8003c0c4ca031406000c0d207800400c03407007a0f201d01c07000340544508000b80011814040b09560898892090107500d41c960baa5014146410740c11310321a83c5400810102c24040308114404011015150070441030400d030724220300901ca8103002a1209089191840420003540d00c0703103402118114040100140c4030100c25120b80c1c04e44603c611844000401080c1589071800b00c80c01588141c4070726801a4481c4526103545035a01c0506525000c01d1000180c0360300c6a000424580c08a6800142d90300c0d060080c510903ca07818804 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 219238498 1250 219237248 219237269
    0x7090608070f0e0f01060c031404030f03090801020f0901051e070b0a0b04060f09022d040504050a0507200109020a0303210606021e1213030b0a0917032703040f 70
    0xa04c50910601c84d0aa03040d940107251858542d515402c05441c0f0764000b16a0310b0001c6070008000007401070408545070454860b940d041086681c031400b0354280d000724404030300c074080100891041e643c0698010b0042180c1075100b0342c1092003800c000d0040d5000b00b1410748420b96180100080c1e110030340300b1070000070030440d81081282c1c14000c84a2501c1114021840300950002d8143c014100807613005800c07840310341e58006800003000c1c071020300b50018070034030340a0760030b03c07001c1880c4c01003030301405108010650700c01070300e86046036400305940c0785003680c1d40480d5038603000040541ca400031108003444c00f90301c03213010030b503102c01c5590203a0110f0b5022241e10381c40c11100b03104150380071070462480016070851080d08110302c4100c034180705000d140060f800c2c600048004510418605c450f00301d80c010b04440c03a8955960108ac000ea5005220040010829019203078500d020400592740041c6001c0c0900500402c1211082030414280d560703010301d61022404100c1640188401800340501800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 219239748 1250 219238498 219238501
    0x50102120718080706030228030204060e18150a03060c090f050420090301060f090921020a03050d11030709080d020c0a21051b01031104180e07090608070f0e 69
    0x102e884d11164140151000c0503000a220280c0c0b041005000c503200000d05d92000c11405a40406002540300e8030030580890b00d91001d4444a251821240455440c2e03188400e83c0303640ca81c9807482c400541c0407145540105ea108000c00070580c3c61054003840c02031500c0318801c490030245e9030354480c0c00c1035100c940f081e41002c80100b03001c0c1e03001608400c1595054081d0342c80745030510029015028a41003883c1e502504a0009040344003900f0284200e0300580001d030013030400c3e190103281d45865818202c050385c007252103080024454001403114020400001400d804007055214940d071013601c0711720020700c0302c860a0050110900c4004d02103442800100f5031540c80c0004180120a50300c1403c842c0e05182c18010005000310a410404640c80026580000f40d0b2040b01110889040c50381c0340028589250700c3c0c4030030402d004440586403a031072040a802c808404050182010301204102c40c01030000009540c1c81a008210181c00032002422201d410a07500d1007080074241d0000c0c594000800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 219240998 1250 219239748 219239759
    0x114060d030e150d0e0303010f12030203040b090105070b180609031305010c15142a030f070c140a110409020609010503130b0c07030e01020a03020d0c050a050102120718 74
    0x7407242050310140e6040b020741c0b1900c54046070070300444031400001c030f0411025425007170000c0000c40c141c4401c148850640c03900c1e081c40d00101c10100e0300c001e000d40d004010038400c00700c529000d09810306052500034600b5a0640c0d60004036407041d0740c03010241c40b4184c040c0014401c1030044c0c561040b80c0c40011410002c80d5052540301440c9403094505101c40504203009001803120325072030004107104140911001d4001164403000c0454000c0600c0301d503103100c000714000360003c3d881403c4201000d1811910b030b04d900c9440ca804013505040c1032082c6c00543c18005141180761148819140020341000ca0142c10041d404903038241003c1d10840c40c040c1c500d0011f035155000e480c0440c00070701c0c1694599613a482e454941601c1703034101402c000390100400074031622813401081510310a1380e41c00710325903590005a07510008600d0007070150708041c0310ba601441c0b291414100b0940140300303c07500c03c1400d445523800ca900c0840c0700f458200001040100303076074014401480358414a4490003540b490039 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 219242248 1250 219240998 219241007
    0x601030c08150f032a1516230d0206150d0b1b13151101021e1303060504080309010b010507171810030903020606180c0901050c06090114060d03 63
    0x1c04603602c40c0501d00d8140d509510b003000b001c0213000190400c0c54140c030040c41c01140303020600e02e100e4401c403040480c0288000c084007c1e180d400c102c0e0100d1410f98031031565110a42d800c42d440416440c460080038081c040d0041000c10102e400540281c00c540c1000750381140408074010300207014000701c903140e8000076001125540d008c00000c42d129400c560b0303642d01801600c21050382c0020100d0384000810440c0120314150660140e42e111180c203c01d401d05a2400c0cae01540703c032410404609140e41400444060080a4107040030107000e0580d0348030340d641c5044440550b0183d40c548004810048000000d118102d40d030202420883d06240c255540d005044441c00d1203184089000310741650000b003244207101034484028800d8a40d43d54800006005240503c1c080d40180303c2c04021519600f4481000c4441d041032100700100340d0303544140400d01d94840c1003941c2c104041040b00c0741462205103d0140140c00d0f280010071282d14000100202d220068000e9102d400c0c0c0c20329450020780c11 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 219243498 1250 219242248 219242281
    0xb040206070609051221010509040204090c0b040b070b0c16030c0302190506040501050f01050f0603060325030501050a11030a0c0e030d021501170309090a0608070306050601030c08 79
    0x1150001d9441810340b03000c070040c003000607005005202c0e064200240c14101e00103440703440106010b040f0160805241502465820f20800d50000400c00205001d4101a08410b05150241e5080707072950b40d40b040e651003076911540c8140088003010541c20108104e02e4140d581200307081402600300000300b024440c003110081c1c0000c00b4821424001e404050003400200349402401e1503600c090101420455100c076012a4100d45552a00c4005920021502061410b8034400f5011460a450038014010355a01c0504155030510a001816442c0e81402c1000c002e8807040c00f0100044920f90318010b400d45502524202c0d56a0601e0400038880405406590384180f090101203a1800a40e405455400070003004c0c642600440f00d00c3c20f01c207a00052281c0d0007515044010406a0784c51240340d08051800b800500f03590400c1007592000d140079107286401484040c0700040c0295100000c030318108007507000721180340c1c85c0c00c10800503680520401c1c0602000d810300c1503035071406c46d000000f500710 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 219244604 1106 219243498 219243503
    0x20c060601180501050d0b0405040609021c17070809030a030e03160510051309090f0303140f01210503041221090603381203070b04 58
    0x10034569008001e480d0784100c20703103c1c18040119039a502090707607401415110f46c8030300960782e04c40c401c1a00803031290310700040d4419180f05008905454001d403044520808401c1c80100310151601d9540c0525980c503941e80b110b1904d00313000130340a400c0a464252145805032020150401c038103c610200450468042503080541803220800d10b00600d90003299902075522241e009101808006020765071840095446084004c111002000d0070b032030302e502108900050682511540e10503031075180c2c0400321498040900c4c0322010042c80384041d54454501c1c1c1e80c10007243e1850b40580141d120091b031750307181e59482c421200320481d020251a01c0003d0b1130035001d60a40303c0585a481151601d81d1025545400b40c02d4004010550010741001c00001041c545821500603017009040c1800c01e03e0409200d070424091042e52045601c900c0d54004c105030400b18640d10495a401035 = true := by decide +kernel

theorem cover : BRFrame.Cov 219064748 219244604 := by
  have h0 := BRFrame.cov_init 219064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 219064748 ≤ n) (h2 : n < 219244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
