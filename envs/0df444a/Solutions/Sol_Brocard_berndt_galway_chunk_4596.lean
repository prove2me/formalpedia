-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4596
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:07:46.165988+00:00
-- url     : https://prove2.me/submissions/0e11a677-64ef-4df7-bac8-a58afdefae64

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 826438848 ≤ n < 826618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 826440098 1250 826438848 826438861
    0x71b12050706180308030a0f0b03010e0304300803190204151701050303190512073c0f05121f08030c07050d02120601120c270b180a05 59
    0x1090020403644583e0600503108200180030441100e40c001180040404d01040000103440a00a5400c41c2d503031550805201003400100040540201c03091111200d0307000760b240041883d4000803000c002002d500906c10b00c0007081ca4480250f820000543ca060358000301c680700c075012a0416000074050000020180e440954801083c0c1355580980724416010351500d800255240f00740c0020205a900d5010701140d080d010b2007e6902d13401040410700c10070315048100038032210f01800506180404924010407029140200a0341d180c09802c4800d0b00341d841980680b070211912401004000e070400013841c0d00040c0c212458080c446000c07001c45c10009152080100c24a1038110243d954018040040949000240d500840d80705440140b0f498500e8004203003290100c0d0740c050f5842c850030000090341e034107203c1c403d101039020780642110140c5580c05418125100c4084c007204071103c0e01da01e44603da0540c04440b0b104d0005220018100131114601c9036000c003140c601d0300300c640d0b40080204 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 826441348 1250 826440098 826440107
    0x360709171c03020310032004110301091b0e09060a090912080604090f02040902060702030a0f050606010c0b0f0907080d08091002130308030a18050604020321071b12050706 75
    0x1007070a0682029811880e0082e50b1030340081040c407002c0c0040d13901206c0b090a1401050120366862030103030051043c0d41c10070100a00d641e000b8860f40326040d1500c070004005062500340e510401d10030740c5d18170061606d080d0410402640140140394000101c801c0000e900c1d40710300ca41500c0500c1102c031010b03600c1141e003019081c1d550040805000b54140040d490000340004185214030780c0c110740000b041007642c00400d40d123010741d4100a4240c03150200d0302c401d216002d9400ca9545104d1811a04199110740044805000b2110000c01031243c40002c0352460307407600c3d5560350094400c021111440d50f60040746150a511045030804030303441e4410f00240d4281070010748401105e000c001d515010207810b02c2d44c07450409120142c02030001101042130001da81d00040729116a0983d0100110485d081880c0c86090035034040b4801d114000134a01500c2100321824039211003c40030a003090020744900c00c00344041c8951104103890350f1004280e20200440c107480850003080149180b070b08080000c0c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 826442598 1250 826441348 826441393
    0x3020c0f0303090604031403070c06090e130804030204020d0b062706030c04060c06021c0203011707030b060103090f0f0302070e150a14191436070917 66
    0x40c042c0d0410425416280c90b4a0221307011a5031150300140004007000c94503007180900900145000c402c0c0900298081d8811001802e4403a4400c1c03900891325000c0d0400003003008030368020f161840512040015192684c00f9040a6401c40b0f000f1452140980c0020080e6101e100f032403ca6078a55035002802c045425050b43d9149001d5a0b49440c40c1004400501070f80140d00c0f440c402c10001b1301c1664100b2281e601031b90403c54650040d40c1090380d1081c0420060b410034007400550200305041c81900c0d040c0000d03100c0440b90000001c0640e52182e00044025000c4100e0540303000c80f125000200086813440704510319030099016040480c106818038854141c003030030881580c43c01d6041030340503903500341c01001101c41035880b004141e1035076008a140d4202c110300021030750f6030030a000130384001085080b005582041351513103011980900a0f82860808183c0390703031b10384101441c01880300719941415070803010f9801c0c9600000ea95010442d107180f00308080c0e40d101c0d00480460560180101c1031203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 826443848 1250 826442598 826442629
    0xa021005040b1303090e0a02031b1e0a0e150c01051003050606010e12100b0a060507150207080c030307031b09080a060504080f2a03120a020307050d0903020c 69
    0x9100c01d0030191603210400102901c400303a008440079a900c04c06025010f0740004060041c0c2e90600382c42e0114000009400407a400002022040902c12041d5944002ca5215208000c07612070b1043e8071484224042d005030304400300b40305051088400340e50b20204050017414441e10307403560307035503a125030942584c0028201000d460030603401800002d4010402580c865421718200d0b01c0410312000045209640c80344558003400b444208a401140c2900006d00384d50043c1c0c0c58541d802d550b020225184e102d0707075070081c2001d021104208500700480c0c000f0910b00c0c4c0104030300d506221440322110b045a2007a10800d000c02d90301c024410003110100e1501c0000e640c0e81c2411069685027065082e102c0d181c01c0d000400c2d647d40c40000404200006060310051990318040e9625403003140d118041d0480c00790080c41011a00111902d4a9840001181c01e80015502c0205403500d886005ca03019410207401403050000500102d800d0001d24442c00a92a010b68010031000712082c0910003031802c03003c000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 826445098 1250 826443848 826443851
    0x1d03130906030f0303180c08010902011701080c060f0909160806030c0d03050306030f1e0f0d0207030219031209090c031103160c14160b0406020a11040f110a0210 71
    0x802c003054000030303840c00031a0103080109846000500c41c030b4004280880040207441102d6000c0703540e140c15404005894402c0e2140d85880b0502d4a581c104c281c401d202d00c0300690700140071004682003110107030140c07031080301c0300a06184a010018052601c102c2e0800c21011070302ca010007000340d00c03408450300a90158040c10146a094011901a440d41d403405000e1020000101d415a00c0c200850302c0b0400d02c500643c4c40303010402c06145441c290b4140c000a041c41000c02c0c070020020041851204803210340c00a05c0380a00c2c1da03080c40700c50741841d00e000303080307000002c000070101d00c007000c920709200a070782d44d407030708040c1050005400c841c4080409000c0500e0998281c030700128400849400c160031300012107030a840c44600715050704990708010070300120501da94203007401c0002e4a00d0502c41082c0002c1401b610b40d182d1b2802e601840c8151030040c1d2241d5041d1000c220766450410300000090030106a140c0540d0000041e2003ea0381c022012403c001075503002c0c2a070500c04c40c002c142c0548030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 826446348 1250 826445098 826445111
    0x403020603151005210402120604030210110309151b0d050105150a0e13060506070807020907020f030405010c15020a11010606210b0f090a0f0b150307121d031309 71
    0x104e030340b60381e980715942c03511142119002c50150740c5c0e06845003442c88e00403c201c440c0d03850940340082d00c44042201c000409824541c8020890f01090207503032260034080001c02004c0703d0400300112001000d01904030051180b078100c0d48911881000f0f0bc201c410f070260214465141c5010b0007035011220002d002c41400611809040640c4004a05c914032401c858692268241e10b040400410150b8401544902c0004d40041006046809407180c41d0003100c8a0066076518075040e40ca9032601c684841c502e401c2088240802d40c0607a4581d0006c038000c01c01c0d000d940c04402006812a13201072a800046882100d0b0031500c1c1d1030900440c0082c01a07403401030708052034802c881c1d080c0704103045080c1041b5161241000e841e118007aa9810940c00100302d42070a00305000d4400081466012010314142007000811480c203102410a5103100020021440d5a030ba8032411550842c0f180c000b816559104d031409160b0341c18451841d5020094400595501e00049c10000400416640041c0c002c1b4200b00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 826447598 1250 826446348 826446367
    0x62206050a08400c0b030105030712060612030206161107091a0613081501030f030302030709030b010b04091808093d0e030a120f050403020603151005 66
    0x1e0440390480c001c114000c0c000180d241a168054070b549840c0d4099603900354000320403184944070305005034082c292130710303109032919013001d0b0070721090186a40591014034204010011001d070f030034059014281c00611683c48074542007503c401107200381e00607480720051001c0c1d06011941d120030301c03d0754104000442422440140c403000d10b403003000b0755070b555822002d2010070200103180000c04c006280a50300d08005207080b900a840b1f00130070841d4400c484d03902000484058103a0705a03500a41e00219110050390110007a500003003030241084841840040012110401c46001e01844400640c9039424044c17803c0859656088900380502c0d102c00341c82c041b4600c0300488000c0d8500b901e104050303944418103040441d00c2401d001703008000c07502c440303103410118062000c0601c2460750394029000505080603038441107207030080c00c4500407404910354140626400c180c000607034240241895a40d80024007550000c441c22200c4050035516035045280107610b14500b40214100141003501c000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 826448848 1250 826447598 826447607
    0xa0b04140610110708010608030714030f09040e031b0f012d022505010c081f050f04090506040804030506070206100e0601090302060a02150a090f110f062206050a 71
    0x1100d030070043c00385840c003c141d001c005114000c00341403203a00a204c0d103a56002626560307446407005480b80c40c8940c0a81050000c084215651000401001420201250100002020b02e01c204038054030040007045030403c151080221800d8105000e050101c021036001425540702c01c1500d000c0c5185c0d0040043c4010240b425003c92112030240141c480380780460508000c6c807419000454100d140181000f0030205411000580c4200d95401403d07880f0308c4044030f00e4054950302668000d40d105401e01080c04d0121000740b828400070401715404049489140c01d11a0a0700c05841240001805005005003040510b42040091005040d54940410184659802030095030407960700c0320041840c981c81110b10002840d0000e1502c1c3d554800000060b40d51030300c0100c035641004445c800500f0102d6079100d00c04842e0340048800c88181100c0d903c4442c441907080c4020b5124481002a50003a22401c000e4152000940501e090b091003110f0301665100d42c9030f11200c10050200140101c9582c00b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 826450098 1250 826448848 826448869
    0xf030804030f020d0f0507090f05060d0314042102040e150f09010b0604080a0b01060e0102030a1206090501031a06032a0a09020f04140d0507031e0b0a0b041406 70
    0x1c030740c2c504124035407803000a01300d012400010b42160301c103892807814001e0101d010130407a89903000400401c9984e0960744181c580840d90750b54412003081c96540072902810903c05030100120410f45002e0700d502e00340407165200500703004c00b09000f405990031400d03d485502d41ca20481c500400e4400c510b034400e4a00001e004200c098410160030216100d00c009420501c4291401421151600e4540004990300c0300096000d44031042010000544140036402e405030403481030380603628000301c0c0f03002a2a4618501c8680754496901c490000d4148003a02c00c05000c0c5100c0c02824400e201207e42e08051000040c4c101407080e0090f162043c00283e1405200000d4621410303500a0f8900140004481300c8040d407021080d1400013402c0840042c05074018000d6901c189109210400c00d1300034403220b030000c5000100b10354410402400440c201e0000860004401d1a0f100300403141607480d011040016610b1280484d10b8002c5404c6901d003e0003860788111010100d200d5501d80000000d680308031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 826451348 1250 826450098 826450103
    0x7152d0903060f090b010b07060e03042c0f2d090a0201020601090b01080103150e0105040b2208030711030706061d150f090a0f051021051b040b1003090c0f03080403 72
    0x10723146040001d01e8100030441400242501e45680d0707101040484001e0344100b00000c80c0b001c40303940c1b01822088091500840c41041990382d2907035003046220b40758000d40482c0d0b8948442c03400d0450032402d00030125100b00b40800140280030454400a131070500107802c000b6080d41080c040700d0303003643e1182585044070b40203105e0356160040c000c1000c004150102c072910840d401c0c1800c22042c0002000010302491038001c00019018441d85030704421841c0c0440100a03900c1000800d00c0303548642240c0340310309007000940707246c0303205603407124121503290f4400c0c003e40c010b000c10110784a800c440c0c9958802010114401d641e401c50380002e034880c0304000098401c440b950081850080c003940710300c1170800c0c00700041010341011080d48084621520031f1310820b10b1500720a4500b2402d0401080000342e204000b42883c8044a4824044000300a40150401d40d199148000d650380c0c05029041120f550310006100c14250030004c00012181d042480d4000c046d040400000d54040c04850851381c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 826452598 1250 826451348 826451369
    0x30c0b031302010f030906140414070e0f0601090518070f03272f0310020702090a180204020a110d05130311041803050c0f07152d0903060f090b01 64
    0x6629029001045014400f17008145450400c40b1002481c0c0c80c8c0700d005a0080fa172440c17004449140d90350380d40ca00307800f500c4017a004540118400079070b00e031071041d0428014148200070340d4861021948025900c4a0880c800d41400140b0a400b6040140d070203004c0d580746003c1c000071001d0b000c038011080c40096429800c0340d00924036014044100c025801604941511600e51808074509401d04004ca804d110303c203003d038600303200800720b261003200c11440d0301915103000341e0b8130030f11400000c2030712103205111000117242c010700580e00c61000301465005a242d00281201c0b030614246070094082001087c00810040c245c49405011240c00880303902000c0790204840b40000b2602410f1108004151060b103401c50070205904140a00010464402180c0d1503010840f5907595903111407098404030210001e841d00f80354820050440d811070200030844144601d5020070401c2084100144c000500d110024001c016a034051924031021a25044c0b0407030390541c50b0f208082d4410310840d0101d5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 826453848 1250 826452598 826452617
    0x801030f060b0303190801050f21010603230606090c03160c0606031a0a050f0c03060f030f060613090809060a0c210e0303030702100f0b030610030c0b03130201 70
    0x1c4240d0b0841c0a03000c00141c02d60f0f03119107010400c104426002c0c000840842d40903c00419982801c510300341c45000010040740744003144445042d1030140c440300041c0155281e0f070010003c1807501866400c00c0d520f044c843c844c07403000360b09454100764010303101074440d0a101041c03050300c40891080d40d81040d00d008030a00c1d80c05040100ba41e0760050108010401341c20403e0000c140808400c564610038244030101d4455960b4034140d008980086891010800011002c0327440d0307407030323481c041c51384210040c1100380107520001c0020314105034074010300c200d61b1000e010400d035410011054001806c2d0444248010780784c2d590383d03690500890502d140241e030040f404001170b5201f800d0f000f105641122120f00801c90900c400c12a800e4028500004507005042546a50900208492140017954068030b600c1d001d15800c800607080042d12498400e03140c1c4031055007a601403202074003034005000358512491440c41c142c0b01141053303216010061041c42001100c0c0171410540048550910b09000903 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 826455098 1250 826453848 826453853
    0xf0c08061905060103060305060108071d0712050a1404050706021e191a0406020316140909060f0a0b031902030103171c05071206050f011205090a06050f0406140402010801030f 77
    0x411b05da03070003c0c00710b1180800010309030b07101052070780c1500c644821503d038201208000c4c03101c45170144e440c00000340740164941610100c0d64001034000400340400319500f44100c1c030760061300c842503038141c0c0c0c1600050301c00c122701074041001c91000414540c0c1940303010800030400e501c400040340401200d03840600c0300e1042202d401c403803040c1541c94058100c258140303410030100942040300c80710909216a585060700e1170060100c400030030ba6612810b464060000c05120719580c0282c10b19030010800380542e002d5607030307841000014104004510751640781032512681c40014003800385c03060300c6c8100014404540e10312026031040c40320300f06440c1d48509540c001000b403040e404000e402d0624210901c2903041c0d014070f03604107a0442c0442403010b140c6540401450707c0c20030910341e01142403a80282c2d00c1d02d07980e41003250b0024006080e261403c074903032950f50a4420840f0301c1c40c0c032000c8110401c0104103886c0310715000918101c1c030b0090a841d0590020300844418003000d411200300f030400404 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 826456348 1250 826455098 826455101
    0x6030a0e030c0609060c07020904121806020a060f0501050f0603040f0501020a0f020609010606120b0d0f0809011107050123130608010602120c030906250f0c08061905060103 76
    0x56031140340d003280e40c0c0d030450507021034a030710703042d079141c80319010708000b140ca1115a802a1510030383c0042c14185151190b03035524042c0c03805003c2000500202226207489042e219100d64000e10203a0042c1002d4001c40c40e10b0022100b0303806103086e2407454080140440d40b604840b141a5400960f04c41703540307403283d0a0102d4044002d020003000c540c000144804941d51182100d01005425001c036641a2204500c1a0a80700213001d00d00c0003500c2c1c0d0f0040403074186550007040f40ca000180c10082c640d0400d488000103000c07c0d00c0d054500502c0003c608169591154401007401c91003400350801c181480300080201c100132160700d0b11484c81c0320044a1240c420f42c100c41000d81354520700d0007101d5851201400d842e03002d1152101501a8106400b0b50b441c4001c2210070340c0041902031454500d490007040802e8101e00f02202200443c8007012a100c00d0b1a0f01501e1010300600051106081a01d44940340103156000503105800003414481025819480d803001c2803400140400d0560320040102c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 826457598 1250 826456348 826456361
    0xa110411040314010f050109092d06110c0c0109060f200115080d02010218131116051c0206040f1e0b0f060d0507060c030e06180a14060906030a 63
    0x81c9480c1000080366618030301503100900e010f1022030240061fa90711911041150300642000e000c112100b0100600e22489551031440f5060300f40d552013400c4100d40f10324044030b00020034494510760000c1c541904034001c000301d20884800b440c182c01d02d142420401401a211226500140700e40355540d035119201c8464241021a103905c0200029400d00d006403440c40d12a1150740c56500031024880d5040c0c0c0f041c02101c14150204032a09103828002040c003000b8804101300340c4072a59900e25550380312940e2801051015201000102030f292941005420b080300d10114103a04c01e5904484150203401091560f4000c3d0030100004805c4018185209800c0341c802849040b8400c182c87c01040021b480034850042c031804c080444940d8910041c4404802040400341480d4480381007000014812081d10702d845109150094502003200c0200c0c0c80ca4004a580015180c410a0813000780d0500c0c2000e00014502e00030a419040ea0310f602180300c0c3d100d4500b03014011000000001c401d50798541024 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 826458848 1250 826457598 826457603
    0x51003050a14030f0c010506090a06140121050112050601060c0b0703021c0c020d090906052809060b09181005130b030607030501050a1a0a110a12051b0a1104110403 72
    0x22640c3c5c0c4044850b00c1d000741412180e0b00c1c8540900380105806044a00c03c00091307a08900d1161072031441080159451049414002e40d1240c42c1c2021101091703031405180d0003454054181c021a0070707075140450070403805030080d9040181480c0500c0c04a0749043c0b200e5000b40d01d5081c0181e450800c000f441c0c041d802004600000d080c00d21002a001e241e0009608074064401c1d40c0705e000042d01c4212502c140d508034402d40d68006258043c62070054002007000c6905100c000c4001141d65903610400309490096100c06146400031820a0003400c2c04081c01000c50040541c12155141115440440800e980100b034006e01d8044810024a40107074000e0080e034074010304851082c5081200180948800d020382800380d01c2600001075400d0803025841900c511000c8010309208d0189000c90b070f061120304003841240310b0004c00d40040388030210941402c02442d80c0f551380c0c910800e22034103441d1003001201a0558460300c2e600c4045003080410790b6802504540c041004800040b441d80d0900560300701 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 826460098 1250 826458848 826458877
    0x90f06070b0f09120f04032d030504060806030c09012d0e01030309150503010909020f0607060e070f080303061509030d0c11010e091b1b0105040204051003050a1403 72
    0x1e1045895008510703034422041d0408030b500031012013400f240d150080940c54458458107000a1000644c440032010001b01030005004040f495201d01d11940104c07518140d005c203c0c0000c4c20311006a0003002c40b039001c101a00245100380c0901e01150f451601403146080108003009030344540f04010055002560030854042c170a9034443c00d610a421401788011030106144000c00100e10b400a61280e203086c0c09911f90a0460380707400030050182a400300100d911601066401490340d603580d01801d181c3c0d00425000640450100703803a890422540c01020728156102d800700800c3d4800400c0381c0d44044103585035000740c0c4982c00c030214140207151105a0501401e1031821354280c3c01100c0701102d500480b5400703010200d9800654140e0820748110360025071707000015034400a0a86451201c101420a452424032a8646c2d841c00700c1d02422980e003180d44032010700055150034051503411551050320f000da501d1640c2e039000d541704078240c0c00910b07005540d03c160b030f090803007401030f10500b041c4c1070074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 826461348 1250 826460098 826460101
    0x9030e0a06090f05010906021506060f07050309040e0f030406120f0c110d0806060405010f090810021201170a0b13051603140105090714210114010b0708090f06070b 72
    0x390900609008000c43d161000c4400030b09584125080c8080b90300e583c028050100e2922404c44a0f0030b00242441d82060b410445150b1050141c0d006000c0c1d0ba010301d02071611603407a103080006603141809544943d90121205590300c00c0040100c404948150034030402134071100081c0d01c042c1960b00a0b5031141d61610944289454100f0312104104040e0307800e5401c855074580003690244401e441c07154100c0001c1c41b0a0055500400b41c441c98000f442c240014803a44c0c54005c00c1c5480c0e07083d10011001c90b00440e070000408644124180984200c800040c407096914107496503855031b800f00500400703500c4011980e4460016040f041864125040d698150500c07482c0340c825000c40c1c88100c0d041e40182440071940c0606100301c0d4090901c61000d000721a150034005040045001e012941c4442100c60101d0443c031440088200c0161110000c26807000804292030b180c80e059102ca28520713020048000011a04001c03a0610501101c1c8400c3e80304101d00840c4030340c000c1000040ca608078880 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 826462598 1250 826461348 826461359
    0x1053709020d030f1e0e1c150b010e04061211060d06060e09130c0501030c02030c1b0901060c0c03150b180a05010611030315010507020a0f0810050108060a09030e0a 72
    0x18154031803090691140e0002d28200d030a15000b4440d8840500e00040c6e210340c501d01c06150141303030710214400b20340d14019500310545039044413030218060314915964440c50521956007100790103420000c216800c10500307240c101c100c210a00301200040c1410a01724040e03426903102c42c1a902c20180c0b600041003015140c1101a200321401c1c01118803404070440042d03440014a040b02c810320b0340c03114100050380c0c83c05005402174000d060b044003c0d800240000074030303d1010803a01c0f4480380701c2c0707103020036005954092104405060b04040200041900c0c900045148580a1402c07294003032480495041502c60740c4000307201c1711624540c004000500316020644190340c25010384074207101007066036072340c143c00c0d54030051400d40c03600190001c1c80007a4207840c8410002d1411881810070310302d418010b41c0002c04407115500300303061907000700509000d080810091056070804c40502007203554140700072541d44402c011305031410340c1e0701d40103403100b0184240042d1105c000b0141c5064899900c50 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 826463848 1250 826462598 826462607
    0xb13080312011d070c0f0302010e120702040f1b0c0213061d0f07020a11031507020607030e010c1205060f1f110d170907081203010801053709020d03 65
    0xa104005002c000c2030b000f42c401100d070010990041413039890301d107041e410304e03079a08140d06925031054003995640c2089a0075100180600c1e0708403209800f55650b240344038130400c41207030252100c2d5030401d0700e00b80b404074945455601307180f000703003003400d0910510480f072002441d511803480d140d60030981000f03000203842c3c04143c00802085003181140403181d84025860000110031502000107a00a00101c0c3c00305100c2641e5010110010301030340c0054940103000c3c50903410681e0340d800142d21860030007611552510030030420132514002032021862041c00100346a020000c0320402c9a0344501180a07540c0d200c45007081c1980103000503034034403001201200242e104861220100e07490a09a000118002c520114190b603246c607100e0220f0f80b044c09410fa105802060412244500e40c8003003070050f410070a22100d807003009542a40d0350706180344e00b8291007000d0560803035102e090490f40b852415600d45d50740b200c0b040c007802a0208100f41b504d43c014040c0d030702c07003c1d40101c48901081d0915910 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 826465098 1250 826463848 826463851
    0x70602060408030a0f1e0b0d1101110a050f1c021f0e011d01020a1b080d020922060603270b060a0302061b01051311010c140f07050907020d08010b13080312 68
    0x80306c60411003000a00b0521840741135140f4024515420b580c20540e0039800b03002d0211820751204210f44194003580e503a01d01c0c19a03440281031499100741aa98040b00100705400d490756940c0c03015000d4500c282c405050079401c48040440d40a0b101c840c51400303203601b58401c5450301d1841a2032080f0b0741e110002c25000b5030048110500044082c2c01150004040d240301804040d40b00c003130300749090b51088000700250440090755502044c8844002c1c1c10f2150924540007a81d10480d0020f001464200060102c40805034010715000703c00341000c43c049c02c20060000300d00c0c1c00c20140a06035581400240a40d40d0a0704000d60180001c1954010f2030108803030389040d00240c4000300078a072103101c6800310311010007800400c0c0c1c81c0075071804003555100c3c140800f5101d2080e92400d600041c00c00b60b45040c01810942030105078030010301002546000c541e040c0c1c1100310b03400138018107505070300010300298050190f80300f4070400203038003840c0c10854101c940003810008156922252103440d900311041c0d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 826466348 1250 826465098 826465151
    0x30604030f0f02030406080606070804261c02100c030e0a0602130909051c03141801050105040b030307020f0a090203090f21180a050418020111070602060408030a0f 72
    0x822420b4100d500000484098a80710b80326168945d980a04028455002d00012910150140000074101d0780e03800e030120400c1c0e4001920420681c05400342c2c0e207003c441c00c988021420803158280d00e000c0c0c000c5040144a9408840450a030420041c2a00603141150500d529849010510f80a1106a42c00707000841507a90b0039502c029940c2880d1230070f07030312841c03005422a0413001c00185203565281040703e1a0240d420003180a0759228141c0301107440c229842100c1d848100758400780d5240030310406001d400200c804116442c0000c1c0482d54034040c48900034052441030040003075942e6003e034030000810316050300795540e1621020454030b03007050084000071485400c00b07403c207069040c512003400c2c940102e0a507091201d07100c4030b55682c43c1040c1410307800a40c800301c0480c250321540940c2c1001522214000701c94549480010250b401e40508010b10345c210306400e010996011801c1030700305401144031a101d85130302c1440310052155400c4074800514105212841d901400b40040b8001c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 826467598 1250 826466348 826466357
    0x10908211005031203040c2c0f0c040b0702030102162102030c1f0f090309150c1208041401021206012d120209030f0309241215030604030f 61
    0x44500c4100518961a0b0040c90b900d90001544110420b205402460344540140004060544c2e070710710310481108058490000340c2000e60026510f6610303450502e0300070b22104100040c40c503128404280c039003c0d600a84602d6980000c983c400c2d550250152001f840001c00318010220740303843d010701e11005014a0940c41001200c0070385030700f07001109031102d110107007028201d07074a1540c0602c6a07080b840303006040000d5844821a1140c500e030f10038040900e1103502c443c040300e4200611103c0080d0303200c14540c1040455000100010440582600068032604180406440e146010429001d000c244a81f1940c40451042c01040caa003c010f4001d81c42a201d020307585401c9000d80f0001591001d0364020044821951000b20703118902000700303058001401800c1000d03c0c40024109080796006111903440410103c4041c0350010b03501014544a0807140ea1180c21038110042e40e00448e481480d86003940c2000030480c10030740c008a59019001400d5501d2441c10f450064045095031500c20000f5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 826468848 1250 826467598 826467601
    0x15021b0a081f050f090604020607140307150b1207090507020102070b09071a0c0613050c2223010605130b03130b0f06010c0209040821070f020a170c01090821 69
    0x900504885c0103001c0c6002a10b0242c1c1c0d541c007031250550148070304031095480c51544a05102003840600719141c03081406003074034030002d00100141d40580e54000d00c14061b0049a6143c01000594002265034110380800c455542e24026802401079030000307850040624104010344c1c0740411500145c038a1400d40081613402000028454000c540400d0815030100c00070440d08030600c440c107107070107105104440c50340c1c0001d004605101e28980008502e44810240c01141e0501c0f40600d02c4410b1140e10700100f004101d4030a450001c0f810301c00c0c41c0500c08002030101001d92040741c960054011303001c04640d2402c0004140101007494a0700f5110003000030702149105d0741c801d030703200e006403c169540042c10003e50208a00702c04040d1003120300500410103200010540c0d8203a8040c506081d00301c0041c0c0ca004480500529005400d00085402c40208000000e40c4401c5040400495030100394071a482943c1c0c0f03078010318840710f001c0d01d00d84011995030780745551100284194080004200442d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 826470098 1250 826468848 826468861
    0x5060112080301051c170405090f0709170109120906020606150f0c030d0c020106060801060306030335010e010f0e04050a020f1801030503040e0115021b0a081f05 71
    0x21802550000c0c20705004200412080ca071164103481c000001600141036541c40759548070000f8108515202c0c541e001160801040c5030899000307500c00c840000b480490310380b00340000c02c41c2545016a00c4000518007201c3c089250950096038001d6000707506800c1c20360051005841c0c040d452207548018402c045c0050890700349114a10078003614000b1040c2050b030305020b1000c1d103420164100c40607100c14010b00c02002190701406c00380c00c4094000154541c01d002c2d000b40503040580005080c1400c00c00100000385d84800425080c05860b01c0c07500d10030714013a800c174104d055401640912840e440b4000700d030b04003840240d11304950800e404008030300c4d541d4002c0e811380d0300201c0f0090020342100035071002505101c2502c001c400741c01081d5511001115075019003900082e0000c1d2600c0e80046000c0c0402c5d0544048240900010036070304a41c0c1041c0d5000035540d0f0404048214503820201d01084036403031315a01600500319403402d803803040c8405404d0200800168000c004183d00341800300e4075 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 826471348 1250 826470098 826470119
    0x340b0a060b1603050f0f041415030c0a03050c12070305060a0603140408090d02030604060b011b050d120e0106090f140f07050906090402070807050c030105010f0e180316050601 77
    0x2610510020341d500c0072032160f102a191a00400601651403400304554420050400e0007000a0408104080f410340b40385c1040c083d40315000c103941c0a504800700f046c400c07062812030989034001d074a890081003030b5442040b41141d5014043d0000601c00b000010311801540581010f0702c07801080d40d000610542c1d81d40c013102a0f400e2301001c03900078100c000205001c19100c800503c01100d01030400d60103c40a075012038544441128103540032660394110084c00d60703009180d08908a410341d4104402400c40e2586506c43c4036001c140f905001c8000740080104109410403031100c01600000c000c869562080d5101804880c102c65200f80d1402c1c07454070003c41000125805020360119001c00755945042c1074401d50703c1006801d5101b0310501c18490300d0381e114001008858461919241c0700c00d880e02e440e41c40c240b40700d20400c0c0f180c0d04140040c082c40c120001000120b0b6591800829161554130b4900680381c80d90400c550103010000310a60342e94500c000300a00144110200c0781030760f0ba640342480 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 826472598 1250 826471348 826471357
    0x1c03020a03140c04140307050616050c040b1c0f0602030a0e2505011112070c0302090603070503060c0a121119030605011d0f0a0603060f05030111340b0a060b 69
    0x503c981401c0c0300c03d01600188500410414002404490b07065440e03400060301504060030404000d1942c11720101088420721246400d0103042d1001d0018411210026911001102c2d0325020005c00150031400d00c5011240d006510741c01110440d07690808502901c0548000071604d900c0e48140c0d04c0d500c66100031005e0b00c01445180300d105201080c1480011210741400c0310700440e9030301c0b4802c0c1007821807100c2002800d00a1280c548091f00c2e515608c1030200c10fa00080c0018460340102e40e003084a80c070302040c0158010541c10465507a68440303c41601c2184440c000e03590080c0c40c01001a5042c02a540100b178a40c40c2c80d500802c1c540b101c0d51040f42510118010703c0c0c00a00714886810300b03206050503600020703d0042c80d0303000004001c008104c9640f07080c0c2c402000a5103031001049907406210110024141c154000d0041c14120100c84070a0b00c2810f02d40d08003008144513015416448200682c0401760500c4900c1c0e4003d810705000d558408151400c655141c585a40061203491443c01c49 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 826473848 1250 826472598 826472611
    0xe03250c031211070902040927060c0c0b0c0315030a0302120706230a0605100819150b031905090a150e010c1d0108010501050301171c03020a0314 64
    0x803034054150359032040700800300740141c1c0510515a030500d18009042c040e5001404c08090010303210341c941200c110603610309414540c290031544031400000385030300d50f005850035080440030a07504280d0790101d6904029400281182041c4401c0c0040c40100380700071030141c2c45101034115991004004c1603103d68481000802603409075481c3e143c840001d4000e840c030180199000a02e418200702481907101040700305001c2224a60b040041d0121144030700009030009849440000380e240002520b02071002d0041c2c035891048295440c1815520740000070b20b86c0c1d00810000c00c0566495461010760415144484a1a10340160000282c2d2030f00c2285d2007540914000c05162000e074403440748405806c0e880d0403100792070f0005009444424002e0483c55006940c0f0900d03170115104242c07107100b6091596078100043c4400400244e039001d01964103491501902e440320fa4032241403d460007004142001d40c000404540147c030076050b174043d06600c021a281400345040e502500c0e40c0046045541 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 826475098 1250 826473848 826473863
    0x2030304051e07060c08210702210901050d0e120a030e010b011b0c03021c021503100302060a02211207021c05070c0f0f03172503030b040e0325 63
    0x1300300c51440384100000e06401010507624140800140011002d001307002d4071030140300e0000340240d250741040207600d03c0000785803c0ca043c0300c941010222038440c40d16102e04000c404034601c040d010341640454a040c0a0004a0302c013080303000e03031261503604000d81d02e03004203252003240b82c0503000c10b001c1c1d8650341c60705a4807040d0010340345074014400750740d0545c207450a850342580480140c60361784122980b0350514945240d102c80d01d204100b04d810050b204905014428010302940e903021410a9042da0390440f10a516a000481d00320310f08005840400c10824a8100c00000e00210340c0051041c074121501e507911587d24441c091360b40b82e807050340e05404412901d850955491090002e080054450070107042c01694481c5031000e00748030790304034907000c2010017010401c1103a03100681c035980201407055410f28816a40011000c400c6c2c140400c06030301050740c10302c02c0610980c0030703004001008104004141ea100c240c15070b01d800c204046111404883c01c0301035049101112103c4403030b0302004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 826476348 1250 826475098 826475113
    0x3121e060e100f050a0509071b111009030c0b030402011e0509130504030c0209180f0105072c040f0f180c0803070213020a0203040e041a0609010503060a111902030304051e 75
    0xc2c04807c280040000003081000601500d21190f01a210002c3e01d000303403141c00983c40301d6020000441024481d00040c44000710f0100000b5410804d075104070340e407480c2d880351030366507c2c001a100040d466410380b0346a03481c80c0c180b18185421501520f03a0207001e44444001d41000c2910304101d80c0203a0303010340032a111303102036001880c0000e0b070a98460000c03e5881202c5401140c40c80c038240e944100280704d80d444d2410070482c0343d480980911000c0d03002002c00e000807034500d6000022080d002030240500e446084022040389650072400010904030317030800481100240f00b206001180104440c51040c800300080da0701c10001c00c0d10b580c190028002c908030014550810300a5018000250642c0000c1c00001502440d584520348200c0c000c26014102c020201003804400a005010600c9070300e41d0350052256032000107070f466100049150005182c3c2c448182e0348402d0240102c004401110811840c0b09107601102440c0030324403650445042d44a0320007640552200440e449855a2100381e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 826477598 1250 826476348 826476359
    0x108060709080c240a020703150b011b11100e10030c2c030105010b0403051009030e040506030a0b161409061207091809050f060403121e060e100f050a 66
    0x3c005035001ca40304d415049040036901038180403a01303c0d00300780c009604041000c00c240305050740c454110000020003081440030031400a4026040300c60445841c100d40b020803410802c10f446140d81c514001021800c2c1c0303640c08000140045038071401a03001e00b42c40d80b01c0c80c0c1074900078000c0b8038000000d522a48054900c1410408898101c0e19550449085005400405403400c0c41007034081c0c403102058590b62401c500308249450459160040c1003840c0200340c90100b0b03031110f60044e41d00e20485011540362990300009180c132210220203485c2c54807900c00d101c0201e10f2800d052a01c0c0038291107940704200b1420b081c40c0180200e100d055080300040005403002540c1d070b0703121980410f09003003c0a501d40c0780c2810307400744c240400703041c013100d5540c031645c1c41440700802001400720345400c014121840c1c25a002062052012200140c013610346000c0706072a00007100c4441e0150140b041003140a541e03a0494000e410103890710745000001c0003011a201c86241814425110f01404500909103401d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 826478848 1250 826477598 826477609
    0x5010e1503031b0d09060504060509040b060909090d030f09150e030f030a0c080a0c09140f0d050106090b0904200d020301090b060405010b041809050102120a050108060709080c 77
    0x354401070341400300f009075541ca014011030b00315920103200000c0400d0038040c000602060301c02d420843c10703c1800c1c0010048540d02004452600c40d00341c8000c20814041e001080c1107010790f044a5900c12404010081986c01c0003d0721000491503a80910040501455000482d040310002a081f9104a16855040714145d00401440c080d05011a842d004101c1e0541415070004d5a20b030b00310507110101e68886691000c02550401d204880c00c02406114040c050100d80551003031010100c1040c1e00040c1c10343c2d5400850003420009442507207a02c031039292941c02806d0b00c1c000e0124440c64290000001c3c103080b10503d104d550300030040c2001d050036181590340030f0610007030568003007400300c410740050300d080c092031408900c28429038060381801020802550416003011542440030700c000c1082c01c080328038103003850f14a0100019402e0150038100d02900c40c03070654000600c4c0440038410110f200c1d0303122030304176603151082e01c65035101c51104481350183c1d40b150000581c01110034405c6031801c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 826480098 1250 826478848 826478881
    0xc1d010e0d0503070b010b030415020906070f0203010f061805010b09030d08060d020a060f02010506030f100203061314090f06100626070e120c100c060204030506010e07030f05010e 79
    0x2c1d001c80b41440b02555550401724402d8210909084000c81400100081891040c05d5080954000c4d414079100c200454500d00030741001038144908500d244042d0b40b402c0d84940e445c410400002c0c8021a2150142101d01e0308850200034070515000000503581d4900044e20f040c4a40200505985400708104441043e4098011944541452a03140c010b9075841c3d506401846103403510f95232000c03105406400c580e00140024040d0b040380c8a502802c2d40d020501d100101c001040040e160f44641011845000c3c4a07441060301a280200a079465000520b44501c61142141100c0c20b01c00130403000340d210f210980c0e032311943d500e001c0c0c4203209007030081d0218140304a02c4040403400300c0d11085e01ca01102016030303a080202c2d500d003094280c0d900304809194280c10f051001004400742c0e800118222500f904400300801200344881020480b080e012640219080350803a000c03541c4591030de91904005503201008a8030f401500c3d8080074181c010903048540e4407000c1c03241a5500620107461007107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 826481348 1250 826480098 826480103
    0x70e1c1218180b120d0206071409090411030f010209011d01030207060f05061512041b1d0f0601180b0c1005011502071710020a030906020307030c1d010e0d 68
    0x9001010401d070b4803410790007003001d046031408520941d00e44184010403460003544401900500810800940c00184143c0c100303d01e450040329449044803402818091680036583c0202c50b00140014802d070a035004001e014210140c2d5a004007000505080f032050344c803d14040f483c034500c3c80b5022100350700c0301e000041041c1405860000540d685408131181c11390128419540c960074070005040c4807c110600d103112510141c50301c0c01c400e002c0031f0349820061004000710340001c5c0c540c02800c0c0d0429014000c10064a1801080042e5222801001d0040301ca030f80401e950040065180e6200380d0380c0001810204041c00b205504103194004164010f03661400d2a124040c2d00419006003441085e00900d4184007a5210010f5030100900b4804207a005002008603000d420340d00010114a00054920021006030345148600040c0c2c060700d611b00c0c0107014944040100b2a049030150480700c0c01040c5079944022512207000c44804800c0307a922403a0015050b500441c1041c1000141c2810460 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 826482598 1250 826481348 826481387
    0x21020703030207020d0b040b0a020414060d0b030706030207050d2a050102040b0f0d0b0301020f03280509010b040b010320160206041d0609040b040305091206070e1c12 73
    0x1034560300415000e200c800d170b040f01c1030a0f2020401013444404104250402d019520035031401e413618102400540d465a04c03184103190018110180b00c256034404c42061002406072030381f25554010180094002050580e10f50081c40780d0480c210740f2a0f06866032821450301250350100a1000c2c1c04402161880c1c1140e44d59401c220110351810000c000d03206010080003944d03901e241c3c0380362000540304020b01c0c85010380c1c018414014003100f01403c1d41c2e403003403068030500f01da01c0010080381d054400c120f04800c80c0e6494101806214501904401550481914184804c6a503071004408561000303000010044070382e001500280042c800502d0500ca0000c0e02c25400007280c2c0014440340c0c4940d00c242c0c04001c01c25520743c10154520710240c3d0000c012140c919907480d10f40c07281c201d84100148014100140045e210300f5941d50740c482054002c4030b40c0100e61080c42c0018000e0b00014070b0030103c1384140f0320f42e1b1140032070b801c05c0c51300b400d400c540c8116407035001400c1100c01d983d0b88076451100d82c03031035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 826483848 1250 826482598 826482607
    0x806070e01230318100e0709090b01030b0714030a141b0a05180a0f0501121b0c03031503060e070b031014010c082208030a08010e100e040b1006210207030302 69
    0x2007005c0002c81c415009410780001d10480d4060010315004095000034281401c05044102260501d9402030449402540d1035459031f883c494212945043c0c0380031510302c1c140110030310107504201d900180040001c5400b41c219600c42e12003100c100c2c0707461055284041000c0002d401082d1250b00034000f0711400c004842400020070340000c0740c1e4421034020300c0c1c0508100000b0482c0e03607804446d50000803c488020007400442030344075403c61a12000400900101004600406109034800314552145290700040143c5070f16144c000307425105655102c1d0701c10000702003054810401200c0c000c42c64451111152403800c000a080680c1e01c40b0400d051099413045040403c0d8440b00402001c0c13003c40041d08540c10403004038410005941082d40c7c55072060000e201d41c26088440c05054036081e000c5042c25590750b1418099044d05a00201544a4600306000070003c0d0040160f0040d4120100d25480035119001107485202d0300e00310180103404190161007041c002d07802480820701900d005441d2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 826485098 1250 826483848 826483891
    0x3050303010b120f0c0702090717090601260a06090f0b07020303101202060d110c0a0302010b030d0216060509010210140a0c09140126010806070e012303 67
    0x85420990141104440000b00c0307503104004940c1203580010303030015802c00b5050100503504203001e0f2907030090058008030081605140100506200440280000000c900c3c180280030707201e00302171098940346081e40010102c0180101404904802408010030a080068031850090040c090081c5c641680d00110680030442d4000c2a920411a54004559030f04001060f86034640c0c507544501c28001c1c01c0c521080040e0f075440c0c12030705240a05540491001d500c40c9105209100b009240034251003800484000c00d40c0642000c00800f00172015101c82c000c00b40c0b41139803070f081d042c41070380040281045c0501880340540c01400b103128040c4100d880f0100c0700440e0000b250140b610000c1740e002d100c0300304180c80703840d170080d100c202180f480c0801c3c0c00d602c0c040101c1240c850504500d4144a8030900001c03044085d001c036140c80e03c6a50000000d29691402040d0f103c14003540c24000249841b10302d5202540100e40400034040c615881c440a9070782080c500c030958001030800b0816210078141c10a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 826486348 1250 826485098 826485103
    0x1c02041a070f2306010b0301030206030c1321021908030406110109020925020d0503071b0506072604150504030c1209080708010e0a030507050312150f03010e0a030f03060305 76
    0x10340070f20512440001c1c400c0504203483c1c4501648007240b203520410040c40103885c1c0300103607500204054529500e03050f45440b0030b5030b58030080d007124a251540131501c40050304004060441d941c0203542c0d150300840142182540008240200041343d8010441088242d01c50f03035800039030071425000003d008503158005050a181510b0304202c02469010941202140a450050310400c500092070a020100000341c20f600000f41090203100700c9000324180c00001500801000344e0181c265500ca03d0010700103400b0136019090400303c03103000e10741e425a1200445040d0302454100380300c0707503000650f80d4a500142000810403402c0001c15501600041d841d80c4451003075400c0d54881220032130403d84a03070324110245c3d000c00107503810700c2070f052801071010400c0303186680c0500d8010703503c8842e401c00340d145202d0903e07103110645441040220000081365181047c00d01155401640729400301050b00b651202d85022026400c841114000030303000b8244a03288900500b0080745040c1da03034941c0c60 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 826487598 1250 826486348 826486373
    0xc0d0e0a0f03060609050105030a030207030b07051b0114060a0602070b07031101290f1c081207050408070e0103020612061504090f060501090623040509010306021c02041a070f 77
    0x110b8503621680244a0403405d030091601405d0290000d00c1251142c0d01d009645881920015000040c00e2010581e00c078410f40c1181d5040b011120f401c0c200c0c00781e03d000c80e170003051000c00301c000d115101d1001c1030303480c50401c00b9002111025401400094100b030310051442c0e220000407414007051050000640c0b1007070145070f000011604aa607600d040c20f04215410014029400b4812404034511020a03034503076400ca9071622421070604014586890540401e2040c02c07082e0071001280340c01c01402580c403c0041082d20303604016102c21036601d55501c1c148000a0000a61000003403001c00b1b411862001e403194400c1c001010214540c0780c6042020050b48030350800c0e0802611020801c030000c2080c06020000c00c028a490310003146480e20003490744401c004041408450860244403698000c2c090b1006448028900e1101396900d00d0101e0095000390380105520740d50700b10824500e189442903808a520010391000d80342d2440038003040c3e41c4c1c0708501c2150440780080c4ea00c1c0100300c0240307144 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 826488848 1250 826487598 826487603
    0x90d1419261207020123060103270807050a06090b16050a0906050d0b0604180b060a210902031f0f1a0d0606030507060503011e06050906181302180301020c0d0e0a0f03 73
    0x5011b5030070b0110005098940170800d02408c078810805c15482c0c0034100c0341c0001415081580c1a8a991552820380c2c288a41190090409030a101e5101e0a0061000b5524000e406024042d8040c0b50601402c1d9401d0058600c11800304801880800041d402000104035250740c03110002550004070001070b009401ca070300200b07052070003210b0f00005138030030348a60b4496180c2110307060b0621404c040000e000740c40c805102030b220307118615120250052703034002050f083e82c0142640c800c043d0032840264440070803807408101c6401c04112581c060094400c0e0340000354070501c4408400a00030034000081c0855004850940d61040c000003c0340c4140450005450659034096495240040411036506801103403042e610400404004082c1c002044846aaa040e50403c0d250007c1d07804031280c12a00306401a04101c682c000076004100540c001d041034418004070780c0c0c0103842e99091500b00e00802074540a036910075000041c0140c0074010000314580020854214191120356090580b41c1a034000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 826490098 1250 826488848 826488911
    0xb010b040501121406010c031709061b0a020607110f03040b040f061b0f11120f0f07031a04111c020307060311090d14192612070201 58
    0x240706035a4040d0b480510710001c0e08040c0541c050f110b00094503602c000c1e0405060008907003640040501941c10120300d60780d0128075140b107151607007032144ca03603004513144191407070001907203000e40c40140181c03450140c01c2e9000300219a0740b410150b400d02020510450284504041170358101e00400040c00038082030403c4949980c6041300703495035400144c10150502c640308030007007100450508007000e100d411560b07210b40d030392090406a400d52944c1c0c00154000310644c041b0f12207601b00085581103c00200c1c12110f41c26200519562521140d0000400c0c0f0300340c101003500030f040340301c80d00394015000c0c1c0d0031105c2c0c041800c030000309040c164000c407000d651040144034041d4a41480103a006103c41d08050082040942c1a01040d02c65040260f11a4040841100620000c0c039245041d045240c411119640c07601001203401c1d450011049500800003440c40410b01c112001a0808144100b007890600702047c088920000f170041000301190341e603c0c59403540c0800754190b5102c2281c0040b4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 826491348 1250 826490098 826490107
    0x903031d2e0f1428020d110703320a050912250f0b091e03030f0409060504140f04140a080307021009110d020307090908130602060403080f130b010b 65
    0x10340021000004200d0020400e0060f84d1800b02540915050100c69941d140140da0700016178158006103440515114110808210b000030150015072450030001c2c8080e1015a690305100900e80c51180c80304040b84003803040c031010000138041c1019203180c8800070f02c4c40c00c0d9490102141071401030701218080c40019028503040c2031080121088024120007559061480e04181020700705c1d1103031002e0540240110050000c4403110f00e100901e07040340080a41360303194800c001c100140d0700b250003082c0300246000400503442c0b605110741c2c5031804101d40400002c1e520700c0c020001c0100c0040050340d000c00d1a201e1812151014032940c0081c80c8100394458a905280500070300e80780000545e140403501d07200101004c03c4d40d60b02d1182c0508801c90381d001304540c1601c042800c00100c0d0344070021a5080c9119807003080401805410701c00c400000843c1040da445d2412a69008190b038040c011070420404140c110403000c8070554481940c2c0f0394418180348554a03013082c0b41d426441400500000f14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 826492598 1250 826491348 826491371
    0x109030f0203030f0103080a0216080717010209151b0a0b070f030b1503100f0311030f070320060c0d0e0108060307050a0e10080706030903031d2e0f 65
    0x990000000c403a2005608502d02070200102c00b00040c000036203158404204299590302c200480d07a00d2842150304d0080855884401036a280102d0081a0340d901d442150b08245d0a07051003540e4259030010030405001511182502c195031014014501151490400c010b05d600f0400c92200440d209004400a502d40076200910f08207180c0603441c100750610002620343d6070780060b0001c00c2042c007212181e82e41c44280c406080c0390019440070b295a08126000024001c0c10750817455050000d5003902c6d0a0003a01000540341c45090000801d036241e096450034900000b824007030308004c2c02422042c03812040c1c8510301e15201c2e040502e2000100309020910440d640701c600b80750819010f8004100c0e003410840044c4260940e401151320301e102c800001495010700414010081034840e042d0b483c0da07529644010083e140020054001c2400c03c01021507102c1c00d04001000d80c0110009000748110058101c042e45510300c001c41074a031551901440d11101d144a01e4803041107080700080d0901a01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 826493848 1250 826492598 826492607
    0x15030b120c0906151c0b120c040c050408030406050a17010e091b060706020903120f030a0606020303070f0c030309140a140102070c0e090f0d120e16051c0b09010903 72
    0x90209002e030350351144c4071069104010503a000141002c0050169200d22044040104081401c0940c002d003c5030601401e084003085507600884292800e12905500c0ca009071903e01c201d100b810a02d600410040040a1289000d0400b00d020361500d000014442c0c0c4124244c204280c1114035491a65420b004460004020666164503515100c1400d42c441c400040d0041c015030501400780c0f0780000f0120001c1c1d41c00e1108050194483c04031a480d030501107040391a40e0011a90030303404902d4a20b0104110b03000105484c40b80e401c40d0f4030704001d910580300403035034140d248800310103150712035081e0300000d003400500207101c0e50800001e000030319840c00c0c100b1030220f0a2800040b2a441006024041341e00320071508252041c21440100320f0322105000e5180000d01541081580200c4404042481e805282600507907070000c0d061020070030920400d910784110b0041d44012080d402c0041000d03080c0f902d50240300703013544400440e44000c20788401352000401ca452580c82d9641d041460b0806802 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 826495098 1250 826493848 826493851
    0xf020d0209120604080d0908090907030516030608060604091b240c020f06030702070806040803070806090613110f1206100c15111b07060908031315030b120c09 70
    0x8a900400b402d013042d4440c84460310981d0000310149484104010920401d101114005a00075100d0051841c3c40c04008008141c284c41c0302c0e0440500c40c000040d5a40309008010644802e94040c040b5a241da504110043c42e0f20344003183c24014800d0241d81ca1491342e40e042004040300a1140ba41c18203440c24401c480c10300400b102c092282c052513003400350f01c0c0c012440300140d0b000d6480a41e82e440e0940240d2a00c2003030380c06010244640001c0000300320f01000a1402054207442d04d00850300c401017007002d20300b412941690400d8a1030304070380301c1002580296a4a8071403020452400e4250860991642d01107100c000303840e1303180001d11059003002011241080824a085007609255641d8419450340d00c107101c00126171183c50910752161321030111030f910000c80040e90b494815101c40981c1380c010601c282000b28a480c00005019040401290054010709400048107414111294040c0810070791003020140d41d8001100b0310303110f4181346000d00d000c41008151140784602004000d071300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 826496348 1250 826495098 826495129
    0xc091e05090706180e1602011404150605010e03030304121103040305060f0703090305040e060102030d1a1201020307021905030d020703090e150109060806010e0a1d0a0c0c14010f020d0209 82
    0x4901c541004521700924107a80c0080803a4401c050340081c00c44103e0140c21400b2031948451045400c1c0002c115201c036542a94144c800420301c80d503955400151050ba0310b000c11150190002c00000300018001c1b0345244001c01c036400d000240b2416501070919680158000321040d80c4100f00b88114110006101917001045181c10703c0508900d0354005c1c4a401507100300c3c2210040c0001003141a8000c2c41540da0b4070030b103038604103c4003268072005400a020210894010040c5405848440806000f1684a0a07050f00204481904c500c2000080c451100c030035282070005012807003140440c0c1c001000854041e690310040b040c1007104141c914030001d032101d02c1c50082c64241c040356036080340408088582d03e04005d00303079030341d004016910903586210095005040c0307031000c1012201c500f01000701d44014004210240d075000e40001c200c51840c05030f1004a10f41e179041d0400039500c5402d0796406e0b600c4400200b40c08034155020303020382c1c001c4503180100c1600031401510300c1c140b4005075081c450 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 826497598 1250 826496348 826496387
    0xe0105090705062208120a0305160e0d02210124080d050309030910081923130c0e041401021207031109060c10060b070c091e05090706 59
    0x740380c0800600307140b103070507040c0284100502d408440c50060039541c400401401d021b803910300b40707000010402c65000010400110b4541170118041081d810031041c42d40c1c415485882c0361200807010424409a6514200d9024000c1d4100c1c042041c000549502150302440000c1001d40c041d81c00750100400740f401c80d800c03d0683c00400c0142500c006110f400c00b030300504200303590341c945e400d001c3c2c00c610800c0003003074019414403440d000030343e801386406109060300107100340c411142c4d450040507a20144583c40112029028a0341070400640790590230001c190342084031002c0599864a02c591079901001c0c043c4440c0040100340000c0000422040781e00c440218944540ea0100010291001c0d1003403007011b0355601e280c1c0c1c00e0030a080460f403440d40010306440d100c0c1fa10059280c0d85400c2c61000c08030300e80c2000310000c1d03051104416180865402642c908065003071282e064024010015000c0c08004502d545481e0030915102e404c1c00380140c1d034050302012f800c00b43e01603d180710041a10740b141 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 826498848 1250 826497598 826497613
    0x7180b1804020a080a0b150a050d0f0b10081203100f03060c0f030b01120b03031308011e0b0105030712110d02070b060906030a11030a083c0f0d0e0d02010e010509 71
    0xc6c0034203c00342d4000400c9030034149403000040410301c40b1085802c010f400000d54120002170041705081d040f4191f110754003079042c90352060803034001c004141c4035028850380102c44900d603800c42d14010f55408418002281c10322a91042d00b09001c18181d0f00c1070320940c3d035a10581852179840b4208400c0e25159003014054149842d0000f0b0002602c4010008010351740d1040e44450b0f9000d10482d244004016000c07200e4a4a41032420b00130139a14603991451a9290303660108a1914002c401c00e8590585480d03007540e0b00c0440c103403040d44200320200100d9a403060480c8074540301e480504181080741c84016160520352500c407095460203041244540e00510406c03c2c141d400003021103005c1c1d4800d000c04401c14222011074940100d440f402004104040750340048000e65440d0080c01d89000705d904d03a01600103a0528201e20790750310462210039410025071480004600c0141841e124201b40040c00400c40c00d01107003800880100d402c0107035100c01c82d031800d15100340180380c0c104e080d400140034007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 826500098 1250 826498848 826498853
    0x1181a07050409090f061b09050d0b0f09010f1104140111120a18151b0309060309030c0203120a0e03030903030405010c02011214011a0a0207180b1804020a080a 70
    0xe00641c0300d410b011948480603081001002031703100c04c0c0198051030a101c8403402e1006942820112005900042c803840400a428900138041492150700301c80902c0c01a110301c1c2101d5802070008081c54903640d01d5007901146210580318040c50105d242e02c965444900b0071071200703910a0858030260400c0300318032085030f0600700898081c00c524841c1141903a140510342080d074521030320300907031002c001c1849400106200075800010000480e9076541181d0b21002d0409007564001050140010306881c01c01d0203858020350298900303d002e4100315288602941c00a1300d04042c40c0c0c1d003a00440008100d40d44c0d12a005018908100e804501942c2003c0070b40000c2030750f0740a144078040c1040b400e07695a009690082c0d10700000c49181d41024803600100813a000c0c040d850a1140c503909110a00302100b0960004094800090981d8090700445180500402084042c942c5200819a03529440001a83c0d9403805000d02d0107a0b0b04034586070720f418010403141d00815448000c40d900264a40c000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 826501348 1250 826500098 826500107
    0x302130e070b0a1d0405160305060307050d060501090509030315012102030403020c0319031205181006080c0405041e0c3b45030706060602011506050c0c0301181a07 72
    0x7489416441c0026080d52b41100281ca44080c030352085420440c8810300d0810321001d0b42216040e20882c000920058490310750345030390703407104071280422003a180340c5800032584613503683e030510000092200024074074107800d40b040b40d0080d9070840160340b010b16000d01e10305051084040a24540b40c25407445503032624040c10b0001d40d2110004100d554000003042c0702500522121003116510858400300c00b055101c1c0001c14143c007450f405482039085e41c5c0c5075458507000d42442180d1045107440c0039403d20702c90558060100004a64642c04460003051055003403100c0c60b02428660a10142440d829055098841c00c0351407080000b02d541040010701c40c1000c99078010000700e80c285908100d00c19003910600c000803070204030301100c0c10702002129a0000058080d941c01000100300d0320b5911038090f0300300c880c4070b195180c4c007107510041008901c0c0100040c0c200b42000300c05440350305d402e0300300280c00c41c0e1441070085001c1703501c03402450500035203101e440b000da00000b00380c800c0e50501500103030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 826502598 1250 826501348 826501381
    0x51f150f140d060303170c03010f0302040c020a0204020c07140a081203090f010f060603290f03011d07060f020d05030604020c0a0b010306051e010302130e070b0a1d0405 74
    0x4144111505414881c040810450b00156140d8000308215501c83c41c0c010140006140711103c110340b02c2011856101c1d00000300c030704031102c1201c4100317035910395801d00001d480d500b018038056015040403c405a06e4a00007842c0c620f925102415005040c800650b6161004012042c050400031406221030400020341d5091079a5601c0030039186e68825034018500312802072040380f954200303220900c000d1101d400510542d20191410310840207082e041028040e428020741e4a48003040c60b000400d03082160754022400409800420030316802009140741c103503c2c48920b17069502000c020130489502c0400090341c0c6419101a111501051600030500e01000d02400e01c9241d0008484400400130041080800d500c0048140ca07903959060180003004101c51501c01000700c000e00c00c0040750181078582c1a254010000344000c500100380c000141914807a04038035115058010600b4001c0c4c9010f055050354503654414071000b05280c40180322001c11074940a80e0521051005402800f0740f0305 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 826503848 1250 826502598 826502627
    0x201110702041d0313170f0a02040f060506070c0302031204080703110d14100b03010b090411030111071118060f090a1509020403061a060d0504080d051f15 68
    0x12810994001114058029090f0440b502c0e2000051800a0000a40c2d0150031100d580d107000740c0802c0b50010301d0b92078403142200d03c405a08440c008200500c4c00b036000d044860000c0e01c00090003500c0e0000315400c0d500050080e645d00000910410451a0400c01004244505898141030524040f01c140e6644001d010050a50f00c043c02d000103283c070744090140d12a0340104140e81a881201d0807140c556001c0144884c000781004403a0800b4181400f59689606c4064040c040c0e44ea41d50315500702802141c000107600d035403103440c1881d044414002400c2042d001d007882400010f582070402000841445000c044018420100700e00c540e030f100e41c40712802c80700361007522903940c40411000007000c1000410140118062010420348540d074042e0080c3d83c07140c8010045030402c009170048ca44580a05185d001d082003081c1a50210a80c10194100e440307a017440f4204514803004e202a42c50131281e00740004244100d01e030702c45030f00c1110f16004000d15001c048070b548600c13100804803103061000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 826505098 1250 826503848 826503851
    0x1306030506070e06090d110a092003100902040830030c0d060807080f060c030c091314041119050105090118050d050706020601060806131e050c0910020111070204 71
    0x240651910741e00200e52040d00010710010f40540310b49030147c08442e120740d00740c1c041e907800100495015928890710700d492880d49030711041c1030020f2241008651005003600f803409955030b800651385140b4009003010b808144082c049400d1084d1041101141c40d00030402043c1d00140082c1d2041020021a50440081c003110344d0350390f18807100400680410b6110311410320a40310009080500800e01d000403081d0724041d2042500e0302c41400d156808207031140400c2c08410040e110151070043c02c86e03800d103c840389001c180c40703074540c102203c0c1c81c00440b8250384040010350728250070301d800c110040e40c41e8103120900b0405030620000070000c0c0948030b0034074140020400b0700b40c4212458030b100700c0101402080110440c60524080e0748500c1c45120751070242c89043d001080c1c0303501a000b0144035a80c050f04600c400d03040281e00d5000303000f07842400014444070281d5181450072a00a1510030704141d409156584000d00c14400254070300c2c82d2079401c69250900c0141c04c1c40101d8100c480b00c6804580 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 826506348 1250 826505098 826505117
    0xf030b04020117161115182a0a0806040c1403030d0f0c090503190209040c0810090201080c041a0c03190e09060d02090403230d02030105130603050607 66
    0x698403503c040c801150224100b604200c0c4022844000d070580e41202d80d43c04040300c050f03d000a43d5550b41111601d41c6540d6100001c0b16070b01c2e0120109401e0000404030f0b41d10009031805044000c05496140740e107051040032803800d60500c07240510040400354000e0659140a031a92101030455024450552120000540f400d0360204195200402004801c20065070180f90300c0008000c00464000803540342c2500217183e1901080681c0e41004842224415403100d608200311080001d10890385034000c46401700308400100f22815104402640c0000c1d04055400092b101410042101c2e08440c0d00300028480e0041d10000307075410110f4582c05548881c266902c66017140108668400e0340c0e00d807004004050f90b4814071550b83e560007660308032825192181170103108600d03610042d4100d09030380007142c0000c0c8901c046400460022940c0c00480c103d1001400c0168058019041165004001400907140610701071402d400c0c2d0000804c10302d441c50381c4040e1908070081c0701e1800c9c8101280d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 826507598 1250 826506348 826506353
    0xc033708090301020d05060901090204030b0a02070f0b01080a030201050108010c0f14040e13060c0503060904020f01111c110c1f020a0206030f07081e0a0903110706030e10060f030b04 80
    0x9041e1008041c00500a41d12001d404480c1c2e4003e1031704039000f42c825099a400003800301c1c1c80b8800c41e0103507600886030100e5603443700307203000107075108400c102d03a603118041c10440400c280030400760203888820060802c409190070300a00b5104107130804206645000d100ba0780340c5420203210b00041d1111f0400f004c80c0c0c118648030200500865001c1008038107032400300706802c0340701c4d41d01d148054400c0384c0400170315a020004a6030350000300c4103550000703e1440403c000d8074040500389100349052601c6200c2c003416407420390500e408960003000c00c102c4031014481c050740003400d00c0b041c90003100c020140c044003600012840110181c44240703c203840c0c1c61082c0102e10034029641400d0300945000c0da281441d40d0010802e034011190003001954003070114a682518000d0801000164a502038464075051200e200501c11000f04078103118151240c0440443c0038000d19000b495607490028013001d10f20040c070305180c4505000c7d502645040002e100c0c00d16803035045804d490704090607118558452 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 826508848 1250 826507598 826507613
    0x9040518161410121505120a0804090e010b0307030302010e010614030a03050f040e01081f0c0801050f0a170607030b09010f031101050d090f0201020c0f1302180a03050c0337 76
    0x44c3c03d1030b149007480c0071000350650846804044400903501c0c1356005950000b0151181180ea40051882c00104070030014070000b5044a4541c5420b00000581c48403400002854041d20f9801140540d444200d440106103003031007071030018603c4a80c40204011901c0000351076020600f80241400000b05050704030501c40401d45001d4a40c1c481d010700076507100d442c05036550170741610082ca20f5201c02140032003046d1a01800035141c1030f50b00c4651059003400b08001d03145032500059904070081820011314442030f0403100074881d016501074901800d110100500752080464000e0007641c3c01801008080c040c0310141c0c04880d001142c54110059038001200c030b9205002c1c00340e050500b808840810301074507010380e40e07916200341c08071605d11400304113001e41e14401083c000d0784241c0c18070303480e00315507401c1d001080d080c0998406504001e010b000003e8072010300d03401c10740c0d041e07201211241ca24101048000c207001880c08031001c078140e2440c90300c1c0b01e0590320091301494401d020300c88001c01100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 826510098 1250 826508848 826508867
    0x9030813050312041b0902043816060b091b03090a0804080123060a0614070204020c0303160201090b0a0b1908030921030304031409040518161410 64
    0x688941010358249420004204211910003007628280341c00300240d640b0700c0b4801c0b20211200146c04041c0c080001c040038a103c80b27404d4210149401080d424120054040c00a007241c007003111280c02243d01c2d90510344100d03944015200c0c014039151091004011b80300301490480009080709554a50b00e0811b001d04082400310014804180480c01040740034064204103400c9605030300d0880c1000406074000100e0780182c4510f60800d949540c244980740c40307204810103d0800303161252903c0c00c01d6002c01c4c02c99008000701d140b980c1020080c841c1e502a07004020b150003030144000c0c00100704030f8550103000d0b80090003c840082e0b4401800d030b00d5445a00c1200f003042804854910420f80d14000d01e610703540700e40b0042d48250b9401c000c40b0103001c000c2c0c003000a4080c13180001d509650750741d5801d803002e009540e400b030810003081c0f00f681d845a40702d018040c0325040205201040540702e000710391403e2003200c021145440c2d8004140510385480041e0800c1c072030100d03441241d10f07911000c156000c10380b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 826511348 1250 826510098 826510117
    0x4050c10050307020c1008060105130509100302240316031d0f120408070e100305030d06180e06061c0b04120f020d050307050304020402040b0a08010f09090308130503 73
    0x2202080c0c1640a6000809184900d08503002c0d648500066001c21140140d92a21b0102003044200400c03480e501c02c00c013801c43d00d20880014117106490b0710024002c074004450000c2c024080d80010300c00c50a02c03040c0d0203902c0c01d0003840341101d03184d49800356046001c01011f070a400708109559941d0b0074801e400a4040d4410044d603105401a42c0b04100e480f0352038010400740d207200303852440c6501100f980c00c0307504450701c81c2d000d0020542040c1901d21000009400d10701c884408400100100c0c0040c40240124141a0340000b403151511044030b00d4090081e00184405180c43d81d03510041202007520307540050103c4070001000c101d01c50401388169000400350a48a1a204200c2000344844001d1501e041c2901e4010341c08100b014100c0c0d480e20000b04000000700180080b80000740580041c42c1c129200a00c0541007603101c5184c5c1c50280c000c00c030300c3c100052a000c010882c4102034941c0b00b0140003c0d0b2018002410705880150184001a0510240e00200c1c0310300c006101d010710642d40c2c40507 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 826512598 1250 826511348 826511359
    0x61005010e040212100801063516080604030e040b031009051f0605040f1803030902010504120b1f06050f28050a030b040504020d0b04031205070909140103170304050c 73
    0x900b01d0349190144007502500c806581303001d60100d04940600700c2881c899501c502702c40003c1c089450f8000c20310285a440e2140e0303105280610b0312070140030000001415605005080500d0182002811601131049160080c2d1400003075030f031503840204100011a1024501050085c501d1400d03a14186600082e00c80c40c042d0074000a503961301c00d810080807203a0031501400850340b4012007500b00c1d204240700c80d032140c81ca0611a00004c1c0a41c010068003030050401600301170f610072000110a2901404460015440301040000c8001e8205107420042c8642105c0070942401000382080c8202c010322030800384003040c040c0c8035014020700f030006182d29100720038100f00040c01c09002604051849008213081110710b1083c0c2c281441854822074000b84250480c0c411907c2c1c009030000040c02c1a410840d4001c0d010742c14003124003510340260510760301d14668a1424502c0411540c20051144800c1c14407001000403400300f4070039003103004000e000f440e980c0d02c0d146015880c3c01171031541684c028 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 826513848 1250 826512598 826512601
    0x1406090a020f060306240f0313120207051e03010b0402040801050103030801061b030509041401080f0c030a082208010905100501270c1101050f0711061005010e040212 73
    0x12010800c411240e10039203002080c00407090411025020444040340c1042c1c52994411010ba800080e4501821294004a1808105007625030459004949200785085030140302d40030020f015a0f80440582c5a10141180b981401c0005410610041c1d5445000c000c4440f80302e40c956003135000f092020b1005104541d00c50791050200e028123000d100c29000302d080c6100004078140925500006104800038040f01490b0340d603405e65403500f0120190307801582e20302d840c03800d00c54420f59081c0a0642d0b08014070200300300c41c0b82940b0704407040c598039000350000844880050310110550b030080703a501082150600a8101e074400c0400b00c0d07440200e0703a40c05c142c40e52081c0480840c51070a200c0464070180030036a20b803081a241a9a00ca42207c0c554503140d01800c81c1202c554041e07114148a890b2890b202403084001900b582c205540c0040b0480485003401101d0360480b002a6240d1030740d0340a440a4a8010442e01c4180c04910640d0305103c0082014900340e038850703044425a400400003e25507 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 826515098 1250 826513848 826513861
    0x2d0307050601080c090c1e091e090a11160f081210230d03111f1a010914041d030c0d090b0a120609060b0c0c0405060112091406 56
    0x7107840a109400c50381c080c0101c14442c2c2e0904e00d0b00c03544134000e48900340345490704011050301804400d130346100c0281800d218001c50380d82da0040c2c4000c4403402c1c8400f003035003418480030802002ca010300f89245580c90038030141900d5501c01c0c140c2e6000381210003403040140040c105034401200c11300009001c01000500c135a00c0100b102c408900030103450b80000c03107880c0c807200d1490603484a19107071400c4c602c529041c0c000030301d050341403034540703038800d18000d2149040344804034030301050b03c4150312003101e400500c1034025015100d00001c185a8900186079075680c813002034618161402050003401c2c010844c40c290f51150340103001c04000035581d410041c044030b41004d40b60303002a06400071034001c00106444103482241c8040941d1607450700e031440c03e12500c40541701c150f2011490518581c56140010301000c05218540003800042d0703c1554901e0086409814588030214051055103440c00707100c1c1c40c0e42c0c0461040c4055003603260014001840341046101d5400c4603807110031502c50030313040110 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 826516348 1250 826515098 826515103
    0xc0b012c091c09060230031009150302030c0f0918030f03011202030c010201050c03130302010e070e2710020a030b030d050c07060206061f110712140a02032d030705 72
    0x11102c2545c240c400b41c400c1104092006400c0c008441c1d050368600e003800c1044044200195001303103103001814407481d6582c2802c0d0549204103404454100a4001041941414048500f008000704c90500749244d03640002080c40314050300301068004a9028409904020412181ca100401c1003898513581c2d02d00c6911500104100300324060300130398150703e056500501440340240d07031f1800510300707542d01c0811b02c1e40c01d00718200c1300f5021992104010074181c402407040e1405491145a21210ba240c501006800190302c41070341215030388041101452281d021aa8034000c4100c0c900141c0c0d24500044210090035402020319410b02812780c4d9a0b600030f82000092410422080036110300c00d43e9007206a80760103007243c0d49904100a04542c0c8038480c9000040c1c6030581650510810f207a01014009240c418107401400120821201c4081448550445403d00680550003490940001e0b0301207503e07000034040e41d440f10100148408051881078400b5081ca0701e1410032284c03945890300b002030303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 826517598 1250 826516348 826516367
    0x18091e06020904110c0715020309130c110a08030604091a070306090b0a030f1104021b03031f031a090309030d390b041509030c0b012c091c 61
    0x500c240c0c070b00300c0826130700c02100b0141c581c54003106016055246c90055501c0c050b41444146800b140002c2144100c1940c9003080c4100c00c5050309000a13000d00a20f0380601412844240301c00c5960040c2103080c00a2058802c899010030240c070080781564492070300000c4000c0b004c00c940c0ca4000310908104009038598411000c441c2040c43c144040442d4100b4002451245e0101900210380c0081c40c0d400b2445020106c1410a0081c00c018a0000710340180c8004d044040b00c410607503000001030150021100c4071849403c4c0100400720401c0d4910340d11110b0044030451065080c2040c00002110804103009072100e180d40601a03580703200d00010020301c1038003c4981151003240d1000b00c00d10082144600092900040050540d030140640702d0084103803000748200c1d10000d00003e089240300d80c1d806045034031340c0300b030b190001c01c40c00c80e01c1c0059100205800c04041c02405102d18143e0220030301d840002c01e018141e50765119102d4401c00c1d8203010041300b0b002c0c002d0242c000c4c9203100641c03100780e22 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 826518848 1250 826517598 826517617
    0x4080a1d1f0206070504050a03080711060c061b040f060c03030f180b010807030201080402091503070f0e0f07050f09030106080717070e161d100302040906050301020418091e0602 78
    0x100c0040c2c1e07800101761850f02950058582007c4e4030402480016031560003011140e006915101c60100c0790310020b90607501044240005d80c02c0300b824403191000b00c01b1401103c90303140001034106800c000300900304a41c40d21800c810080559007010030315000780e01000c69280101002d100b02d0b40c2c10210f070f10010701065422140c04660000000d9030300700101e00c881c283d0741e050792181c0482d00c8540030040c26000150a00d500c1103820200d0b035526503020495003005044802071b003d00203160842000322070710010420b041010009040082c02680001141ea040d81140113054075214020007003401808980c000c02154440c4000128040e175140005418441a41d02100c1721251104500349545e00c083e01c4090b148101d10348035000f82e0b4082c401144421075000100c0c4451071941c7c0c0003c902c03d00440396170010940c000b4080c81415160300480d4040e10007500294940340c41d16410501020014403065500366a480d9503208000a103401e41d01145120002c8180b100c2050508900030b60140b100ca = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 826520098 1250 826518848 826518853
    0x270c0c02030a060c020d0918050601051209100c020d0c240608010203010807050d0b0604180609062f0f0a020c03100609050f0c0304020d111005041d04080a1d1f02 71
    0x310461287d038140d0241d540d86410402c0c8581c206182c90042e200c042c10b0a414001e052110589004e5100e200c2440380c4c14020042103151541072001003101c208644d0fa104540041100f5185503401c0700c00707812060341c0502a40c0c1c41d0303510b01160350100b4030443d0007100c0460401500140140c1e05402440c1610309420a4442480c1d5031810041640400d00c4001c000101400000d012490242e0051100c0c01001d034201c5c0404885544040499010a000b242d00c1c03966007410a01d524024091690348490700d09601e1820501c1030071800340b40c0074071614001f060b0030000311a00824428804d0940030705004c1e0455400d0b0000c0115800034051601698425a1901d000501202c0311003c0f00c901a5505502c80e07031075511a0380a10005c130282d881d00303070f0704148900d21505e80c035183c0b040c9250802c101941d400f0340781d506019602d440720300525100e5032060388003018170020840790b004030360f983c01030303402d010200e0842225040b040a0010000740d60000084800b001c09251941d060300c519000744e8207 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 826521348 1250 826520098 826520113
    0x50108090d0e0111030a091508041e0503040b070302010f0b060a051c1410032607030516082a010e120d0e070303081f14010302070602161b270c0c02030a060c02 70
    0xc22222790788201c50140c240780816102000e02100c01e40201c0c047e038080d90a0300e182c15101c0c4010f0f40b050748070100840050390b55106500031201ca03403080c000a40d0040b18080e18050907180001c00c14003a42e64a420541e141c0c2605030000883c50748a08016514030010b4295450003401654107080c031440151032100d5110828141d401400e08203061140c400d071030070f07401d044164808990a030030090001007544288040c1c8130114038041c02602c4902e4081140c110700d500307450803441590100c1c052040e0a0380c1000e040000c2840b02058a245440c01100c851342c6a0040040c83c50117489004c2405540d070140710004014554880e61152165a042d0013801c1005515002d00340303980040e10406480804500e070100700366110383c005004642c05082c01506102e905280c0304400c2e10b550b5030450300d0400c202942501162a08150705c01051000e81d801451811104131200c01541e01e000280295500c00c01141d001e40180100e92442c3e4000c3c0407a0034042051414800500380c07100c580c0e026110f002d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 826522598 1250 826521348 826521389
    0x60b10020d0813150f0b01090b0301030b01050409020d08040905060a050108040b01051909020c0a03080726071209120806030f100e030705150f01050108090d0e0111030a09 75
    0x41c41000607100765100409961041c46256004528150071104030910700209041684503004200680072289170004038032180c1c00001d000940d070740d40700c04203400d1305000400100d1030308208241120401e4802041c01d07549803000a030414143e010090001d01e001c100856030590551001d84518000e44004800b1501c07403005461a81003110028412a0200010f00650070900940700d266a148100c17602141d484540800598010f00702c4650940c0c0300c2e2400b4070070305511600d281c0e0803141c1c80c10845035080c42000c004500051080f07800d02c43d07210000103e01002e10555004003241080c0d141001201d002d482c00d8034410b42c0b01b543c070300c0010703445201141403441c020038800d800c0c0f01100020701070381003100c14440c050084501d4030382c0035000512030304002c200c0074442200c03a104441a00d0946103000054041c3c840340680040f0b040004000420036400c00006140003992424204500b1602281c3d00480d2200444880e4a16131300000c5030006140342c014040e1029269941e0804610709000c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 826523848 1250 826522598 826522603
    0x3010302012a1103010f24060801230307030b0c07020f03011e27030804060608030a0509010e03120c15010911040608181e1e06012102040603060b1002 66
    0x2100440500002e0920b540041c40007180380b003141002500203c2d1004090b290760007180d0041789800303203001802d40b600f104003e206107a800908094100401254100030f10142410f00402c0556001d120300b0804200030340e000c01ca51401140d0210105090345070005401c002d81e00091003c9005890f0340000f4003007890180648010302c1e80c0ca83d00100d5812a4a42c03640c081d22003181070780f0f4a101894004210400120403907001207010b501d070342c48181010700c2c2020441e14030750300404480c1c0051080380c04841e808803c42d80c0c50f00e824603210070040000000603052207000d00c903a65811000103044040240b002c14072484598070b002081070b0583c1c1c0d0b1f2a0f40d5003959540289070f45861400c0205011140c040e813103158005100c00b00d40c01582100821032407900011040007103410150f181210804e4800b004050f140c1e1003c00000d00808101100a50f070314101070140c072410001280c00f80f11000c4240d20380c070501c20380041c0103021044c0d480c00c0c6600245103180d81c181c06100181054a400d6000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 826525098 1250 826523848 826523897
    0xd0f06030302100e062805070324030c0e2e0503010b0414010306020f19030603060c0f1709010216151401080307020603150d0501050609010f03170d0207080f0301030201 74
    0x4c0a08401d649807020110100d24155107410501b0204d43c0007040100710b44901c512441280e00d000a0350030182c4501c9580e0100450488200300000e502480025880c1045004954007460649007946840302945c10300880c172041c80030101d03d0301103100c0b9200c1469401104441d0154020410b10140900b0710043e144c0030040040c2244030140100001070f02d40e4002c1c840f075549030301141d04119002d604a58035084848407400040d80b6494140300b801a684141800082141882c03034082344007800103450006460042e15501c0124000942c4001c000e40440740e05007543d20001083d00e02d0b9103081c4100d406032007240078330540340511090303001d250310000a05840b00d49005500303140d229402c0040540c001000c1c4c0035040c48000d01e100c0562240001510302c0e510540000c0340c035180c00024410041c40c164031034115154040070030030116041c01e51180e45241001400307940d413060324004101074401c03600e0081c0484000602140c03070141c4c1d50043c606880c404d907100303501c01039149260384c1a40b11 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 826526348 1250 826525098 826525121
    0x20906030c0a09030209010303030b090a060806060120030c0f16120609170d05062409191d0106121e0207110306090a02040f18170d0f0603030210 64
    0x2820000300e0055400d5401030080c0440a207000101d00d502c960100f08840001c0e40300302d02003902c03044040d500b031401c0d010b91548406542020803000c0d113091b00d602c0e940e4030040c00e10f50601c00810007602c8005241c0809858941401c0104e035030314003007555066916a20b1040c00c200a02401c8803810100016506110444030300461507c0f1081c056200c00d0001c00341800200c503110380695a481281d4052009802070303006807000020140741c1303203084c0f1072007100c8221402c03982c0d0600e0303080c2d00c614141d4070b050760000d0700300340e600c0d030030b08081c08618555664080e0410f280300c3c04680c03000c81003e0309843c040c6040e68403a503101c100070020402e03c4004d5810480741c540350340c103400e258030300070080300d41c060040c00e409a4103902104146401081c00e000c026a2108405d400c4814100254105801440100d4110b84001c109850300701c4100075450b48080c000403d40321280b2080d10340390100d8000c0d260462100c1904101030003007000014028299840100d0150246424550207a462442948445403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 826527598 1250 826526348 826526359
    0x501050a030f031416381f0b07261905090f0a030b15120a080f1b06071103070506070f2303042102120a0903020301090b190209 56
    0x12035541503510349040c240c3d4000100d01880b171400b000d0146400348010303a01442100003d4000c0c0d5076500c0c042c06010b085100e0101408040300203400c240c00407103901000301001c5070394031210b401aa000142603a8862026000c0c042030311000d01000034085110110070a8240006030480001c06801c1d001308414a64842d070542200b0414034001e800510104100500e8481001c01510005031005840d40041c0c0d0b148420b101000221086005034039000102158140f400510340144551f88024540000302096008200c1d01030211509043d90001d40c42c030411100404c100840595a0302000c40b251400036007002000d040501d030100450310902d4202014020596820000791002d1074034403100c43c2080504a8007441316198103000d0501504c24811540d40c03824a81002e240d44000002c40c03491044802c482d1070582e503000070f0084502d1060303451090f1102c0e0300c0181a256107103642c2c800394065080294070b108010700c06070418801d6400300c034800c03606075140c0151800c030300030407001c113070440b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 826528848 1250 826527598 826527623
    0x3110a05011b060f0e1923030904110714063301030b030705030a060e0708010209130b011b0f120807020721080a05210c04050f0a0b0c030d0501050a03 66
    0x16299820441051484180219400c5c4c111102075103042d01c20114940da80c00480d2a02c01000040e6040075071100709025901070085116a503162603104172100140705941d105004106000d22406603a50f054000036480e412070250000c1a1700c80c042114076080c820044010204449401c14401904128016012544400d03820041d0020028080e44a5140c4078a500c00181a5410003010b00a54071651010542000c0100e14616281e895046044280d00521814140361940002250072068000010a0410803540140c1b002410785841c2c1d40d07070080644c2c100f828000c20b2140b2084092041050700c5040072011300403141c82c030094448100507000a80c04201c05040d5222103200ea9403a2000c1042c50340003692588040c1d400f80d41081d000c2840800d40462012050310005900310303020801c4505440e0a43e0070212a1043e030180714404c0c807041070001d1542c1c542c40400302c054510f60b90b0056a0710316802d21300d941c80d0401c1d40c0c0b409000782408004250350070302c20b0707010003229486070503580320 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 826530098 1250 826528848 826528853
    0x609040c090b0f0301021c14040f030f03020d06090b2107050607062a02071d010b07030c0c0603060f080a0b0f130f240239010603110a05011b 62
    0x42c0c03020030380305a4451101100c6041d03503507080c4000d06010040c1407514480031003810040d810b0326484200001c0309000b40080002281089100c0c111569242c0303030100c40b640b160381c0300303138001e004445d54070640b540340c5400403440c400b07540c1c0640e103001011289041854143d0014440c601c8004080c0c4d030380c5400c0502c0401480c1800400f8080c005c1c4104008120700d140f8410a44020091104c481101018815014070440d010f00800020301a8008002144244450003000500b410300c500c0c44041030009031030381454456030030b241c0280e500800d800b4a06a0340c51005001e010240200080d11111041c00180040001100342c01e00d603100312060304c01c0d5240c00c03080742c0d003041c014811071103900c0000324100050403485d044001c02d485145a50410101d5400d00324441d540e0840304500303648108409040c602000c42441101c05202c00c004c00c0100100844142e401a46054002258200b04020040002514100000b000c060f1a041c560313560311001103031480d0f18480300703109050000c2641f001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 826531348 1250 826530098 826530101
    0x9020d060e12180913031e14190e0d02150706110a0305010e0705030915060604180504110a0f170115090c0e010e010509011815170609040c09 62
    0xe010000c2819940b4800302c0c0b200b41d224035445168a60008107144002100620300034022075003120325030202004810744c5d998083c01e807100b032020280da1441d0510300890303018495965070b800c2c21000819992980c94110010b101c13420800c101c6004203950003d510042d051226050f402e20760018129000d80d1010b2030404a154030035032040e01e1085d110000b40b030b89510884001c111021241e5000100c80d0b14105507000d60b24405446a820840100140640500c000400e0b90384480e90078004c12b85500ea41001981a1003a80c0c0240e0b0241e55500380c000044040344e201c58130541c0a034118042c807010b2070f4100601c01c40b142c0107000c5030060303004040c420030000d014003520540c90b480001414100448140c1d010309410f40c0044c456540341c2603c46c000581c42042000900b00c2800c00248503500ca4001910740e000d2000014104240303c00c0c003420241c03900400d5030003031941544011210b03091080040c21001d1942200e11180c075010041420f038241000500c0c4610b401c00c032a10581401c05101c41c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 826532598 1250 826531348 826531361
    0x15020d080f0712180606030507060806010c08030109180b18070506030c161412030613050907090c031b051e03010614090303090a090e120c0a030c170a0903030801050409020d06 77
    0x603504c10860300d903000140262040101841c0194000c011a40c50030030010311490000700294100300a084c8001c0000c5e2400c000c0d603040d43e8003d000030803c250300c0700710010180701c40b01d03020704950754440900251500e00c1c1a08995504680180c0390420345803014005a4881a1610078424404202006500900420490002c1e214034403405014810000b405c0c5080f54245c2030390051071001007032140074600307c081380c80f2100c0c4c001410712603840d000c1c0c04140c503506244030340103400e03032a507003030840d1035201e640000c1040e243c5030300c2d0703421131160008002c08170f03041266195811218440300c908111100801c4d281200c2803a510030061000c1c0004e4001d041c5c000011160f0540b00900141003c1d944a150070344c00b9200c0594001081403002c2c030650b15141035a061035502e440204171541c01e00d030300072460180da5901340c24509840f82480c40c001800c0550640940052074004c82c0f03001e0304ea1703841002402204d0095540b40d6490b42c0301c20030002201c100400013548800d000080710002440d40d000762 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 826533848 1250 826532598 826532621
    0x902130c11010c020c01080603010e07051011070b030a0b06071e08071a101401022a0604150e0103180210030b0a080f1204050a090f0615020d080f0712 66
    0x503034494071110602030079a02894820409a003014040501039640840b07aa607006808034000d014800100c00101d85817089805100d0080346420380d02010507000d000c10701c10b442d0318041250f50486e614249070b103094100f9108041e05908101042400c0d21b05442521103207900400304010750014400c80c0900e80d2140c180c00c6507411818401c000101d035108030b0300d40420b07a0301811840580b400c8900302e45044403540050840507224414503940c0c3c3d90011f18450122011106100384c0d9144601045581c9820b41c0121b51014000401140043b86051000c0300c01c005c41d12181e001c2140d6070015419a90040045002c10b0350503001e601c0503150103079000c00030300c18500300000d21408584c0030030000c0d0a03a401c1949503034015000354402500421181a080f081d0700a050b040c80c1c24000024010289803044201c409e450b590400300c80d40b80b035070002000340101c0d15480c0c14410080000b94070382041800340d001042c40800084c004126400400d407280541365220072101504141d020010450314000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 826535098 1250 826533848 826533857
    0x207080a0c1e1406010801020f16020f090103050d08090a150b010c050708031b0c06190509130504050114010b0904091b0f26031209010b040515010e0102010902130c 72
    0x480400c005112586030070600440c40302400d4003c60901920741401a40301c50300c82d030310400140b052010880c080c0c1d80220103a400080710070703d09000043c46081401c01c200da0108002000000f080000590000301c8609900d44d03640d00e40e107251185480b011105400340400810a07540921002c10342d01c00c0300004014100003103814200c0d10740c20324102d10707a042070740640e000081c5030203200300048100b030051409800410100b5080c402041942c040d500e83c2042d00e000c51180e0301c0070240500151141c520000d0403840c450050410100040d00098605441d554078000b0000600514440444e06840404240924089442050000414041c2c00a50b140f2040b078804240141d041101440100003080c441020b45080c0541c00d00000012615101d43d400c01002000e800400802550900d0300d03541c0c80c0c0b000e16680c62000c82d014042c0514251f92140c41c01b070400800f1803c845034000d8021007139a8020603040c0640c010790032250038200182d40400121613175107002420341c1104841c400180b81 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 826536348 1250 826535098 826535123
    0x70513021e030601030e06160819150504060504020901140d1119020706020d09030f110d0c140105090904120306030203061006020d0e0d171b010902130207080a0c 71
    0x184080780350141e03030900c04648800001e118a070b40e4503018170001080d00c00041e000da4180441120280800b000c3c980c801c1c001b024001072a4440030750341c02d4001d00304840003401131a40310302c03080018400b00d00031144950b2404c5000300c2d803418240309881004206031a00e501002d8140c184000341d4001c4803035510580d49a0365038103c503500401c080c00c0b62095060081c0080240404c0180c01c1440340c1c0c11403c115801423680e0600246d1007550702084903008020454002c482c2d042600d600e40c21070320344a410582000d444401c10940550b200d0480301e07202e4189000700248001140e40780b1070020000c0d4050350070000306011548420404120301683d0500081140d503e80c0400c4c10040b08480c003540340002804204140c030b4050100c04240c0307146281044500000c030001035070000d100d40000c1c003030b0301ca12120a503540600c40e04652514501c05c5c07800d54040c000304802c502030f00b845441240964034803500e00340f10140c2c60007644d0000e98440301341800c0000941d402c890042d4415801c0d682c5a041e6070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 826537598 1250 826536348 826536367
    0x5091908041e0306181203020a12060608040c0f080c0111010906060e0f010b12190902060f1b061006080907050402030a0c081506040504110d050702031306050c07051302 74
    0x5401c2c15003401c503541e161258a1424400111a05014050b0030b1100d4001d4500000d00340b100c07250801401800c00588a0100c09022603000703003546005e1040c18500350b4003003101600007a5540c800ca11a0940700072041c1c803041490f55040c01c51145c003429030700c800000b442c558042e007024103401c54018000940e100c51519480d0585880b40d12090340c0320084000c0c40031040e2050200c5002d00707656062070707140050340c00c281103241c00e000b0006020359a04480c0da10100742c0701c0c0c0001d510141c00a00b0346071079082194400031a40d100c1c030840e01c00702103421035040000f007011403600c2c49200b00301d003044002850034405a41c810030041100c1118002c146010030f15550301c1c805180036241c46500041d9a442c280e40c06404484c002d060030440d0b101031481070300c00382e440e08111000d40d18140c401141c1d20602055801c1d150080001392180c0c03604150410440c1d030b9001018102c4d40c0406071400c40d0080d56803030203882500c82e01c2c2c140303100380d0480700342400103040020b0104a0510a10340040c906903086 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 826538848 1250 826537598 826537619
    0x9082b0e04150e07090b09010503040303020306041806020d0c0e13021c06030303140601020c1f020a021305100b0a08070e0a03020d05010903081e01050f01170f010501080a0509190804 80
    0x5400151400c1403d509109000758080600d50160181c50220743c40c08010400181c8140002000241056000000a001a2950703003010114900740210186064050300d841d1010350404400c01e15041d24052030800034902c40c91450b042c109000d0619102c0c5009612071034069400b81c1500c030180f0b0a824a83c7d00c4152a6100307010086009a1b4001045e44000c0d14550075078801a08a504540c0304038120046a43d03041100308800c010b150b40c01c400380d09a0102a4286800c04001a46c4a041da505600b55021160050b031b2241d1007124605884549480710859540200640e240009a00b000040d01c0780e03000707a050034260340000f041400d60039560707400030320302d0304034040201e40594480083c5030400d0741001e40c01c3e401c040b0880a09940d4003901d04c0d0702e04440c00c1481140c0c49048207121081c0c450b40201d40900c0d150402c1070319540180f41c001070280410700c00b0701c11607000404100018525103600e2280c28083e40411000c0c0c11030398000441941140304095007034800705410440001c00b005034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 826540098 1250 826538848 826538891
    0x1d1903020910121101030c0816030e010e0304231212090a03020d1505010b04060f0309170f0301031101050f04090e0c040e1e3d020a09082b0e04 63
    0x305130710008400b0f40c2c8001030035200d018440c0340a11400c40140504c0807504002c0c46401ca0451030006a0480c294140714050712070705002c003d43c2e000014004c1000700495a0b400c408000000c1400221358120f0240720710007014000401c0b150b00200d159014a1b811400140b0074041c0040c254580161a500051104a280360040301c03a0610780304030b901418140e0290301e004198480da01410180780c00c501034101c04500111504256554038a50200b081d500010404400d0f0501019210503240c039002c165a030081c002501d01c03d40c49960000e0b90340c441c004031003550042c801403a00300b034902580c00c405441810582c0450340108044040170740c40310720030140c1c1c5000e0354004040c0722a03184402090130408030390000c110780020101c40c01e490392415034444000c0c1c0c04440e600c1125288203400c510603c007409410a107500004542403050b0b849003403c0c040e01e01c05800d40d489a140b1381c11a1100300c0e141d0803940c5296202c20281d11a0301e000b00c0300718401c80c0c1c01402c0446c141401d40e54220301c0b50003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 826541348 1250 826540098 826540103
    0xc0321030403140715020a02010506010e0f15130f050118030818010309060504050309280b031305010c090302090a0b130e0c0402030f09060f10210f031d190302091012 73
    0x1340840c03d647c48540c24040e50750001000c1c00c1c0001c0c02010480400d044031703101c40101c1e001d0000c110400b15185900f0303080311324440c1440c1041c0e40c4142c40e2508045003000034800e0b28000340d02c036041e01042ea00c69103015800c40358040a4240b603d0694042440b4101c0007103120741c14180d5803c00000491507070300a1a2007641f2a001841d5103000ca0b1040000448400079845402103403403980342c402c0c402001c0c070001603c002c407582c81d4590342c03110240c04510740311000041c29542003d000355a030075000410941500d100300c51350600d030398841c100f06044420021541b9403080c815504d441c598011988100040300d046025074a807801e00701c5c0802e090741c0c810f8800207000c281c120100f282500d424440580c010b00038480941080c2000220100014194081d200400c20342c90b410110050400a041d4079459200d1021000c40800b070501074489a0f140c448021646405080e0f6100c5103007030944450400301c200184810103055400744403074240c1c0100030707906030420050702003894410201c8600b0f0061 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 826542598 1250 826541348 826541351
    0x1a0303031510030c1713050a03080f01060503040f150f06290a050a14090a08010212060a060207030b0a0f0e031b0105010f0308030403090f080c0321030403140715 71
    0x40388a09102c951140c081862040600d050100c84559900c803007000444450034003010701c2600c511880110786c14840400034814461b0200003400c060300850464403034205400307006c038503030fa852a041c1c40500c812103000b00110360360010000000d80ca181602400ca0580c60001020300f04100041e0482c3d403070b600100000c40c07481391040407070038104908070710311140c1c080000e09120000b80064442e0007115011401e100d18542e81014040f007410a071414604028030f5100321541c1c0b9104203000394080c02d0895005810310b00043d8090401d000b274001240e00d50741c000d04800e4030b036445042044001401d410340300b072b491319128400303840503010348044102e806002d1651054040c02c102c0b032070302c10702d103111985034100001001142e80a8a00340e045940040d0ba8036644e90303c501d0215006450f0360442140b103004c90f000421507400003d4483ca610f41c041e41142c021002454650380903486c0c04203900e207000030410010f130001e07110b208020b140240944d0300d9410b20740680d64020717030030120001000219 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 826543848 1250 826542598 826542631
    0x17040b0927010308070326070215060102060a0c031514100804020607080a0e0d120908030c0c010c0222020d05060915090c0409110301030b0106140a031a030303 70
    0x1071420651024004024844444a4114404681c4101641448090003002010580700141030180e04041240c0a5010380c90f4012515072110900580e000e44000e0014801c3c00b030140300c82080c11034564000c0d60140c0080210380e442c00f081d003002d0300565882908140e2035048038000c40e1201c00d03116000d80301c480e0060181c42e010f803060041541080403000204441d13071080c0030140e281c05003101d5000b030300040410741d10001110203035403044040e5007158200fa0541c2100c41440000c0720348050440c4207960309506107603a862a40c1d0340c2e0207047c0c00b1440b0380c1c01800710503540b903014483c802c01551014001030400028030f540c403194001025903400310305070000340848540c00288030b810b6004504580d03104032404c0840800300c07181c0d5589901e500510154011a0103d9003031340a44000701911031080c0100c0079000103501c200c0c0c0081c44100c1d44070340080004038486024202c00008041d15044050815089510440250620000c3c000c42103400720192102c03610240b0040d07200382c0b50802400c002c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 826545098 1250 826543848 826543867
    0x501031202031305100c1e06050a0c2c09070f0305060d120f0504150507050d0f0f0507170c0c0a05100903030809010b04050f1e2217040b 60
    0xd2000d101842401c540082111200c040f1000d0004020b0381c0c0160340080d0004065242581d24103403d11010700107400b0700103913100b003d150008405603248141c00901c10707030b1110701c10081521140010034010074600002d8010540000078050b03111021800c031901c840507281d0100c0c010341016035400d80060403111140350100e8041c00307081e410107019100c442442d50396480304807828680c0078201042000120300c141c2412b02c29030a540c0540340070b40c0360458140d456000a0072640c043d4408a03400d009102e845070000c1d0041c13000b01d031841c61a0301c0d61781148181c144202e03a10380c8040b00484403a008441d1041f5040301000240c440e078030303a0300010180c501512040000144181d842188604600100b00714410383c03100b242e004490781402e20000030f840d01c01c1114003620800100e05e401500d01002c000700b50701a20070302c0f4041c00d039020310145250200313403140d150a80111441004c1040c01788822a00340e0700401c000040c1402081c8880b070005107c2913864965000341d105115001020030f0740030700d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 826546348 1250 826545098 826545113
    0x6090106062f01061505090922031202070f11011b080a11010e030310170a0c06080c211b030f070f050d15090e15240d06050103 56
    0x150046003031112848521610841181e0321404421040d900e18800d0000c42001c00d400c404040d0560340e900d82110891140001d056411110300c7c94401d51030072000c2003400b01030311641e0528206192044030b01d8120ba4405850480440f0316100c2e01c140d08000b42c102049003c1080f5540503ca4a95098078031040000180350a000c03070310349400000840c14041c0000c07108811210718091a090500b400341c2d400e01c00500411254080000f86d0200104101545070100107079019598191f1080d40c82031110b0000310781d1440d034404d0040001000034014000c8500540784154440030180300c05141241440514459070450300d818803801c4024024881111600e000c45031040e0443c501c20340c00e5203010700408038401405440031050000c504815504144030742d080f1240c08507400c2c0c2c00c0c020100c4592f80d146541495110303003940940341004000358810041030400e01121508246006512030129400d56500380d040380c0000450350840e00245900c7d42000000f0060003008006455899800d2229 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 826547598 1250 826546348 826546361
    0x6080114030a1209090908131703031314011407110a03080105300f07061d1509030a0524040209070f1229010201020f160807060e060901 60
    0x8151405103002068a0307100000c003900e4294221051200e504203d60081c0d49010b8207402000d900c03414200c4c92800d02c05200014101801546c2c10100031680d2280482d021400c0c00005450503001000807414501c0c460300b0b100f078101c0c00f0700c20b0160565803c401007401c40310030b00c206507030350110f0408001c840760f0450a1120070315112000381c019820380b0303030f8010300d80310050241c1031140100d80140349804c41c483d6900ea1000b04c5090a6602c0070480740d00c1a0b50751300e04861400980d00c203407040802d242d1300c00c10502c140349a0b002148030041449038100110448030310700b041276182d01402109071070754003044400c0d1103c2c00390025010340d2104901c5210a5400400601e19408403030b41030200503261400301540c885024940328448442d0b1500c12214000c00326103001c0940d0806804c80c001040c40880f04101815030707000300312104014801079090780601c0fa40300c01101401c3c0011440d400382154104d100c1e6110303000c210300c1c12a007566800c007140d00f404203d00d060b03840b840030070910f20800d03c5a031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 826548848 1250 826547598 826547609
    0x30c120610051e061b0f390402071505070309031103040602060403080a022a24070e0a0b0f040503150103050d030e19080309010c05041202063001060801 67
    0x224075802c0d00812030b51903d90030303840c02c3d0040000140c1503540d680e10f100d003081c05070004001c1e45c62142c2102c0d03881c0e42d128501d07811000396a20b0b400300c2d00804506a03d801c8000001004400c000fa00e40d401004000c2d0800c000c2503650441002c90b4081400d190f03c03809100307c10540303001500b141c2d14100288101850010314005a000300024031a01d6000110158070980c5031600f80308644d159078141000c2e00442c00604017412803008402886400da030203811441541d1012528400c8000c414004041d004005800700c0c41c1038070000c20041e51180c200d44001203400790941c000303640c0ea489080442c0c1d100c14204518483e01080a0015107402d000340b41c03140303002600c50069541951a9141c0300e2000f4400901032590303c0440d00410b080503c9440c1064403803041c14086142d4509000c03225030710443e207103180f9520742140c50301060702034400d440503543c03600c0b4100d28422042d424072030b0503440024001819100310a541d222150341d02da5240b09141360b449030241ba03514200010f4182041a0000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 826550098 1250 826548848 826548859
    0x60909090b060405041a0a0c2d080a0e10240e01090f06150201050403080106180909051f09110a060c020f0406050d1109010501090806010e06030c12061005 68
    0x1940c011030901c6500c6900002c08a41c000340940780d41c075011144c0240c6030700524aa40b200400c0010241040d03003c1180d17014261581c207010380740708204a45000340c60b4803114601e40e0b428800315a0b54485d52103194048001c0c00005454000303c031405141c010790036010702001da00c40c0486075040030801e40c41c4d07000e0020b01114846207428200340130303040081400345e0741a446c3e6440c0000c10301c154070740281000b0030104011000e41c00410710024040e1038101e80c1540400d004100000c3c119100d003010066101110380300ca40f0749410510000007800c25110159003e200d6610307801c9021400d141e44242c03251201c000002e6060141c0b81c01c1c8010410400000e100b200c508008000140e008206290480d0303044990100841c80500040d00030551500490380040542e08443d00300b00800d08416150f540c101c882c4070700c0383e903a0001101c46542c180660761042d00550300400113400c100701d04a800400003015101600005004507042120450480032642e000806102060156000440260030141c41 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 826551348 1250 826550098 826550111
    0xf1210050405190c0c080307051e0c0a0f050c120a0501051f0302190803220e07051b070503031207030c090302030d11010b09040b18010b010e010c0201050c070807060909 74
    0x103d079189408400d01ca000d10340b10804c4000741c0348548140200b0907846a140390716410154002840e90300a00064406104100750045d50100e0403c2504c002c070760500010701e001402607413440100c10030304a00301e030303c2c1c42000640a516030300c0d1003001040a82000040440160a0a1080c203480014284c4c012507400d005042030940c4065401200f42c0c3d4064407240690101011000c1072616141d2103400039010115008488103001c1c0e1700e0040e280d03900c84030b146945440d8524034003103600c1511280b0105034100031810300392248184083c03425a00000380c1d90800c0d643c9000ca41117a00c07d440450028908804000e10242c1612034070300188014500301807203e040d41c1c0841c0e66116900310603014060341d00d050306c0d0945002d400103240c00101800d86905410b09180480c142d8030140d952903502210043c40080074034051107100c21844059455007221a0000c00560b9100704414042e410000108041c0305a40400c10420005000d541e00611480d490f00100070040f010342d4001c94015404c094 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 826552598 1250 826551348 826551361
    0x120916030b0c030606130602030c011515080402130603030e10110c09180a0c03030e0118050f040908030403091505070506010314031315020d030603051b03030f1210050405 75
    0x160440e500040c01014160341340c50321030000741c0b03500903800403d60a1440440110b45c031a8040f01038502031148400a01040000b004c0c200702021032409905c4403085032400c0343c100c1e184242e103001c0d0403a0024100300103440f01c603840b1100f41d582c99001075010641e444100185070912440300003042901d8581108200e00318144607885000720182c0d24882e044c1400480d880784410104100c400b40d0550803030b040b1040529080c418410144404d902041c4038050a004650180d00c00505080044000b070700310340d061004104000c554207803a55089075881c0c0b0060700241d05000158019800f030344400c07a40e10f18000c0c0c0544006550107054080100c00d000c0f0600298001034030b1419240d2100603045c4001034500c07014a1030240c0301414000d0437440ea070015000c01c0040c1e03001c101e4801c9a00380c1d28198640e004c02d800350b5025206c006c01562041949480040510085c1c4620b5280103082c0c4c0d1405c9002c9001208a400001aa4480d15001014840340d080c50a1100303000300001c2d501403000b4070380360 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 826553848 1250 826552598 826552613
    0x15030405070617251206060903060509010b01051b0c090a09020a0b1602090a240612050601050a030504060605060c0d021e0307140a050a080d0b01020f0706030b1512091603 75
    0x1054004c80080080000944a901500c80c1d002c07040003902d81040040e9070340f08001c040d80503511003a00d58502c0e0030089210800107008000e648030040e105c807403400c000014824214401d0044034002402501c1e00c1e8101681c420400500541101c1c8011803224428010010000a582e0140040d41020000c80741451012100300708034a404440d100c2d41c980d694001000034000203481c054240c220804071318400464183c7c4230081da0442d0392980d0a40707080e440000200c4e0000e6070000d0116405110031302c200b07071080c1c1080303510601c510310108600c2e0343e03040840c1031a00092848625178024641c41600e00c1e42c100b00112208241c80714070201041d1749168180c0703d2140c108003811005030b03031a0750039444400b00144401c0d6644801180c4c0903400e24140b1401c16044880c01c48000c2d400c1c0f03070756a0f103590302c0011000050045500a482041c2c42c05000341d0080c42031500707498101c81c00302a030503400d03030101d000fa221406024581d03000502e040301440c3e0400c02d440c4480000c1008801040c230109010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 826555098 1250 826553848 826553881
    0x4030207060e040f020c030c0613050a020409080d110c0f0304030c140d050a1506060f12180507090e0c0d0c09091401150e0603010e0309090615030405070617 69
    0x50038810703031000c004004600504061003c0764484d43c00021101980540040204a0540c00c141916070390344038074580d0048503c104001500c3caa006a041e24090318103a840751032024440c4030000c0c508419400384c00706480002e04ca1a1200c0004640d601c40c50303600b40440315403444090061440c5c81d0135591202d11228150052000307550643c07807071480a40318003a1880003203401508031080b07910203182ca15044806034942c2c002260821b6000220300b4080d00d0103426100c801e403107801072101611000d40013010a1103180043c0b00c009000417006c5001840000d010307000302c02c4c000c07442c614140c415074500b40c007481a044c001c060402400e0041001108100d003500d00c1c104000c5407017881070400084103100e000d0908010b52a11640445403280841d8400482c1e00040c000034075962810300301822103500204003400c9420822542425162101c5041e502680003492214a50341414500809810482e42103031294003481040c040c0e56080303514482401a19810104603282141d410100c2e00070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 826556348 1250 826555098 826555109
    0xc0c1b050105180a080601030f02150a1b032a060614100305091e0606010306060f020a0b06030304080a0b0a0b04150b1804021801080c090a030b09030d0609061d04030207 74
    0x83c0319041c403c01da42e0503c0386401041d403a01100d5482d44c4a0501301181c907504181244100342000400608040c11410f0764401c40064841c9846111080b01054502c00400c004404104443c5121038603440340180358210b0303500d1818441d4400d4194034029080320002d42010152074401c03599400c50340e80c2c4d044d031480000c45e42e00d00070500d07484000009180100140c0c0d20413451039031902660108100241140c442c1800366414482656582c0701661002555949100160020705c0c1c20000b207101d01d0840d58002802400304d030318055980240703a081c1100c5080c100d40b60344901041c44a005114050f985580008940801100b000021002101800742c42524000b0b240400c1000520551890780440004050410b554034201042071142c14030104440501083c0076030b01040a9049807130907100041c034041d001e0084241135445030010307000000c242c0b00c00f070701c0100a400d2040350387c2c0c0558070040824520106107582000200c5405c80e0041c144070303060802880812020980c0003c44104580 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 826557598 1250 826556348 826556377
    0xc1f0809120a052506021c0b1c030c1509031e0804060b040209280906142107030303090b07050307021b04061d070305131502030a0b040c0c1b050105 65
    0x600d80d00c3d8440b0800144c9213041440c0805024500c20302403030303070010880d40380c581070060040009001c59100f2141e8001881d034000c13010001c24484502041c99050030705000c1e08207444401007031350303414421500d0000b000c1e040340d0310394100d20109a0003109010b821072141c0480080303004845001000600000d10160600c1d880300b03004c21052303d40c2d40c100c0d4056070000d00b0040385059078014443c10141c0300d222240340e0422504000807030070070520454042d100011541010a2100f600b0052034105001f180115580a901c00c200400000c0003800020b510988010403c0d480c1800c101e502080002c00b0302080c050100200680264086842650400007200c01d92030100640702080043c081a00f01142c1e504230002401d100351b01c4420000c2c46103c01d96000d020542d1080080741050001041c000c0034400e050110240c444804d0b0040e40d0300406c0d21100240228455001600b511960104032004c2042c8810000600ca040702c940d100e080390341c000c140219458040000c01c00c0c0b0a000e164440300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 826558848 1250 826557598 826557607
    0x4030203012f160b0a1515090911040b07050601091109060d091103010609050a24030308071e030b0306090c010219061508031b0105190e0c1f0809120a05 67
    0x2c004000120944907080045042607180901c5001c0080106c003000100c2e60340100c0740020103240181482c8903e081303d80e80d02d00514507141c010005055800300301c0d225884207200100d40d0224810251040710700400051240f035142074003482c1142c1c03120542c070b242550200503044403625050111180e00c20301c0d041c00a2100b0f03890900c0b040011801e5500e40d492350818100086042d0303541c0016001d48400c04040046003942030354481c4101d18100740150049100004202080c018003286600203041d082c400140c8600710040c02c1255415840300c40403a54807502d4640c0c0c3d040421500754000c200c82c0041800c844500f0020303541e603210340301612005103600402d508000a641124040120266182a8803900c4000d07c6440c0c0e0880203096054180606c90720000300414003540f4010718500c0c404c8a005042c013440440a443ea40000720300c140701d0861031441c5600c885040c1296101048401510303213400c0e40b4001c0408601414400c0b59600c2041c1d1303d800e04040c00112200c0b11114100070b82d64 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 826560098 1250 826558848 826558867
    0x402030c031603020102012a08070207080a030f0e0a081207080706090506010e130b0f040f020d06060914011d06031e0307031e021b0a0b03040804030203012f 69
    0x102005940c940c0c1d014001c80781c0407245540d4030480001524400d07002440310440f15440240c005551070424441c0b5000140288041d502a1568a801c003d042c41135034806604d4021480c58101e031034100300c0000e10550320b65010168030262032940c110303007103a0388003116160420403507440d0954114603910369000078510040151401c104e8036942c0e4064014424000315041c129100d0b4003d1080360211402140010f40b540000c1500d480790f250301565054094480411810286100410455140303204035020703805640c440340c075480300500c500b8000c1307051030600b100401940c88482c00e00c0f43c0b14400d60014895105848000c8008100c0752080c59030703a6480c100040d14040c015503445e4540520b100002422070320100007021440d020751102c0c3d00310180500750201802d0600d40c0000142c01c05403039540490f0340c08104200ca40c00003442d1014030350f100c525031400340e842604c040300d0030000003130304004504080c05000e4082420b265680d40e11a01c21038098500558035003900f0180d000090030808 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 826561348 1250 826560098 826560103
    0x20a0207030b13050c0312070308100b12060f030f031e071b09050606070f1202031b010509010b010503160305060a0f03060c110f070b0c010605100f030b010206060a030209040203 78
    0x86800502c101e40608203075440c0410a04080340a641c075006032442e2040a08002070034400c90a40c640c0540c3c9484c265803400ca440701c070b002e050110b403450701070000140101d081c4060a25040c003204e100345142000030420451985124000f80a07400c10f2494000720107010041d01c0c0401c0d901840e0005141d00070146100900ca9a100200003045082035964410150203080c0300fa02d070000010071461b114201040070380c1c05070100c014000c0000503130240010f081e1a0702c2d0080310506004882c00d01a601c04d070b410510076100c11101300740c2c0d0f440041010041007401400301100082c20190b1640c1084241070ba061051080341109254075540461900d40f10f003680040200070103690f000c509a101d00c0c0c00c8000d04102e49a001c009804440c181c40e41c1c12000c42e0014000c24000000c084d40b601c1c00c072401d100741d086005511010b55070fa80000903940c85a0102c1c140398241c80d504d104403d1244c9801804680ca0550403504541c8a4004c0002e0303600c03803000c280140ea0701292403441aa0300c0b480043e1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 826562598 1250 826561348 826561363
    0x2070f0602032203031d07121e0204140108060c07020a090c02010f0e0f0606090f060d08091806131109010e060909150a080f0d0c02130c03020d0c0c050a0b2e031208040c09020a02 78
    0x2e4100340f3305150600d501031000d00182c142d4010760166034442c3c81e0802d0044042c00760381000780d071084401d08200150400da9010b60910f00c43d070b00011a40d80d20041c0500d049864007403102c40303182c003c210904c40516051140d154080c0c0d0844082c1c24034241b01c001040d9120340140510f0048c20140742580c184410741c0250385424a004141c6410141c02d01400c2030b408805440d0a07000d1042e0300800401554580500d0258010f10b01942e0300341a29100112031400d110615130b9045242000b0b5104151a60034a091040f01c2a099815800c80030318180401c40d01d032070f84070200799001440342c3d4840039400300d40181d9501d911315060040a02c140005905405c2c245d00e840d2204c0d14141440c1d0710070f5015005089090482001004810100c49054414001e41c910080c62a0031100c48100002e00d429049034100c4880ca8812f024004060004501f400508848107448043c0900410800260b05048070150307207103103801b00d03090415941e04c12031400700b07000d151000e507001b00b0060a140d00c20804d82 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 826563848 1250 826562598 826562603
    0xf020313060908130f05010807020c03060a0203060d06020414030f0604032304180e0d020d0912050c06030f0402030c1f1d0402040f03110402070f0602032203031d07121e 74
    0x16134901e94803592405001e01d1841414007007502d4000248065001040c11043d129014015000513500d15800b00001d60005282a0b4040c0002c146040455218070141003d06904002d54404004c4641014035100c131910211302a940400200300029602034000001c0038000c0000f600e0714030401980b80d50900403900601d0101d9010021801c01d07001d41e4010f13003155a1204140c1c1c000d101d1114049071924140c89a0002144445c0410004403006401c00421117000d0801c2c0d40188030f41000041e80c0c1c0e8001e41d04911100e00c406c2c144401d515040c010042c00040c00c4618509a841303414843c00c00401d500c1001003480656104100c16030270041d04000c1c00e80005100319900c646656802c0c80e609140c2c00280c0b1081c4040a141e02c050900f842202d01054000085003099256039807001c2c041e5000400c14080d020b803507404640100d16010b2000545482505c011424280c403103010202501610541c1207294414031081042d100b65030042910180c11482500402c00b5502000f07d0401ea20b4900 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 826565098 1250 826563848 826563877
    0x150a03090b040501150602031306050309030c030720090717090f011e1d030301150c0816060509070b090d05070b031015140f0327010b01030f020313060908 68
    0x2000200f142c1913000041032000c885189420390744a04040b640c90280e85009482c2160811050068900641c091070340301e04c1400c100d07480e180c003840002d0304642080c08100e0b160074441200250050544244100703d04090f524500c0c40c2c83c0c03a40d0000c050f0b100200c1d400062141c01c502046800e9000d102015100910070300a11150103280300c0001c0000d50390514104507442c01c4c58021540b48103104400031519a41b0085084d0b908100c12890380300325900c0c0c91014880c071091038000298640019111144481c54814200c003c0c0c0c1c01e10405a500080034414103800444017409142441416a4600181911031100c0380d0480e241c22071600e42180c02c03101014001008001c18106941d40000c11741d21203c04000c4901810b01c001e8881f0f00b841e41c400c6480b08001c3c0722110200d240c40014580c0220300e030102d080c0c0301415400c44a4000f1600e44010056510380982c075000d543c240c090320791011900c100462440c42c001401c202e051400740d1008040d640c66005800522500c03000b0380300041c080c0001d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 826566348 1250 826565098 826565101
    0x40911090d200306010e01030b0903040306050903031006030207030c0b09010603060203012c010303050301060c08090d030c020a050612160201020f030c0d050c04030206031611010204080307150605150a03090b 91
    0x900e1600091a03250500c0e204041a2120740780b0f05021405174125108110701440036402c566445600800041003400940300c00e00c40080456460b000c0d6600811001c8090355407420706200803107000c0015000001458010030502000942c40b0306400e5a07103401c85800d40340303034640056450140030030303600142140b07001000110b80e02c1d4402c03d080e815124100e078038411000c120341e08441030071750901c40603010900600040100c14041c80310700070150b1180d0840c901d0b000500d000a0b1408444d0102940002c591144120860610341603205c09000d08030740c2e42d0704100010810910302440103104072402450900100c840f24001d40603120341482d42902d0ba81c8916003002d0720700403500301c1446040c90030f0070640841c64061003a4201d800752500580328510715a070b040514030368082c01007040410000100c420304040002071000d4000b42803d10050b66860311141422402c1c0b84950641c5e51041e0b10b4080100565950090007020740d828021074943c649a82e4a401d50003000011005483d0b1740e100380 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 826567598 1250 826566348 826566353
    0x15090a0e0703031206050a05030d0804020f091f0603020310090b0d12050c0106091b05180901091d0c03070e0a02160c09050906060f2b05010b0307090908040911090d 72
    0x980c880d00b43c4e000d08100709a41c5070100303c9440f8031440b03010f0b0035801118805440c6403290034401d0b44180080c0038200d400301003c020440310041100e0400d01006058400c01a54503551451002020146419410b40c10141d4802ea40c0c1801803085100b120f950f4040040e041d140c9108004246800040070300c3d0950a004025065a100d0f40140392594038208012480324180e2040d800d0780020101c22000315003030490292036540c001c50000f14191000203071840c01e9650354015034043c101207500800d0181420103100301c1c8110015052200360448a00c041031500d001542804a61207141c260100f51184540c4500030710814000d088801002421841400547c0c0041c004035034520000304001d90382d00d40c5481d2a081e098608075440000c4500c43c0302d85142418101039980406450304044c035900c0c402c07500c401c1102d8002211165140c0c0c603010560b10b002c0c09454002e103116801401880c619681d4444588510b016102c001a540e0344132684d1b68407000256541c40a000e09901000c070403d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 826568848 1250 826567598 826567607
    0x60f0c2506050913050a0b120619051305011a03011503081617070309060f08070804060b030106080307120906050310181e150506090a0e04020d08070c0806060915090a0e070303 77
    0x600d03281c041c580a200304080c0c8c21002650500c98402c2c03080c0b2060b10075040340502c014200103408008070000502c0c0220200700c0070300c901c0c02c080a18480fa00400003203841418251039040000c07400888203010100003186914003110340c464003a280c16031a2802070f28002c000081101e641002150000c58820109508150f17a0415901300d61a0108131210300002100c505200710350450001d0038400c00328000903000d401c8030000f140000c00214107952581d045a00e580c000c2d10b0141d9030507601868042020b500001d040c03010f8000751804030f07e941f41c603074080c5903031455500c0342d51060501841c0b0111f501c0b40701e038800c00c04002100070003c4019820400880941480b00300e004203010b091400080f5843c189085a014040140003843c00e280341644042c08000d0003403080c1e0700f18220a0740900000c855000034134641e445030305001c0b0365500f00282c20340741c00d500400c0707a8001d20708101801691840400728810400007251030700c06941c2e070506c3c00006018103440107020703482000804010140c20 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 826570098 1250 826568848 826568861
    0x6071e0c03150203130221010c051b0303091b04090206040605120108030a09031e140a11090411040e0a05121c09030806011d060f0c2506050913050a 65
    0x11005507842e41e0801c8802e0040b448140c545003203403e00c20300c1001c010b040001c00c038904030101011804007241d00110103800d56012009800014500150310810300100e150042070002495004506514218403130a50310021f800c00100c0c1d454110b400184250b8803a0000b404942e8007030405620f40e44e0341e820144c99038003e18840c0700586a038000100d4002c00000990301e82d071207640c1c1c600c941030386161103038188240c0000038a49081041c0f6201000700312400e090040303c00a0038000c2680c4a03040c11f180200c08003483c81607202d5038500d001c1c0030100d40b46581080e03901d03404940008240e001d002070a4a030200440d0004e00ca401b4842c0f40402d03030403008018008004004030301145150070142c203541240c048030343c014003003440e9038080303065548074407038009414600ca051844044018400200c05402601414250f1040043c08130780203002401403101d055148607052042c1d0040d503460030150807450203401b0811001080c03111032a035880c0d12000345002d60f007404000a0a20000c5030000d0101e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 826571348 1250 826570098 826570103
    0x61e0607030806120c131a03010504030908070f06050d0e030c0a03030e070806060a140607061104090c0809070e060105120a0515010c1509030e044706071e0c03 70
    0x400d21403d09042008558404040401441d4406c03110315981904010400e80f60300740c044c80100f422001a54509204a82c001c1e400307030b100d5003480e51600344414501400364002541039159441c04100881d04501074070159518003501150107120071800724074500564080390f60740c0c465420a1001d043e010340c808006100b019080c0c80d40f9030744900300503540b45c0050380d0301a04900c296408203d44442d0186150394040000c1c800d500d07018554413400103035100c401c59680c8481000404114104180c440d000014a6905181b24680350002805440d00124401d4191b105400000965142e2203903013122071080f00000c00180500340328904200030301007101c0315100b514407508a00202c0d0300030740305480700990150040c07440804184000e030191042d01c1c4220148030055607140c029a94901403980e001040c0d01d03408010752032007000b200c5041112800d80044250300c01500305100e20b9010030000d241e105a419940e07070300309482d00f1034040c24402c01f103458112001051404000d102c402d040202ca0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 826572598 1250 826571348 826571359
    0x1021309051506030c0d060305030309010507090608070210050408270f031507112d07051c11061209070306142205100c030606030f090506061e0607030806 68
    0x303982c1204070003074081d0110303203540c0018144000b40c0c40c001c40d10028024503446180104042c0d80d203949043c615007080c0e50014150f51a003040191a50303002071200010f001514110085040403070011f17441d03039400c608141005459100280c10f0105500840d542c010803180414200459865040700e280c0c8949041442026000510002894000b82c1e42d402030341c10042081c510740f9604000c2d030b08403140400900030703401982a2510000c0000603404a010038030007507113031400c100303100d2181800c500b0307046140f1404401b032a16110b416600f03106888a6489803040d80d0400203100080c0507400740180c040e41d01c0b0421020860700b40c2c0301258070701c00c503445480203009035920160780303103407108045401480101c0391030b03960b20342070116110b4448058000c0c01614040000c44048a058600d8080e003000460307150001042070700c0d414411080c0d03481c2c0181d000c2128412a6176000c0e1101c001509007807040740d095020000d591228a0711910041c80100b00710340c2d9403118a0301818440301200e01d07601c1071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 826573848 1250 826572598 826572601
    0xa0f0f0f120b031b0a0b180913120302040617010e2707080106030b07080c030c03040204090c0905270d0f02031c1a1009030308070207120c08011b050403030f050c0102130905 76
    0x6c44404041c0c480809405c00c8181c1002d00b140288000124007c05e2588106203c540c090b000c100c0da00c000112001c0c1c25500541d403603051410150407044440c4841c601c8515903c01001100000071a00790001c800e480b80702d401c0c4810540c0c2002054000d18120319a02900000103120141588044201c0344290240c030314a55510005a0389040121100e00e9400810000940103c2c1510000c0d07501500c011b100203a03528070707a110542045100d4122040b0159564180440100c231a2039944886143c94015048405c5465032940c40381080303207490051004a4100300401c42c0203000340c60030300e11401d41e10f007070349078801a802020b0211b4240c00c1c0640c21854030007004505100170850300d544441e803500a1a41d00e0350390f00329041040105000114010940e003c11200814a0402c0406001d80681d032100c600f0600f0300e6007102c9000240e4980e52480a01e00e100039a0000c00f80e50407030b0b800d07003424a80d0f12080701055030300e8850801c0040c102c0d4030005054141d01000094003065600580701000755 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 826575098 1250 826573848 826573859
    0x61201060e090705090f150c0a0221152502030d050c1204030f14040e0405060a0b01140d09240c02070f03060f18080a0f0f0f120b031b0a 60
    0xb8918140c6101c3e000a0042000e42010304001c94181402c920191000e50301c000c0d44e05640e9096000440d0800090f0825660070043d483c000718881c200d1003407044503d80744511840e03140d60350a540d814140a030720320b50340000c03030000c800c00000052520400913659a0492044001e440c0c4d484101000c0d605468500403035a2500700301c0a0310074902d9840c44500481e00d0325101542c810384001011000c202d00038622a400c141444090001000117400c05242820b0a103007090030004c004203081c00807407030407180030300c56a444090211008180c3c0c5440b03648112406400d00504849000605000b40074024403003402c1020b044065243c3c05e80c1d60410141500040481c2c03242503900c140c14500d8040300e007e001046d52580494401b04003107200140c6a032001460010b44180e1810a44a009001c60703100c0c50325805c003900350070521603481e100303400f90302400020300740440c40c0803804c080007000c0408440f1b4010903804003000c007034001c0032201001c04000a40801f90404018980a1221040300258 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 826576348 1250 826575098 826575109
    0x90d0809031204030b0f1603020d060b0a020331051212070b041203050408180a090c05041701020901050301120f020312030a0c03140a0e0709050f060a05010f0f050c0c061201060e 78
    0xc3c0d0001c1c030580e07400b0b131f080340d070403000fa40112040c0358203075503108000074903180e44d81c009180801158000c2d503101d403400c960007160040e040b03070203508030301210b039012094070b82c00060b2009640301180d005083e0790801c00801d160010005403079541800014030f0909110740d4400c2507220702d1048025140d100c4211000b07c2c1600e42c183d400a2000c0390510460704d0091600c01e40c451510806000d038200d02c1d03a9281c9960940304140e84041c04141c000409010001d20444640c8050610300e0007549012040c1d800209284030500c113010302e900c1a01005000c01030345888000c40c42d07400404aa035110300c002c6d20420141d105940e00a25a8074210039031010601030b0052010751000d85840c0131841d620001c1d030102811006194080e1801404404603008a06100c0c181c010306107185005c410340342480500c441c1101a800841c148036200312000c1e056603204901c030700c5e000303514a00700762900a022079052601065502d00d0340e0188010810500d02d0141da181d260480c1c60b03aa881284401d0082c0c24402c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 826577598 1250 826576348 826576351
    0x307060e0316021c08270604140d0f0501020c0c0f0a08060c0a0207030c09020301060e060313141603140106170d03020c07090f0b030d030c05090d0809031204030b0f 72
    0x7500c502d03005811401519101030500c0c070b03c03000249815044200340d501c040050340b12450003020003251180740c4101025203885500040c8050b510345103403d050001c407280da03002605009100d501450b422504200c140d0460f40c210f00d501000030340d15a0120626030392240210100d83e030181c21a0410700042d0311b0a00000c0301100e0380e010190030740d07413100202c4800642c81003003002c1c00d40c415543c0002c0090b196081460003840b0742c0b0310040c1c895041000c02005860400c0b042c9100e901e00340180030208890b6075008410540c030050082c000c0d00011081402c0150704840503075880c00800b000820b00c0160340406010103041c07402000703015240c1454803240a00e06940f00c50540c841841c40000901a80c01444181e051604540c0480d40d28a840c2c400e94000f55503031a0300701c1e25040c1c0d010b8181800c001c0341c1500c13151030606220300300701c0e000001d0140c0130303480c50f6038031860036007940400307000204084400a80000c0c2c00e0b103042480b00307400c1c00c01c2d9602c0b40c8411145c0c2501a80003800c020486120107 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 826578848 1250 826577598 826577617
    0xb010302090d02361905040c0e0601020c030f070e09030f03190207170a18180902040b1003090b010611031819060f1d03030403022704050307060e03 65
    0x10140214940c0a010b6074581c0e800c0d90f8955a940c0c400c1c8403803080d843c3c443d008842c60410f0313194065417800720710144120b40540f02c001641400c0105100000303070b48440c0c0c00142e862401340411a5520040103d28101c9008210b9400d405010022503600f40c0114100094444003140c0c40015290f030185161b5038460a6070440c40950188045202132025001c6410003203060710026050400907105c601001890200d81e0102e040001000c4010b141c004a503400540c2407040a004298900141919940804c007050217501340d175002c0040440d52958424500e950b8013070924000d00b001e08401030003c0002c0039060318078101e10000000ea10f07116010007441150010701450402c140303d008141107000d448202540b2001f1903202c441e04034044591340340109407541d50031b00980c4841c0307405000be0b40d03154a03400b15140c05a01c02c1301d03035407400012141183c0d8191480c11500300c41816041c030407102c80050321035503402c0c42c090100340312000000c0e1454038005c04081001c55041c5c07058955034030421481 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 826580098 1250 826578848 826578859
    0x705090c031009020c06010302040f050411100c06140a140c070f0f02180609010626070302190e01020c0406030201121a04091505090c03120c0c040e010504060b01030209 74
    0x40386001010060764000c0d1045041148064543c0c400e80c09980103004100c2d01540f004004000354501400342d2003000540c2042040a07013040d480f91003c2d2045040d895014001068000d0241440b440307022100c20f82103c800c0105c024111088402c410090303440060345818584040c18820003410020f002d82007540c0b54516100b2965902c0009242c001d6041e14504080681c540158540050307020380305111514105403490b1003010014040b1060300714000300a50720100c0d400e41003c0c18102c018410f1500c01580c980c0d580c002040f030107881102c41e0340da203401808446100305034006562580149098090356140e03150282031104551003440064006040801c0200850300e1590140088500000903d100d100e885c401182c01d82d0546801203440d980c1007001000602c020388251070300030944001806802c0c040c040001e42d82d00020f00e81d144444070010b48201009410011041013a00182003440101100350400d402810100d07020b031000c500f40841c4101940c424800c0358170f203290007441e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 826581348 1250 826580098 826580101
    0x50a06110d0e060405060307020109210e010813020a060f11030a05090d05010f020f0c1504050a2306010e1503070333022d0910081906080717070509 65
    0x41c11500d00ca1032101207900400c00300800302d0780e910b6510046200309042d80002c0740c88003403441d01a980030b0b058060140c04040072080d402095074095050510540f09190000c02c07902c0d20180411a01c5001c1402035214101c0c1d400042c4180c0c00c06000c2c2101103080c0c803580d6900143c0800903849216140360540041c0080010f0022854096131004101d07000740c0001500e00040c1c0c203450200e134020f42540e5218900854000001c404c204040c0c1840c1d07145024001c1e241c01c0540c2c4081d40ca80c080e400c0241140c0740c0010b00703509510189042c0d8403010100701154125650b070500140040003c2d00c54214000000c40903a0043c100003c45108595100e4040c41d0700c911004c0c0c01c40c0c04003940c1c40c043c180c10fa48035500034404580314006003c0e203100c850074591600800b460040090714140740d031a443d5201c1400320380342c0740d641c503610402d281c3d825003810340203580e40312039484480d80c2c890f018558052500001181c140030006d446d006071154003040c810404038500d6040d948000511032241c1c031180030070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 826582598 1250 826581348 826581373
    0x1020406020a1403271207030209063d090819150b03060c12010806011809112206050102031606111c090606050108040b0f04110303070309050a0611 65
    0x1803810070110b108003ea07801e05c0c01c0201d4090075043d81c9080302240e2400b000b030610341498001036082c2c0c15802c007002007880368655030204280f440c0090103d44200c1018880003803843c2140c2400b4819800d038820300e03e040384a88035405110040c2e1140724001107082002107281c0038001070620192501000000e066901a943d06200e075582100e1102800e807110b604603c1034801b040802c0c003c2c01c4008105845d00c100c912424a1418160322449180d4801d500402243c0310f41d00321fa5080e00300f81e10003c6004c4100b81050180303280c659640c0c03504400302480800281e81a5036041c106500e628506100c0310f551000120380d0381c000e10314040030442e806080400084c07010360060440340c41e03c005007402d040c50b0202c3c42c0019a007503a11403240341d884801da041080802c1c460b100251200b4280b02c003042c03e00d502c403c0c12100005092102600100000c6010310460300000012030341c00800b02da40e21780580c50000c0c83c0c91140d00c01c150240340101c1e4082503440c0213494009003e14150020400c114026 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 826583848 1250 826582598 826582613
    0x90308100b190306170703050d23091906080f0c091c0f0b070504090f0c0c030509031f0b03190203030927010b03090d02010c08070c1506030c080f01020406020a 70
    0xb20340082419a01c8100252000e406140e07890f88820711000f8116080c994241a4100600e900c6800c0030403d80312041c04a8060307007640b80b4114074200006680f02d034160004540d140d84c9540041004400c000300010380140d008425074416240850494165103460b221000c1038090320201c035074420321b10911a00c03480709407004e03030380341c640100c00310611780140d501ea0111084054903240d0019600107810300c0b070b203400e0b40581e44520b00c2050782008414208a002840c694108000400300301b00019041155a010000040b00342005920118040c0320b2413410002407050780700047c005c5c0129a5248080420541840311440d0040c0c09141ba01281c401000000d09803060b08001582c24801c03010cc2d503119400f0700e41d028200e940c4003180e40341403050480b4900310213841008111380c10090150901944100401d4100d13420707041c0316445040e03504d000c00000802d29a041001c91501e040081817041c100084812600380d0000e9841c0682070f0a0014240d108a01600003d45c1c13040b0311410008011 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 826585098 1250 826583848 826583887
    0x160203190b19090c0e0403020708190f06020c2d160e060105070f0b0109181703090102090d0b0106031103040816031b0f050f03250f0b0901090308100b 66
    0x60280003d6920384994584650050380e400c00d03594485100100301c00c054040000c1070260003950b0040c130b0700030803000804450802d2000010328071851700e403080c070810000d174043d0b0300c5002c40c6a0940c0d45240c882e00d8110901700b80e01c1d8108001092460740b02c4126000461240f00000410780d005c12490b04105030074421440c040c00f0701e41007080810408021407108000c41555611404003481d9652600c0603100c1910703110f85074240c02c165072046003400600080c001101e024001c2000c161070b591030035401802030141d20750903508003d40c02c5c00c0303100f000402e00586040c0c684586080080c0e500841041701d40740000c480c010402c1200300205c00300070440700c50403d40207110b880d022007011082c40000c83c50325040c4e5002c07120b80c01d01c150a00c040000600110140360f201000460800491000c07001100441c58240707007174824120307004020701494041c00c0603004e4000b001c0031600d0510031a01030080183c0902070300003820703190104441a4108032520200c07800700c01c865081050803194203501c0c0c40ca = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 826586348 1250 826585098 826585141
    0x2106040f0b030c15040e01060e040605090f04030807020708070e011a0301050a06121508100506030d021504020f040203250c080702130923010506190b0c12160203190b 73
    0x10601001881b0803e1a1240d0b020340b456035507044141801105020540ba000d0f0840351050700c0c20703020005440984c003801980240c240c80c164180d900c40310760580c28030045411211841c061541c0202c3d4003492881c1e070030f0407100d2907151130300b00e500c01c107c4030580e44c0021f0080d0b81e0302c0100f815003003140394410303118001c0c0c4202e60400040c06891600c0c40040884d01540308180580040901500b8050b8a104e61580f0903415005040b2000c01305500a464100c02820700d20310510200c0850103540313424030045107243c00075000715541e050181d8400405d5605403907058616400c2001c1040c820701c28440000483e900c40d40341810480707180c1c2001009446081c003510029a10030100d0040398184101f404920b0440e40c0d00d0452070043e542e17090a5500041025010303640b44c1d80011000c16084910400b00c032203c2e1a400e40300d001c121151400c00f00d01e808844491280031600b4401a1003120b400d1071018400c50442da1303101c2e00c151020104145404024110400c44400503002e1400941c1c0b45030307940c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 826587598 1250 826586348 826586389
    0x105040506060d05160f050f01030603021f02070b1210060c0c140d0614011d0103050d031d1005010e13200d020a090c08010b0f0d112106040f0b030c 65
    0x818a07058a5280b020f11b5210703403415901c280c030410240c100407400b81407258081c44c0500c41141181c001c14030a0010072241340d0001c0580034a011200d10a001260181c09114102c03a5541d80d6184200c1502c0420390781400d01019900c80001e8183c081c000c0040d02607070004800449230300d4007030102c05e001c030300c903400f20b42107400d00c1142e5001942d507100d501c2d9034004803000c441d00c65041000305010082e000740045500c08501c0014400700e5000159145140311070b160114000000b0030506d00141c6418002601034401d4410302044d0116941216050b81e800600c00e000036960300d10303411007043d11444041c09081e031004464982d0300706a00c1c49501002c014061507804403107039022a003844101c1d80030030000c582e90600b20200c298401d02c0180101540381046080c61500071440b0840d10500480340101d41e51081d06440d09010341080d9075924030345403102c0d400c0410b5500541d211900844110744518544201e40900c0300c1148210703075403c08050300a00d0781d4298002405080703800a00c15030900c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 826588848 1250 826587598 826587613
    0x70507030c0b0702060103060b0f01140901022d010b0904122007090f0605011e1d0a031202010b04050115081b0c0319080c07020402090d050f0a0209090105040506060d05 74
    0x151140560900030503d07540100543e600d1414000121040c02e0070b264031510355189119a00da03444030035030312440840c08001e599010b1100050340786c111340c804c0e050710462080d806031541c800e00252240265074a24001d00c918011070003000742402c0d04603401081e21461403500402c15114002c1c022011a2185a55884400ba0b10480707141100c00d9202100c4646c4409403d00755182ca4002c0314004d220030f0030b00e40d0108080400050701900050a1302003041700f945094000236840d5000d02d4400742c80a420030031455100d041c54020401c02c0a8200055030030000c04106134202482000d04882c0000c0281141c1c2d21001c0040f101c0c1200a010b85c2d5211400d20201c0401c0060b500042070f10160b4100203503500c040341204241e80e486040b480c0820710070000d0030804504c0d122802c4a03000f60781118010781e02c0d607000700000c54844413288050041c0c4540d054050308403a00081100055000b1107d60126550346201103098904c01c0b00c0c01440764001001103280c81c240050000ba0051140c1c06444a2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 826590098 1250 826588848 826588853
    0x6030b0f06221a09270709150306050f04080a0c03050d0204140a0801060305060a0e0102120108030d0e0115060305060d0512030601030621080c010207060504061a010215070507030c 79
    0x9145000007054000c3c2c0d9400316151480c61400300304211030001d5410010707034686030060208007658201c440c64000e07205040414045001d00000700988180082000000c8446141c900b41c1303138480c00201d501d58985408124000e8100d0182ca114a505c08010f9240c0600040103c0d02000c04805c21401c0c84401c0c003030001401458009840907001c41c80c01074124503422030030000b462507564089003d99140500074000302e080480d080e54005405803001c690541c0180c02e0a00a11035600001c146250103000455601d0020004240740c40036088103100348518201081e00729940d0300d2600e101c403000441c00f00513060280d00a5548070030020140c1e03654800c551100d90a0000c5021070340202c450010030001d0315030301031003108041c0c2500b240c660111460759500516001d42c184001d03045660201e0381c44240c4009404032080164440414000307030405c0e18020307001d40540d2900721036403060100c0c2048254800200d22500040100c03092855895401041d00c3c81d5020031019001c04c07040b0305445c0302 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 826591348 1250 826590098 826590139
    0xb0720150a02191d0418030f0c08041e090905060a0501210215040f03060209010815011d13060905090d0c050d05090604050405091e1c180503010c120506030106030b0f06 74
    0x680904210501b0402800da160051000c9040448603040c01403c5408001003521001a40c0c2505d140008100034a0181000c5e43c0c04d400e0303107504c248840c50a00900808100002c26860b020321504042408981d0b20760355902d4a040300b4103d15400803848040a04c003610705490441c4607444c01204003468583c45172800c000f07059580e081641c80350b8000851504950780000301c6a841030501d00c6241101c409080000c054016410b800030004a40a00c1c0c582250385039528501b01c5410f40b002000143e0b550b00400000d0f100032101042103005641d05075400381d0240782280303045a80700c000f524001601e0802034403241c01c120031641e00598140400b040d9a100c42c85078074014082c1c00300808440440707044840040c101040b9001040c2c00c0302029801d140c00e041c101e0303400f44800d03082c94032542d1b8a04484100e040c6291303020701d5142d801e0000d00c6d9806500312007a60510340070f502c030038045d50341c50000303150a035000381c40018040b0105000040c00c0d1a43c0341200307a00320390024049554a4aa40e40025 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 826592598 1250 826591348 826591361
    0xf0102030313031d121f02040f06080612101406060703140c0106080d080a0b100e100210050c0c070b0c070504020a030213060503310b0720150a02191d04 67
    0x425440850428400c041ca11100d0006d80d402032010b5150900300080c0c650890450321074134040c4202c541c0030070040e9444c4450a40c44c003032000115211450481018030240507500440b40c1d100e43d02c2c40c081107241c00e1820455800a8046d100c01c80354807103900881c60b495001c0030118070295690300b07000ca000e81091001e01c00300885030f81c13041c0e50350411422540445100343c0200b8420249140001c50242e007214232806250400c880707105051601240507810311140c925080501c601d0100cc024140c2081d138080c20913080b0040449100544405a0a416101359230404056034400c450802c01e0f0b1803d071300140040c1400340b5015081a0100c0805250214581c02c10782c08548040300304010f55200b13050700c000400e050206c0780b40040049103415220f059100000d0008541400040c120034003810941d4898046200500044001c40f5141500c840500705503100c243c60807000308110441038003d4403000d0a40d040c84004e040041d4001352281210001c2c004803410240034008000c4c0d03514420038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 826593848 1250 826592598 826592629
    0x20307030b010b0d050108030a1d0d170703030b060301140d170c0601090e031804051e1303182616060c050111030c1c06030f050c0f0102030313031d 65
    0x613034454400300060015928141c000301c4d002da2050014140da203600c1001e20603401030080e41003c1041016000c41c080007030305100640f101c0e0a0841c01020358060100400d1480d00a80c3c08010340d511502c00c0082c0e900c002e21420b914a80144c501000900e003401d820703041648500c0c009940308140458120039500680c0124646400807001080720411501410155008842c0511300c0e00784207004075400c40000e140400d0007165900001032920300c0c40c1d01a081c4071046141100c0c2646421861504030102c01d650841c00a036010729500e50349404011004c041c4c6100142c8100c9184103d400b00d1405040000c44929070f102e455070303044800c90380d140054050001540c0d08900c03240b41e0f042c0642510046003030120805410010480d101d5264000e5640c0884035483c1442d82000041102d030113071031550005842449411008800c104d40016110400c078419140c40241088039801aa2030303000c11901c004800d0f80321040800041d03c24162507012070440011040c0d03003541840450b042c03d003007092a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 826595098 1250 826593848 826593869
    0xd0f05060102150106022509090f1e030903021905120c03251a070515150301110904021b060903120c0708040506090f1503070906020105090712020307030b01 69
    0x18080c0550307060141c1d0781546094086000b0302c1d450b0140c0256201d0500d055200010b0140390f1046c204006040c0c4040101008882441201c401e41440c1c11070748040b542c225140c8102461142d0710303805c166030203101e8540588500902c90725540a020105ea61f544041c000038201907804a115038601b580342c0400d088080051500c4508a810315160991611134400c2c0081366104090360700030030300ba42c00c05031002040030741880141d0740b07012407a90003882002002d03030240740c0c0b040050683c001c001c00d1080c0460300507010702090300000c3c1800c07140d450242da0011101040101070606064004107204520f0a0b0005c0f0060b5440078103a0404805a603003c0c0d8079040020b06c541400c001c1c101d025000b0440500280c41c100469a42c0d0b01c6a21452041d18042c100101c0c2507070156984450802c80d80768081c2040300100c1c1054285181c40d40111025008254402c001056581c41407080c984692038040003449401e0419015002c0d50a43c8013003260b140c81500700c08400242d1100000f40200320b104603 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 826596348 1250 826595098 826595101
    0x105191b08190e06090c0f03070b09010504150201320a150302090411270105090c0c01051503070b04030c030803040618080301061403090607030b010e060f03060f1c1101050d0f05 78
    0x180031b42030440002c40c643c42030900c01001d040d2640e000c43e22034121201d84003c0c44d40d8160703174030041e00c0c680150703882546d00d4100019100380054064004a0301c4070304641c00e105d00c0c24500001070750181c40b5080d100c4109a1410300103000030080b079210658a400072168520002c0d0b482d40003a5442d00116000c0b0340c64001602e60704614107000030403200b80e81595510b1204000000020442c070031051283c14442c480c00030200b800003000c4000c1b15a68142003000b0311070791070a460406940c480311900b1078000e1184600004100112070103881c140c1e644600c076443c0c420310f59180c00c469504040c000f40c80b25992200b0328200a082010707410f510038403d50340c10b03440b50314214004e06180801440c4440640007001001000d41004c10110f0740181c040c100040c03605e0482c1c0040700c190b00060951070300650005815841c0051107409180f103428102d9103440c40825050900c29800264044000484600c6c0d40760b030005104400096501c0b04189006410b2a4000400c4c5e03083e10381c1502000c607020f0f40d540 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 826597598 1250 826596348 826596361
    0x4030e03300304080304150902150903120f07080732011a06090105070c1505130506070f140a0b0a0501180902030d110703080c0105191b08190e06 64
    0x100ea0aa0540446078094114501915034400c18400280020032000000c1c4a0f40881034441c3e002c06c3d00c00750090000b00d2191504d11445545901c22002e0f184640300340200004801074410454905628044500f070a0000540d20401c007a04104011100100d0303034000004041554201406546031395402c1c2d1008c1d005071240c4a0844203000b440e02205400e42d20144582c3e2680f070120384800c40c00307180895941d21a4140300410000541000000020340c044949115a000303001e030011028940088143c1c550380e4042100724800c1d0000104450550b81010300402c2840060b00b824111600075070b0202c4580c0e82e182e04800c0422200da40340c2e2550703240180400d22078507084a4a52502030010842c3c1001e5800007940c4103000c4074201c0402544c4184c15200500501c200c000841d401803140d6200c0030f80406540c00b8107400c0300c035840000b21044c1101c2c4441206d004050400e240085c81c2c2c1e032890720880b021030311414010320308440c2103280194a41c0c241401d1103680c68011403d009001c1c94207054 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 826598848 1250 826597598 826597663
    0x60e0d0801180504020f01050708070c03061b181a0409090c031103150a0b0a17010905280318151d0d1718031014010905070f030504030e03 61
    0x9202e542c526880c01c0f04000040c0c841d0024400795090900300b01d0b44907401460060300070b210302d80c001800808803d00000c10007000750484600030070345940035119100003020480e01405000c50b01c0081c04419503041010720300300c24a59101e0304899070341034981602c400c00719080d45c4402a00f01c0344a081e0320720130414001c4803000038480c00422405003204a5113110802410a40a0091004c5680d00c103860241951002c05800c002c3c0300c0245100d040c2d140c0100c00390b000b8250194240c90901903850001c1d50121840c110b040040c0390300034601c1030040c164408864220103200b803000d11004e030b9a80401c40034a0703c000528a6045580e030301140707100d44140e4481c144403031080507000c2c035582d41e50100040c0000d4400400301305080503054950301d03480b001d100300001c12509150103005040410110b50b0302ca41007852100302440b07403448d0030b9036180d03070741412544112402000103070500700b8003941a00ca5003106401501a1030710a1140ca0480c000a040c80001d0400039080c0d42101c10902002060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 826600098 1250 826598848 826598879
    0x510030e0601062c0f0f04200403060506040216030507020d08030103261303060e0102070f14011407092105010519050606071205220608010519031e060e0d0801 70
    0x4070702a45580d55051000c43c0007100c245c000c452203000301c00c2070107140c0d403100d07030081154000010316000c1c50001707400c01030440d0f40240010380d080b038242000901e041c20a40216030601103d07076205490007216840844d01500440c900f20780c0301c0140100c0f500481c901c6000b6502844c0190310102020304000240205105010316078a005d00c0c041c05485000e03c40401010100e0350402400300d00f660b02c0b210150300a2203402e00c000c11140241c0c0b06c0c003050181d04250701d8942d8511304004c0042d003640c2082a01c400000f100c21400151150b80140100b032203040140000d1565020005080d0005955003030a4071003c80d01089241c505010302540704000c0d0042d250400b50035541c0a240200b680c80d0003031b10249400d184400c3c01800910b035031100030341c15240a103c103502013000c0000c54840701c008044c00002c0c0f1a0620a14100111034150f118038a000c00c112a8484003141c078017841c4c0f940500901e4000b00c0d00399009a642c038200000c03540284500f100461596491203d951304007440880e15503507 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 826601348 1250 826600098 826600157
    0x30801062d08160908030405040905031b070e0708012115090809011403091b06041229090c09070512011212020d0509010c2306101203090510030e060106 67
    0x40004c1c1005021408011141950b200f6503010601e41a1414054958421806a0307503404083c0c4142c011816000701c1c5003070680b5101c01210780c554480400c02c9402c41070a0207801d40c060799004201e01400031800c10052001c0c420051480c8694030541540d04035070602c074055410040002d0b01d00340940e408860404c5400c404100c243c15410070700e03103e0b41d4407058801c841d0138038500001070000e1070f5107003800d030703401056240425080c0c4400791030b0641d810014540d40d94044a1100d080044082b00b03070052602c9001e00c54010688402607600704010030402401c07240a0110800c0000c41c03413110240d206010b002084101184104585070084044510030403034004c54010101c030301c00c035550100442c0d030b8803e002d03c1e25161080e458141105040800c05d801049500110180c1d011104042016880b079000f418001030110368400311800c1030301003500e004000070300410080c400c1d4603050004541c0806140390000d1014410f000d21450020280c01481c049520071964010505000c000c1790034800c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 826602598 1250 826601348 826601357
    0x1051302040c1b060b030f070909031404050f0d03050921060619030b2508240105070201030207210c06050705090a06121b0c140604030801062d0816 65
    0x50710b0316203400003500b40f208002d001c562070b198a030260f03039010442802d0028002e03003a190420fa689a0038801000110001c41c0862100c1549901c42c01c80203081c0c5040742d8014055150803088002000b601c2010303c2011030500206101c03a001c0c44c3c03110999203d800502c1d0209111510a0b040a0391420703130000c0c0306030312504001c500e200490840c507188030201c80c0c0c0080d0401050700c03001c041040c5000d01c10058540da100304a58100256030080340e05e40669203050082d66000410741c115100042241600b41c0400ca04200450040d44250b00500a40e4004e004402c103c09010b4480c110000d140145000040e00311003814040c0255031042c60380200041c18054030b460fa00d100401c0c80f4101c1841070030140485001043c0610815401c0851f00a41030f110004078881d0080d005401020200000e503030b050b01c02c428020308940c0000300301d0300541d0551101c2250360300c0c003501181d26407031845e9900c0000c06001400c2c0420b10002c200e9800424140e1108500c0d4030b801d04c0c481040ca40400145070401c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 826603848 1250 826602598 826602617
    0x80405161404021b06152b020d0c03061506030b0a06020318030307021e090c03040c03020108090a15150605030906220b010807170a17090105040f0f0503012904020d0e01051302040c 79
    0x210351810340c40382082d90640d1340d1080484242404003140400c0d41c0040c00321814120000d070400d00e0350dd401400e0b42c8c069282040714142000a0001d1250341b0b004101c050386c01080701c946c8000c1505121070268100400b00e0b031400708690701281a00054a01c4000c11690b1407a41d118249001e510143e40b00c5001000b19055190944a012800c8042d220282c1400008804111481414085000440c1d000154414140b5040c02200002e210414030f0740015070b40c0314030101d4000d100c1e0048078000d034001c000800715921612510184130044180e0017802b4040442100c001402d4011124000c1001c074001e4000949080000d0660341d0f10031000c000b1a030440480b240c005015261039452028003201003540301d905410050b6101e20494000325170441d2884000541e070540706d407008003611416002401501000e070007440d030906821065003200c1c5c1e0b245400d070249007860703801780500e101e48403808907042c0e210a40c800d0860308240c42820041c0c0890a10b0010750429000c0e50f00e1300b030454030f04607411 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 826605098 1250 826603848 826603909
    0x6010c030210090c030605090703210c0b100f0e060415062c030102161104060e040f0606090e03030403020d08062815080405161404021b0615 62
    0x407009204428500b5580d21980c0328180071001d14403501556018100b04241c0c24000c44456036400349200c1100c51403040c200482044a8813603070410410040d03281c0011108203540c8005120038010645c190302d009a241c0081d203840d04081c420002c007031100d0b40000c41e041000a0209451100202e4180a5800d810402c650b5a1144510801d1102c0c0725600325408100350315119007450008145078558000705007540b0070034060703003910400b612941201e40d85c1e040d284240800d071002c520131500c42c10104400200030641241c04c01c401a0305c5102c0000b046c58035220190200d440320b8400c01c40591001c401c0000305901001911000c0c0098200402d184c6049070029440884d880ba000401c00a00c000c1c1c6c0308400410440d82e000781c10140180000b041086200611140c02114103581b00c0c03140300000018405141c564801307580001c48c00411241ca50000c0c80081d50209120703c200005003058814280c10a1240c903020b01841061000782191560400c000581701340005900c404200b03049100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 826606348 1250 826605098 826605103
    0x80a0201050a030f0e0d050a2718020f0d06051320130503010204030809091006090603180b010312140408061b0f0f030612010912050d090c0806070806010c0302 70
    0x80d030110503d00416800085a404400b61a51041030750417482400d500d460700c250000d0140a031243c41c1d030350724201070080d001208507450f400c0030142221040500103200b00030b00d591180c0d000c142003200240c40e11849805481860f03000308048030a499851205204c2450080013408a0000ca0101403100d102e12800340300c00980b80c034180f590410340c000b8240018890040c00c100042200034000c548440e5681081ca8082e0700100260b03108078031000001d60314140710f40c151401d540c041c2c2d5614001d00e0521034168000c00001200305035003000c014844c1c3c00203a1980000c1d01862140d050711801096600e00074101d101c3c4240030303130b4851009200a106d101400030721070f42c0c03000302c80280100d056213405210601c2d125a440d0074003141d00004240d244050348500440c061601a185103040c0c090340da0140b400c0b03804001c001045140f032803008c0d0700b04602c18400b62010400000c400600c0141c280d803101c03074001056000e02d081360011030410400c59000364509070321410a082c40425000c403554000d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 826607598 1250 826606348 826606357
    0x17190305160e19090911010809070810090201030905100c1218110120061e01050f0415090617071509060c170427020f0d110d020f0301030606080a020105 67
    0x28081c4840360004811003483c3c2410070020001010204105405402c104080c0c00e80f0241c030301c0c04104800007041100c1c0c000903404049640840281808006684030500940b10008003030741010303210301d03800c4003282c02070111071402104000006061800c8a02c040d042c5a01c500310b1000c00352804509840c2d04100c494105141c65008040300d410050020051b5201001e041010b0025142d44018060002e00090781c2c60090351862000a405400444405c040e42400d000d190b030005590801d40b9820f0030290413681860322090100840e694a40c04040100c4e40541d104540742c0c10455154944004140440406080c0740300b10ba0303a419902400242000c0b1a620841e020008002d0022040c41404204c01c82807410303000c04140d40e140c1e284500588280001000e06c1d0590f0b4480303c035150809a44200c452016400081d54206100c9205c1403000b00380c00c45074280d14280400c0b100c040b1405510042c0310300010f8045031522541142000c00440c1c00075003001900d81d200c010948050f0781c1000545 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 826608848 1250 826607598 826607627
    0x512100c231b0105090f0c0a1a0c0c040c020c151303031101090b040b09010c0e0a120f06090605090706031404020d030e120102180d080f071719030516 66
    0x8079034a10b20010389a400a14114145506510700300134010078890109002c402c040d4080100c503c2c07451700782c082003c08000c5100e1034405a1140800b400c2c401c1d9000c1c0540050078180e42075588107075000d030100741078074128000c0100680082d9003050040c81d1403c9440c403403030500c03005182005107801d01300d52001028000507081c01000f4200c20010042500030f2152140c0c495800c45150070f05141c5142d251405440700b195550038000f01e00e14003032190040d0601e540c0002c0021409034035100c410703211106144c0060340c181010000d81400b2800c213010340c540c40d510840c40010245003090489062503803d800c9682003500b040c40c2082826840000983c0090301140c2c8140400c5c0c0700d00d003e503061440c0c0051940c210fa4510700b0080d4080041d03000e030180c80719591040c10410712420801a1580f182d00004207824020b03c0414203039442d90000c0c01202c1d2003251900764201200305804c40a8002d003607102c000d25540204018295410700849810900c81004001500308030000508a44c0d51640d05 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 826610098 1250 826608848 826608917
    0x41b0614041a0d060e040213051029131401081603052205010b13110409050c09120106180612120915050d0b030a02010c03180512100c 59
    0x42c200310a9950049440c95006440300700f2080c0d81e22015404010421a000c3c4e1042e90040e14800d51144140a1140701e6004071b801301d0361071420580305c2401101ea4104609035802440c3e4032031a2405200e00800c4e03280744801000140c0c91806107890450694103500038100014078040c0103008988400c403c002546a0802142c1c40e070f0341d41e103190385c20641105906840407051420205104040d0b020041c4a41e0030b0f1018001600000c6200c800d0350308042660180c0502044100401d1919900aa400841c0751041c18645580717400003420307075241d00c210782100e650340b00800c00102d900c440380c140c6900c0b8110014001245802c0640d440d000c0b1841d0050719094042e5180300f0140c1c440e0804001400b8050b42000001076070381ea00034001c0d00074060b0801c84514056410840e4a00000c003e0f0b29190b051707441d000d0000095908941041d640342d0fa2a4074403445a02c04581c5030388005403944900100c0d8010f116140d09188007505039007041c0c0c0c00c04180084d0f458000281313601550a401000f01c440007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 826611348 1250 826610098 826610129
    0x506030f15131109071701050301020a0f1b0204050c22050108190608070f091103091f0b030a0305030403080f15060901140403060e07080d1707020a0209041b061404 72
    0x105101c954400c5101158007900c154108403441e0f4000020b200c65010001000186c1da0701c68050500701e01c9080318500c041015100c05100780380c030940c82d83e014203110110190049a0729404107054403420317108020302c604081149261043c10003545020055003041a05138946402d0020300008400f80c00d00442c0c03000c0341c0a215113502107421941c01030201500321a03003140c0c0e0b000c4440403d5018021500054203060105001141e4502034a000d11101005020884584900540d4580d041030441122a85030342d01d80300c0d140e50501440301e4160183c0c4079035039030345014500144000e5000744030740c440ca45100148080c0d00381800d41e0941c86401500d43d83d03940c42c0007800590301c288031109642401e5500103004001c102103904900700b51028001140e52403629080700310703290116055084000740441504c0148640d0307403001d103074014407240181d40071300d50b054021800c40c3c00c0c00c803410381d9001d46c14200310440e0346208401780000c100600c4c00c1c0d0a02c0b00c424806624520a80c426601c144210302c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 826612598 1250 826611348 826611353
    0x50103020a06082d0106121a1c050607020d0e01020a0b0406020d060e040c03050d0503010e04060b0a0305010c020706080c0c0303011401031503030f020c0d0b0f0a0b0d060506030f1513 80
    0x8413980d000e003c080101c85180d0940d21108540002409039400048011465000c16542030050349085c0380a071850300e1001b01d101c4144089448551032100003040074004d0303100416002d004041c0a0026507026144490380780c140035021380c00d4104481e04643c0b00713034443c001047d4040340003904650300400250350384c00103c2d0038102410058004031b00e082141424401000301580307210302140d00c1141550032490040f0001c1c0d071140800d1040702c0c05034440000240000b08030ba0b0040c443c4180040c01c00415545a49410f421280030b481d030800540d120107400d200c200d030082002d5511404110303003a85030130040718000e074685c00188030b1811031240d02c1c040100305a000b038000e030104410990305052a2507480c14002c0c0000301303030042e40000d8062102d01c0800790804032106100c160304100740c4942c0f030701d406403141c0a900004062200e02076440701c030b03044030b0f54401d4440181d160180754049140d040c51801c240c10070203170800c0c41751961b02c40082201c4c104031000392103512101950f00c504510200d070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 826613848 1250 826612598 826612621
    0x5120121060f27020a06031506140d020412110603060f1212130312021b010e1809030901031a2b17040e06030f031611030a0503070213050103020a0608 66
    0x2810f0080c144580720b000800050030000c81e800c2c40b107008943e200c04d056525042942120080d075a0103440c6440d402050000318010040009c0b0903a08040c1c42d0700d01100200c60504903006604120660700d8880001d105000c1091914040000221695440c0d0300703260002a44000d008180503004009601f2a1480d480043c055203406007140c0803d550389140351680c0000d50b030034600045610f9800050015003462000401400400310312082c440c45040c49001501c0d41c107560014182d10041302d420078020200230401c414002d0400500841d1030b840b03107a00140031f940c840490f0014400000088800658400b84011901201c3c01c9502001102403041e641e24070111070005410700303c14140d4401c41c0003e0340b000b0400c4402c486140781c0d858503540304040c0c440501400b071810a9109120b0301c80301c614024200080f05201d0b1280048001300f500120741041b240074016103803030b04003040c80810350400303007000c1440503540c0c2c9041000d50b0465000800a819038010720042101910010303918070f100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 826615098 1250 826613848 826613861
    0x414190b0d02090a38040218041a0111061b070320060103031b020108190204090e0f07120503030109110d0e0a031b080405090405010204051005120121060f 68
    0x15003400f0a500e00814208054491658040034200c0c403110b0305146040d0002d0715030341d9071058514420b210044142080302a40104c140034081c028104e92a032880e41d91841100554861100000001c0301d82c071001421075050101c6540940e0004010860340c80c6280030700b810340280000c0c0f140e44512560908495030150806081003011024189616119000030210304a0b48a980c0e841410717a80b86021b80d44807000a400240420690004941a0100e13828581800e00c2c00c0500142019500c4c0b0306041a601c3ca400f080e41180c10050440034400014001c3c0009003d8202a4180710305140c2e854a80d60b10051080820403a50340d116030940a9182046404c0500d80c2a07003070241640a07140e954844d814240e0450100347d10521201190440303410868025400802e098142454070003030010840d0010803c80d02e5550800c40410242e40d03c54401c091350000da40e80036264400da103185141e1400607044001c182102c26801803824003010061502503510140101d05404080300310805800d8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 826616348 1250 826615098 826615103
    0x30903051615051207030504061e0e0d09060c0809010c20010e010f02070e040219081b06090f131b030209040f0b0a0312110d0e0414190b0d 61
    0x40e561601d50300801840480151018803070082c1004408050948043c0300302d44007240b06800540000315424000d07400766a02501900000c1500300322001c0c20540401ca030640c40c02500d60b902c001030707118039003000a05081d107034900305a0002e504019014101410200005000c1100001c0c0c84d00680d22a1500c01c1c0c0f07042d40507140c50385020b01801210001300300800100d001601c880c04451484d886a90803141c00c0d0f4a580250600d9401e1151006116100a1090f6040b0005075000d00c04220441030181c021310030f000103065110b0307001800d0400040c5d40c2d40141e119440501c48451542c5d0b0300b588003071408801b25003810401e980094610b024000382001c0c170303049104080b03149c50120f4140d0003c00e00310504540802c094581e103040c0b0011100c0c071201d01500180226070500c00201d100010546450141c20030450444c21030081c0c6151118003201500014042160b041041c2031502030100d0100c80c50203248110318000d0341c2c5181c0d03200b40c40ca8108860351030f18440340f00f03a2540c4c400b61030040c1c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 826617598 1250 826616348 826616353
    0x14030903010507090501082a0a020c0d050109020102060c03060a0e18011401080c150901030b130204090605090108060f06061c05090601030b010506130b03070e100c0510020f070f03090305 82
    0x600100064408411380c40f80b5404982ca5000041640c0c42c0c02c4620070b82900012844070b01c10f603e1744100040e603009240614103610405032003a038250b460155801180d44918000711b0342e00c3d990302c00241040701c06811189a48028401e202e10f503560342c01e00c5001d5078010340c581400c507034400540c1180341c0d007651040c407020751800100c440e500e41000c0c5280d0507604e400040340c2c4440801030030310240c0740504c40001c90384c000074010140107601c03035001301d440c0fa40003d2000e1180c00c1c030341c3d803181b080f64000d9002100d02956030b0303820809421302d41a994010003001c40540558a021012914583c000400b814824100014080b49101d186110000640d86818007040645003840e0f0701690791030207000503264201010000240d915000040764404520301c4424910545880704040d09504007a00b00012311080f402055001d4a50200e50700036000141c0e42d0020480550a1507400c11280c0d15841c0c0c1c040c1d00402030140a040f41a00b110140c940c401402982051541070440e0b262419400040450 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 826618705 1107 826617598 826617601
    0x30b01020d0e06131d06040f02181210020f09150a0210020d02090904052a0a0b1b070f080d05030105100c14030f070b011d0103140309030105 62
    0x50340c811004d0b0030500b40c903018000e40c5141080c100108800c0280c1c01c0011914182c0250b003500b14901600710314242180d004800c13288880080e55008400d001121081110104004080700019180464807050701802c48941030303100414043c8544140706600781e00c219424108d5511800c16002418040d0402c01c024019412410802940071b0b800c1c82410400e8a85845c4941b007680b051018108a001c100c03030422107400b1441e02c2c0c92008403c1c50440e407490300c4c2c14800701d041c1c540302001c0940369841175040e907d1000380074030302040c68010140d0008001d91001d20120564940350305469103112580d104440314002445141e0307000b0080d90529800c103018412107109280501c40d41d004020710504040c0c46d5a00414008d10f0003d0b00180d22414040b410282c0c5024203000c0490164440181041e09944881030001411862600803603130303403c0c1001c0046410051000c0c0c028044c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 826438848 826618705 := by
  have h0 := BRFrame.cov_init 826438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 826438848 ≤ n) (h2 : n < 826618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
