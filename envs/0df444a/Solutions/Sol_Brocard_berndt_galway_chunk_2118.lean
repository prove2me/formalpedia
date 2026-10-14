-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2118
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:41:33.150987+00:00
-- url     : https://prove2.me/submissions/d8e4e9a3-47d6-4cf6-aaa9-fe5b99c99981

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 380755395 ≤ n < 380935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 380756645 1250 380755395 380755429
    0xa0e01060803030118051008030309070504060b07021e04271502070206090108060f03010213051915050904090204050a090308160f03050603010e010c0f02010e0303070905061803010c030b 82
    0x1c11589456000302c483d00300b0a81e4a0340c103c0d12030300842c0001d00d9816940c400303059408e041da41c4030f150100220303585020303078400c88e8440d50600310300080050300001122249600901003000c0c44004090000640982c0300817983c001d40d48400500c01007140684a070741e50104200301540031481401d1a40031701c28002003507100144100800e03c01690740801b02c650200c0d003804c0c583c1d5550354090000365190310955995801d5400095040c409552540488050301c104966130710703003880f0300f0300c07510800002070040c0026010f61510700302e240e90080c005000b031240024000b1545043c10350216059034420b41d00189840d0300c80c4020000c0541085d80310307903c0303c00b001405541d420b003004001c0408801d50b18210030316586134082480ca03103080d08401210401000207000480e5049401088203650350544c0700103510303156440441e550f02104590113031030240d855581d914100820040a40d03c1641203000c0604480212040d070b450a014800303c8003038644000444001c4102441010102d903c807030701c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 380757895 1250 380756645 380756647
    0x2d1218030a21051003020d0c05150a1403070203041e050a031232180402030c0415170403121407050c0706051303140f0a1b050d05060109021806030a0e01060803 70
    0x304100340750041007130484e40c040720800c082d030095040c1074809080c0e0342c0011360031043c580b40c2811a400c2c014010108006199900d20004003000f80c1c412603404140e40c0c0c440180c208100400c9407107084050a0181c0207104666149c41344d0f00d00000e520100c85500c1211820600072400e030066400030a80e0105040031107900d42048e8002204250702000c0071200d0754100030201d0080003000ca158070740c0c2d25000020b00b0445d80c030b050000100740365811a06c140f0916008002803266803e1107404290740c03100041da044412901e8503039080e102c0160510210059640c0c500c0c14034100307002d1900c02c90285c00203440c1c00d0703510748060031820f05000c42d9070811783c1400b404000c940d81030301c0c0f2904e8070070440740c100d0050540d906440501d43d08208918000d000f084c41541e003650248000c060340d10070900340d046a003c482ca40d032041408821180610080c005400440041000e504150020008002440141040f0000b800001540780c0c2080d40c00020465407103001c403180c03010920500c806000c85500031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 380759145 1250 380757895 380757901
    0x12060b1c0c030311030904181b080a0f08220f080a0b0c0a02030c03041508010509070c1119060206040203060f2509050a03082d1218030a2105 62
    0x5800c0c8100c0030b100040c2004422440e1168040060043d60300c19200103005000140494038410008500c00806403003c1c0c05101442c101d00c1c22000002084407400c1014049102880d220b0300754102000400340c0d0484001c000c070119240c40715035000844004201c0060b8660b04240301509080d2080d04a0030315070f800040030801040b001008964460142c0450503a916402070089045000d9405070009622000c03a02282060a004014819501a41c2c0d000c5041c0e0342c6a080080a074800d0310140003141c9525a898085849444004001c0c4009403801411200303019244403119840d0b441000141c110340180310840c603090200035000000320244424130705042c8141d400c1c2210b00541034a1519154504e048443d01600d101c070002c100041c400445280c7c0ca052080b400d511004040b5400003044007601d194100d501072841e040200b0002c00e0342054000808080c83c00c1c0701501c4080302c409103860307425014104200604104c1c0c120341d900180e410900c4110a5541105020144403034100410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 380760395 1250 380759145 380759153
    0xd09060903200c1e04020403052a09040602030703060f1805130506060105130801141603092003070503010603061415090408032502010b0307050a0f090905030412060b1c 74
    0x2985900f0325040f03818801d00152802507104060340701300d405070080e0022030004280480420041c80c0c92aa842040b002040081810f1100c003a00c094025407103841c40d0007180104005602079075010307429080009083e0f03210002c0320b401900c10b5100006152080c21001035130300c814010713150442d501c0b910003600c115a0381d6505d85c8a0600500c0c040c10000080345075501c6507002e842c9a001030001800800031300700358009040385940220380c1040d0f0000e104155184480c441d2041119158209001540000c1e408111182550910311040c0e45031040541c04074250f2340a114120080d40308400005400d43c1c41d0a1040304450014800000490380621102158a4840704142d109500c014019a680e8900b100c03020303408d40a40304514a02038103000c5114032501540b00360b034841c03003c800300c500b456900d004010f0342e80040d019855100241d4201004101c40582000e40090322032800e80741001d03258004068079142800b015107030543c0b284a00702140c1064a10513408644002c0c002a8241c52911 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 380761645 1250 380760395 380760403
    0x11d040503030705090d060608010b0f090702120d06030501050a02250309061b0605040506060301050a0606230f13090c0c2001030b101e03020c0a0303110d0906090320 73
    0xc180000d200e130000c0d0040aa035a2607240c80101580840304204440d1120a56802000c3d00c241c1035000e42d060401c031184514202e6000c902c51146070b402440624507002e040d00c05034008030b140c0406503888481c0400000c60a02070307a481111104001601c5010b032840b0400300d1a0555030303444000d030a80c0324001c0443e500070b903044c003030710260701f800f40308402150085521403000740c40252003d80b8283c18481040004548140160402c0f8000d0020362214540e4404071401407042030007181d0304e1218034144946455810100c2c0c0200400942400c141f07800d1008158040e101106d086805c0060501c46805c0c1c610900c80254124a00b5018061155480c5500c410241d40755500714070f400c4100c02c078140c0c403d0b0420350004101520700856400c00e864060300512544560401740c640607820241d03081d00c20310a49140c140b80d440140a05ca2880e10240c004009180781c1c02d02080c41002800482d018500820400c54886c0000141e000101d04004250b0342c03405d4100e640da501b02c0d404d0b840e10300100003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 380762895 1250 380761645 380761651
    0x50331140a21080f0304060507030e0a02010e0a08070f061704030f0507050c0a060e01030b040c020309191a0405100207180216062f070503121504060e011d04050303 72
    0xc280000c0032144292411040350000c02c01048054001400904400b00380040c50140b48642d20034030007503c41074002c2c0c041d038000ca48880280e6104112074030140d071003008210310810000c1c10341d9102c01c2c2c540d4100390403c041600203201e0050944400c0114503406440c11000e85401d0b60250400e09240c0d40080103111020300362001c005010900509020061007455007204004002d280015503402d000b811208190f0241804030340303082200072480c1854000c83c1503800d9258051031800c0c0e0003004100070303036041e60110200140503000c04907071268a0007441251a00000c0030680796850002042101011400c2002c119003000380c1c1044515032440300d000780c4e0700400b480580c80c0d41d0034107600c00d000280c50390003a0825040c020300341c084d503a510295051689013146555901c1c4040b502c940424800c50b28011f04540c0200500040c1d440c0080740b0503007140751105060000f130008400a42540c0e00ca4004e0044000094010030103c41da039140c00403040416a10713050715281644a030380d1240002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 380764145 1250 380762895 380762909
    0x30911010c020f09090706200606040513170702040c03021314040212010909060b0102060f070503040f0203030304060c09120201140c0313080f012a0c050331140a 71
    0x110303140d4115912052081c00f001805448060b46144c0a049203544a41d01d22a040208031541000c10405402e0380205540c2c0c60301000911090b101d240a11000b0240105050306078100c01c24280001840250211146800da0451079216071050040008807415912440c050502c100b21841d04c0303c0b004d4160504442c3c1504142e4000c1c1c8250001c43d019100e4407000d4030400b1080800401e21880030b5010b80074041c01079108000c07240405005aa9419080da0180820f018080026820602c61802540d1040c42008581202d5242d680413901d1908103840444000f40c0f10790382d40d00d038194808003e00c000c2000c3c910041b002120f070380000c5c0c4000b400e9260b400c0441e074000741e640030700703142041110201c00384c200070010320a41e07c0403a40d4a50030000110550b5500380031650000f0038159008400c5900c4800c640803400c0000001a903a48810003001c560501052048055401d6861090103000481c4000f07581d99440c00c4e49104110301c410740001c41c40b642c003124030410980b2038000080680303c1c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 380765395 1250 380764145 380764157
    0x1801120311070b0a05130b0301120b100b07080309010c02160e151906140301030b0a021303020603071709060106021c020f0a0f032309041109060d140703091101 70
    0x12410218104074060300303c40494030700041d400107190340c410014015100442c0d0305107081512000c0a03005403000f8440d02000d51b07059076107000850145101c0b503421200c0c0c00b900d50011130391407040c0c6040740c22914042d110f0f03601c0030042056a01c801e00448c400011648051312904407602955003044036140224852110381d200000c8017103810407400c104240700100329401c0f540c076020b4241552110f601451000603001d010346601c0d501c6038000c0d28143c83e0702018251483d40c5180d1040002d400c045042c1c925100a228008090b07100e01c002903001d8801540e80280c10081e58400c8000740001400d881b000741c1c0900010449640e02044007101c084100d41e80358200c40542200700e150119422140c50180a018850005c104d40d48007481007d070f00c251200441403e00404900300a101164544605d82003042711408500c1c05134014100b40006074110740c2000c0750500800e0140c5c1103603176214412a038600c2a01649036050314116070095442c94103100ea91020b603900c0d0701c3e00c01000000c03414008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 380766645 1250 380765395 380765417
    0x150f090c030b04050f090f06010501050d0c0c020a140414010806150d1205180d111201020d0f0b1f090e06010504030501020c16050a0e01030206070309030b010801050618011203 77
    0x48079421000d03542000800c2804582000c0031081c40444003034400482e584940c8a0034004003001013400c604a43c0140c4070681421020074401c07014080c28000c1c82c0821510b00d5100f00182d6500c6100c0f00980651340380380e00800e003084180f0007110719402d02d00b522015101c00411240f2000038041c3c0e031108820707100900c50b90010000c90a07001405400811500030188800c2c84030380c0c08000341100d4440009100040006d501c24000a01000d44000c5c08034103940000040c0780c144480608400b00880c0001481d042c5030180700012909051152404952a00440c51407803800e040a80d800f221a1001c00c020f0703000c40e0740080e000c6940c0348200c2000c0c4c0f1030000019906d0703004005440c02182c0200080d56244c0548090503110520118401c103218003002c00814a802c01e000b000d41955465950700e0056400d50b02000a10f4004010403010021032680100003c0d1000082600030300b080b0b0004038450900e0010090740000000c000c01003014070000400024408400000825402d4209210250 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 380767895 1250 380766645 380766647
    0x90a0b060f1209011a061b0304091109090105040203010509040b090705060706020c0706052d0f0703090e010603020f040306090f02040c09030b06060304210215010603060603150f090c 80
    0x1008204604070400c001141c0c40401c440c5102c0464481d89402000708803a224085a040c902e881c200c0140340c100300c1c280a803200100e4107842c0310481c0f40d0700e081202e080541d10544c04055809200342c0c03118101011907032143c00c6c00c2919110380540b000320f505504642c10314000c92400d4100510241c0800c05071004500d2051003485824042c0c100545040c4d500c8003e03061000283d804444804807601c588900010614030400c280c0300b40303242d41c00c0016011603940c4010920391410180c42c2070080020403505148a0700d07030005240d41d17072003500c4e0002c1992820b000c00c103030002c05a10200915004105003000c0300b20507811202070700c6e8820000a400903590030010b0002a1081c4002e4009150180020b0340f01c2d0083c8403142124850003051055a41e004244041800305540c001c000c110400541130301e088440030241511030881c03040b42e8144240d0409281d80e60403c1c0e00c800301280e6100014412954036004820a05101d0240009200d00d04080d61041b1503d0303119603106180d54085034510f103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 380769145 1250 380767895 380767897
    0x109061512180c031a070516060b0d030f022b0539010c140d0b012304060e032b0504051905030c030d0c0b062b0312060302090a0b06 58
    0x1041c10801036a401902c24a00354600207040d001c1600c0d654007140c011000b128948150611440403507a03030320300300030f058840d0158808100504650f80c0307480c2c070300c3c0080b15200c0c0712240d846580280d9944a60802c083c0d0060b0501c4e400c0706442ca0f1a25400302007803812038060341e040d140030100d498201ea40d10000062584079503142c40d800307980c0c0016a50320714040072182c05465100c11204001700108401c80009032402207901007900b0503010141300302100c091090740301190005060411310380c80410b1481444041001d230240341c0d07410b00e000c03509200159101d0004171803d501540203240c4502d2400807458000c03a800078143c805040f540c4103500d030382d10900542d0010721010700f8442c540c04009907000c03440343d40c90041e039002c0c0c49412101c5000d40b500190711039005034292544003a0301a42e451b010942d11004100701d0f0840031032012085040e102a00508030b820803010b442c03021006601c3c0007810032004107404a2441d0034044240056540c5403046500600c0354840011202517500104550b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 380770395 1250 380769145 380769161
    0xd210b12070302041b0c02060a03090f08030103060605090c1903060f030c05090f040b0103171c0c110d1d0d080a05180418021003060306110901080109061512 69
    0x810840e00380e052950005031410940388211400d11081142c0700743c04038883d02c0800120002500c08072200c2c0507051820081224102620300403402614644035821140740c0010100c509200000040003801500e10075000580011036540103036003040c1e07444060724061440c4482804107440540d00d021f9010360712140080c268911101c4010380d403420300700550071a500c01c450041f03080030006041c804d0340d01c0300c0e144250b511018402d0181d0a6031110340911140100b90441118100080c20104c0d8800d840304900e107240d41408141502d810000030311510301c0000c0c0040980c480c40d90300705030a4100d40e10f1000041c2c801b07103920400200d240020511503042c03901074035001000480040240c1e0200c010104c249006e0045103070207161a090101f152034051740020504250768424006141410390310024119526004c074105407217031500b4044035230310b03050080c060000003003450507960810925801090b141108001c25450121074080c0d600b514151103003040710204800448090030391010030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 380771645 1250 380770395 380770399
    0xd0906051902070f090903120b0d140a02040f051504050c1e3106090e0f18010501060905040e0102040807061b0803150f0405060a05090c0f0313020906030d210b 70
    0x1384c81d81d00c200400090100390030540018400a205446018007402161002500508003900c10f101544a5418040c0308000000550044002c80c074090382c1c840c01000f04852030301c0710008040c10170240c5000729070f0f070344040c80d0301450800f000c0026146460055034039540702036003132444200603945000c44510503020302a8441015140d69040c900b0090543c2d1120841504c204881544030751060718200c03e107104142c0402c8a500c002050802e40005590b0004110940c0c40214004d039404142541e1007608464005404110304021a18160141650902036072008501c2d05d0b042c8002076498140324001d001c240901000443c03452841e4807107144403603402c00b02003a160f0a00c00e42d000030f803290b207018040c0300d5080481c039400790380382610805000c1c910042009494501e0304043c00079000006052001240f000d2205061104084004511403504076166041107d01c40c4104101c0c506d02801e81070180d8001200e1400858215401000c103148207584481c4c08409071240d400940049008a5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 380772895 1250 380771645 380771669
    0x110d0e060c0a0543060509010c060903030f0b151e0c070e07090b03090d0f030e013e0412080904110304060c020f0304050d06090615080d090605190207 66
    0x4c0c0c01c809070030300c0b542c40e04034002d0305100c2444001c4d8410180d010392007107240610600e031134104003143c090b000510190006040440c90804c003500c4040c126480010242c000c25150200b0345c0ba4002e0500c140442000c00b1070740306003010880540d07148180203220080e003494000c610712040301c40101041d10801e21400080781d240c036885444044032401c003521114041100c03440702260214090f41602e219604050080001d141d03004030440d00c440c80040444241a511081090550428040c842c00a501c0082180c85068058104030035045800e8502030400c58010b200054918868215400c842d000c80c0262164401c0e801c119006100303160000c1d50151a0034401008042d841020314420740c01880c04125056007044140c0e00c500c0d4480060f4455001084280083d1421125440d0058080e4200240c0780141b642d902e0f084400a03c1d003040c4c40c043d11502041101c01c10021b030442c00f080f42c90039074101c0e8502400900140190032a48880c41007d80e44541e140f031080004600518580200b4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 380774145 1250 380772895 380772913
    0x80d0603061107060f020f180a0b0415020f0307020d0206031902040e2509051210020f0405030706090e07080618040303051501081605031e1501110d0e060c0a05 70
    0x341c60b99921144003240e07040e0801030b907071403511141c1c401e840080301f82c1852149048881601e40d10450108003007594080a8a100862600da2241c060000313400030298a020741003a45c2001ba281103640d8010b4803550b80308001201c0140c85051681d14840e6047c1d5405499450b000542408422051501d0322002c1c0f01003000242c1c44140d404141c0038101c00880821159064610200d50141815003400844c5220008004e43e00b00303e00b201031805480704c251070460280130410001ea900480b0001c02e003140114081c422441c0a000034001400c250900d2440a8a42102c0004900000340b60340e007031040c03a0000039030070b0b12526400c05a4051140107d081131400c2c0c90050002d082c01ea4010341000e003110100882c4e940281d40319030160240b210b8034506191511412100b0340d000411800214540104081c00030b8900c0843c1402071a0200c101c01e94100000700044c920000018a20b07141d46c84030a038822070315080070300e51401c008140e034142d940ea48106041868100700840040203845a1300c41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 380775395 1250 380774145 380774171
    0x1a0c01090b0103032006071112040f03020114030103030e0d03051207030911040606020703060e0309120a050d03060509070e0402090a120203010b0a05090f0406060e160801050913080d060306 83
    0x74103058a109803104156a002d250b0031109414460300121120b0340404007240c6494020713024202c0d002d40c2c150843e2102e0702d040d00d40c0c0c01c054000740e0044418103801c00c024030031980c10501c85130308442d103e4100c82c1150300d581c400070030300c0010a56050040c80400e148406061042080710007158200c070f0124068108004020b00510802400b0391f1807441d0f1000804040c9080d0048404a0307449a0003401410f0130354440d40c00604d1251841441c0f48030420010000e501c421301180711550b4103201600421105050141c1407483e114988020149811800d001a40d10350340584e80001583c90028960809034020800030b1003424080f69018645110025141c03ca1540d15145984250000d000001c5440140f03e03c82c2c296000766540701514a000801c0c0c5c1000341103040d44140508404a403c503a11038602034040820783e00440c00c040c0000e4032904458200b40d155004200c2a580c0c0e111a1800705269540c000d0504c8008210940001d6543c61072402500100081c41d04841d04110740c0700c00c50300c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 380776645 1250 380775395 380775413
    0x130b040b0a0b0a0f0608060a17030a020f063603031005040b040903020a1e080403061b02060601051614071e06020c060301050f04020d050a021809040c1a0c0109 70
    0x721614600e0406103501c00b1070400c0305400040300d03030110ba403e8455040540603916030340300520081d0080ca0b12440058215010101c40341000c1c1d0980c065035940d9840701c402820601c4500200c00030381e02034000e101240020305c60030110803801c400b45048a5030710610804041d89601c1110000d4407002c03062200c2107901c0c445600c00c6500403102041102105030a200507a81c0304100540581c010815401c0461408d52818409224070034040044244030340d28106960015007050b10f03010f96481c0802256144021a40841103203400248200d1a2060009145204240b41c00320781c404003074880703400c00c200714103100300c0b06100005460b4076a031a14150350381e280149009440c000d03000000040c0060020551030305040003d04000c0c44e5a007403009200c65030040e200b44c0d50b007041c4c0c06c01c2861030a59851041e44c1c05020300b1000940d0796034058170078005092107064124850095481480001154440548221075081007960000c0c0e0308031a105081e40983d1100040c994240440c9108001900d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 380777895 1250 380776645 380776651
    0x350f0715020f0109051b0a09150f08061003080a1205012405030f0c07020f06070311011b05090f0a080d0c030206010e010b0d2d0e06060d1a130b040b 65
    0x703401c8400201d000d180c52800e8070400000a080740d04000c040c0401c080d24003022002c1d141d0060071121006540340f0041c0c00310f1310b0303803901c00c5a40208000140007403030118201c40000c0c8288070061949060003030358490140030600c400ad1648400080044005014038a0b20902c590201e400308655a564060919407a0303082c040710520055030b200341d80c01c85016000352401907015442c03601c040d45d10000721404590000b681a64400102199501c10396034920042c45068800d9586210511003400010b0954803d2034400401481c0040b0300200f00d039000c0180c40815000300c51f80c20001c0e2100d408130380c4840d0742e03412025082c01a841c3d58400345801201c120816480b075421154a80e9840c071825107a81e0302800381c5120f103c020445010f4144240c2c0046c040c0c8080c40c146480700c0380700d0100c2c0e500d078814010052030b02152612502c201014082c03060303960005040c0d9990303440c0501c0f580c850401240004042428070355100c040743c00319805590880b50280e004120007241d041500b05101d00d40021 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 380779145 1250 380777895 380777897
    0x316050c030303040507060807030f1b09050a1d0a0b03240901050402090c071a0a06030b0108070b0318100213141f0f03110f07020a350f0715 62
    0x300e6030400c15040c00021284600d0f08040030700030403800c020301115484030148c03080b1708042c1c8410144c0e25215281c841c01c95003100c1c440d001201c4103440c45010f0401400c6a1120344a03e005142c10804043d10390701802110706044140c5110790781e1444c0304001400d4a000701505803207003100f01c0f0a050b82d4000007481c0d00c648001b122001e5a103904105080c2c460485009401c00c1840c000b00304c40a001170042d2000a1080c2d804007104441080c0b4041c0030641103039a21b40c02501c0716010000e000c070941545004d00103d0780035048a40c01e24140c0111480f01034020384480e9000348480b174228000340308201400c405201d0541d994080c0d002ca6050091081c050380c042d1100c4810502d0f241d1034441e17412120090884031040110400141c2910340d00d1014595005050f02c542c20300c00356055020042c00403402412241d501c03402d0301e00500075184519046a003640e032105101c074803c1c08108a0409908407440b03080c0411034420403a00342000c1c04400c1b460064800d00310003154545940c3c00104000504d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 380780395 1250 380779145 380779153
    0x70603091406010f0302060d0b12071a09060304020f150409050f070206061503180a060204080706090b041509030204050a1b0507030804020f0f1003021c09150b0a08031605 75
    0x10024400351030b08030a1242c1d0741d10b8000081d04000500b001005003034400044100010010924004902e200d08041d90f4000140c100c500d080c072000d40095205801100038400003401e010a00d008600c2d284000742c03000c2d100d820298100344c115a81d1001c860401340d200d0a005e912140c0c0c4805c0c01c1c014260503130b01c0741c1454036284005a040d900c0000e2080c42040c004203076005550070491202d015034005042c0721a1840140504a9050340400900c01040e10850700182e6491501c2c80d004c0c18850307a90070180410100307610400c0f4103600d400c2560140d0704d07030061410034884a5003064580e04560317840250810708220030040d00092507408040943ca19082d80044a00d0312041120180b04412004000c0b0b41c900d0040303409070401c1034030401c00b000068200f0306800d02d15400528000ba9810f01080026000180e20200f00307000d10b821144030401700380500400666581c2c80c9600000d26100c1c40b9155a07400d2030788000e40d0380072a001e000304020320a1341d944408501c00107202102170301050b107080c81 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 380781645 1250 380780395 380780423
    0x2710321c0f140f041103030c0a05060a0b010e0a1e2301030515130207020a09180302010b030601121e1401020a02161d0c090a0e0108060a15091d07060309 67
    0x300d290056114040310f1140d107040d40d842e9520a0408400c40e0395058141c4410300c41d200340104100304102005014800808035880c20724849019541c107492580d042051004420986440d01c12000c8180c0d0910003441d42e590b80800c905445880303896206c00c0b9a0031041c070900e4000d4510f1200e074070b1008801c2e80c00780020b03a80c42c2001c0030326006156000b6042064918001e04507546540600851071000304036000f503695915005054441000702c0924000c001c8660300d04051b0248160301400b80700354094a507541c0341000040712012080070190a648060782d2104000540010003080f807030307000243c1c40864001c0903005000f0f421500c0c0640143c41541e84021188409554403030440d5202c1a01d1f40e10180384d1201e039500014041c26488040a06200b042490b03511056480003400c00343c0f0a28041e036140c80b081d289000d0000c0c0c420042c6514111007001c00c080c1d5401e44034251051201c01040342c01d201c1d918000448030721002d01e88207000d0003038041141c81d03050300682c40d924040d90304424104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 380782895 1250 380781645 380781671
    0x80702010c0905060703050f0403060209030f010e0c0d050f060c0301140901120303020703050409020403050d0905010c03090302100c08030903030a0507090605070201142710321c0f 79
    0x2814500c01d100c0482c124850400c450324102d402084510700c00d190040c2041100c44035220250001d40040755820740100b852812400c00300302010740030949800900c103283c1401c2a8907140e1400642c4103014603500a280c0c000d00c4000c01c0158103d801c42401c44d1b10600e044428100160028000c0c280c602f4001c40364158a490161001c5041e1540c1484110100034203580c00d0b4003c4d0704c4840c0840c1445030501001a10400900c080c000540c0036002811039000702d40c8004040c5040b64029a06005c0d10640b00004030350310001070801e50ba4140c0c1d02c3c41c0c41b00c22104c0d003a07401500c20703e8020b08600000040165001001c00a54050103031440f0500c0151079240c41520034141a0080c000003075001d0001c18055845441d00c0790007020b205100901c0c02601c0703410311105aa5003044107148611034905d01074030b418030030201a4070560b1450b00c03000c0b1800391211010440c00107155028072600d4100e0071850209180c0842d940b0600303004d40a10220440b041300c1005e03190009001143c41d2600c40300e05560 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 380784145 1250 380782895 380782901
    0xd050a02030d031a09180609011e020301060831050a050c0d150213090606030209010f031104060c050f0d0804050c15030708190203190516051204050a020a030f0308070201 75
    0xc86240c00403030540d00688180921030f00000c000c903246c0c85030380311900c2c08120140070307c9001d075540c4000442c1080b400c00c40b0050300c240911181d16454410001088001d6000c00c105800c042c20702c0300034541c148505000070709071580c034800d0461048500c010808100c8002145240584608203035116101913408100c0381c8020300c00044c0c99290300c500380901580300d42e4010000100060441d50f219034803013030038004840d4160441710110354000349128042da0071581440c01c0c0c11103403400380411110180e04000c40e0082d445000240f1200d42d00940800100348590003c0c222098100c40000074114001010050709032015640f5004840e92a2120b080c0141c03a0f00426444003800d41c503503160703030000701e51300d07e0014521800c000da07075403800120b03007020700085004020304450180050040d0024a04031000901a408061030009002c5541900001540c81c821014112030013070356101d0400a0807c0c8001000135489140006c0c04420090013180c09000c05020340c2d9001d2003559124403da0032 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 380785395 1250 380784145 380784161
    0x100b120102030c07031209080307090617010f0b0703021e0c010f020105130b15041a130b032104080a0c03060e2a0312040f14060a0522050d050a02030d03 67
    0xc50f010031610012a01484503890342200300c1c1c00010311100c06803103e111a400035102d000c001440f10004020095002d8000049130100e03140b11281c075450082200001500b602c150aa0444046a80010f05000784850035a00f0199000d1303c8450420986060300e441004410501044451a0310142988144078261060718071009504084d0710355141c40170f1402004089805020f1031074072120759519140620031040880741c04410319292603c08000004016840800d1f2203882c02444c201c15540010303103221081500c4c030095640381c800c00c04a00780c910a680040ca042e01c00c00b40c0e0401000710f400007400c126402268200106100d6090303c50701e5101c8840d804d000003288490200b01440c0060003000850401801c035036901c0c5842c48410300503049603008621006200000700940d04621321130440e100003c45032227250010508001e0045d0092540d80e955040e45101c10221043e0f4004420014260041c20702201c1c0120b807a0603551084010001c9000340035856400b401c0714024081e1000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 380786645 1250 380785395 380785411
    0x8010c0203040e0f04020406080d2a02150d06120c030c0608152e080105240a05090109051819020a05070807051516020105010803120402011d03100b12010203 69
    0x2002d0740344ca41d849004000c0152050b607020381c0d02c250010305c0510130080070318001503645074288003601c0602c49001005414200d5115124040070090041e40d034080059450b10703a441d062031715100101440c0001300b200340c210b100421240d2103040f045c042208403c0e01200d2040000c0059103860fa0720440395190182c66403500305403050040080c0b0700e03000d00000b01c0584280d520741c02c0f8a02c40e0076410401c9030b0540e442c0d000700f6036440050040d030400349031b560100007210b2020a000b415107040d0106c1c4d445400600020003001007480c035466841000103a000b4507009110b40642c140c09624080814401c3d03800407034884100d603c15174240000c5c000e8540c01030340c40d11000c0c10b00f00540c86244081e07002c0c4070211001e01410301e90038102503000040500420411082107030300c40322101d0180c2103c41c181c11004081d03100748000104c9101c0f182006501650a00e071202c07401c4d0752003030814002d29042103100c0d8107000d2410340140141c40c070b83c0210074281044071129560302d00000309074201e22054034034070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 380787895 1250 380786645 380786669
    0x90907031e08160314130306050a020a020c0d0309080114090115032004200319020403020f060c03070c09020a020c01140a1b08070302151e06041a03120408010c020304 73
    0x101c124902c24480460103802424509243c8100400e2179106600100302d820110036064814810303c2041d00c1541e51001e0b20b21011440c4c0816110042c2d0350356032083c00e16102c2d0000000e20b900b0903214007403040080c01c010000744103d82206121160400c0216000c001e90342c60003441c0e002c108000e940c0c4008403508124103840c0e0b03888803050305421480c111081500182c5070035903c0410310030f220117100d40580e110340843c6c99080808071024070304440c502641c0143d0040c0030600143c2d441070709290b08444101d500c1070f84c48041c08501411409080381c0a441001140e200084000443d0000c02607140c00ba800da42203485210015184040802100459440c0900001e6080740c003600d89a412441503013140c407142207141e134036070030542d0000c0c5007140143c1040c03411082ca02e05660036031ba04454421901c1d01d0b00e0a4000d411440c850004000c20320490b103c00070a48100714058080100e050040c0039100302c48003400040116502ca4403030fa800d150f2078012610903c900c00b0045e641911003c803155 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 380789145 1250 380787895 380787907
    0xc030402090f090f031204020f01050705070e04021f0908100e06150d1b0509060607150b060919050306010e1006140f2a06060f09040f02090907031e08 66
    0x311402e5600100900e245208103494134400880400107020f00d04143e0802121528191040c0030054480841650502109200000c00580c01080500aa590710010340030180c0e41c034000280d041d0522190316090142100700301d1071141c0d00506a0054905201c2151103100c246c14202703044071403448801450f81c04c144d0105440111803c0350008032030004140e4200001e0300c0d00c81c1402c888145030003007491640128204800e041c401d800c0c9034400c0d0200c6070356091101d0354403524004d814034060303100001e0360760711003c18560300d140903242c2560700a401c02d810800002d2003010201e610b4040d840c07282c82050b00000b1003540054130144503200200c0f40001d0103107009426903138a1901c90300d01200d140180500882c99070303108080d0041c8080701c0e01200c1c020b0440541d42c0030001c1c0403041d00340250007650411100751a000c01a4520150030345a11620360344d54100385a00000341040290301c8a0403400748101e8200004801c82a240204042000510352001030864141707010402420b1000c14015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 380790395 1250 380789145 380789161
    0x7110c040b13020a0207210807030507061d1b04020315150403060f06090f0506101214040807050d0215040221060438011401020a08030a0f050c03040209 67
    0x10002810001e040280a0a007400110040c0c0c0c001d2800040164002c0f4010070000b0000a040700e41000d11740c4103419443d0302c6823100740c000c2c130600700c000d814420001080f604014040d4001d003c1d43d4820640d0140403548000c1c0962100d400038403016207018040710440b2949081d01c21280104808002e11801d00000320a0250140e107900a0782003000c82804002301041c1700e40515070618450a00c005001400c041c0b801040701ca881403c1c1c3c078883d140804007c1035813180c0d04030021000c81c0f1304110820503010316000000e84101d44c00d0b010310007108070138401006080f00241000b01c1c400c1c022349a00d07d450000481e500c0c4590203076100c00e5004035020901500b085904001401c100c0340155040f9013550006901d009000c0d10102c55029000c420000c400c5c007030a0500307400711a00310b1100303000e40e928050783c4441034060107503000c070750f04140080105070f0081110140103503101300501d459180000020b0014082e07a403204500a04080c00604055101c8003101d100b40d034002e00c0841c440c0c9032091 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 380791645 1250 380790395 380790401
    0xe0a050f04111303030305060a1d01051201061802040f08150c071406070f0809070e0a0e011401060507200105032e0807030c08070315020d230f07110c04 67
    0x41500065031080000740c1e0081c600c4801900130b5400380d200070990341045428400c0d0300304a81e11034110143c81c440800044028010640e0443c1d00455004400001e10071041c0c3c01001d09900071781d81ca407044140b0407160181500030340700319100d814141c5c00701540c2d0740302c00340c4840c041e50100341108840d10009020030405005040510301812620000d1441c070350300a440d000c0c080c0c1d1000046484181480d03e11940041c3e296030118101c1e0240055901e40030404510300740c080d1899006584610400f42002025400b02c00d2001c055800440b103560348403130140071503206680940707110005216441c84000c6250034001810010b03900d00b4070315500e00b0b50144900300c0800c041c0c20314020441210b54840c911030000400341030b05030081d02d503c0f887e510b410410940d1a81c008510f03500603031001c0021480b00c180d00340d4005490400541e5401c0e03e411001d00424a142240980011000080c00c1d00051402040d1281022500810060700c0710101030b203150040c4581e646a03a4040c142420807030601e50 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 380792895 1250 380791645 380791661
    0x14010c150c03090c0603020d0510080d0c06020c0d05070302071e0905090a06063203211611040507031a0409022205040c060c0c06300209010e0a050f04 66
    0xca40040c410703143d5940c20b8121400c3d5030100001130b801180c50800e90485204031500002c0d2000c7e000801d618000080c2d0310f600b0310000d01300501c18100030b04c0050006039012207052481d901c0540720548841c041c06003654009030303001e60061103210808111214141030218581d00c3c0158405e000c00d1a014220000e4080100355420b54011043c0800c0090064016803000c4c08110307000081c07400002000306041d03c1042440100c8a85401d0030710b0980c0c8012401020180f8001c40b81070b8259250b1000210ba48aa00c3d15111454820044041031120348600d80c040c11204441c1888140c403159011826107080020a203010880061100550b1070554031080046e40302400c089070900844d011003007410030402c02d10402d01e40300c508100070015484142c3e03004d0002d030306002c80041c81d948c86400e03103161280120f0060000303624081500a8180d0141c2158101503050400854248810318002c0d40211040310301003010891004900d1825000b8102950409818008100c140c1010000980400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 380794145 1250 380792895 380792897
    0x5101205070b2206020606150702130b01021e071d09071701091e140f0a08030a140403020a0302010b010e0f13060b0304080c1207080307030506030313080714010c150c 73
    0x1140d0740e550b10301085801c0c0f50007081d294020704240d25140e000d0100b611405600300c80404401c0184000607560800310305c00030b0110140002d242c9290310010703494100d07035090044943c40c034405c0400650100090030000d461110401151b60250a024004034403001d990036066a04403030024410421000140c0c04005c0c00d82001013110301190725502c04a4404143c1003003d8054110001e050119a0101080709a400001020601c070b5a032669603c4081c407080091500700c00101046807015141c21085206843d0f4200c291542403902c1c0203507032000a41e5044000d5400d0050b484099800b0703505403550408094000c2c51a240c10741c0c00c000d00c01c0610a81124017a03900d21002c0390800303441000c0d5102e10300c900011690b400700e13404554902600b10250010000b0200301110001d40c021083d40d4004e262811b0110351522000006415030040d520a0071b94820f440b0400903202c0c00000c1c0f110100c9070018a40d207003800c8074900466600ea030702030002d0002400d00040d591400c0c0b0139031040040d9006 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 380795395 1250 380794145 380794177
    0x7030e01080601271d0f040f051c03020d06140f0405090f030408030a080108010c0e091008060709090e03040f030b1b1c050604060e1911030a05101205070b 68
    0x2510900d11106244405502e44c2c1c000503613030603c549580a0401e250b031440f041343d02c80c002d2401030000d2600381c1006000901e007075510107000080060421400c00441540070840b542080d003200001c00a401004031071a400341000c0d4009880798800c2c0c14042080d03000b42c504c082e0b661070305051001030031025010200500c14101031840c0303601c00b40060406421a100516a103c00310400104044010b801502260345020341490016821101ca6024903409031021009a5101c03160011101d10329800f188050003500100314200d9840700c8180c040d10000c8000304000c0105100b15550703030286001c1c1040c42a094032040c808641c5100145a2000c0415880101c0c20300c0200743e20302d0368006940003400e01c1d8960068100901c1c05024907540178000b510100503103441c04000001c11000078103981d003541e00e005200e004e420303025003100e9802040406050340e24101010b0100041c54101d4000c0524040d280c0080f0341c0800e43c8285102840d00680100703e410300300021104641d01101481d480020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 380796645 1250 380795395 380795417
    0x807050a091a1c05010b072010030608120403050606012a060504030e0f030d050913020304050a0b0108120a0f11100501080601120b0f060a0e010902091507030e01080601 74
    0x21086000c41042c06400d00481d403074600348403805102c0f000c0390304040e91160030640103104681070700050350341241d0013020308242d031050101810682d1210318001500200c0040d03510441903010740050707044401e00401c0328450358a00e6101e020305e002c0c50000802136000800840d8081d0311540143c04000f01150360035000410401c540c4114141d01041100d080746c41740c04100a044d000001080132520585914445c052400d00103501d400c1020100424000f0100d2580d440d6218080c00e100e400352000400c65480c1040d0800541d10703070541d401114441081c80c004a031509001c034051201c100d101d4840c0741043d1580c04160741790152040d43c03504100760f10040440c140d20421000c89101642ea20014895050076905414100140c00080b43c0a0618241100045660b00482d80c03222591040e4060f0351103d0000441c81c003a40c0d800217111146010012800c1806940148600201117034114104001681314641c58010541c010b008103100459010955024243c01c07075110394141f41401000c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 380797895 1250 380796645 380796659
    0x2070609032603040b040210080402300706020a0605071407140a0803150307140d0803060f151306170103020f010c0c06090302030f151314031206040b0405070807050a09 74
    0x43c200711816030314541e0701e41c10700c070075410320002510320260740707181c81c0800f890b041c0c01242000c0c1c0d0761003001c401c0c4041c002d0b40009034801c0948a040b2000554144d443d00d680d11a002941c0302d00062083d66007519210215081c6800740c14006022030208101504180082d120100301c11f107855421000d5001b24070b40f043c00940218011840f82d0b141020100d1105c40304c0003410310b801400d40280d60700000012150840e1ba45409480030016400700c5c4c0c0380c2d035980d03484000c6000b01312042d00182d000500710221007540c0d030f1400040c2007001500b40302c0c506115a0b44030101c40315040056a82c0c54080301000610141c00c2812540c1c591580c1810008842401561041400c0c20958000c4000070b600b070205204600d01070021848400c903001c01400f100e0698078100c80c0d6000c003d000c1104170548620400100800d840d501c030300214034203007a85d071201c40d0131490007031418084811503c950303c0e1941001181c50b00c0d201d9a4041c001e02d54404040390b49401082d03803207500c0040e0311418410300d010000707010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 380799145 1250 380797895 380797897
    0x40504090c0e0f07020c13140c0714062a070b0a0209280501081801020c010c0306081504030e01230c0114011505030c1909050a06020706090326 63
    0xa54458aa10700c00103240200c012005403000d42a004145008014804683c0d0f0004024104010459441005c4080d0614a60040143c0e0803c080406020300030402d084880d0406455002e0161a201c2c0141d00040c91403922520200c4000048090003200c0c80d504817401c641002615403802c0506146c50655200c00c0740c089011507030310100c1a00042c50080b10308181c00400c419220000c40d00c501c005a200c07026a0b0b054007800359904010118002902c0b590070707100003996460600000310360b034081504a080c041c1c1740504d10f01c0042070800c10001880000007a03035540350740c402070305680152a507640407500c680c609110760f8104551000300100880b0302601e66240c48084504103562180754804190a4490520070207215000141c010020040c603d0961151040c041c03406942c1d956a00c0002c00f0306000e4004102c02c0f0516140311400b9007500701c441070058480845040c40c6150351090304076900c0c50103005105c0019446401000040c68038030044c0d844040146010b10071000c0050b401d126 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 380800395 1250 380799145 380799161
    0x23030a0c060306090902010e0d051e0c040c0c0506150402091c12030e0a060c050d0e0610050307080c0409020604090908130b03160f031b110708191502040504 69
    0x40c00100030200020394043c4118801004180000e0120b111941c002078510603541200034041c81d8040242820800d091125200066030300c041d00c0040210205206d40d15421104004e020303d00c2d02d00d00d1502980114030301983c080e1321400130101c0d40c0c5c440400c004507a00c290001c0303401c00d40034080210141d481d0013103021814000500701d001c0c08024140308161101580c00c0714281807602c0810040541c0120b54450016000080420761034000942209d542c403602485e0412240303001d80400c07a01d000441c2d00c60203001091000d0410940329020161244000e100354000f03548843d45071549410660007107000d5134002484541001d50302c403110350545086c0f6004407840c1e9030000d02c0d600c0b28510340d1020409045da0b016643d08601e01000000b100b03808a5400005000221005000a51098200c25500301420103c0c0200021680c8060860a180410a91a40170301c0001048040c1d00041e00340c5040148a20004100101d444040aa0400040311800940c0810000c100da4642e030181c200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 380801645 1250 380800395 380800403
    0xa0605093709031803021014120a0203010311040c05190908030706061503020a09090f0e010905070612020c0a0b040201140a08060f0603090c0603100302180a0e1623030a 74
    0xb4000c0700c0c0d441e008041e0440c04055061044034640d0a1000d83c88a1441010070074440c201101c0c00d0b0211051403400e40241b0400c0165043e0180800c40428610b401441c101c900c2400c0800c00010000104001e840740b0110340710004000784040c0150800c0e51081003414000c90812034201038403089200e0a59000b00c20681c0c3c174588a04080006105004030250943c0541c60218202101079100800c408201e2140a03c82602e5500c1c80080d80d10503800202d0f0580050020020361095280c00cbc2e031602c6d50f0348079100105150240603075448006002f16224a86410b014001110326540c0d0b01089036800b6005034104045e1840c050042d0348240c0061482104a0b1900d085074609401000310604900c83c0d10744c000e01092081c400301200001e0002c40c01c2900722000c076169a2603040805c2c1b014400c4c1d00c065440100c82d081c0303143d00940840c1c1c642c02050344800c18048180e00c140345e113542d26848504209001400c0001b00a1001440710040c414540301441c04825070b5180700181c03074a4803541c410f03a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 380802895 1250 380801645 380801651
    0x902060c0c0f0621070e0d0b0a0c051c020304060e0303241f030902010311041d060316060503040203070f030b10080105100605160506070c06050a06050937 68
    0x1040724504050302d01c07181070085a03a00d10342114880248451664030348200350540c414000318210500580266000341806800c90040120ba81040d510345841541e0902d0010b183c030514018072031041c42221850400c9501c9502c018800528110080d400100700756181590740c180354031006e000340000e502401c091807004030344140038420342504c0e003140d4101a1180002010444020031200c800c00d081a0031404c0c0020a240e040c0016005050a603c11160441000502007042250540d00e1125405000d04144d51541d0341000d145c0c0e00c40ca010740e100c031082c603001d800300040c0e485140207660051001c0c05032408a907540c00003000b80740d125002142d0300f60183c030800c4408501700e171003203005000f520001d20044c01c11550050341056980500c204010780010041b40005280b041280c80c01c0d0300c0300c101c41051810a10090403080c10100440d007041c1042c022401d10810ba00902003510002050311815071100c1a0500c00b50a03200740c10f0001e1540311100d4030440c0800c070003441c61900741001c04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 380804145 1250 380802895 380802913
    0x1407260703031a0a050108130b0c0d1a030c090c040302090c04030b1e010b0a0c05120c0d02010501060806040e0a02030607030b03070e0f0703050415060b12060102010c080f0a0902060c 80
    0x19041c0c461202c1100480160f0b03880c40c07211a5240c048040c2101d5080c00c00c0c440944070480d04021140359420302801100118050001e029045c4c0007d014601c3c080031308200d400c07000103441c56518003c440300d0740e25600600c40041c042c90810303465500090710301c00c42e0346001d603252302090200404032100880e1038804034040090103227203030140d9480103100d03c03601c91a01c14140a000c25044c18025900b08200100301010180d0080a407039107066080b42c220b07141c2c0c003020441c50645501c05805804c80e405400c00320f2501e00d00500500b0706880c0c0c1a2200c0301e0540e108024003004050101c1700245c940300d03840c04a005618148035650044c0d03d2990301051107031003003003454a03000b1141c1c04000319030503803030811030400400383c0d20941200040c0b8011403552118285036080c441983c0d6507135481481e03c3c000165103c4500020100102002415070300c0390f580c403005a080340c0f00781c2596804600008000b03040c442d400c40200340e1100501c440043e6480044d00400d1498004028204c0c46030303c40c000b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 380805395 1250 380804145 380804147
    0x3040306050727061d090103110f120607020c0109080606010807050409020a020d0e18011202030c100216090501150c03020f010f0e0105010f03021e0a18050414030405011407260703 79
    0x51440c802031144115045d1741a0004283c0d210ba0511001d41003820b8428480300c540d680c00400c0c04038500c02400807056400460701ea5403100780a480f00005841103110300c500650091080e10211281d02014107081c1c2d60b40d01c0190340c0350800a0485003003103070420020072400c03000d1014103c0d100f030560041444c1c050070380e4094000782d0f1220403103208138000403d21481d400d030b813091641522540e58001603014801d101181c58048043c0c000740d40000013160070305d889580000ca50010b030b85180340c0382d9a42d9948404410440d170080c05429044032a0700701103051240207805566103a0b10910464100009420000d42195000d5844003041a00e8043e07e00004a0900800f40500b0410703d004500524640c00200038036282c407841021544552028103240d52901a140d004000c20b01880d8258074403800164000d0004407000c403004500391008003080d19000050b50143e50040c4c41d4005c1c0301020492620f004d400c101d40c11915031440125610241e413160054414064050f00015220101460 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 380806645 1250 380805395 380805407
    0xa0b4b0a05010212040b0d0605030304060f030c0314040305160602031302031c1b05010b03030a0e1c03090b0d020906071a1e01120204090611190801080304030605072706 74
    0x40700504660010314440304d04d0207240229011240c043e0350752a03841c14807041d1600034101c181e0041c0e034103020108000641325040b071440014003442d80c2d820022010407607016412680400070701d200102c1d402c000100068090401402c0072003001401d07220f0130714640e40708801d0f0b91040759040d1038030417000c20a03021403e01f00b009142c03400015407608103ca140302001480d420f00c403e00d41041d15100e980c2c80050000031750000d401c050015003a2236489191840182450807001b030100c3c014001030941d84042c0781548461524194103a503216229441e00030b1072104c60b004401d00c1e0b000b0542c200305a61159aa00009150f507921032018040684204908215030510080201011070200c00d114a81091100070450540f80801c11036010b010036400420000c0c100030300c008107220b1030000d1800d1048501400703030071501d503030b40401031410b4280c8004441d085828420014a98001c1c003061000800c2c0d50405640079005141c02004403030300003030448000f080c00700105074601c0051001c1c413a1682c040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 380807895 1250 380806645 380806649
    0xa210206010b03060402030705070804080d120c1202030a06080f0a02011106070e060a0903060f1b050403020d020f12030a091a04060e0f24040e0a0b4b0a 67
    0x10000d4038140d031502102011512009040038415540000064007060280c010b40342101e802901494456803a45585591000c032100b0500c08640c010305580d4440d40d440c050560300f210b42d5a503860030000d0100b800710203900060300001503151100408110003004001c036101e005e51002c014142c3c7e821301c0c00050900c3c40010381c170700d803660002001c00202540207a01082d2246054071240d079134a0020408903000d203043e400040c146818600c0200008200740c010070000f548078021805000316032801a10a40705500c402034104103481701c61000f5190540450005203000303041800c03190b4510040c44e045503c0911504040f400c030400c207000b0000789820450a983d02c0410540c42c06042ca900507200308002c00c2914446c04070581c0c0201d454413043c4003110340150b004240d07034005100042e450019045401140c08165141d40040c88070485401041c1d02d001c005442080d015000710540f11001078800d95000d105c0603180c040e806001c51849130307613070000401002110149029010040c40c0032141e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 380809145 1250 380807895 380807897
    0x11101140411060a0804030c1b0611010b041e0509160305060708010501090e010b0d110d09050c0405010b0f0f0403020d1103010b120601060e0114040608010501080c0705070b0703110a21 81
    0x600c1010012030b00300c45c00e0303074005403d03040c0942d44a01d1485c2420030040411046601c9607a0804001041c130b0b003004620250100450080c42020401c805010444440c030800140d581a03c282003901d945039030340601c0c3c000340c1000a540e0a00c2c0c9414036800c0d41d1220303900c01c803241e9104008001009601050a5000d8042440c049111900c0c00d91100d44810040c041c03908007160004150184030055406540f010300c400028540f0b403c04040b0203c01004543c6050b17605000d41074402c60f003840d081c422030b816540e45060543c1400301400586034a60400414451008810040400503036503140715803542520410b12804801030074020b150030b4421a202841c025a9450080c00c000200400c9080c1074411500c0c2c40c11b14a4040b0004a644040f020183c411500c80054049895980a03031a181610707000c0c3c1750341d40f964840f2808862184a4181e003e0b00c1e0b60400d00091040c022034a0007000941e00904d040362018000c452028144104032401300c540d14013400d00c0d0114860500c044150200b11 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 380810395 1250 380809145 380809147
    0x60109210602030603191101020d031107030f0c1a010512030711040e070b1b06060108090a150605060c06040c08030703080411030f101509062301110114041106 70
    0x2100180095881003100100740c0d540100c0014003684040203000c81d4a0300d81100318040d2101e41c280402e80c606203a41076030050141400003070304940280103100074003401040d2030389044215141100d25132100b1034038408202c0011810310218042019a40900501d0074000742254502010010f458242d4008000c20381c20500428011550b1982e1500000d441520701040424443d04902d0510000ea003101008401c0842c071140f500310011641070704c09010764101c41840d112500155a1301d83c040b00e074540780380d00441d440e40c00a03200010f0114542034501c0301284c11030f00c4400281d41504241c4d440c502580c055400c00c02404101c1006800a00328100958a002e04d9614010035400380240060300d442d44070000307540103450820000c81d042500909881c1520700045c12034001d40500c030701d40300c0140161100850300c42158820142110307035070040c1d0f02c02c42c890342400307042020021101e9810300100703070401070000c1002c0c010004007205208848049203040d10789041c0a02c0070790034107802044 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 380811645 1250 380810395 380810429
    0xe010e060406171b0310060605130807050901090f15080d020c012a151b09080c1e040e03040816090533060409140a1b121b0206060109 59
    0x40c01040b03402e80c0341048800c00c40e13110340c60800f007441c01119074080320f665850903a000603600e0740310001d400d54900c550304204044d6030740d0046d10b980b000700e40070b00360340240407400402034044035034480841d4503030009001c00e101d02070900001000c00c40c0d40c4043c1d4660400508860a16418040041da01c21b003420300c07044034000b5001c0d402d0034080020901c2642c0180b0702411042c0a045074003a84d034000a074600b4802008010106500b008915080c00e000c0340e001d5001040602d000304190741d00070006040294084030000780c26000a41101c03460340c00a40da045400a00304040c40280054000c1200400c2107078a04103500c04100f10035130089044500d08024081034000b00400308100c1d40e08049940b0514081d8108060200d6540300c00715445240001c00141030740b001c0d048900380d0444841101c60b80e5a500c0315103415650204103114071031440701c072041440b601480401003a000300c0300000844001c2280000000b41884a1103009640007004201066a202018070b02800000140d803c40d58 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 380812895 1250 380811645 380811689
    0x1006090b0f07020d2a060206040303052206020414090415090c0e0a0c110c030d030e070f030c0e011203050d0903110604030c02040c05040303080411010201060e010e060406 75
    0x148980141400c8440005107840c0e414202025030b00c2803600140181c42100c11031400c1c0460b10b901e80146140c0301d099502000901ca19030f1814021030340c050f006803115a60390340e012001400000e0005c0030003d201001150314170198650900c5c2c43c0c5c81010010b9032030f03081c900742d418500743d1a1480c0d8810246001080006040c4d0500d12003454104140440c500c0c5051401e4105d000c0c1c0c81c1c0000101191070070400038804a1600f0588075400385440c2d0702440c40a5030340e0079444030440d1101940542c0701e01e6500c0c5445209600c25003c05510a094841182e21500081d60301c05c80ba6106482d404803038081030055074250503009004042e00e048001d80034500b2ba6001d04140503014100d69110f5a40340d1030740600d4098400c0d18007800000c41940d59500c1c02d4034024200901908050340207074030f00440595440e000d81d00315010703207070180c8902d40c840e03070303540e442030381030500450103a045548a60340050445d80c10054103028005450664825290441c244011942260303c07800c0e0001e41001c4101241e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 380814145 1250 380812895 380812907
    0x210403112803020304050607030302040906052d030309040911040b0109120b0604110d0912080606040b07050c0301050115020c0102060124030608030f2a0705092505030f1006 76
    0x21110404071a14940d5050590440c01580e00003504400000307101c1d0304155050f402003094800c880010803030b40f0b031a0001c0c03008807140d51001c00103010b04041d106406200c2c3c08107101c500c410040c122480c082c01003001c2400e4550380e40080360b560341d01100c842c1c03c07450580580c400440c000e00e442010640b9241202030303041030f18040942017091000219440ea00d56030070400c00107680b14491036882219100e1000208407820003034a07549044a01c020ba0507100d031014034016a03000f003c440c141b600345808820a40c2c0995012601c40c41584c048070080e0302c0038081d185c0288011208943c0c1e18151080c06800c001d00058482c0c11500404010f00c00c0480001d10f640d07180e07200034050b141c11002d02000303070000c00843d040450244804201008008007a2000748068424030b55103c266403074900e03040c121aa12458030508a800510040c000c83c2801c0c3c1c031655000d600d076010349040c4a90000040f6103204186000300c00030300000b0800078642a001400e40e00700005103031410740b40c1c1c50004011304c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 380815395 1250 380814145 380814193
    0x130e011a0609010c060e160e0a0903020d0e0406033c2012070f1a040506043506240d1e1505010f080703030206190221040311 55
    0x600030340002400030b000c0c06071b000d2219045544122102100c50302504c403091192403051441105c00c440005c0c85400150140b1810b2a82c580c0040c0903a4801d1074007651800011902a40c00c00c0c1c2d175010000104800c02190f04928150717072070400c850961320159900c1c0b44032304016500f081e1000002e0b68000f403c6050035032000c142d900c0888501000050000b40f54407010b0b048111a07200c0c01c9004150700605086550071249668000c844121410701203900c140102e100d00c0d58841c40c10700c01005241d0003520300c1408242c030000c031803c0301189200141400140201c0050141d401401007243d0013000940c4d0002c1c0e00f8807414080140000308000981c0f00c00c0f90742004000841081600601c0141600101d08140c0d000d1007117134158603004040c0e40104400d100e001307403130407180100140072407003c81e0940a0700d1301580940540e694900c01920808041004da403129035080040f1007101da9028000f600084030107010208a04240c28014401752800209040a801c0803200d1b0180c03404980017442 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 380816645 1250 380815395 380815397
    0x7030c02090402130207121805150a0e030a030906080109020304051e0c0409110f010c03020d08040804030206070510110c150c041a0408210307050702040902130e011a060901 76
    0xc0b0755403031010448021064400d80070303450005c20350b0b00030454402507c9600c05182e40c0d4480118143c0c03844c420540103103115460b00700892800e5151400702c0381008205000b10350404117a42d4111401203807030060503580039000601a20414801301d94007038165401404140403d50450030140c45050301c2d600d00030704009100042a1021060f94418401405d40c0c88005004001801d074500780f95960340c410407070203803203000321818600d203660203021070100258041d40103100d141450102511f103120f00ae4070560b10124140000401603031441c0041c0102841036010307002c043c0c4c0c8010441e0603504100c6d42561640001d02800c05c881c0b0000902409656100e00391600c40d0321510131218581c0316981001c020322020500c3c220810102a00400841350a00c080350841c0001c00b02190740f0141000807240d142004001242da102d108001074001d8500040002840f140150b001410040424264604007900c13060301e0180300800b80f1640c410000520340520350030400e500015002d205031a201c038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 380817895 1250 380816645 380816659
    0x141b030106180c120e0a0501051e061e060a050406020c010c050d0509060702030a050f0f0d02060705030a0e1005090c060306060d0e0a050712110d1a0c0d020708040501080c07030c02 79
    0x4140f980c8035940d081600c8144040400c42e100080e07031a5915000d1002007614991700306030200e120796290012178541100b04c113a01d035503076441c0c480c100305a6039a90ba191040b40f581c20a61101a5035a290042000c00010b89685548516101010703040501001819045c488030520b520045070000c01e15401840f064a08150b480b10311500082c9980a1408041e4162040c2302ca1082000780010710450304c0070b00b0004441019000c42502541c0b14030055401c07005070050350201e62201d028802031b54101e1005180070a208800f92002c5149c11000006c0c080c020b1f0f110b6003806011001800011420b210503140e251131491b00d20082a2a44244a100c1c0c4001d40c2d90001001c1c0340405002109030a0b0303200d0180d481c020350f11100307442c000c4200c200a44071b1280506000702c040c5040000809040d82c052301301d10000288038000b00c01588000d001210b0042e0820081d01c140b103035807008010356032143c05d40b80d44030341c1040b000500f640c50007854452074070310410540340400d8005011144450741180e0f95 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 380819145 1250 380817895 380817911
    0xd03020903071206140f010b0405130b06190809012706140c0a0e0603040b0f040213060b0d141b1c060b090306091b0609030a141b03010618 61
    0x200c1d20344a4660b2001c1100840c118486040103010b4202401c00b04000985400031b8480391940f001c001d50130b00c24140c000b002044208058100b004010821402001300010031f800710402040c6147d01544114590b19001840007102c16000340b0001d8000f01994001c02a4901c901d0b408241c40013080c14544c40a44012001c0f802c1043d10f03002003111000044542e041418420181e00303c07030b088821a500440c40307880b0030340564107188040d03074410b54000c01c110ac690b417984800982550340141059801600164045150030030b01d004038002044d2404810303076183c04110103202200c20000810010000d4103083c0b183c015215003602c0d500b41c031031704c1e17010365036856981404407a2807031805070110050170030000140c03000e4050301a241401c2d040d010fa078120354401d203019171102c0c0844403c0306034003883c07198a040c5003070880c040c28070154041c085881d41495520354044005112400340b8142d0712071a84042c00180c0c1004084525030140c000307104a6003400c0364003000260315865505507580c0c075080c07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 380820395 1250 380819145 380819149
    0xc07030c05070914011a122712071109070807050a0302041a19020a050303010b1813020304050d090503070b0705030913020a0f0509240f0c030a080106110d030209 71
    0x142000402100070200074055403201034a41c86402440b030b061100101d21b100f81c85101d80c1c401200c80c80890f1a0100045039944491025507158210303852007150b00040d65140c08803003c200042220000003c1c064946403640b4100c0c12940b02488181d000d081d500040c41141130704096800e07001000c50138201d407205e0107842c5c00c40090007540e21145041c0f600844500500840c00300610f04030300c100e800040703424840c0000344d03a50b840050000b000d95004100400800c1103140103040c42000030074007495603e42d0640000c01c0120040c2982c5c0280398000180401c00004005810903a90300d4101549614541400652034007003503c910158075000180071701c00c021003401205d80d0050700030305010070342c480e8500c124001c0d00003010403000f10b400559020300442c05182550058200100210141400c0b250a403010285601724221407100601107154240c2c2700e040504051030821008580301c500c101e10003000e880041c0d22500c180100900c414010303003804102140f41c100352b4100036039034030310b40c2c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 380821645 1250 380820395 380820403
    0x30c02031501091505090403091a09030f03030a15211e0b0103030818031603021507230301060203070b060a081f0608010b0d0b040609020913060e01050c07030c05 71
    0x5080703140d0740d0704500040703840502640f0003804122850200d0710003a480320184015507806860180202d85c1c0134400b001101d81204074100d20309030300c1130304904004039540441d2400c1c05800900d08a0b40010042068200b20740c4500034130402811188418079180000c0400b1055446071300a8100440111507002d0201c0c51062080c03190006694030200030903420803000d0b0140c20b01003100000d81881c0460304451402c80d60f40a0441c0c88406149491881c4000e0f07425803018030811010740c016082144800e041c607007007041c401c465546890039035040c1d2031012035a0b0800824000b2401c6c1d01807005019003031380001510078980d40803600d001039440c0e242c002201030b8125807003001c0601c55020800c1d00d0031508400528801c0c00c070305090003466181c04405003030314405407881e604820907490490120f400011041d0300140903c000040366241d58010404a02003110141039500006103440100401845000d5111104400801c1241040031050032648510200038041246e01c882c0304050006c240 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 380822895 1250 380821645 380821663
    0x503070f0c0b090a1202060105030d08090106080601380912010603080a02010e010f06080a120e0d062f031506040b0c0f190510050705370504050904030c0203 69
    0x3a42c2c10050701e03110360003a5840d070425000b1224000c90a1406000c14000158507040e6000140545482408014100d0302681c0c000c4c0b001c0215926401c0000394600140030060180c28444a69070007a4071a00d0407903511080c840c0d100c0740900c1a100c1000c0d030075a00f50142d481c034403001c66a11100e4084001651f000d041143c0000d0038045001070741000b4590150710050700e8075910710091120000c1100307440b04841e118030074000c070b9070445449400040c8940440c0e06054005060100e8036900350004644c13131501070041161f1455036103d01d4040c2071500c0c140042e8040d040203411828940d802c0d162010b5000142120101111008120b400340c0e6543d4182d0700079003500300b021a00c60107141503641d940c94000d00352206600812980c0c06d224801080d0000e6040d400000a10981416070160402443c0050200c02004000c0c05444c2d40b4104944035a11071300b014400c04ca507982c1602ca000b45a6a96601c0712400b070060410003040381d6202c05c000298441d4042c00d15820381100e900101c1e050152031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 380824145 1250 380822895 380822903
    0x1120501090b010e22020f120103030f17070e010e0607060212100803040605030f0601032c0f01091a04020a0509010e0405061e06190b07030306140f010503070f0c 71
    0x1000810000c160b580582460700c0243c0c0d590200c1e0005805106800e211700b80b00e1a005803691920800724031098005004c810f2143d80301c1403800489905101d1152401e820860010700a00318075500b0503889004140710800c1d00944803168102044068482048031113031505111038080d08000d2661020300b40c510307042e0800c2c415507480c2c1c01e440011050324000c981d6a0387d00c0012860100c0c0b183c1c0004180e41c00c0e02e840c0d84507580707035403207c2c2c1c404480ca0307100900507410107880b40484401d00620f041c801c20f01c4421a4645610045001141c0f42403039081c041c1b022440e0314160034080030510300031100c0012902603081e10400c0d02c0d81d00200e00c09460f00e8000f5034110845000028201044044107446180200c055418a458a440342c1003022020007a80b030351466400e01107034a0703140941c0d5034070540e1482641e404d8501d03520071030020560081c0500341c020075652103041004240c41c1d21401440001161000162410400080d01030b000c0540a41c0401048a4845581d40e0140640c41452500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 380825395 1250 380824145 380824151
    0x90c0c0f031e03010803030442050f10030303020714241e1512240108070509010e090705040f0204080c150a050a020c060703032003150105090112 64
    0x4081000340d56039201d9260703021041000c0780103001d41641481a00c2c16521104082c61843e110741d11441d4694410400b81b843c0d102601512605403208003041c585040c520302410351034a481112640d0072900c000f090000d00480203c100300403115514502c006a0781e26040060310b5088a05000d47d00c00c8240d080d52115200e107000f040a03880000d11040c1d400003400d10707191419035800410f48190114038075a480c60070300140103c3c1090f2440801c11032100806400c00e407a01d240c00d00d8a500c0d01d50102400e4800526484204030040300c516142805050744100900080e0b20304004541940c205100e14070f10a002030700800c402c000140310715801040014010701c00544184030150007503010340b01d000000c0c4103031142041c0b02c0c00c04101c44400886000302a07401c0111a50f0140e6a0b940a130320300c1d10031401f44908500041c0c0c1c0f041d0240c46014080c1d680040c1c0e40709807003d1042070f030051110041c400d040c20700400410007401510015401401c0c64003070b460b2400350f001a100c854440030a8400182 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 380826645 1250 380825395 380825413
    0x91202060412030e070626010b04081014060d0f080409020301140d0c0302120304050a0305010f0c1e20011d01110c07030215130e0103030201111206090c0c 68
    0x94009251401540540b05041c0360003903000090301219250014903001c0e1700500002c0041c40d00902d00c003629107401a094520444810290201c4504241c01041070050302103030034001c0150410016000c0702c0003000c2000b080441402c9104a03038001010184155680e0602c0303010841003906034040c06078070003241074071940c684444a010303420900550303001500742110030b180c500c1c10034040700881d60007140080480307040d03800f40032090200c26003000ca01e200c09c00002032680c4800d01d2200095000f00000500f0345110941c6600f507480050a05e400c11094241584642c000101e41e402c000d19a030a01100810345146283d018203c0c948504c4443d519140400c6698010880500c0e845c20b005402041004ca054104003001d002c3d000322109940c2c8001c0301440182803280e01002540341511110b814480f25050040b00960a60041c024a002c102c004008240d02400354545a10b40d4420450402085070203480e28207a0052840d4403070b00325a000b1803100d031900000c40d040f00c0038036419140303808 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 380827895 1250 380826645 380826647
    0x41509080415030c1416060b190812090a09020a020c0d030c0b0601020723060903160303120908160609150c120212060d05030c0610060318050c040905010912 69
    0x1c142c00144601081c1001c4440c141144540d009101c001241a0b8540c00c02c1144204180c5441c4040b808880403a0307145114051503949560308105c01c41d806a0035050346090a61050604403082d40c17014012205003c141e0140d5a03501d40c80080d10b00307083c001a201c5d007a03280c0032441e11040d1520b164010380c0c0c510851341410b501501082c1041d004172b80c004000c1c6c4070300c0b0049a440c1603d1046540111012004251040300940c04030030090b40100b1082c10045064000303030038003032280d603108018112120300700200358000b00000e40c120b0403120104520501d0b601d603060184582d402d000c40e00440902d03607204000c4285d0145640607041480f00c0010b80741040340314000e020a0702c40d1004100c80b03211903240300f1268002c5400304a480301c0d00d40c0e0240c0b900e01c18003118a01d100401c071790318003091240ca4586401040010312401615a1a101c01d03441c002c1c000c0c003190100050a05040800601000411000170303052540d818151800140707a289420898010030701d08000070000c80d03280030341245803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 380829145 1250 380827895 380827919
    0x50c161a040f1b0b0f0717040f030b0109110909040318140109050915040b12030f250203061f09020706050601021204030b06060a030e030a020703050f030c03030415090804 75
    0x918464020040035403a0a0800010f0854900ca6404e1a40301080103485201c041030140c5181d40c421001001043c8180e814066941c000790080000d46655170350070400e00203041401c50042401110812080d09861521103051007003507100c40c068078254011400f014450325a04100724564407041362003584483c1940c0c0300030324101e5904d0000d0415100800e40f46441b40300613000c4e0401c9210310750144102000e000207004031290403680085500740e512402c003410710090404482010f041e03a0307a680607201c0800c2441440c240c401e03105440021320380058400150a507000a00d0120840020f4101e25082c0c14003045038104a07800c900101d0850104550b5030400c0d40500c2d0240c00b40c030340c400840c40381a5214004c0340b00203440c003c880004100241400700040600c60020714021604140803a03038246168030111903a0b0059011503410410303c40b0900250140a030b0940144d450300b0124408180c0d40d00010b40046c040d12032003103c20700141003580c088045070380d015540c5e58480740e8442c241468 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 380830395 1250 380829145 380829173
    0x70810090f0c11010c050d090503090d03020a020102060717071110060e01031104050405030f090f0d0f12030203090c040216020a030c06140304030f0f030b15130801050c161a04 77
    0x200f01d0b0b4802242c54000180501c43d401d02855507803e09128144400e000940401d8005865601041060100c00d80301d10a00c601107a000303400620640340b1904c0020302d00200104883d003003011880c29540c90b03901214a26800820520b000b03041d445000300748a06052160030710545051810030f0000e4420002d0319054120390003681c84089100c624428003090313030011503000b00280c0003001a24508000c9101500175904050102505401607001091544804803003d40c0c000c0e05012060341003240011041031a080603250a50035800d2518603a951a080c0c80b90180c0f00e2500030030f91b0740302c0d0340c501a8003050b50381e0010500b4600c03035a28203220b440c00816000e00400150081511413940c2c8000040301d000e55030554600404c0e10703642008503404001103955508040c3c49460008480c1ea4480101c0d02d0180c02c940d00b559074544d000000640d080043d8017000380c40e41440c081015160f0b190085e0341104500c0c10790f2901d2191549000d80e200d19080315459444d81c0030900b80418840ba440050319 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 380831645 1250 380830395 380830397
    0x1b03190c2d06110408120c0106270506030d05040510020a0206030c030708070e060406300605010f020606090f07050f0409050106110a020907030e0309060f03150117070810090f0c 78
    0x124050760004680da4a1049024180c02e9506c240c094104440719400103005610011000103031482d100c0880d841c03485c2070540080001c8503039003201c47c40d0010034490243c00c4401180100b03e102d8111401801a02583c8141440b940c0107080d0704050350300038814201350f1680200304a03600d180c000c41c6c07030005820a840d8100001d130b000001500460203111049404c02009184038100b9241050803140701024071101c040001d07801da808a85e502000070391000355100650003185860500c4001401703034041e41c80e44811075001c0e409000c0ca540300c8561081d00800e2140b2444001d070380e0389506035958424201c2000003560000790011310250385034003e5040e07600d142d072140c0858010120132030b0742d040c41c0c0e20065800f03050040880c2d84603000f68414440c65080f1400c0d2410000c41600241c1c00307400099100d10390030317030000c20840e100c0b802c0026400d2004003400c160a1301001c180c0e59140006009100c482413201401c0820f649040401011004021000040c41810350307420700d00000d40302240e6058 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 380832895 1250 380831645 380831651
    0x3090e181e0106050d0b0103150902030f1c0504030b0c0c15150109090522050709020f0904050606040b0706020903010f05090f0d020c03030d0b0607050d051b03190c2d06 74
    0x1c2554078040c21178a0a664010040d84440d90a42d110300e40c0703000444099006643c1d465a00b04010f03103050020034040140d00001d007400382c3c1e4245803081100400d1810008000040105000045410b0082a004649107240b1501d94001380906803070540c00d030548a800c0f400d0601005040904095a00c01c202420b03600c40b002580c2d108120b01c01d40e07409507003414814560403040d02001100002003140107000e5070445000a6031502c1e9402240e00001203c3c100300c1001840d200107003098081c841d00001e054502500d840d16006039460280140b5000900e40c1d40c000904103d255002d412a83c601c0c156008200560704000b18201d6403980c403114105124000c1c402203041d254004038894a0800d00a00034510f004056820180100041c00d90158404002c0c0040404650100300b41d41c2c0b0012143c0f100c079a150071a945903044c00380d02036405c0503158010030004040300255101c40402e00c1c0c2500b4124200002d42c0b814580401e0008600c0c0d001c000b038008860031651041000d5080e503030045e0420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 380834145 1250 380832895 380832899
    0x106120f0c0603180b04020d021504140f0a05011407231009020306010506131502010c170408040303050306060c1519200a09150207150302030403090e181e0106 70
    0x1601511004c91003140590480580e481c0403840c003100056009100400101d50341207154000344944440c000e0b0b00d628940081024401d066401e100c1b40507030300e07048070500350391503000d00001c100c00070500585040004580c1410001e405410990300c240794440c1c00009201d80c807032210124407951501d00c0020f4881c1821501d00810b06205540f9440e8000e0090141c076800c1c08d060040b00d9000d00074046503450141d0001034001e10010300048841080e0303001003038802403003000901401031500318607811303c00302e4188070029906030111004c80e80e15082a03622036403903000094281c080c1c05031a24031030144004843e2580c1026a1851280c000080c13003101100000084400b12904c2261000706000c00148031b4424584001c05040e141d50f962030300382c5030903440d00340e401d0240b400b01400c01e01580c454003091080d240c144422403649401c07450114118645074400405801c014400d250030101027070003081c1c0c1c06207040c1c0420b020f01103090845a0033040305104070040c000c86203410845510705400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 380835395 1250 380834145 380834147
    0x6040b01091505090c0705030c1507080106080f0c0405091306060b0715090203011b090920070611040f12060c081b03070c021008041b23030106120f0c06 67
    0x10b0328414240b840c1080825504101c00c0c000e61460117040e06914400a00c111800141c040000b0561420300c0340140000410451400314182e401400420500002c440180701842d4810109940b01001ea140c842c0b95450708065010a0700c15500282e03001078441c0200304009404418810031144100001c0041030307510641d445980c001c0410003044d07441310f01582c0b003a41b82300ea00091b030114001000000c41044102610700d41c40e01540e039100120b009400200001800340c442d020310380d892104100c02e80c0c080d440c0c2d40d02c1d651264501c0180300d40d0351103c590381d40300070720402d9801602003804600c00c45030310b4000e008614412688103c1e00c3d00e0170700c000c03041503034800c3c01954013940c1ca00340402120b80840c8070518403600300400c40c070200081410217070050382c0e4120030f0035090880c540f11b50189003000d041403140a13420880c45001d1041f0400104a07a1061000342c046d442c1407000829130200d8010002030150540354821164104070050040600200080744c642051154068074401a95210 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 380836645 1250 380835395 380835401
    0x3070f030b010e21030301150806240a09030b1005121501060c060e0d05090f04090201050306190801050a1407020d050403060f020c0f060a060b0c1b060403120206040b0109 75
    0xc2090700095040d6403c100c1410101480002043c0b46207000d09905040d0f403481c2c0c5180c200340d01000c9034031300c04c01400c0401508080f469810035400d94405000e4403846010a410514108500c103041400242c4516228031a5403054040e51b80700f4440d250030300f042c40c14001c01f620507004851007418188102e442e102c1001540c40a848040b00a511041e86848401c3c0d9518800314406d48034261540000d5030304070b106204101141401d40c44040e2502401c81c107014040c00880b0f0b4a500651500c00d8600160f03030400305413580f0903821109250101410403807045844441e500ca60010742c2001c0c148444460b050300041c1320000b0098020201b951284002c90355605060f21402c003080003088144041004c5400c00344012100c00400b51501c060f583d051803814000000404941c0c100c4002c0c01030744542405581d0003001580c100b141070450726184a030f1907201c00c00c2c0c40b040340e08900c109056561a05020384009603000402d1401c2c2c581007800180d15000c007281c08171003845100d40046210440b502c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 380837895 1250 380836645 380836661
    0x30e0f031305060a0c051507031803080c03060307031a0403020616050f13180501180c050904050618100e06010305130f060621020a090209031b220203070f03 69
    0x40030022001d180405021955124010000c20003034100c1060340428030070800320401ca8510001c07a8079610b01004004c0880e8501c0c15030f0701100c0c0301194404088cda100c00b8694008444010541e40c91300c4100001c1d280286940c0300070440b400c021604048002d103001e040707204602a8013501d0050740c40c0000c0f2100400400361940c041601401654404000e03500948200e40e8400016044035032510249400520700d200b94202c042d460310014040000400701343c50440704480c0c810700c10240d2080000e0024055400701c3c900440d0f48800190443d9180803004000d0003140100c0407403404d0407001c0040c142024000c0720102c100040100351254801d103c1d0071b10446100c030300c5840d1072a80f65205900f03095401c00540d00c464440e000890f250400c4401d120382e964210b002c9100302c0303101d841800074216290b8007094405106001c11a080d440102e00c0d4032001e11201c528104408049002691a5003031194000c6028103803030128840c40c030035600849c0910265100c0c000c1800340d84100302c0a41d1880d03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 380839145 1250 380837895 380837917
    0x4080f010c02060714120a020a1205061c0215041203090518071101110a09030b0901050c090d0303060e0709090518030a0311270a210209060105070605010303030e0f03 73
    0x1035000106810710620b4140c0b171804001000e580340c0000c6034030341c1202003002d64421200640c00200d4000d40c41e0444000b4010300e1601c281408503140078800225041c4055141b00002c41928420303004541e250003140014011200d822500c13640c5070151007840d189114800c07804194560030114003440c010714004036200984817107194176625000110764071007408054196641d2100900d540c10406400500f40b0541c1554407110820314508085858200242c5104d64903490328013403015504410302214005c42040d50b00c00d45200d120700c1d013100100381543c81901041a01d4050110103a40590180203c422010040c84a506c403a81d05c2d520942d400042c0803540d901c200812500725009400c14041e40803842072603414074442642c1c480c81031035524400d501a680e409240700482c0f034a81251005010202c168440c4000f0500c071210800c1d42511006e03201e40803010001c1c1090384240100c5000c1980b2660500080d40d4034a070203070141200401401e41c60140381119142264004159803c0c5080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 380840395 1250 380839145 380839153
    0x1090507150f0c03090b18031002090a12080403110102030d050c0913060e01030f0c0e1f05010509010c15090b01080d02070b07050706080c07020d0b01180903120908120415051005010c03120e100204080f010c02 91
    0x61340e0340b54503147458115805810750000303210f5441580e41d07512902e44204d07009004507581d03c40c0c8008000701000c2040d407104030720386000b805100340840d0415840c10f4a9110060001c4074441e07050420317110300c8a52060b00c030581d26804100c59515540c14100d4240c8102d030051840a8907035005603642c1c003481640c14000391018004c1404659400341c156440e02456000152a4000c0c0e2a1898181026000074072998001c40038a6004c41e410480440100480f080701d604020280c0c0d280c1e500c03203845100301002c201500000c59070002c11042107801c3c80303a00030540d00c0b500002d4500f241d0301e92824492348031440011460a0420501c9000e101d5949500da07580400c4203101240700002040c10360002e496800c41408140c21014074060341d41d004900800e231b00264050804055410380b00c0040050010101089042016982040c0310f80d84a90781814094516900c80704100c0043c1045102e122047c420000303c02003503400c4c1e9008005503942c04094448102d0b50300700090036103004001c00001644 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 380841645 1250 380840395 380840399
    0x6070201020d0e0f0d051b0d080a080907050a060e0109050103020a050706020c0a0506090601081b10051c0614030111160b070201090507150f0c03090b18031002090a120804 75
    0x200c9071110414280c0020400742c498100130002c104509440001101c01e54024002412004801f1600c150030480490700040381240303550743c0d2071a0f405618503032070521805c140442d40200e0203100c3c003000342c8030241103e10160358031032006003c030f9012a200d0340800e01c40c04012885502c680225240c0d1300f02611214034105aa40d0384400950040d41d081c3c10754020340b6000d1001450600410340100c03210002440c240d41003400b4203003400c0d006038103203800da480e50303034140d0807621940300c283c2d0b40b01e0345030070542e886000300b22500c0030541e02c402044075890724120020a080720700343d083d950200b506400030000c0400d4007c2c56040c0303100d4040e410003903000025041c8001118110300030340c0301e010781c4000726a107103c41c2e5599191080c96007080f203034030160881e00100c0d1079103c0840b501d20403452400e2b00004040c0e4034060001c0d846401054141c05000440350196003c110041d11090405800c80360a2649458060020740007540740f18440e00c0c003910005140c40040100c0c440c0d00b60002080fa2401e4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 380842895 1250 380841645 380841647
    0x14191505090114041401091508030306090703050919030908010b0d0f17073e010f0f020c09040b0703050c07080a0810120308160f140c0f0d020d02010b06070201020d 72
    0x2030109400700d0390141d2224400c45e4800399005000d802000e4403800070400040d20002503070f0059440d00461a150300900420000d40d070741c3d0040740d03008121410005195290008024103180020500f030101d8180100d101c4105035000322500d0454541000800c800034905041001e854201003024281c0500d8140910105610703071425402c4e6881d2050180c07a00d51280e03034207035034146038801c1035054201009500c0307200f00c1103032080b20314000341030204402c00c0c0d4070f200082c141c01f40718040b1508025800c0303820210316000701f000400855005000075150310b410328140700661011035001c0c000a08020214000e040541c0075103180e030b68410105410320400e039400b03c17465000240309001d91450000000799004200c19a00c0c0131901aa5400d451850503401c0c2400104420b0550700030800d416000c080c8041c1d1101c0e0100c514403091031015541c0040c8545540f5000301080b0050590080b0708003c0c0046030000342550b00003100340c0003401071401200420100f8001e522001c3c0c0580c000c02c00e500011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 380844145 1250 380842895 380842919
    0x6010306020c01061a0702030d05090105070f030905060706021e07020105040e06030a060204090509010605010e030c090c0c060f090d050a05091215010b130e15090901141915050901 79
    0x8034080c0000042d580d9a1403444d41c0c07030f00c2180c170100007a42400084110640c2000d0040a1201c102070500a28002c40c4400017031051107107910141c00715041d0000c00040500c40c83c003600080900804c0142c941290b03060030802540325840e44182c034032130402c400d000c81064000703580440e50141c66550501d0314160340c40380b400c00020070f110303450302822001c600044d2a51005d0409041c44980001d91458041603d42c21120181c000a0504c511035034840410b07540062050754200084e114601d0b80d0302d40c0361780314819000d0b4140414190207210200003441c0c000a140c5445150071030212021244100402c1e1581d02c2001c0500d0002901005145400d0401e4441022030390110011a000c050300c010b01000307500001e800c15034004000040110400203041e2180020f002c1c180ea10180508003180076959906080084500940800c000528094802c0d40204d040da40010f40820044ca4880b206030410106407050f804003520300f00c082d05031183c00d0507003c003c1d12000b81c070091142e400e062400b400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 380845395 1250 380844145 380844157
    0x30a1a071110020409150f061d180912030601120c0513080d020f070f140d0606061e2f100f05091207050a0605130812180106080601030602 61
    0x107002500c00103820041040103a01c0301c030001d02c0001601e0b181008032080590304603603e0301281100b40541071100000c201984000c48546081c49400c03032a07000036088020075035510a660007101e1846900d01c2d802c2507415148a0421041616611216245090458001502e00d10700041c2c148468451294007075114070b00c03061442c109a803c0c50340500d00d005c0c1c203001c59000081075401c07201c00031079255010000350405070300d44405444c134141002e10222440780c80740308a80c6243c1040d0f203014019207440711010003072030300110144501502d0b01300150032109240811001c851a0300c030040c540a100d00f440003034071258490044840c1e610744c1c950164000c15800000342d603000d05642a8404083c510441c54801c3c10550041454509640924104046402d102c50f40803420021840050340c040b07000c40c90203900c0b00000a041c1c46500504100b2001010000c00410b00000c2d8130b1044600e40300141d00c140c0e074059000c24030941c01c0c90514280c803458030401d5100d03805400180000707203045e0041c050b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 380846645 1250 380845395 380845397
    0x70e04180203060415060506040503031c06030206120906180c0d0302010b100206010510080103050d120b0409030509040b030309010c150b0a15030f0203060607030e01030b09180c030a1a07 82
    0x40814032a40000703060001c11380d8121035049034032a81081c0110700b801900c00802d400c0700e84500f06441c050100e500e9218160385a4010210900308851000c107039484040a140c02400a64507283da045c41c1510354101650040c2591080e400001c1e000401e4004050140c01104060300c0a007455605000d007911241c0c004805554941d07440c9588c1d51220f10400e4900c95040d4010107055241c2802e010090011140c024108030080d801400407401c000b500000c1c001207850b00170711008031101c1360401003802c1050a41d01c2800e00302088180760b0710a02901e400d0304100e41c1000456160020142c0e24800c0801c20303408a00031000c0300000c00d0f1007004d1414440c608013004540d010300c010015003100c8840c0c00001907080120032a034165a418032410002c454401011860350604100060f0b06001d0703441d008041001001519880364420342010344a5070000c0d01030005800c040380761b0401c0c2404401d00d007070240304242c000503040c0f800080c111041030300400404003000d6100510a10b0002c0180070784 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 380847895 1250 380846645 380846681
    0x20901140a121121070507240207060b0906041506030f02090d051c05040e19091a070f030902060d02070836100e12190c0303080708070e04 61
    0x2944206660140b1900c4103038401d8900d5644c1202003920b4898081106070b9140415040c040003c2640c000b412651080c3e0460950299118102040074458241800e444d01150010800404000e001c0d00700310f00e20502103a520000343d5450080c0000c0b00da0704040700080802107041040558000d910502e101c00c03e6800242c58810030001051024024a0049a0b00e030301151807110340382c10000f0408100c1000c2d152072480d140c5000e440302242c0c60058540044944c840d041202503d40c158000012554000c2c2c103644522180715100701c0407502150248041417421048004480c0300784145070000741e00801203800c01c203088400300000d4210b6003007101d4500c400c00c036841c0520400c60180070401c4901002889076042369561168403071171464800d01914000e08100d0445401a038241e459880a96201c0c48814044260310b1900e00c1c0800d0200c809841c0c029a041404440e2941383d068038040e07103030900c1030349400c882121015412a40c04000404109000025103840d4100c078280c01e44c005844 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 380849145 1250 380847895 380847917
    0x36060806120312041e11040f14071e090e010e0901020903121e070308060d29010e010e0714090105041d0f06060c0a020409230718020901140a 62
    0x302d246a206058084000c2c040c181000200b00009041820608244160264414440d668406600311020300b1a100b1030311155240c114150305d40c4103502c4414064046181e03824203100182402e629019503829803082c030705081e180e1030700544050b811520403000e0035030140c5c03900641c0703603d031031000c2d041b20510b54003002a076000380e9041103400005000c0d251003a9032a2500010300c400ca41061040c840107410502a51b0082504080e21591109041d02c123029015500d10f0010f0194804000ea41c010003080504001450080c2c04101d0503541c84005007582e03643c8403062160b03708401ca94210000d96800010541103c00c40c0250404641c181030080c01c4c0398803100030380c40c056514a1041c180600520402c60000420301030907410a4085d1003007440e01d1a05a4482d03107031162040040e001c2d5803924105410440300071081c01c852410002c1d400d0010105a50035610f0341240c0c410a0355030220b00b595420000824801c40b0071080381611071850f400e01e007040607020740d0000c143d61818840c440c100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 380850395 1250 380849145 380849179
    0x11070305010c051909030f030503040f02040204091e090c060f0507050709020c1608031812030a02060403110f0c010804080d0609022119020c03071236060806 69
    0x150154482150311041d03115000c0c00703000030120036101060130030010610001c20100c1d10803040d0f0110142c02d490701550769034440c10306a0482015443c0290401c6c40020000f8091403164030240f0f0801203802003280d42810016140162484150040c082d188099000c2045078064141409200000d00301242405c0c2c1070740b20340b41000c90961010810503000184451100814003a180c0d1a074003d940a510350360900041a59038005d0340700d4488650500030a803c01552940b00e129a030b450741e00308032980e0b10000c3c48009e4440c074080e05d084004c11140500c56a2642d40850b0f00c80700040b07460024445ca615030360045403601c0e00a4026919807008202d003520018a9028000141003007a6000da65507101d0f130081c408151811281c012200740410030b01518840b40c1180750326030b118030140941c99a1620313071117500354480c0010007410203048000c145445900328801343c1e03484104070020001c00c41400f0707882401500d0140004400d00e200541882031030b000315800f42d0000b101400f500c60688040d01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 380851645 1250 380850395 380850401
    0x90606160c0e07120905060117031204050102210c030c090a12030c050d090b0313050c2110050408071202120703180611030409180b1503012a1107030501 67
    0x8101042c2c54400200916941c1040030542c4049800900300600034040d1681a1144c4041c0540d003c000c0c03022a00c0c0c98076020801c10381e40003001018204105d401c051414500035440380c9440c40005c13442245d40180843c851801f01c0c41501e0844d041403a5507295010203609a01020310941d04c40300340080030844a082110415945201c0c2d1140d807682506420254909144181c00f40100007020805001260714201500c1c1c011030411580510f141440c9820350401c0848403a20b60040124403171b0002c01c00d01c400d90800d0340d1131007100399482708940c601506d065900031140500041c00c01c002d4403001881c098503441d0b51952605c192101d03a081c020188035039500014090340040c0340040c84100c0d881484000b4001003c2c0c42c04c0114005039088242078032400f407441072111460b40c540c65840c6030f40c3c51101d60010240d11034010f050b68500500354411030000d0302d180ca4029031070100e805011381800d040c41c504103010315008bc0d0112130040d001700d50940c01a40900a05d00802c0000000150700f40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 380852895 1250 380851645 380851649
    0x30c06020f010506030c0a0e09010f0c0807030e03070f02090405010e0706052109060414030c01021603030510051e2b1a070c120e1509030d0905090606160c 68
    0x290282a003581c062880d10300303480020b00340724421b421400107030703003030742c3d507205070030040340d8032808109440c0d60340c80a000d00400c2881d004c01c1c401400d2140420f10103600201711445034080b03803002c200c0c41d21040c800c5540c1e40030306080204400700000464000d0b01d040311343e8a0f4410700c502c00100e01101d420070b10500f40100c650140010031004036803101e04031141030421014040d5100303000d110f46060000344d42c1c1e0300801f0748040c100d4000c5c01c42003140b54100740700322000031250100035540da00e690800220b41c0d228500084d40003a280c41d0203d02003000c00e8410104031140100307010300345408500c051020292145441d079100c1098440c200350980c0e4003001d01da2500380b05440f00810101c0341010400b1094280b800800f00898004000e1003d800c106840251078000e42c84128907111000151910840808980da0200000b0a8010300300791100040201c0301d01035054618503448184103a40b10212070040a07031041960001610505014000e01180c2400f0000c010401c1c2090b103e00526010036 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 380854145 1250 380852895 380852897
    0xf0f15040504022205150402030c1905040807031b06050901020a1b030b0112062d091a0f011716051516060603061406060304020915042a1701060c02010504030c06 71
    0x2420401c411b00507403050022102c0c50544056241d4944550214400e12907148080719800003000e42548203031003142620040c100c03090880380c0c0140c4a0408024104103000008009030b01d13804003244c29031003042a03c10081042e002480a002d2940d100400744104280ca03100c2c19403071010000c00300b1504042d082c000e04500325816000346c62424048159030708050384031000032200e060798883e115880c2180300c2d5800d030050001449949071800c03039155081e001581c58801c0c000800d0110f411426104181210000814100d80c054450b00d03060722240080380c0540c9201d00c101c010811030908071010856080003501141c90284000042c10101604000503641207607078103030600810140384248085240209a903d242c0e190450001c0e000b8032000784002d01501961000c104103400c2d8025071060031500070420322544000700315407100b41d100840e1507102c0f16225404802a60f000e40414239120522003403105c00b0340e003096030554030f83d440c0803c03c034104001000004046032962000700050002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 380855395 1250 380854145 380854151
    0xc05460503060f030601050a0306050a060b070515010504150e100e010b0a0e01080105061801030b040e030d110307020a140a051605090708150d050c04060e0f0f150405040222 76
    0x4035030140b00c0e1028031140f4641c0a03a000d100140880e40e074080c941e40c01c0380c5c2e001e4070102e0306940720612907000d8140c6a0000c8400e0101144030401c100c2c0c0801c0368454220302040703425691380d840e0704120507500300445201c14615441410700007000b81064040c0c1c050391032145c1030015030b80c580a440c1040360981c00b5000c0311401041e840f1503641c0c040a60840080300b40b030140c0c1d0950625002581e240311351070000344607078283e40b0145104d90280d0481135440c0300042c810880d0000102a4070344a912a8080030461460274a6000c00096544260703070040345650300078110062503985511001c43c24460094651013121001000900c08000441c2e80a4649000c900a68a04800c0c0302840d50302034101400d00a40c0c104004400074840843c40c4084011544104088600e00781103041411501119801c6801c01c0700101d91480c0240e43e6501540c000318076010035503510f40d0070b101010416941818030a422210b180380910303154020340c0d00140018085420522a0f010303507030302001241c240c2c24500761 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 380856645 1250 380855395 380855401
    0x19050c0a030905091620010e0604030809070603090b070509010c0b040c0303030f200f0904091101140a122711010206010f060c080d090c08010b03010c05460503 70
    0x2d0506100b1780010209040413002c042555000c0e003482c59842c0c0094018410303201c3e512600e81c09410802d06c00648900341c40a40c1841c1c20000c0c00001c04680f181280d11481400003250340c0700788240c070201030300218045803503101e20380d0031552544248806410800140c5040c400b044400e91a03501481c895000035070618514940941901c00545968660070700c0c1031840c00c5c40c8040089070605078dc4020f00e8140d65248420708240d07590180c6a01c00e9085031402400c00200001240f0120b010390003600c0b2800b0003410b401c0407044a1107604c0c42c0400168400410400c681c20541040c84034840c60304036a001384100c17540107c00c40541074001e9508561521780800c0c156010b03c10136000d0211140c04226980c2040c402601c20f003010340d401040d4020004403902c804059911915801d42d009005284c02591462210f001c3c1091011552080d484e04121032005030103442280e5080109030340b821001c031035584441010004422511803085640807240d5180045000c1c4501c00703000640f5650b881341 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 380857895 1250 380856645 380856649
    0x90f03060a0e070608041104050c0f04060e1c2112050c030f01050a0614030c0906070b1506031501050a0201110307020a0b010f0609121505040c03030e041119050c0a030905 75
    0x42a03c0e4040740c244540917040c48040303035201c000355081c0310f01a04c0c003155035140c801c00964144900000c140c041c0c4804140860141c1e80240d510002c00750072901511ba800303050303a280140d1480400c2c0106004c1000555502c940340e180e442070b41d04001400c0140c40501602c6424050300d00498048440e40400810801e050030024151230160106480b141641400c00001401801010110b4000c0060210004001c160303e00c0c11110300e403001420103034a4a20511b0140712066060790b0f41a00105050310600441c108002030301c2c4a000080140b200803ca01c40046d03c499000c185010f085540340e40c0395180b1494208000c0d40a0000303a0b0050420b81307114140740b202e0280c180c1101d06c2500c41c2860030060154047c19180c2078400c0e2040244000075540b418001c40c1e0a18450324a01d1801c0108110503c0440411101240d01980701c45d440342d10032000b08800c69104860040002d81c0a000007003050405c0500d41c201c0f5801820802c2c076282e0400606480c01141c1101240041c1e2402d40c144114 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 380859145 1250 380857895 380857903
    0x703051b0708030f0c0f0d05040e0705090307060804050c180126030706050709150305010e0117062e0b09041d15130803150103150317090f03060a0e 65
    0x1200c20040507001190904a601d82c59100d4518081d08114001c075a5920300d000a0041440f801c1c04201141e0210420a5000d40710380c00901c1103440d400802c8000810240c01502261441c01c001405088103c0c05c3c0300b8141d0321101d020b8425250340c4079032143c110194640c942120840000413001121540c9040c0030401c20328220112000024401d49662207a0200001038a03c180c1d8401000704241c2e650350000c40d11100f01c4d5001d03a00e94501c00d952010000d400d0b600c018181c1f100f20008c40076a130b0300c510340c50f01e50700d0301001d01c08007560246001840701140e42d402520b03040c00c1030340391002c02810f010300c0d90b9075004680c00001540d40006017020803490701341f081a036016000d0000c11120790030300f4082d0361100154482c09000d11840b0b40041e00c48a18200c3c0000f0869119800c9074807030409542940c800e008404180380401e00c0c050080301c106840d21700a80c200c1c1c0c0e203c0103607004a160b186203150242c000f105501d40140c1d5132083c82140e5582030089078401d4100c00c200040104500308420700d8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 380860395 1250 380859145 380859187
    0x70c02030d0e1c0f05061e0609130312020903031b010b01030b0d1514011508070212090d0204020d090506041106090f01031d0615190501050a0c0507050303070305 71
    0x740b025850009480341c9404a495829140c0081104486103240c100000308551000008109001d644100322240e412004011070301484103c40c29150341d07409061100601045d902000200007000d50078000a1151641c240072041d502000f509002400020a285400040000c2d0781c00d100d0b01001407402000b4490b009400c6000d1034244254000307d00810980340c01e000c0d0150075100481c2c54240700b041680c100d00002d02c0581c050741c00359030b52820180c100c190071070321040004501401107180c0510008801041410f80040745181011b01420049a862039800c00c82c1c10070303003c3c400c00140c0d00c03082c0304881c0000d0203440909414a0586010264080d000000e05e204000a1182c0d0849481d10003040c00c28120038240080c0c1103420741c14a413581e0604003080c12851017030800700020702004001100c0120b5003039460000300380509100c40104040c50003400d0003c1d2050001010723540c450105102d00758010380903505c0c0e0340d4856010a00f96482002c003078001c2000040e501c032107000d000d400400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 380861645 1250 380860395 380860397
    0xe0d0f1404120b040c18022107021b010c0b040302032d1204060e0a080d0c0e090c03060604030b010b07110405061e0303040b0d0509010501051e0103051905070c02030d 73
    0x85060304103502c0050301a040d01e4064101040b9600281c2005500381a800c06408440d520381100b400a031504d00103540443e0120803480404420703480d48241d81c04081c3e0103580d03240c010b05402c403500c158942a044449501904001c0e12072500c6010a0388003210314018ad0003a4091661080506007900e0040e104400701202401c0494410140303001e94010f81d009143c0e002c8141000780c0703031810044007034040c440240c459806108070100811070b50750008d2405642c42e100a0259072040441960000800015180c20056420024038001e442000842d8041c0008000b682403580b00d86981c00440426046002160800034810040c810005401807804108403010301140c0b900d480441d9005400e03000307400e5075a41001055603a07680900660b800f4111118249403142c9500080034041d040a5a100c4250351a00001003082c0c1040790a64140c7d088452000481c00b4600004400a2800901c00000c06542c141c4003803080e041c41c024240a40c11540d1110790321141401054100540d45501e58 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 380862895 1250 380861645 380861647
    0xc0309041b022b031a120604060b0618060f0c0d0f120207110108062106040b060a0302030d0503091603110907020d1b0203030c12070605150114090102010e0d0f14 71
    0x903001c00324890f40c611080d010324010071500e407411201c6001a50b6042206c0e4025070304c0c6d04c542c2d80d0740c400103000303446640210303070030f0011813114024800c0c50b200300c110303c5402d00c44e024100c900e142000002040072100c003003c05450558044045802e020001840c0400140e03440d411450340ca9002800078000c0d20300309411840c010041e50785500a4080200007410321811030001106a1b50307a10500280c48803444041c0404d0704208032132030300c5a0080700d0840300141002c020401d1414001c3c40d40d41070780da02030024820000c156900365603035000204540c03458403441210754054410000d803500118480c074440944811150304003c080c00340180717082c00b1540201a40882d583d03008110009440c6e1002850380c1030030082c00841e0840c0b1071540c0c81d81c014032802c4030f0602d00c48017180042609038013400b01000079499501c00d014508119448890025081c0303081070320070798112401845c40c0207050000007560080126903d00744201c490704c1802082802c860b140446401138000040d483c840c00780c00d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 380864145 1250 380862895 380862943
    0x1050906100e01021e030a0201270312060b0d090302100c020d14040806150a090915020309010902041a010221040909170304060b0117040c05060c0309041b02 69
    0x3044006421152181c01c2100c50140030a650340240004840b0342c9038541081118490011341554a60000c6a039038015883d08102041c141500b2005c07150909030b4a8a42099081ca524205e81081013180c42100b03080d521040080d0310404800180641110b0480c00703d4640514103020381000180031103012440d0811088180c480c0d80401d00c4883c0d0462030810307000549088541c08440c0c02960480ca50354464401401440a0310302d074006241c280c2100e1095400351150407100175a801c0c40001001001d482c4000307440313003116402450380405044c00001d03000d41d194002400740c560070440100c100403021070344600303542c0c1440083e500480b41c140c160010311100b86d581d0380b648520b21440410503605c111100800005448110910003052820398582c1030509040d0001e28032103000078003141000c2c0050849030303580c0540038400c0ea0400f11380c4554070318000074040e59612041c02d026281c00100a25240c03580e50f48104008013141c00c0e002c5541201030b8101900c1d001035000d2201d000d00710a448 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 380865395 1250 380864145 380864149
    0x1707091a030606090a0e0f16080f07050105090427030e040c0903020409020103153203100e0f0706170708090607030f090b1f060801180902190b040e01050906 69
    0x1000d0381119058400d4011640c070009200e0050070586e0441c5014040c03007a0380c02c28003100088240000c03000c408048003103075640c0c2031140c0d01c11041448864540106008110540c010300c090924064060004501d08002c0702e1307100c0e807400341c4107981035280038010684400d16510007800280070304151420070100c5075490000c1c101240d0b03803000911076903c030080a4116440fa802c6181d48100d0300146041c259156000341c801d500d20280c500e800c64004280395001c03100803282200e54100c000c0c0241c0003507101c1c00c2c05c20020703041c0213800015501c60621014081f200420885c0c00805981d5a1303015840b030314045100400c0406007200b02080724070300502130030040c04104180c000c402400c0c0050a40e40514003200940b12100016100c0f68000c802c004001003000d0051005100c440d281800c1541c64032400d0b03910074401e01600390f04d20861810034019020607404600c03400c1c0000c007a074034250f030415100208203401d50004140c1c0b00021504100750b801d20382143d17000d00011510713400185800d40c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 380866645 1250 380865395 380865403
    0xa0b1012050c1204080a0206060901030b0402091b0f0d0e070b220306050a0902040b040908030615090d0606050a210b070c050a0b0717131b1707091a03 66
    0x54414555901c1000c504041001c504480c0e0380700249408045034a0030f81090069600150300000140c0500000500207183c0f181c10300e4107803a0b0060310700c0c21035180d1b40c003440300350740000385010f13816080148a561018804009440001802c0704a0790b40c5680d030080b01e00645651414101459102401c140034030340d9040152401803040c0c401111034a40b80c5650780017000702690000d000e5500d41001c3c010030100719007080c4e5046000381c0b0144048009031f03050108036100c42901400300c030b100740045000f0b481c01400710441c0a06040465050004813400900c00c40302501c02100d40c1076032032804200b1400c000c41e420b4000c1c00e2040b07041440c0d107100e070151441001d1842d8000c09002d16600050f0441d40141109040207401501f220101410740c075005150ac41c090360004082045150503481d2000406407061050890028001c0f0000c0c1030f40d501c641d01d2844000e02c1031140c51542d4081400d280f00182c1d400e130b41c03440c0030090403a03d2a09400908031155843c1c3c0384c20221450b00f980b0644d441c002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 380867895 1250 380866645 380866667
    0x501090507230a050f070605070201020a0813030c0b06010c02031b01201c0c120c0b010b041a0d0e060a05041e03050a0c0831080109051903051c02030a0b10 68
    0x4180142c0e140175640750b010051103800c0c0020100b91034801400300d8640d0541c00340407040c4168031046c9454480174070560144c800040018005104031249100040d4110b1580d90802c0040c1000d000c400c90075400207003080c000150300e04075040380c039110300351540e484816181004042d20103224203884001e01c1c661910001c40302c0302c9030541c804010110080c07040c0008141c0642082c0b0307240c0c0c800b000b00b000900244030a80c00342e903010803250011a030130103040111000c0f184292140300306284004a4151160040440c003001c59a4482041d80b1801050095600c00c000c48140000c4c945018a00424000300c0c0340243c04481070090b100340c1c000794020084650250080c2440043c082e15803901708164132481c44680c040e440300c0c0e02d940c4d828007180350742440c000d4a2002c4004103d61550101400c940f07404801a1803035000f100140c10350180e40302e403180b4050191403c5841c101684880d800625007403203940c60802ea0010401180c80810b20030103508403003c03540180801d01e01d81e0300901c0d02c007140b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 380869145 1250 380867895 380867897
    0x91a0106080103080703021c0507020a090b132007050303180c0a180b130b01080108011a0616060203070e01020f070b1e090301240e0415021c0501090507230a 69
    0x30345c20203041c020800d207007610150016040d00700013450401080d41c0c0111401b2805451480c03400b05141019000c0e2850b03a0740080c1c03226160518200390400580416080601040ca06001c4024060101d10040c03003410b001c2c100641d40d9082a0340242000140350264440c590010b41c80700a480e520300b44940e04844910b404004505100220175000380340a82c0140e610800304034500c0c4503800075402590308140241c0395107041daa0fa800710142a6a074108040075501411030b441d008600d011409403482564200c108003601f00386644072001c0b80c0c01a100ca0011036852a054130003981c1c10002110148102000342405510307041c22a0352031301a001855007040d800200b043c403240030b401c096411449004000380212002003003400c3c0e80640d80141d005072035246160110f0b2000e010507080e4041d5a01c40d094600c10381c0c100404000a411403004401c201002d403400305240da000340500c4e4041c001d4071310300007061300740080040e02c1c8a5080c210406010300c43c0d41181650305060341611481442 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 380870395 1250 380869145 380869147
    0x417030402061b1006141219121205010605030118020a08070f0318060504050609070f140105040315050108010b010c0f0209151906030b06040803030402150c010c0201091a010608010308 81
    0x55541c2c440e0800d6426400c4d0b2604510707150f400130318a401030a1803510500c0907150344552400c14200c1546511a40d0381c0300c034a490040b0607450004e00c40c00c0444c15201d00c94604801102c40601400c81038074000e90101c40082c8002c401808a02c0007210305544038242c00a0851038940c00b4039018010401c000d20000501c20341c130064001190080d007180403050119002040301c0e00d0149044001010f0650b000e6400f4454840002e120715400541d51040c0ca00d0310381412a002d18080d00030544a0390302020b42e04202d01884004002152200803a120203914240440c4940c10100c40c0c9084407500c03940107041100011800000c1401c540e103d003131894050310054400e558000300c1600c00c0c40390300401600500c4241d4896248008103201c1c41c1590600e5030240010b84201d4204040703030089015138a226082000410018902141041030b003101d01c0d2841401c1100448117242120920050100583d455020700c000b0000c0288141e451110103039407015481d410b040c3c0c000d200240c1408000c0100e14 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 380871645 1250 380870395 380870437
    0x16080a02040b0c10050702010c12020c101d060a020a32160b0105010e0a09020c121b01051e0118021204030915021b010c060b1008041703040206 63
    0x5540c040710003400c4600700e45551140c0f44408180e43e01600c0840e1482e04e0316003000308581034418000d42001c0280c503036602c1d101314119101d440c029400144000302c644100050241e45014900a0b0842c1e03c079000380c45001840509510b90500500a10300c0000c00d00c100100001e0b942c1241654a0b862000440c20034441aa80b15007603010700313640c44804400c00d01203811040e082034003280310311007031007010010303c941d0b42d60340150307580081464215030148251405005c40d95482d80504103540303004007250650242c0e40c0e82a0503a9006204054001e8081015071f00c92490902072644c000410000104010443c10000c80b004201030240340180c603003d1607000810180380e0141d425143c001d10040070b41d0301381440e02805401c072520440b054010501c104500d01400031410014070b0304074003108441b111286004455601c880704080701d084d41c0d140c48443e01910b90342d41d1203001548030f868030a0542800d003441b40104151050040000404004100041c0c9a800c20350b054a4102c1c403484131116 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 380872895 1250 380871645 380871661
    0x5060a0e2806060f1e180b031903080a06050604050a032402040f0608010b1201060e0109030501020c010b191a090a05040e0616020a0c1a0c070f031203051608 69
    0x140307030240c0c0500342c241010404910343d00089143d0b81181d601081482c20307005000075089102c0316610844004882000c4c200f590b00c90113400000306550000e06862101c80c50080001c2c2e40c00c45507034242c000460079410040d4814440c49100d0107081c0c110750050819107800c00107103070800e0358000107108030148101540c4502409200160b0f1041e00d007800d6403110307156920390068400b039209440000b1843e0000081d6a0440b01c1140c00b0b4041040601105a09000050b40c1102c41144401e040015244001010840c2840a040d892004000200e44040c130310b070420980051501034810041749941c020040840b0044010070714040340300185481d2000400001c00008440d0b0089810906044480c0407410000c0742951090380001d580c07102803005804220380c0c41d440c044009200e40031601c028088031680c0344480d840703407110800241c9003c80300d45215041205036441b49411030700d0402d0074420008100c2c1030005051152804002c5440c064044041c80c9241903421410b001018002c90440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 380874145 1250 380872895 380872963
    0x204020703050f041202150a0e091b070309052b2a0611160f0603020d1d15010515030114120f0a0218060109060503091507080405060a0e 60
    0xb6003d40c0c1d000d00d8843e40c0d14940425101ca11007070482c03040e08589085400d0003c58000d0b1032901e02c07180c0c0d6036042051480140004483c000c0d050060f8911480d60845181600708000e080c0140f096a407500103601c1c040900c00c000c0303c42003040384400107222815102e1510264074013006a0030640d900e00110444001640c01d008510049c5242c0c4948000480c003d900070f01c040c101c0d110070b0401c946194010021200c440c2c03440e8010034100700d40c03c0b0010015140b00e500179110b408007000b170018210661140f408000c0040c070840e41e40300c0d041080c4c0380c51a01c1c017a00c0e020340140820303070f00700e41c07091000c140030005071105000e0a04010038140c99460540c8814460100d600e658500700d600b42c0000041d41030783c40d94091412072080d40310080c2c0c0b0040c9003080c500b0078041e11041e118000ca160610205071031079017004100e004c40348500b242c0810442e0103161400d0150815884202450401c1d00309503003480343c0140f000080074184440305441242c0002c4416040c00030015101c01d0780b0310380180d8010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 380875395 1250 380874145 380874157
    0xf030c011206150f0e01030501031211010b0603090a02010807050f04051507060e1b0406050603010521030d021b0f0705130e06010b0a090509090703030834031d0307020402070305 78
    0x21914800c0035440c2c03159048200401c20311440c2d05ca0000c413440c90401142540c0c0c09000007003121140c48103074103441d8041c4221030184c0c2d55070000402c0c10303200c20700411295001102c02e0b498560114041d103080d941c00070722480c2c00c88414503211b460524040d08004c414800c3c1d118440c00307614002c4a500405550f801921a0340e1f81c0410300303201035002040304503500c100e80a1542c00b0340c0b04d800421500f0b8076051050100f290302c0a0606404c0d6841d01003081b00020640c010510b404408030310040d9004400d10041140120715000103891300c800c5080311540025110a2444507401544241c00c54100040c95004031502120b4259898850080110141c120302154030114403d43d400411000c00610151251200741da48000e8542d65a02c01c02c81c068030141c0d0400c0d1247c01a100c2440400d100f140400e0703019040e0580d0f02c0700100c401c540035030141140500d9440031088825400aa283d040c000c3c00c1e4481002d03c0201b07005c038030745118180c0320300c00c0400c000c0c81603500003655410540030b4000e1301c0e8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 380876645 1250 380875395 380875409
    0x604060302130b01030c0e01120509010207080f07110108010b0d09020f0a06030614041104060e041e05190209151303050604150c05030106050403060f060b030a020d0b0f030c011206 79
    0x102c68001c0300d0040010b0705070f04240b68042820604020800c40c480c107084054010705039a0721490b48685480800180006841580a95000c0000070041041e1400411282d0442c48482381d4504030380c1446900c0c100d44400140c108020303040100700011604c0d064441c14000d991002865400510000b014001c0b8007043c07681010a004002903020f4060348004104c400001250009094036810401100c85a240c3d0401e1010240030030b2040e548580c1c416001c82401420008090001248900341e000c810000754051544800811096000d03669289448420b1070380c0950070140f0720380000c0d11040240c03503080b07072031103000c2003400c0442102100340c001583c2000503103c0d00d040c1810035040d00060320450326022420001080300161240341224102d8025a441600b002d096640300c0f000b8000062003041c80f40c0e100c141c0420034443c0705005501071555000700503644d0310590210025500b83c101c1061140030b10498050030350718003241d1003402900900e480114070926913a000300604003500004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 380877895 1250 380876645 380876659
    0x1052203110115080f100213030b0c090402040306050603101a150d0204060203042c0601050703020a1515051f03050402030a05010f090303140912030702031b0c1002061b030604060302 80
    0x307140000805c1c8920020014401d41d01c01d4040104c04800b6480364200c01c202d00000b12804201080d45060503a80059032540c00614040361140090181d030000d80065400d00c0c1e440b8280101450200040665111030032003d1203070000350480c004e0640018090b0501a1a00500f160310002104003121503100441104540301c03907e07134000075640c1e0094003c160440901c9028055811000f18184042994a985580c6035540702c400458207500009411429407060042090010304040340704031b20040c50300000200414240d018015100407030b0322080c01403048010380c6500c00c29001c088040d15400c0d003008a001e40311403012910f440020038014259518295403100888155080b240c0740501038ad03024040b100c08038007405150501a00d40c00c4080e80024030b0701802000d050041d44d8840000d0040d45d050010584c000f41401c910182401c1d50f6401a0b00c0c20740322850000e80c00100c0d10a070b48010b041d40c1c0f8111f803c000461070700c01c001d0805c0315004800038031183d070f4640001000d994050075107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 380879145 1250 380877895 380877899
    0x6020412020f010c0c0513090807050c030607051c0506010e030a0b070305061806150910050426033a050405060609090c01030b0f060c0a0501052203110115 68
    0x11406400c0402412032007025954840d4095600c04c182c03128203d90408842e521840c60401040a44540601d698a956444005040c042208200a0000c490043c80601140080c40b800c00d41050b0004100703034240f2a09200300c01c9516480e65100d80b0b01c000040b40029562101e070016104424601e020503414801d0072516010409900a402d003e0035441d1414001c80d1156007c00c51002022600807a0f1084082c000a403646080100000700d520b044181d180380c01568400700e0516100961040d010660024080008404400c01030260a154144030320125010b0480c1ca5120710640c200c00c00443c841d04090909400240040d01c2d4112680000c250a41480400b10015113012170b0b00750b54501425001420340e0030306080d814841d080034800b8240307461000e401176004103080154240c101e9981c404840702621030708010585821214000c0c4220041c51510034207403440104080344071502c0c104401e0042c840b800c10518100d0745030a00304854504211014014485101e1400c80111100c0380 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 380880395 1250 380879145 380879159
    0x80c04050c13170705041b140720132d020a080601050d0e03040e1602010c0207060c080409060e090d03091109181204050a0602070506092b05060f011221030603060204 73
    0x5102013590594a42c11300b042d07110f2004e002300e4040c0300006013401c5038440d0b40d001150060212050489001019400c8030854500c2e81e0342252012818640c4d20074103440c0340c0c490002c410f03012607414002d00d40254940024410024002c17500903103164184040030801c440c00c10220342241d003200380341e41c08403030303c955039601d443d030300700340151918105681025000d845091040c0140c0d04030000c0c4d42c00801c61149811000c4400c509402810340d44043c0510010420001502034640248000504c15001c0c0c00c0c9105c04030f080190081130a828145411403400028152906d91b50901008a071880b040f81e850aa41d50030803421411910014000c0b9a21110b0010781c0d08007a00030b035601515610b0030700707444007002c2c0c0e41c4078424050554020f400b44880906072820801092a03e1507006144066201c110f031034800070070481008079115086181004105d4240b0b17001c0700d00408070400c803241281035030385415900f1168000580c06140c0584562544540130b904400015944000110368a50751141 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 380881645 1250 380880395 380880431
    0x604090513210f0305071d0111030d0906050c120c0906041508071418121c050c1c0f20030703020609010506030106030c120615080c04050c1317070504 66
    0x60030901003059224140d080500c244145c500c69022515001c0d2841040070111040318665049103041048a510ba00c00075034080c0b000c1c1c0045a002580400c006103c0d160034030540d10001d2854031a10300521104000104900c409500014814051035841c28201d002c40c40600c0303030703400200c103020384d80b10400e170565800126a48a10056070b501d81c4035441c60910316500d0710401003035a03d10705808411601070719040010b505801640ca0450344008501810f10403d1402d410190022134000700c1c901e0030440043c03100c281024002e40196a406008400241011a44400203002c000c0070181c1b000740c0648075880303c1f0b483d090240c22a40c860f030042c68002e5440030100c8580724a5400d00b1b01040c0c803400d05001d688c0a5903801009034078483c0c2001500640e0000004007550340c2c0c2d8a40a116075102840020030014004503c0582084030190341440305a60016014080070401080381a040c05115000c02040d50780351000d00307660311800c00b01d40e40340c030400c0d0300810341c070034a80403464590081e061 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 380882895 1250 380881645 380881703
    0x406060b030c12070306121e0c0b0d061401140c01090803090a1b03021005030a0609050a020a0e1e04020702040204260f16030b06030307060903020102130f050604090513 74
    0x30103c00c0d500d668082c0c0c105d083e40c466205042c583d8007000b0070705000403107441c00c11501400d000212005000c0540710b08151240030303804038000301c0b000501c440c4800c01c24001c00b00501005207421002c551200c1c0000c01070404515812541c090208540256150a4000a00769a002082c047d10380c14500d09450b10744000c0d860803150030312107002c1d0a0b20740d40c0c03070308181c07040300e8004000c400d580785440000c5d00c2942c0000c042140442d070301c00d000710308a50b03207100b801d0260b010340e000180c03110080c070000780a8111000d070041c403c105803102d40140b840d04884c54050014245e90150311200c3da84003060190086802c50040c0c00b40351040803036102a8920404181104007040394108016000e01c0e50700e0320320132101003000c00e044150620108440c2c02c1c03007503084030000c0c0440389800200e464a208035030043c2001c50061b5000078444059000c843c1c1d0307071b801401c101c20035619001d20300800501c00b0b01c114481c0113502600c2e48002441490703400110390009030400d81d011601c15582c0e0700c486000b41c801c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 380884145 1250 380882895 380882917
    0xd0e10060e0703060e01080c12030408010510030b0f060f01050d1103040f050607050708071101110f0a05060619150c0c08010e011b0e010e03120d060e130305030403080406060b030c 79
    0x211300015000c80501009048609520261910300c0403102848600c05095521502d9403100f0480002d1584003407141612552903241c115240034114500f055914034080c3c501c40000000368188002d1ba0741f203040100e5208001d007051540c0300300004081c1c000d0f108248a41900c001c0c048204020700c040f02c00b0702a2040d10031426114a540c41e110191000d00a0034400780914100f4001c910000e5111408030200003c141484081c10000202c0c10345003c7c00159034141784e811009240080100c2000703901e8004000701c0d494503042003102002c03ca54081ca01c600d50708004449010201180100170350480356404c000000d01c1540c40d0050035001e0f05a103070742a0348541c6440322162526020002684a070b0072543e03504081c03e604400115200c207511310314140d25001d07042c040250740400300d000740780100c1a01408a10249012068100032000801442c1104041000c03036001a9001c0c0480354441d5043c200030340c903611036040420050160744c0045186010000500c611070007400040c2000ca208 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 380885395 1250 380884145 380884151
    0x80d09080d090b1b010f0c0c1a090a0303090c050d030914091509180610061404050307030b1f090203091e1b010201110703030c090f0303050d0e10060e0703 68
    0x2241c4111220b0b1030b00d10410821000c00e114003070303030207007070701d1661844c01d21001c000b05026001c460034800711020466040007054004051004204002e48600c66108418028000340d01d00f1000441c1c441d0200e000090825544485d14002c102d41c4180040c060180038040703007008a120700e006410070005000304104880e00c0840d054091804148480c821443c0c2a680c500d4031020400f8406429005401c1300c0034040f4103c40d00f0880041004500e104541024004604600e414005400903154121000c14140108000c5c0555100040c0c2d450440e41e018803130020955580325840182410103042082144c1c2c0d2047c001146e50564000d5030007040200f0544501c0070304003908144c10015201070400c1c64000c66890040d80da40c1a00300b43c14031070180008100040f6002e1f0201007944004000c6020995855808aa13907a1001e07017040a01660540400614215103000e00350340240740040d002691501a90141e1000612201e40950b010308018004141c17260540904d1f154103c5000c00003c2ca = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 380886645 1250 380885395 380885413
    0x503010f090c05040b460e06030f060111030a05280e04020a02030d11071109070c11061c0b0424030813050307180b0609030c19080d0908 60
    0x480b48203000141c1140c2d101e80d0f1030107180c081d44d20410b401c510307810304402c0b1000e520340000f22410700b442c8262210642e0440f1500342c2401c01c80715001468080e00c010029000440d07030f01340e203500e01200c4d0041002c0b0105007882c1d8482e0012541482000e040c20344030f00010802c60700e203e411002900304403c00c41c00ca800c4551484091081d0000c90303924030b00006040201448003800c269000740b851500500c142c6e4075010b00c01a0010a40340000001901014002a61000d001d40021002d91101c41111085ea0354141000000c00e902151000680007103494880c00c1420b50b01c072021122f803203860f00d015039600c00d8982011001007070b905080d2801141400032041160190b1149040b0001c425040610480d0030368a80703c986d41c0121041046c4000c6410003c14242d07410003075800240903009003d4420b81c1d103502c05c50144c2390b100e10800e0040c241440803802c0d5580200703180e04210001c1d54150000c040f0032190403500042c03a40403101ca401160451844141d0240c0312a0540701684200c0708420 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 380887895 1250 380886645 380886659
    0x1c06051009052211060a0e13020a230d0912020d09050102030a0e042d23060103020a1707020a0c170705060705030d060b09040b0d0209011517070503010f 67
    0x180111603006101500b018405900f8003422000e0600500900f140784400903a0404501d15600441c920380102c3c0301d002079140189085000d82d00c443c00007100a5040a21406002d442518000c0b5181401410107200000c545c072400103030344804003480d03820304c5207e02c50f05008205125005522006019151060381300c00d003d40d0fa200c0840308180c0c0150314000c411042201c01c80883d041d5594000c0c0c40d920310702c40681d41c003106900d070b85030030052080454103003500660480d12128103d245d144245648016000012480550300010a080260f038641c84607400b02c841c00061240e800710252080144003407141d001400080c41445944041c100e02d03180c546005000740002e840f100340e0744c0031827030900443c03d2880291105500c1001242d003400d03640003610007600c3c081c0e0412140c19a0202c2d21240c9882d140c040d424035403a00303940d60301d44295560049003180030305000740e140e510304060810300858442c84c103500b09550900c10b030505034104250001d04660003842003406106070040041150 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 380889145 1250 380887895 380887901
    0xa08040f03051509062202130204080d0c080d0203040303240501030605040509030301170f07060e010311090136030b070206070503090d0c02130c020106030201141213021c06051009 79
    0x45003040000c00c0a659515491b01c0e141550524a82400e042c14101c075005888440c613070418128582d00140c1c40d1800c2521a91400509c07a0b1420100040e5100d00d0010860000c100c410610000c0c0c400f41c0c0ea507480703007015005400c88000c4c141c48035903015000b040c03117152401c4030301c207a034003d036811301003e5514000c000136603000341d5041140b81c00800041080107496146a040000c0c0341c415182c100456480c920708004066000d80041031103c1800905580d061207900c010f0000e0350562406e06041a000070419034031000165210200b0b807100c1920003042e07130350400d001014211a250200c1d164030301587e2802c0c080d6850809823040c40c0101d2400787c0983c00f0f880c440e09652008160b030300b4040d8811a9042210344050fa0407040e0010381c542450030a010f00381c002d40484e000401c400e0b140d84001440d10707a20005c58166850203200400c110307840f41c01090b03005400c17112004203102a5000040c000120364410110541d9001480ca0030400c05800c00345c824550721100780b8005e82c1c0e03201c4420035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 380890395 1250 380889145 380889151
    0xc0b040b0f03151509090709080d391a01210609060504140f01020406020d05030a02090907020d0e0f01080a09050f16090e0309010e01110a08040f030515 67
    0x200424485a4807444125000d180c0c49901e4000d00580c07900e011011030032408022410805200f4001044c2000f400c01c4001560022054500308001c1d42c90609140e0b20381c0400414581041000d046c100c03905516100030641c4e0100c01108200201041f003500c0c0c48441400b03808640108030350308201280310380521240d0485000c108400418844841c290007200744909045404581c0c1c1d51500c00820304602c51144610b1141018002a00b07480c1c0c945803030417088918668103a0700402c001e0124580c0072821403440b1002e41042ca032a501c41100c010064000c2084098000300c588042110056001031408850b0300c0d281c680780320110f10482440604040c01c942c01e40401d45d1000480c0c2c000e122540098152030041060b10307082c9010040c00c50602e0300c000c001c409100e044580602c0702c41c5640c0b040d40c449203503c8004520381040c03a00040e001080c114001814440e00c070302105169a424001003c0d50745c0c2c404041d0380d0f51a1206c0e00f408280e40207020654480c880e030038140540c41b1003c2c0c41d10340 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 380891645 1250 380890395 380890409
    0x180f0513020d0f052104090506041a220905151b0304030c0201051303060b010e0909070e0417030123010c150f09060204030f0b0f0408031b04080303090a0c0b04 70
    0x56298443d100c41d8500b00140300129a42e10410214003012046038a49800c400e00850726941e641d03290030045e1003600c1e005001c09114616000200c912040d5240303c51030780c0082038514200f00190803416411441e0200d4012101e141001c40d08010004082344a40c84842301458201036034640400204c41100c203d45024010030040001c40c0100340200d503015079281c03051400b103240108015102c17540c0102548111106500c7d2018030200f50f8208811407440c2d402601c0748542841e040003510b40d940d00e580310b05508818000049400c0c00300c00c512a00c41100c0400c0f803a46e4950355000041c59400d4107074004012a105004070f2412584200c04603550309410211115001042c00c2d141d000900c088411010400c0c3c0c0c9002c407070009130290000d80002c6010307001c4542c0703440b11414900140c0740010005004414060100000110300c501645d4120110129020103011030100f400014481e90304030300c07402c1c0700210800061880009940c14040c4c4280c100d112065514081d0341c4280c01130b0f000f422 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 380892895 1250 380891645 380891659
    0x90605120106030b120d080114010e030a1227060905010801180b060c01060f030212160e070c02120c120d0903060209030102040b0a0801030b131109060a180f051302 72
    0x30100e031294014529031003004281c40c09101c2200c0341c184c80d102c41b40749420b0104030344400400140002401e101810303502030a05a0b800c8074403400280d2079269040d401002a1102c60712146000d110306402e4030300300c0000103111040c00c050310320300c500380b007a62149600060500383d0128603948504241c43c100c030840120101d500300d00c92491310103404002c07804c91300202c06101c0c001244000b40181001001d00c210f800d4002030560050140c502e2010700352800740c4d405060b0f1004c0c0c4803000e640c204100d840c92117246030f240e210100102c0b51182480d002039444100c00480f00007455000c104c2c0801003c04440e0024420030100700c051f2030b080b0500624001c25900581040890000d80042c000583c00400051400f41c880504a84e290065240003001440e10f038018801c000c2c4429259070030a155418000f003908442d82c4494910070720482450040c4184804107005440ea00144405003003450382400344100004c42c0c220003000386864032007500e41400d01181030002400c00103201c040e0054102 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 380894145 1250 380892895 380892899
    0x2031905181c05070b0415150e011205060105011d13020306040e0a02010905060c0709020d0b1c0b13080712030203070e0109050f010c050f010203150f030105060d0605060d020414070906051201 84
    0x9528450700041c070548400101d070347c1109003807209224103c582c2c4886070020450500303007441070b900e000d0140c01520b01190558480c102050b00080c0d1503046400034a130500204545061b841c4003400901c0503690071900c84089281e00111a030091351181c842590300700614a20041032654035524110068042000a181801913041000c000d05007410114121248242d80d0001042282e0007002118450796991140c12940d14040251005250889906d40c4048085444400071007001401034225404c04121300303000c000a4005840c1d403145c003c41190160004418050041c1d442141d61f14000703809540c40806540c003600701141500c1b000380c00701602201240065800c1128420143c6162044a0444c0804a03003400114803c0d54450302c000d483c407a0350814405030002a01c05548641d0404081002c0398580409126445810980128a644822000c41c1600510602c00f9410a0030240e00342c0c0c00442030002c0c2030150503507035a0b05040c140c0d58441152280a0526605413042c0780f02c6c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 380895395 1250 380894145 380894153
    0x30210031a300d11150601081e0406090209010b04030c12061b02030901090906080606010e19030c210201080703150e07111b060a0302031905181c0507 66
    0xc1c018003030b81c00c403000204501a0402011a40501d0075004040d035001080810300703a41d11106005180c3c0c1d4140040c28034104110011020907801072100d410000d032100061700900044100c0f21404d2560b4a80254604141c1064006000d031140140d00801805c40005403070406201100c003242e801140105465040160342211071f00d850708180c408a8685000e01c01c0341440c074241e511254426001540ea4414100024100d854140d000b1180d10346442c00c104180c0801042c00303030f8081024039021900000f00070000e100310f2035015142050307008115000c01040188600c0c481030340e0b00c04910034000c0340150404d4211002140c40207001446642c082040d19010b5001a400c00642600f0400713015160000d02051a0044032054000b031084280064800c2c01806031007507504003849401200322903003000c190755100d0344124404056000002411074410090340d00010340800c20144500c2c00c0806e10621004851450452980641a082100b4040020b160703141246c03d5101d1501b041401e0315 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 380896645 1250 380895395 380895409
    0x30d14090406080708061801090b0c07020301060801050c1b010c090e0c09030303130308061504120c090207140d052d161203230a050615070606030210031a 68
    0x126254000b07455a6001c105a00e00740090400390410b0700041c000740c60809070380c100c00340c1c08581203911640350001100108000c011819480501e4401e09540c904041c40440e00402c01507028031000d5103060144000a541c0c1401802c03580708801d0f02d80408615110040e00322005881c440c0045252a00100614042c18413a10b62220001c4041810074104401290640d401110f41070300c00600342041100309604400650f411031420750f802e8603010060318082100d03128500803150a2a040705440c1308210700140c0260142031185002e6448984606d84283c40b200203040081c100c3c01400e503800260351290055400c1f40e110391480e113100b0310064010815000070340018080d00241041814010649844e01d0303d0100d00c00c03407401000c025545001012611220703203081514403142001c1000141d6101e400d07030056000040060385845800004424070b04000c0d244074105404241c48060114030343c0240e007142d0003910002500f550340c4004030102c6080110949084812180202aa00b800302d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 380897895 1250 380896645 380896657
    0x1506010f02240117240901150305070806070f080601051605060711011b27081203040302010b0f130f0b0402160510022a030d020301180b030d14 63
    0x801a12500500e003105400c2d189a00400710070000072400040020b002c1c03441d44090f20f4120b6201400c0d100002c2c40040280719029100310366030243d1600454170b000c02c00e6204540c40d6424034000442983e59180c21619101148565585400395000040c41140184000d0403803d84a86e82c807200c60303035800e005407a00d4110032400241e4907904520040020010072461f405605281c468010398540081c119081d00c48070300311005d02c80096500030050356006006410b44c0088161088400c00e2000c8804448890a43c06080c051044520b495141e042c0d07100250701880c000e6001340004103034003051011f001400010b25401c5000d1207101500803056903c07966118102c1c40c00442d4245400340000c00b03a80100d03602000b40c00b502e01ea03200c20080b0070402600c01060340002941452042c1d1401900d40c2142e01d119441d80040d450154482d01c000c0c81128102206454215100e503111a614a0101c4980d21107036a01e031b01d00000c80060b40380c006802254480d5590f90306054240b907111001041d0420 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 380899145 1250 380897895 380897897
    0x20a06080406021306080916050102030f030c0c01110c011815051b04090213050d0201080c03090328020d020715030c0504050a0b0702190b1605100903021b01021506010f 74
    0x82c0580c10a82c04440c4c1d95000030207066070703a45914180003c00905020414603070481600301d10300d0400c000e90700841941c107001c1740c202c1c48607100e40c1d9009003a0340e01d20403c2d02454540d440d281260ba4110701102c040d080350200703a40204174580b40c5840c0c11003110501500a00800406403029020403500e030012580039480140d04030048060040e0200d0315080390300812403031074001c1104120b44100c002040020941152608401c0079207400192076840050240350005100000161080a0401c2141c00000c1e4051020346400310240b05003441e0507019259000600034015035440f200c1c800600c05080e00c99030b62811440000d8010260000e2003490240c1e028800c052000007265540c1c0d042100c0100040c1491035501d51a5204201d00c2e503105484e4078030803554207a000d002ea902c40c0410ba54041d0401c108804c44128141000c1c0c0c5000034220300e071070340c180c10415554101513001c00d110400d41050059142c0c0c005c0c0d82c0c4010380c0c9070075803101d415200907041c1001078601d42c0304001c10a14002c603 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 380900395 1250 380899145 380899147
    0x20d0825031403070c02030105100821030406090f170d0501080105090d05090f09090709060e0c07020f04090602070510060b070807111504031202120924250b07050304020a0608040602 80
    0x76540400e0943d40304980704512b80d40c01890030402d4910521142010f03a000100059002c054a01d1a0907d4040640041d2049a440e4101020401c0f61310308040040d4119003400e12400c6482c00020f86a404540b003020110704010001504040502802d409001c070600a40340841780306100b00c07019005000a2541b184420024007496281c84000368019a1103d0142450500f0304008005403001940940c4000c10240c0800050300a0311051b18141913044410342c040e01503880003e00506840e61005d4a010720000d100320802c000040e1800309024a5170041c4002650b541c440d8049000380700c40900190010803210000442010001c00d04034001810b10314174012810800149410a801c07c4404a50f907c0f0a18a000c0e01017040388080c50b00c0075801d40c07400e140400415400f60310888013818400d56100f10314858040207003540c148486c90f0080a105864030001024502c00c2805c06a54264041020810152041c0100d0340715540150058080a213042000c9824500040054403003641c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 380901645 1250 380900395 380900417
    0x100c1d1309051515030703060c140c030703020f0c01050405190b0a0c050705060316030b130f06060305010e010503030306010c0510021b060709030c050402090607020d082503140307 79
    0x48030300c10580454040c0c8020103c0c20b10400d101c4102c0400984611141220541c00020b550303000950301040e280e11000202e030400e40d40400340e554100188009100b018040b4024004c0c000000140113005d010f81d080700c21551203c0d40003074843c83e00d07012450020700304002c144401c0c20a4908408001e10b0041c030b82c0c0b802555481c079410703603401515542000403090320055003486000c00c80c440c0506003c882642ca10704023654006041c0380304101d02810b054403481c40c44031581d520841d1755500000ca620511481006c9202c031001012103011303030302c040792600700007142501d0a05140e5060b1100a0002c41c6182c5079a00152004080c80204890070300c24098950407004550000d0040c998845104500c40200d0706103560601d030004180c2c03410003446000820108402500380360446105480040c3e0761303960700020034000d2141c844c010350012090f82404c801c000366400200780d448120a51051082d0075588500d00004412a000d40003038104540c00b407081030341000450708001c0c1e0303090a600081c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 380902895 1250 380901645 380901679
    0x7020a030c03140706030c02030702120a0213060f08340b070803070306050105120105040c170928030c110406051206160309031d06120a090203100c1d 66
    0x1801d182c100312580c4400c40040006190f007040410050101e5060601800034440802550f0f406070000280c03141900421103885207000b4821902225000340080c0340152400203c2c0010306801c0c800d079907480200c06000a28544045072003140662003181c880f18015004209205044824602840e0044502c01c00102d07500f1038001000850310038100e843c1c4914001c100982201c01c0356003e02c0c180041003050300700d4111500d10143c1074401c101c41c0001c500702c1c0307144102c80040c40210101d40070303038440042c4540c1c644000390303201c00d032744008580d210b00d110004000900c6100c04400100414400d1188800051004080d40c80c4100c01a200141c01c0f81e4460020701803240c80151271182e90006410b016070302015500c0034024009a0505001c107021750f50340100701100e0511058582e602d2502d11100303582e035030000c0b900c2d40101601d81d01141c2c148510b80100401184a0032031003407096141441d0349400074007906180382d449440300e00459428042da443c032010032450195100c0e2414020024071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 380904145 1250 380902895 380902913
    0x917071106070c030c050409021f0e0312040e0c0c030a0302031308070b04030305010b040f0501110a1a19090c090b0a0305010f090614040b041b09051501020d03060e010b07020a03 78
    0x80340c0070714103ea65203807450a021031000c2c1c49400041c01a0300b000a07102c05a2184042c0e503404950884140852000701a02102c0c1d8020041c5a154180141d154401300028008080c01c241c071221303042c0d1051a1100c9a0b180e541c0e214100f441d00450304240a80a4014000d03409103034400100342050003a407910303a4401802ea4030101089640b07802c2c08007408141a41440740902401542059034a440e080195140b043c2005100f030504000000035011106401404001807140d440190003210000e0003a0f003c01a100440c2e00301808007640d40940d40504030b50123642e0610b6000201c4000030750130b041c5014083e003031082015800000740d000000014509104100200042840c0090300d22003528002040e101841c2980c002c05000c0021b02c00414071070700005d0f070403c0e80004c0e00d0386140c0000c103212044006690196041742d2505d000c0001c0381e21a4182c06c1d20403107099080d207500808a01c13090341140c94030300541d000303560403a005001e5403181d20001c10940740000d16001e000e40e0380c2e0b82d4100d01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 380905395 1250 380904145 380904157
    0x7080d05031008100c020105160e0d170c0606011d060306010e0d0b0f060f040902090105190b130306050a05040c150207030c15020f030406021f0603050316030e0102010917071106 78
    0x4102d5840150704205c56080c840c080c0c0045404080c0d02941a4400c0002c03d80d4820202c1c151203101d0340c881400801c408a880e8042000b00b903c1170300d03150350f00c40701c107661100c60488030035011507070700c17004c400d0b14440b01c0a61b1090000000d140302d0650f1609001190240e10b00e100c80c90304125048010b9022881c1408c01030f100740c4098811441615040060201010560604038025420500034a0050b41d4000c0d01d181502d2059450168060b1011150340011009034000e0301350000c00243e5080c8004d881c00000d0640740556000c0c4090340742e2803204000c0324012100904568402c0c132040c000185280f00401104400d84122030300e04d0b459032500b82c3d480042c0c1c1d00800b0009942e40c060040207405001d11211040c07174101a50600b4944000651290f001641d89680011251401c5000300b5980d84048080c50708682269115a80581d082d8083c550104042d0f000c100f04101003c4998030501443d00900d9000030030343c00fa40418803412009400c070074002c460141101c603c1c000315407100e201a00c6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 380906645 1250 380905395 380905423
    0xb0123031009020a06021603061808190207170307030806120d09290a0e0414040f0c05030313050f03010e0a031205250e012a0203010e07080d05031008 66
    0x2c030741c20702d44104000400d06910200554021441004402d00300c10086011640c003c0c2000c070300ca000c80502d009070503a003120024003542010074a214001c00c10642e08a4448080d0210307000207031143c84101200300c0c8818030f11207039481003000c8800a8481d0710315540001006e401d07540c00c042c0300c2c000e80c0c0c14480301400c800c00069500303d04000b8002107158004089044000c4c0c80820004e01d0108c5000f489a01010070500900c8030695503e500d4a51140000e0400300240003498102440e152000b0390786582d040e10100020000402c2c507240c08000c030351110b001144402c11251601c810300c442e008054402c1c0c0c0d40b5541c1c0b1034843d00100c170300340142d44c400303882a0b441005510441d1003980455070080c0449000b21116900502c0074401010020702150860822411000300040101c6180620710004030078a9500e21800d007200102142c211501c41c03089009000d05841031a940c0e13a00c806902c41c0741d1040c1d100e100c0030200b141c004c0d0300854000d9071011080b001c0e01d84031051f140c941b101c81c2001c0c1c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 380907895 1250 380906645 380906651
    0xb0702061806220b030903040e1b040f15031407030c03141005030d092102130608010f23040602091306081f0e0d1d030609010609060803070b01230310 66
    0x80c002d41c2c4078400c000b02600f65030040361704508014004130b940c2d00842c0141c03298010920301090300300b415400070701403440c480711a00b641c80e519044014a5108644074031043c00180140004070540217016600448544403c4081c4c20790702d88508030301031720001c14000140750382c90b040712050041c000f81191042562102c24810316181c941418070303019040d50b980d030401900341024810044a040b03900c40030025144008541d14075400040d03030200440040c4104903242c00c8000881d00c2c810b401501d116070501c1f204011507040c08c440e0700d090070100410035a01045140000300062010790207015a0b80016200080b03840c1ca1810403030031200b00d0342007100960f10040707042c203004410410b120341c0200310f05000d00034400e044201d15681c0101048071818401c01c202059054400c1d031814000e20080102240d066003000c0304014000d12460150f074203603030306041000c104018004111944a58040e525054076841c0c03540700800004001801d00146040b100c0460f0603079010008100d408255103400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 380909145 1250 380907895 380907937
    0x130209070315091a030c1c03030207030e03010504030f0f0c030504090e03040f0f030c15081602030d090b010f08070e1b09062206030506010c1b080a12020f06010b0702061806 76
    0x1440c000c05842103601c18070220f055842c01d0001f01e14202400366041c100540c6509071440d007030740c10128044030607800d0340c640710820040c154002404100d41405441e2030317031350405040040712026280304024002c10800c01c001c0040c075406a018000000e00c07207040d03c0c01c094669a1103100324006501100303d04443c82c3c414003d10401d8000040141565941d0000100300440040c1100500505242149807051151018180203200f120b010407100d4a00304604c84c818641505d00040c20f00920103c800714a001098003900001c411007580c000c101c10502d070b9079511030002c4640344146942a5070041c148698529034a0702c5003e8007520741c40000320050a460b00401c0910600b40c0c3c1d1042e81010305110904c14180d8011380b444e04c031550091701c2003c41c0020354a440100d59582d6001240c90701c5042244814000038801c450052400c0360700391210a08007100d110f603188028068252151801c2281030014078011008000c407008180f0080c441044490003c1c0894102207a4099184840442 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 380910395 1250 380909145 380909149
    0x8060405030307080a150b07030306080303010801020a02010e01050105150705070b1c23070e0301060b28020706050f03070e102303040c03121e0302070b130209070315091a 75
    0x38441e4040702c002410003010001c00c0c0d01d807041074000d1190340c22903040024200c8c14144a0b400c0300c40901649000c480d900d5a440100d24003e5020b00b03020070065292414295406006020741030480d030009014400740c40e40c4007203005896000050031900c030301c5040d000183e4908080040c25450034403030034001c0343c00f1007402d01c20161640c00c0000d280c20042c1d09111403030a4000d0320016000000c62400542c0303c00c4c050701103030040443d074102c019411404200f0000b6030001290062180041556105460340002c0d8183c3e507813140c60080d000400c0c01401542c0040c11410080c44e80641c19150030681c88000c9008035000d01c95800e010000112210302010540b01e0460f814400b003501c182040f446d516281c0c035120401083c60000400b901c0a001c11450202d02c01c8502c0d1380e92709030f1900c0c1245a4000d42102034020b501003442201d8141c0703000c00140001400c0f0320002c11558010b4903042c969504c4080c11401801c0c90102c41014150120021450540ca44078101e144a107184c40e0020203188081 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 380911645 1250 380910395 380910407
    0xc0302101707080118150612060b040e1f0303021f0207020d0b06010f02030a0519030b0303040b03010f09020435030d060f05030c0a1203170924060f090c0408060405030307 75
    0x10b010821400d051494110106d6140600120384070b52600901140001c01d0800141aa41d031050a41c80c00114000c40d203940c8103443c540c001d4603c86000000300242d107150140e00c00b602d10001d409600300180c030010040c0700c43c00304180c03900b01410040c80d209035540007900d4191900c00c19501e5100078010401e8958000503101080e6050b030000714106407400e440105903120344130200c0c01d800c0303100d64074074101030190b0800f1548450040c00c1d41d8480e6120010103826400900c1480d181c0c0302d9600b000141c0032010f100300d44c00d40752080084540086000000b006040068941c1903c1c00088464245084000c3c4080d00403007441080c0859054500861490401446c0c3c214611940000c540c0100366900c81580720200c0e40c1d1081031000c000d0a41c1015a0a48105c80c0d000c04181544400c00c11419004a60703090301903a0220001421803a40c10640c1c00840211002e60b0020702c06041c02c0c48526001c0e800d030368480888070100d480d250301d8034201401c2c90010380e41140c1caa880441480b1000f0741200b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 380912895 1250 380911645 380911679
    0x120e010e011a0d1403040305010c051e03040c051908120a020c09010f030b1506031603050a112506090308071b03080a0c1b0302070504180c03021017070801 68
    0x60b401c07400c4800081e0000b0f41c00308407400001c100c0701890b9101d00e0042800e005035002550404001c0101101002d0301510692201c8100d8411022020000300c00b002050156800b40780c1124503d000c8a040600784030850102d2800808503a5000400044051041100152000d480f4108944810a0300d4001c1d1400c0e00c4074103414071035184540144403000358916803500720380d00000001e07a141c40e1141d0140c1c2c1c50701c005910300d4200100001700300003400c403481640600c094990b4100b12540d07074014040110388241c084020100070801203110b2002540c40304201101221409031000c0320345a80f443c0490322881400c4011500b40010030042903000691300035841008143c0340d410085584e801001100010844025284e40c0d801d0005003900c40d426142c21655041c14260040801781000380d5a00100d00c246071055003032503a1400240e1b011907407150700d968480880c500c0641503030b00700108010008d0842d0f0810243c0c0c0e24028821040c5a6005e00903103490b1102e410550400819240d00c82402c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 380914145 1250 380912895 380912921
    0xb01031a15131d16090b0607060b1c030c140303090a0201122705060c19030f06050904061407050a0e060306011404030f0b071e03050601050c07170705030d021507120e010e01 76
    0x20460f03000e07138460004445146074131010000c4cac3c10343d03c40001003072256401c0c00304004141d44c420f82e008064200340100a21409100c03085235000c0c5400340245c0d6848112103400d019080301d0301c5100194024901e4400f0740040d0381d004a029148030850030996a440c0700c0d2401840107541150f4140401401066041020300303501c1407401c401c2859001c0d5404d691070055041603502c1103403c225084550041028001c0200700001605240c00c4c01000b030b0400c105e0803000c1001c030313001203980346004108455130724405882e0031915641c4641080865040140f00d54144444070903490040c1561200070b002844c855246005c41800354140180010b800a100741e0601400640781481c041c460200c00100303000c40d2501280315030342c00004071882d0096014100d4548940c07807020070f65850b8020300c212150751800031520701c00e540b801015510340300f81c0c04034005038104403622100600c0c182503140e40300c481d60a00200720024000d8880c2218201c0c060403403540d64500808890650030b0203014040c11030707 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 380915395 1250 380914145 380914151
    0xe0304140f1011070f0602030307020105160c020d0c05060a181d0f0a0905010c0309062012091c0e09060f100c0501090206070b01031a15131d1609 64
    0x711010802c8030200e281010184601d41c010070b00d0a80c020807188000e40a41c2c50700400c0e007035171158041d590b60015241c0d00055420800064030780301150306407010803070b410750300c01d00314040780d409209030784524980654240e98505d4010405884101c000e08841aa0780d84111000e140e43d0861700b540d0b21540c0101700c180031040e8080c83d02c40102081c082e0030030030060640110380c9400034100001c0980d960000e04035400c1461549801e03070590701c68100c09005250501c00210a001818180c0d05c101d0588480c81005000910400c440701203000c4d8044644c004907242da4000d100700c40d00403090012010005988505400d04034201044141c0e0800c0040e80c00540300710b50309000911101600382c1101c100039485811000b07110302504600c41c81900030301600d07502c01c0603090040f00350109000c00e0f2003400421030700c000291300810f58980309001d0141ca040920012004100a6407440000d8842c2c090b100c41c4039030a4100240380e22030840c04850001c00802c104403022403000b4005034889203a0030300e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 380916645 1250 380915395 380915419
    0x3070b04050a05040c02030c100501180b0d08090111030d1a09040507030b09070e040605060108090a120c0819021617030306210706050705060a0c2f010e030414 70
    0x35803410b50026188100e07000702c0c10a2052000328078500894250151601c6803280e0700c145c664031540000c0c166030f007482015000500381c84000e42500c0c20b0b6024a50000c0d00800e5000c0070581150103046600380514018540c0704545000d02d103550000d104842200396143d55610b40014441003201040c1e1044d101480e1a25081d00ea0035200c0d610703444050104000764000544d48801844160081d0141d110001428106400d288d0000d03d811126107010503488404a4100c120004a82181643c0061180701d040540320b42201c10f240503070300c1158905000d0040d07588034028251211001c503190350060003441c0001d989100102070603072043c90703007140b04038446110b290f002c02101d0703200310142c40d100c0c414070440e01250444508004141d420f4000e440c07001c600941d000000b030a09501420440d0603d441d50a0581c04986404404a020400401d9951107012803244200c6042a00f40c40c0810448000d0580900351008451a00255000040c06101c3c05040d0130104040d00c0c4241c4500700c0c014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 380917895 1250 380916645 380916649
    0x15030a0b0a091107021207050604060518010306030c15020c04050a0c0201050705031b0f0904060b0a02070f0b07030806010201090236070912050a0501021303061a011d03010f0504030207030203070b0405 88
    0x1302c2014006070252401c2006a00d4040007001520000c0c03c0c00b03810729540f266101c0700204245c12048200c1c800c845242495510340d8413038040c0009594000e81485121450004050720080f628031805095000b4425041c01903662845820712031619100c1c0840c0c2ba41d88510004d003129801040c000a001d000c0c0144010101e4400520406c000b488a0351a61070040280c200d441e4003407003142c41e070700600b0301401040680031280a045c003114950200c0301000d81362292201e0120300c80c01079000c0072209002d01400709100711a015005001800000b0b45540c040d00440c0312000d03100c40740d516884400c2d1225a010160745886c040c11140016000a1801c000a005007a0321903440b602000b9280841810306001c4244002e158107603101000315602c040010407200e61002c0d078030080d6507481c0340800c0c40d003c0210b4880411041c6005075200e801101c00350700400e000385603220115404d0742d030ba08290b12466038144907950050740642c00078140c0520b1841018038241194114075420a01800200825 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 380919145 1250 380917895 380917897
    0x11061303050a1b020a120506010e0420240a0f0c0c12031103070b0a0f021c0c170114210c09040f05030a080105190b0d020915030a0b0a0911 61
    0xc1980c500e4100c80c2d03e204485140a60004004081d41c070840210f400143c0042d09507441c9803462180703080d159560390b1405540f6401ca012640644504584021140c100380209078111441d10014001000c207040440e40748085513800307100d07402a42000903203074101500000954000a49071070034202d246010365801400d5007443c0b041071440039186036071104160040c000344200d40707917200480b40c460045003404010b00105442c1c0d07504041c0340401140d60b4610074005c0742c034080c401c41440c030464980b89070544000e00b10909840100001d0b0301c0c0c0d0022881407944114020040586400c000000580070424940714554082a034180a04518410a100480c0b0103179100c1080701d90b520590b490342481240740030201c4000306903020008468090075004104541039440a64a01d8a0750f1388244c11480c40c40501c3c002d10080039424400003c00410039002490360f450040c0c03101e8140321004c903800034660800c3d80d05980540d00e0f04444031560910204c208018034142c403003840001c401c40b64448803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 380920395 1250 380919145 380919157
    0x711120118020d080f07111005030f04240e01021c09020d150209060a0201150e07050d090c05030601030309091b0905010e0a031b0801060f08030a0f090807061106130305 74
    0x50480c9640c81d5040c441500107030b0784034820704519186e4801c80f40c43c2c445603c501d41020240300e5640240e04009507071182c0150f0b40716290480a261241e2a5600c0b1140c00301da071011406101425950702c005084128052240c001c01c0c4d034000541c4a520202e64800604140c806520110389052841001341c0c0c1d81c2ea8a000603507070000e003000d240040d8800072101900c281440d6582110340001e0b191007c990550045400c0960329190403038041d20b40740b03030707148010f0140e6083c1e0000d80e0a1242c100010029481182c159124030700281c81980d5500c0400c1c10150264029804504481c600708164402c9001d0072019414621103140d440c40301c030300c004d40984154004e03d8100950310122151a0712043c4910002e560088001c410b038494204103001c54140034000c2d44c2c0c4550030320400103003007910000d221080e42c100700d001d18105010250201c4801120102e03140c10480400000185a1001c5c402d18004c1d080303543d80c01042148894845e1318150000d4000d03440d0f000014100004244d021040e102 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 380921645 1250 380920395 380920399
    0x5040b03030910140313021206040203330906010e1b0301033201020a1103090a14031c030b0114092808030309150906070909150b071112011802 63
    0x1001c0f6103500040715540ca1110f44100c80303880000c140684105103400d502843e5100312510740340751810065040d144c20301500c009405604c94086406550481d80d0b183d00c60001c0b1440c1040030740907500107404030300d0040d94203030060b402145c010311412149078407242d030021810101d040501c007449280320303142c40144009000c420f529514092110003007481c41c0400c146078623503190140c9103414018000d611404000700466443c0c49481d00201020050b41c0d8107400c0146541042441e0910400000d01180d10700399140c050010039804c124455261030b4851420b540d0000b91051101c000908803806800300d90792100360500080580351343d03692040381040040c0368601c44058841484e13011f4254681c00c02002c0380000300412800c100001901c0c448044070f543c04403616100d100c000342e21101c06440c5100001c036104c80c1845a442d0a400030301c9211b05004400c1e20040e0340b40141a41a04020803ca030011000d221104491402000001c50945414000c022481880c000580b4800c1c03d484024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 380922895 1250 380921645 380921659
    0x70f0e0c0310030818010e15030105040902030c09040f120302180d0503090604060503100909080304030503070e09070c030305070f05070f060f0c1211031e1b040803120105040b030309 80
    0x500314014207002d0388021039000d1000b540707415200b07510130070840e050500c40d400141c03480740d440000d180409012580e052417805182c9540d00786810312000c1c0c1007809050703805114521803141181c490300529442a800f840240310350760041d242c25224192080000745c109801401461410050340c6120f08941c0d0040302ca00f9544082c40c078046095010f004011340d0710502c04540085e801d900300005521030701c0021540b036034a60305c404104040b81c940d004041e200e86428000a03001901400007181c20141609250180000090000d00e401c9411110f1100044440220008143d054016180c2100103824071506107a895003000b02107004204014107000c00648040d024088170364440c801c0f01100d000c0130f00a000149001401400c2104441000c5510300801051444103100a0300d0046555661001449002080d0041110300261104070210001d641c00541624480000c000901d46503001e540c60304403c40d81605107040583c07240c0e01490030724000c4202a0380c04011514103c90856102d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 380924145 1250 380922895 380922901
    0x10906030b0a03050d030605090901090809060a031104090903030b030a051c0c0803090325030e060903010b030a0b06040c11060a150f0b0d0e150105061c1409070f0e0c03 74
    0x1207510142e0381c0003501a00030030300070342005503041e005141690002e440f101d40d59102c8040080c200c0d500590b014104420500140104d843c15800401c0079075114900494106c1c40d42c000b9007120780c0141c0c41000f400303540303005401c10143c05010354900480101e000d00721404242c5c03500c2d5221040d46c412044000c610b00303454001c0324060b42c1c1281010b60441862a16440c1612143e81c4c0c1c0e60100720003114125404941d404040d55041400a904c0e505d903031003450365a995003d200240c0c10070394145a0554891130407040544040104014080c003e0f000d84041d400d12400784021251a0f010b408100f008090410840d0480040c40300e07000b46011f03600061203101011461111080d03600001e4041011042c000307404034407c4040e11000310305010412441010b2032106564603410041001085004001007009182050140180c9800c0e460b001c0303880c20206d4000c0044840f0b1013130b010404000300051000d0030030100581c1c000750020f41c85100440303007019003c50040310000c007e40b0b2404800800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 380925395 1250 380924145 380924149
    0x6111315031103090609120c030a030b06071b14040c02031b010b120f0d050a1d01050d14010f0b030405031909030f1514070c142d010b040506010906030b 67
    0xb404600c04028140343c40e420800142610f40d402956220740c03900c9440c0c0521580140d071000c40300c1d4200710400461429000304800c0e40500810300c10300b5800501400080302081c141e500042d1603801065103401682e0505082d42100385941c0c1d0264010f514044820038200d070004101e6081e50226000c501a00b10000b286501410078451502d810004036a1750b0f010900000400041c000400f9003035808030b007070300c5030201d031540941c40703d002c0004d0b00030001e80000035a040b12541e41c4281807411503d4140352401100c01e89000211b00340034004070000410030001d00300b209001400d0707071162440c07a508064072515568060366110042c0601c0c0d00603480445401480500010756100d81c071708015552905004035410002d0814122071420400300d566200130101410703220b0481c0d5122000c2030115922004240d400c0c482c45800c0a1041030004448840e100701a03240118200700c0b000e04040d03003580d0650940b00250040b500440c141005d00032203a800406102c20b46885150004100c0b02081c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 380926645 1250 380925395 380925401
    0x10c02130c020a03080703090b070503091203090c0a090b060702090a02120c0702031504030f03021e0705031908150d05190809040605060c28050d0c0611131503 70
    0x20340403288500d0300d480c66010640100d104000b41e4000d40f1030842d680c0c0c0d20001602034440c0c0c05c4005004404c00800140120300803005141c01c0340814088805924500c20144010390064a03000401d174402207030701260746071592154010b440050f20511142d1501e10104000d40a5044007e21234415080080c014080a60580700c0e04012003110744507500782041c001d6140d0b4007032042a4000d00420350714520340482041060300803585581e800708030300b04501d001c074000e40050300c00c44450003203510712000e920013001c050300f42c95004801555035400b0070020419801c5808540f542840b03c030b0410030030480711004410145000a8a000e58007840030710f400c9040140c600309401404941c24100001d202100300a8806004180d504010460304c1d441001901d004011603010598094100d6200c407400c00340040441080c00454540c004070560b45417801c040040c003810001452012049003809494090307840056082001c59142c15101300005148401500030801520000c07202c6192140c402c2d8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 380927895 1250 380926645 380926669
    0x7050f060106120501080f100b010e0d1a10151d0d0b06090112110607140a0b0f060f010f0f05160605011503020c0d0305090309090103060e0f0102040b09010c02 70
    0x8400c0d038180d580c40381d10242881c0c004010501c150383c58080081000100001d18031201c5034840020102d0010b0b01004601130301c490140c290411440e608803605a849241180201521840c12080c1d8584c100003042c1e01c9003401031a070080c0f2032450705d007040b00204441d01001000349518040960310b00c40c400c0c0241d00407000c140b0700d130005132003001841440358041100740100c000b200c2c902c0e403503680c0781d01e000d80c00b00d202c4c10003030b0240d408020082c0302c2d4a00789005024840c46440360300300c01101c05400b82d040044171001a6000c1902600300b20454014003141640f042080320800b4618010000003001d8014031030001c4248404195800b030441d006e04142e82000780303448520300f1a80340d0344c40d024021f06003c1c807805064203401469010514060f000307a078403400b6107800810344403141480440142202610000d00741c0003c00200c1000c0d2111000311340610b009600114031660f0f05d0031101d160007415444146103900c144400e02c090302d480b40444110060919080410050302d00009003140c00c83c07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 380929145 1250 380927895 380927923
    0x712110105040315020915090609040e0a0b04050a03020705091312030e1b120a03050f070602070501020a030e190b011e120c0e0a051306050405031c060521030d020705 73
    0x4d0001908050560001d100c0707007800b03681e51601d1441e114a045d00358010400e003241c1c890401d02410001c0e09050740440c43e280e0388202203030700090594440c0d1060120559007541c550308610400e806158042000c540282000c1c0d0704800d00749800c4403100849090880001c1500010360030180c4454406e40040c6420b40402c000e9402032110001c10411600603840118080c848400d0403e0800102060480d906a0140c40f483d20340101c2d000c154009920400f0110b60b11542804500c012039002d03c05024034030101c0d200080c00b03001c0d001c0d85c145002d070706810304400b21b030340e03412240d000071007100c052411075080042a6000824110b0719440220460700007414080146d8209000d10503400c03000400c82c3d00210715034455444000030305003651400c44003081c84050f54000940010803035405240d10a009006607803c2c5000c1e24441d0041500404103101d005e0740310b41051000340303031500501c180c0b210022040d003164541c001d0f41c65101c1c02001c1c40c0f000c4960340480e049041c01000d00001f0921000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 380930395 1250 380929145 380929163
    0x90108040f140618031804180c090b040501090c14090d14030403030e030f03070b040305040302040203100e0c090a0911070c08060a0c030e1b19060302031807121101050403 75
    0x100342041655604102c5941d9651045518144e802920100807190b08091098401c1036a000000034000a00112194010100344500c2e00401017011a0008400b803c2070603408605201440b0411041e148103800c00e103111403601000101d850f8002c00744160424010f000c0319260fa1101c0c0015108003224400a80204281120182d940d9408401001924469141d2001804da420213040e03a80380031001c0304159900401c0805c020032034140d40c0c2030b03006100c0e140c054a8035880340d02003400d0760420743d041c51512100c03400901c071102001001d15445120321100078100650352000030702c1c10f10a88034640000c0d5817180d4030070760341844008440c4d2954124132074841c0310742d917003c070075548410403140111518900b03010383c20300c80c2c803034091904200c402000400c25041a018851000070341190480d601191030680000119481c24000d0024080c54400688925200d10345210054070360281c6070007a0491a002d0086001071049000415040580c078540d0382c41100060341c1074403858101a150440c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 380931645 1250 380930395 380930423
    0x3191d030a020a02131b03020c010b130b01110c0618030a060c0c060501120c0b09010e030f01230105031513061802010215010b04060f050d020a05030711070b090108040f 74
    0x81c0004001115900c2556106541c0410354401000c030f500101b020011034818210b07039917400344640c01608042d0854400050b0244400c00080c031200c00c8500d0202c080c6d41c40c1c85880300c0303641e084030590f8102c0000310050400d420b0185c0001e41644203050710400365040010007080c150b01d081000041c2c0541c840e800300203607000d070070014148805c444000c44403075041c540049140d600030489040da0a40c00f81d0406022820a25103010301c1d001004428100b00166030042030f0703680e003044a106201d50f410000681c411001244118010900c1e07561102203e81e00d00420242e140000d034103015100f1a20360400540f510040b80d24a030059a001821aa00b007851031040d10150440c140300c2d80f4801d8003115070b072442000480b0481d510910407020110001c0c0401c0041b18015a04411840164940146001c603001c002c00c0481e00900c200d0800141e000c010001c2003a000f1915000d0640004c0080c0041490500c42d48004c3c805d03000c3c201c0c108000a404601007040058175207210b0f9900070307115a80c8078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 380932895 1250 380931645 380931647
    0xc1803060c190309050606090604150b0a020c0303030c041514040308030601030612150507050c0a0c151b03030c0507080c0a05060c04060801050f0a1509030c0b03191d030a 75
    0xa000742101a07090001d9074018102d090003072040e482960b5000026041ca5a5400d0802c42d5030103004040c0d0740c1050700c5400e4114070002c1040120050503c00302e14030380794402010000d14000140d58228084d600030402c3c041e5044010040e6411503981c1d00c1c06844081290004480c03c40780114242d0800c0c0d00860003004010b244009140316201c00e0b44d0070051282d96050054100c8018080640100c40d141c100c00788403040c980029506c4500c50a186107803c0e100e408072480d2102c540d0003a41c4650490f00d040c070481c1d9120301d061081207d240791004000d00044040a05441c031401c1c000c0c03d141c0d6500000114a028405940006800c2030805c3d80799450b086403251540d52100003241c040c0250320000b80b146181d038064506540c069a2002040e03170820003400085030592194039401000d181c400102c0300180d03070100c8150b103400e070389200303220303140d89004440c1112a41203ca81b4074018820403c0400180c1100c49005032201c40c08107600c5109882c0f0411154281c00403800360100203900100c80d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 380934145 1250 380932895 380932897
    0x90507050a140117151e1305010312050705031c0b120c040627111b0d170c0a030203070e09240a060206041b0504050106090914010b030c1803060c 64
    0x9003001e8852600e521030080081d03e4182046038407108101d0805241034046c00c2408000c0c80703084041080c5105c00094000058000c0b002c50007110303074251144014001c000e0f80f20350f071b112102103d003091420003005960759a103a007c0d42c2c0064070500020008330304c84003da60454840028040c000904c4a44c81171840b948a901b2250860f01560809400080035009400c0070303105000202020300c0110210261000501220b140c0a6100e03442400802e25149440010000d0800c8045c010708421500040162020951100c4603890325400b07020052281110001c54400c0c03546481c0050b03407a902c030101a10440244040320703030805180320400055068800c10600d080150030b0615080c2812981006180201da0117000c0c0140c000c200402c002881c0010140f00c00706420040c19401c6032241d001c07c044690980c0687c0020b241b071301b4200000081482003888105405007407104541c14014503180c148400387c03030201c403000002004081181c0c520b00c2d004200d4401420741d04503080c100d02503d45 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 380935251 1106 380934145 380934179
    0x506090d06060b071709011704050f0601060306080c04020f040501051312061b0c030c03080a020c010204080105070f02190204050c300603011e090507050a 68
    0x50306601940000e4407806101c3c54503140d080c203282d2500d51884489862100c01001050280d0345d002c1560a0004030320035100c1d0304c90719180303011072400c404540216058040d42c00041401c41c1d064001034121a042d00c200c402401101c010403080707100e84401c000300008100800c20603540550090400f00e904031404a140030b560355071a06000f203200c2c00844034259514000c900340440c400944800406070b15164508416698014211603107501700901031000160000b4001d0380d43d80c0403910302c3d00c00c0302e0096403940e9441004a01908095a50f100800c5101144170300c01c40c40003c210044000320781444802054580070706c001020040c1c68015002c20801142c490040c0f80c02105000b80b680d8807101075100d028030040c1803424006000c440c820f0741804000c03c0c01e446040701e02c248241c842c0c000050304000500d04149011001d43c4a150081c0d9808400107040c1c0c4004203681d1 = true := by decide +kernel

theorem cover : BRFrame.Cov 380755395 380935251 := by
  have h0 := BRFrame.cov_init 380755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 380755395 ≤ n) (h2 : n < 380935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
