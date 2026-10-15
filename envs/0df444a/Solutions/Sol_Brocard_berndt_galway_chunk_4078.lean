-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4078
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:30:09.5405+00:00
-- url     : https://prove2.me/submissions/7352dad5-52f5-49b9-9173-16b4c34270d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 733273381 ≤ n < 733453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 733274631 1250 733273381 733273421
    0x501080c091015090b03010e0105100c03021c0c060f0608010518070b030703060503010c1d030708062d0a060501140703021905010e03120f060109061403040302030405040e01 76
    0x6060040a260a950803800d0502c020b408200100508004440030041c604d8003c0d400c9903503641c10001038200f03810031082000000010071641c50207200c8a0007010f500c0c184030080300140d407406911141c80c04442c2c005140d2051088011622030080d01c8021503005400704009882130325640c0044c861801414407542ca00380225550041c82d00240c0188400364004000301818281c07821450303000074000505054070780c080841c0380d070790a00031b445030884a50754032403a203400d12846036621003803000401e00030b4000c031200340030f09000482d800e83d01007919894007000e0510301942e562a407044003070907007600301c1e0002842104911500704101f20f417800d030380d0034520400601c074910f401d00c19207038000d025a03c4044100e000210418902078424022800011046ca01e07440350343c1590b00c007040c9100a0594078003000480b441c0c039014150095800e01e000707034800d410b280000d48946e40e01d440351100c41402000040c20103200b002243d01509011700140b004031090403000d4080c00402c00314001040081d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 733275881 1250 733274631 733274653
    0x1021810050f041e09020c0f251a07050a23121603031b0c060e121e07060c110d0f1b0507050d08030105091614090118030303050108 58
    0x10320a42c0d2010301e4580303581d4074007840d045150148484020195602c00510071001609040c2c520103041c80000100190005083c03107250039041046918101e500082d40c050302e1841c1644545011042d01c0d04e40c0c040490a805403041c0200340d0242c80d0b030081040c85a0390203101000317000842103100c1441161044507003c3c500002a0326402d40d01500c048611051004040048082d190480d460b4002e040016804540e8485681c0100001c041100451002c034402010444584242c1301d8180001000d002c0c0c6602903011070005205103074210703000040b034081000240b80f141d4129841ca40c1c0c4071200300054065854007910300c0b1050790103e031441c05014014501a07000d034030116502d00305542d88544001e9a880c8040e074118000e00103413650320401c0000b01d440d4640074140d205c89405601810b07260b6142c502086440000107010100307001510150464240e0440240c2d100c07a14906800b507120101640100c0312550844904814015541000000c0c950141d1005059914074010f50390700200c030b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 733277131 1250 733275881 733275887
    0xa09060c020310050c0c070b030612010209031b060c01050a09030e0d020a060807030924060611030d11070203010906090302010f0b150a020c0d050c0102070e070c02120c0301021810 79
    0x409403019402d604421020b244031a4942d00c1964030071001c42d01c050070702660b075251501e0080300ea00440800240001032020f07614240c070b104101800000c00030b45c5000140b074042500c0f00c4040d54070040c1044c0c4001c60550a940700000c0d10b000320080c0c002007010745040d0820380054003c0b100e080d004106d44150140c82c0b03082103a90302d0000e0350013609600d003462070300c030045072400c1c002000c01042594843c513510006544c0070b1419850491040c94003030415811401c60202c9095600c0001844034101c50f0207030b0036402000303494880c601101c001480c0b6910079100005c501c100326000350715510b0040351408100c002d034007a100643c000d50080011240080c003e200f2100c000490075884004000c000e40c0f00d440762001402c0503191841510a6800204c011400c08100b440c001c5586030821282140c06517810841140140768881402c4194103001e000078041048000001e801021030104c000d8285008002c40c0520480140003150f039584e0b69080c02c0c0c0900d08884941d0b00c1007422242c01c0c010244 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 733278381 1250 733277131 733277147
    0x30507030f0b0918030c030a03061d0717040203011803020102072303040b0306030c180123010f05130b180f0901030b060d03210c0314010f17031303080a0906 69
    0xb009840d00909840301c03002c41c0004104011261130601c0201310144614000b40083c010100c1691400724203542409413003035803040c1d41040080b41201c440c04210b02c00740c0c056903124856000f2a90003009803240e00100780502400306016503070040301c0c0500010140d055000702000b034041d045206030241c00452034012810a8003000c1281ea109100c140039000200008640100000b03049600e0394202e203021885061840600e400e02c522560010403055100290344c0d680900c0e072407800d00e00c400c4941c0002e000080d841c2000400c200700030516400d940c0107110700401500d03800026a0b15001c100c00d42c040c41e21001310b141801480130380807400850414220560681c4d9121811007142c0d07a4240510003c5d0804e44010b41c20001000c101215141c6c0215643e0111704a072200403801600c4004007030180c0b407043d03900c0410300e802e0700010054600c182c54040260b900600340040000d10b4084070741d16500131105d61020b00c0b44101000020012000000c00c6928016140c2e00030407559004141c441355 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 733279631 1250 733278381 733278401
    0xe06040902090610050c0109030e10030203010510121d0c040b030703110f060712020d0806030a1a091204090b030d051809060d050a060f1a060d02030a060b0703030507030f 75
    0x1c070490100d0260303e003104501d000384d15940340c418140303802c1e52001829221020030503804241d2400c68025103040c43c4020310745e40041401c043d403555160001040769075408502010410522021208a81d103240e0401240010462a0003642803508200d507521130302c031035003298440c0d0f00e007248005150801244141c2100c3d0028100c682846030641400300301c003801048250b104900304070a0000540c0d545422580c4621a0300030200340360030706000303020060b0240c0214800e03800404450700048107403200000040044c0710101c010703200d102000740b400c003805040e4810000042404a8100c256a102204c071490482c1100c1d10748104507020ba4503031041d01e1591201d05007481544400c0d003402d00741103801800207000100c0000700d0343c07600c40c20138581000441e5020780b02d48041d0140300c0b241c0900f5032025464030b804041041c9801c0010f8040c405e00782181080e40d004000241201540c0e07003c03500820481410341c0d69034a2516009000b007074200c544502003860015681c05061191180c10400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 733280881 1250 733279631 733279639
    0x60c0c012010020d0b030303090303310f03030e15160306320603190c050a02030a08180a230307080909060a1e1a0a05071b080303010f0e06040902 64
    0xa607005501c940a98818050b2401490705d442880550b500e0410041d03108600003406503460b818000c5a005686458001c108a200340b4042074111424041015800e180d03031103020941554020702d0b080c0c0280c0024100c81c060b40c00350025543e801081c694880f40700d148175942e10303004590002c80940c01c890043c0204812041c080c54401d4900841140c14907100b41c02c40414000d212000340024410780c4101c803482000c516440400282038880d00031010401c0e00c5007803103810500150300081d40c074040d9640d80c10400c03446d000841d00d84101c2c14915146824407600307964040d440d605115036014450784103003040e0900e001d1000b000303003008415106140d0b0300c500e041b85041da0032010000408405418198482001d40001504291002d201400784540c02050040c051500150010500821b040c58960510400002c03031580c0d880401c0f981059805040000c45110009a0f80c20342501900aa07559100000000c560503540c203207002c0c111410240c8840c0c1c50b03a10380b0140410780c0c2020f1802504 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 733282131 1250 733280881 733280893
    0x1150201050c070b0408031009020310091d03220803030c0a180501081305030d0e0c130b15131508010e16020d11010b0409120e060310091a060c0c0120 66
    0x340000b1b0046400c890a00856025203464440c841d04903801a100280300e11458501000720340c07040e003c0e8154108221352256000300310b030003400f600c074459680899014082e406901c20118800f903080000303855040200e940b82d01c0c08102c0d08410398026040040800c0500c4500c0d80003403000b52440c4159081030752070220a80b40c8045103188254110b00c1144d540c081800101c040c14030600c81c03501c106070018010050400500c060040c0b00d9202d00203807403c07604158500e45143c940d40d104101e124104c40e0030681d00c0617400c00321081140c1da0b070020120000480d0301a416568001c0245050320006869030702e203500d4014801040000220151016800000d01026000d0081000c10800c40d074000020030070f19a05400074049a002040444405605102e40003e641d841404000059420b8414a1850609142d84000c0c1300651180f54042074031404100c601a02a01c68240314260242100b034440d030032055419101c2c0030440540d4005401da9001c0c030305250016090712501043c0c0310103445 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 733283381 1250 733282131 733282133
    0x501200304180e1c11030909060f0d020a09020304121b020d1b081e0601030f0f02030307020a12060b060a090608060d120906080c0717090a05030601150201050c070b04 73
    0x10107401140b40d18a0594030a0f07036400b5668140070340c600940340200150f200c00060b1102526604508075440116401801b0094554a40e107140a40085080300c01d0b22440303c8550002c0c0107052480002508441312140c0040d141700d1075000356000d0f62145980e840300102030002100c2ca03d143d104600c01c03000000f20301e807002d801c040f030080101d04c1c06040d5883c40100c81d84005440013240f50f00c5a043c0740e00c503210400c4180e00510f0101e01c594415406440c85501d15100c4032410016030346c0c0a0304501400d00c2c140b0456404104840c00c80d51f020f8003650605950ba10400502940b2140598085040107900b52692800341c00301c3d40000a9911014007040c20110226014200200500c0c0c02c400c1c0704160101040340c07400000c52520141d500d4585503030a000c2c0c01030110703001400300c035000e06060081c90000f4502440c080884040e070f00449480d003c40c0340000e0040c41080e8041c54060207002c0000c640303040102c01d40d40c00200e6607002840310340c840080c031801c144a10b29001c1d108100c203201043c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 733284631 1250 733283381 733283399
    0x15150403060207150612141606050a0203130f0e070c032a050f010c0f020712032d020102031b09030a0f140102031302131a010305060303070b0c040501200304 69
    0x41662805954440920140303035130000129400c0c3d41040801500301184030080102143c20384220701210805003024a10918004007040c282d4010041808004034440015910810540b1000007081002410036666512008403c4106001e00015031003141d000540c00c9018040d00003501d54903990b0010040700c4071500290b001400d030702001414800c0101100451020000c181200b1400c100018954110020152200d42c2081d00c007803d42d0030a0302e040181c40100c0c61241201038040c1050542da00c001c5117100014480141604411940060120920f0368154041c61081d00900107460743c881985812801a00802407015816484034800c0c00c00a01c025a100503040c0c401c850075115000724102d100d0980c1c008940b41a29840240502c00951611100c0b4078540501c580302003022145442d1201d45030702074803075001c0c1410f440d000480c0207900e08004841c10b50380c001d5203012090514162240c031590041c85050b001618100320074203070080b52401c0c0240e81c141d03007000b9484e10741741964036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 733285881 1250 733284631 733284637
    0x2a09020901090509041401140103031209020a0b16030f0309020f0f0607141b010e01020a021005040f030b160908060a11040906090b090f01060f0e03010f0e06151504030602 75
    0x1550400c10b0710400000d4503211110068000c500c6503017240b1841d00d0034500142111081c0110b41d00440100d801080480c2d001f0403000040d031502480031410301500c0c0045141e00b2101d43c0294440340d07001458104041e4640c9030f00304400e00c69a505d40181031240c500301d064860011020354010290840d0484500d0310703251080340e441020308818100020380e258169442c801403008a0a504003194100300700c000c920300c142c3e11000908200b0040111500000d50b80c4031700b02c400a00801c0d500c1c100e5000365014005407001400440e850700382e82ea03102e2601c210512401d6030000550070051065000b460301882d12041a1180c02c0000c140550784c010320700d8040c242e01c00c1143c840360f90400001c1a440390500442000c0c0100c5280494181129000e20505010080000d152803a00b8801400241c3c0c1c42030b8205000c40751403800465007441c00d0b00007070060a11418054106107051101c510409022494501c00c1603081c0c079100c00074078000144240d011400040000e0300b541080144002106030f409 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 733287131 1250 733285881 733285897
    0xd0c06110f120601081b0d060e09011515170705041a190804020a05040e01020c010606030c1106150402070303020c010903030f0e0a0b070e19030308042a0902 69
    0xc650108024914505030340040c8840c0c14400c0001410020b041600625940110080c40d10244ca490070508035244096460010410110002600a5104681c5c0c10480c090300e039804000c2c4440c00d0a221013402401c0c0b20f00b14403c0982040000243c295540d200c100a684090316200800100258501000d0600502c0c1e60140501440042a8a00b00304003161029100c0312040d0b503661210141c1000300d12900c4070f12010800340e0b0040000689a441080084500944000c00c84038000b4111a019005080743c00d5103d42c40e0420000340310f42e050304695180405500c1c1c019a140265840d01d480b980111509900c10240d12800d4000c1c0c20300d0350007095080cdc000c9c5001401c0402c0c454896080d03480c030050945c0043e44641090703140d010144603603850303200b01000415400c1481ea40e5840f044100400003014400020265100c648072084400c608040d1003040204d40da46a1401502144c42500c01381d6141c12050400c2e640c41d5100f0211512a0707842c1c0c0d001d02e5903035141503200800780d441500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 733288381 1250 733287131 733287143
    0x180513031107030f050d120e120d060e0906100626040f0f0309050306060301060320041d030a0f080106210f060909060b010203071e050c1305160305090d0c 68
    0x2d000003c01c80d10f041d410049031103a0050300361031070b031340000516034407820309070119062500e0700c1c07120440301c0025240d54090b0b8007000daa03100c4031b001554900030140d6500405d040c4070084100040481d021904a200d00c0030065017002c11500c50f0400c80318a0034010f2500000e10301c4500300b11044488600319a4800e11843d0034050062065030340d94010750710700d4004c4010403e00d00b0140498a82031001c076600910135002040034504c2c5890b0002c1d00c10f4814042100301000b9212800c95881c0e0750881d8902060060400c6200c040707900013155a40d0000c18904e000800c4070400041461080035058102c998556038080c40c40e4a252640c0c3c007500024288501d01c6645840c400200440ba0046000070300715010001104d400c1400c0900030380325410365940c110b405c10040c510020720822215421000198102d8100450920b0940d207090741600340964000e01094115642c3d55054100034840c016500c4040c00340007030301d08183e0039100301b9204420140c20001c0200b0a441c4900ca25049080c0a40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 733289631 1250 733288381 733288393
    0xa0515130f080f0f0d0605010203030c1e09030a08040810060302090601030e0c13090519261c0204050f09040215090402041d16140304031d0301050106091805130311 72
    0x104003250f0145001288401380440c018441e1041c1d0b1160100426080c0069403543c07030100401e203800d10440403118030716000c0c0d06001d00040c02c074906492502c0009011119008d2040c01d050200f0f420910440555208050752061000701d01e000c1c2c1d1040703a40c064400e140c542c03140c400550181212041c00c02152050a003202505c0e5994900710940c0b043e441d84c00190100755090280c101400940c00c1484201d40803103800c001413040303c1c40068400c460f00c001c101811030312500c03602d03446400200c210603901107510000310005079008200b101e004860407501e0341c040006200070104100d402a5011040501541d003d0350364030020009081c00601c01464641c0b24007228640d201e58142441000c1c03078900c1088010f03458440418030708889410080140c4a542c03011000c0c0f844002d00c002d0400c8045480403501103010740e51035030b800c500103000344244d45e10f44a000f018a4a00d101c0c40401250412810103c01e45501c03d40b400b03155609c0a05406044944003620103450b0004000782c01c1c0b15070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 733290881 1250 733289631 733289647
    0xb0402010c0218090705030a0c0608100801022107021f02031e040614091513150c0c0c0614040311061309020901020c1e090403021e0a0515130f08 64
    0x14002c064400400c039540b0401030811500c803914001745500541e000e54041504100800d08410040342150480d2500c02c0d940d84d43d1030a0900022500d50040c0819800422959014441502800041d14815443ca03529585541040365254a041e0006a401000e22024236280416400440d8402c0071074001c680e140712402d80105003000308440c1a1506655200b12000c003503c00b0a0460304001c0a0004044680408480a07990100905040d45c030701c49010012007008824604052901d005203420010f1200050014080a201c1e49085488000c62440800e800e4007a030360604040307803c816110705143c00d45c2d50381c905070310214106550020060001403e82c240c0d4200c20005000006409622440c0110000e0319044030301c501f46114200c0c105599182e101010010304040f00e00f1594104503844605041c2c0c24001201d054601241c100e00c0031401c1c0107400510319010381c4c458070444000307001c85120310207413071001c5e2070302007415100424003408503c0b805261191240910007840c03a100781 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 733292131 1250 733290881 733290889
    0x302090f28020309070f1a030a1b0305060114030c0d1104120c030c08030405060d240f1e05010507080d14010e060414060f0616080a03051f120b0402010c02 68
    0x5048169084039000010081502801e12085c070081c0020060383c546141407601c94981d000c0b0094502403545408000542d450a0f2a00201c2901714510b442c005204410312004000d404200e03400b5007c0307100c8201c00110600703100122172240c0c001d01346250a011130304c00054083c20f0314408185158005002c0442c0c202440000007007010b100d003890401c43c51451a100b80440055805808135800601c0704000035100d200480d41008001c0f0000100f44a946a00640032030102030000341500c12140d002c43c404550054485c243c0d4500313b030b41c884048000c0d01d015515016405001c1c005081440340c000000c14800151080030070784100840d030408001a1a40c0c0342c0b509074040c0c002c100620080c0821070a151113140c0140c000708110764803520300000800d100c034842d6a20b1a0003103000060a11f030f520781c9074007600041a44030403210342c1c0d81a0074030f00401030702d811351b007407242c0c502802c1001c481051002c0c5124100d8503401a0900c032904030b03071600340507a14004c0050341403142c0c4a20100050703603 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 733293381 1250 733292131 733292191
    0x13020609040c030506090a06060f1b0606060f270311061b010618150302010e060d1109100c0b0105130e0102030718060f05031518131b0302090f 63
    0x406982c3c0001c4615001081095901011341002100c910309101401201e9018401140407840fa0416a042c210364441c1180c03407042c421009003846242c41c03004510750b588020a0090401a65908210079651902d03240440c036801c8140e83c5400c0c1140700400006412400519541c100101650706004c2900050414400c02c001046d1140c0d6540d2801d1008040e5002c155200f248411010004810046901c14140c2c030b1501010307041c021034240d07201c000c1d610306040300c3c1d803041003039030500850f090f844a8000c0c64001002d014402c4241d540c1a26140388034845603141c280c3c010400080503440c0c602400341820850403942003403512050400b0004100740001c0d0f0141045540e1038a8800c000c4004030400140c54001701c01b00040056036542d59076000c0192500043d82c42c0b82441054414000138030b0109040100350400000d0000704000c0301c0b0210400f080a6014499005a000d80380250900d890103034040258060f4400020a00a4150702c8113660310a945202c110140c0000820000e4945 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 733294631 1250 733293381 733293401
    0x4020d050312071e090605092215090e0a0b0a09020d020d08070311030903030403030e0f19030c080303160f030605061920123006030f060f1302060904 66
    0xc1c41d40c0d130030a251081da2a54000c850f10035840d04c41e03091030412100502c4d41c0304810306148100f48000300814901440c4410f81d040700408801001806030100c400400314919104010b0310615002c8403d107400b002244103040701d640442c0c00b00c2d8964410000c0c2c40241b070101c00a9822405ca5040d400068640c2202064024000c14405488181c1450010016541c18202c01600c2e0001d20007031180743c80010a49042d65814100100c080e4490408221000c81d0101c1c4981d00c4001850028091014412400152401b40e400003050039180c00202c2d035248010380307104941580c03076003070500c4d864450684c015981d045450081b074030715aa01c0000340290841d034841d07182c016000c0141001d00d500101c2a45a9600729071500c01075100111407141c5410600e010702d80300300300000d41c5240900d43d00b440c07000341d44048024481c52035401841022030031003c90f08130b40244501c55024044d8940040d215200e0058140c140c00c203591340c0110705600c0201b0040490308104d090003001d2081e5200c1c0908a014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 733295881 1250 733294631 733294637
    0x30507021908060105010c0501090c24080108060402010c02040b040507030c03140f0a150b030a020a0f050304020906040c09050612070306060c0b04060c090302120c010e01050c030304020d05031207 86
    0x2559140c010081d5107007520076410740032059114104403112020a5160468900f42070800d40369205060181c0035111240000340007141c1c9420200b807964050180c4043d413000e14141e801507100700802030b00c0d007040a0140c6081640600c0008005601c21440040107a02c041e002080c49000e130800324003503030001e40b44400440d1b281c82c0050b00c2d041d0b00d4450345c01d0310554038545082d141400b1448a5a5141c058031512500c1d483c1d0804c0010241e8083e0707800c0c000d20f400c004803a0340b4074040b120f010003908500c40d00400a18540103148034948a101902d01130350f00200424925207500c42008018a62480000d007804102640045c503075581d50042c0c005c041842c140740c90b540ca0110070042c2200d207103801110500465820880214082c124807541c065440b000000c0c000185220035503074a0032a43c4029440034429505072a400000300350360300c1d000001e0301c512400b40120001035035140101003034644141c0c800e0001501520744070b448500114010000d682c5401c41c8081c000b540c00a04640e08408 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 733297131 1250 733295881 733295887
    0x4111009180f0b061c02090d050a031116050f130b04060f0f0909031205060a12030c0b070518090a02070b04050a120302190f0909050a0c0806030c01090b0307090e01030305 75
    0x2d076030a8080e8080b1800120b44091500b0fa05a00401c811031003081c60310989640411800a0340d280d002c00700d5545a0080100c4400d41c030186801403079408502c00004541c010442a0320000312140050720030303a00010541c540b401c2c2410140140315092800c400450341e102c0f214952192114403d40d805010b42510700c4010ba402e011190700d194543c1e6100140c0586003044802c0840d6000b21400444000c6e41e402081c1900d40c10002004403141d074001c00d0a84a1042070b0404150b0445810103a152058040803001d07035403500d0030b0fa5a801200f4440300790040c001040340091030005185035005156680c01800d0542640781c2d00300c0710740102ca08848035440810f0800900542c5054140c54610750b2a081d4035001c0e20340040b0300003070603420b072001c280411200f109204034081e0b5403602c0a009000400c10031894800d050780081e20300101d400d404102c07040c01061580c00c002c5114801ea01041c0c4480e5280d503d00488040f2550000b400d0900700041404041151407803d144e080c0254041e6031541e031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 733298381 1250 733297131 733297151
    0xc0a0c080124030201140d0e0706030c170402030304090905071205010b0a081b040203040f1b0609050f0901060e06131202040b190e0c300903030411100918 68
    0x280c440d40402c00d03102c02c820400c80400040c1c0e0310601c807100c01032070702407225150031402c1c180c000a480c80a0810505010f06a008201d4560562168041810503513032100c162640c5000e00c95800c03010b560107505908100400d014294140c0c00000e880c0e8403507000c0340c10031a0388030240e0841007102e4008403103503511154200f10350314003000254003611248010b0000800c4880d03520150994408405001c3c6030040000380621080b201c000340015000600c190f403000703412a2482d4541c20502030040440c40000000c5507070b0070450f0030b02c2c4a640c400340040090740d0070032005888521302034492079404507081100003109507802164000500001c001e02000da240c1d8410802903603007045105010f0801007140e0110900300f66001412100c0c00004190541c60311854a500d40c8601c003501910504081000000e419642d40c0703003640070a03074601c50b00c100d8a44007002912440b0a9a024000903100c40c00c000785c07458400c80d500888106414040e04a82d5a1500306151107078104151315602d0b51148510 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 733299631 1250 733298381 733298411
    0x30f0105100321020a060b061c140109090203030d0e0a05120c0106060507050c010c05011112090f0f0a0b07051b060711010e150a0216050f0d0302070201140c0a0c0801 73
    0x40b0b50b030f00120048600749901602d000b580c0d145519005854182c0ba850807510a0300c0b10004c41344220100021a0820301c10b0410300c4019041c01c040c2500309511031800002d00700840d12801241d2a03006003e10302e0007841020300c1e005401081030300101402080324150000302c00700110072300321000c081d206445800300512a801c641e0f4590025041c000104085d2000071400305410320700220034200b07040c070b51086040090050030103076000c10030060b00051668a0304150055a1312401c450001c842d0519031704100145c8a00c502192080c1c15030002c2c2d044000110001043c40d440700152801908110ac440c0c3c10303c000010581ca9a109a000081404000c0f98810802160120008008d0040340d50001406030b8503003190707480c035407007010520104002c079100da0102c41d103004190411030b20800740d600742261151114501429030b446500c070142e100764000c0c0256001540c0585030b515650211a0705c010f9668407198803481c00b80981c05041001451f149840b4010301410000000c402900011039 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 733300881 1250 733299631 733299653
    0x4090903141c0510050409142109060a030f05090f060903070c03080a0c080d0e010e060606030a1a03010f020a090609080606150c0106150f0305040c1710050a02030609150a03030509030f01051003 85
    0x10b40174002505400720009c0d4036141c101c44240034203659440d9103250001c8110b000380110b203000ca024a0402c010300a1b07402000901c401405000d0084e03500546070714108a641c0d100c2c4000003414203d00707200030000f041f14807000d086270821606000364400501e503103203e003991100e40d0203182c080d49c40c201c0418010003449030f182001c04a0b001032029042c00d9000400e20700005181c000c125803149501d040e140c044841c9a03003400f0b4060020f001d41c1c420001d05501035084411100c5c0003885030200060300e644500c4046003210120f0307004c2c2c4480d0b250700090050328000c028a400c0c04040c10440307500c002d0424810400180640c1810a0743c800c03c040008028011101180301010300703103010311000c20380780c0c00050304a9242100400381250400482810400c0e1803014071115842c0c0000c0100c25401500114131515040f0307810b01d03941d611041544030382150424803a03045881e6090030320000e80a08020b09122a0007400c88070150801c08500c2e01752101242c0103141044d030800c00700100070f01c80e100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 733302131 1250 733300881 733300903
    0x140706050f150603060d080901090515071b0f03080901030603080309070905011e05040504290a061d130618030e030f01020a0c030c02060f04090903141c051005040914 73
    0x4004d1550400d400003a100c1c03144010064284d00000404c50043d82c06104c20f00018078001d04408210302200700c2400d6035400500c002e030743c0c04600348020079642201d600c0c0002070b41c41a50b00b44119608548a15400b9040100032505040c0c0ea148044049000040518402c1c1481d600400a4900300343d00c0f14151703a010703840208082094200c410341c01c030901244100345d5100342c60005d22683e46040100c41d9900180682e07a18071610030341680182948007502c0e200c1d5260310703800d10942c0d43d00d10b580450703d00c00b00404d80200d500b240104800c0f039042d43ea221100c46c000c9001080c10621010b020749240d0500604a01054148889082c2420188200c841024040d8021030501c0000e210281409c41d00782d07401420804903191035001c6545410076070f0f440c18860500592520307204e0094500401c94010b043d000700e500040100b41d50b01c40c030b074100c40b4032030b80c00f41d525881d03074200c044000042d09001d440f03401036200010707021480c0e403034520810045038012b18220005008a1440904000d403000c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 733303381 1250 733302131 733302139
    0x10f0306050d020909071a041e0513150503030c0a0203010f0b031c03090f0309080f06042d0b072c06120a150608060310051006140706050f15 62
    0x4080215982d0007625a107010f4060350760401a988080c502814481c203604210500c81881008003802d01c0000b020303005541d450030b6044401fa41c01046074134060341c1ca20a0300c0d4070800c08100070784e1000d4180c100000d4083d944039803c010030340f00c500281c11504102c4050405a01014900b0300b9890240902e092003100783d84104543d900b0403010a448880c2546800103a25803c50ba0319415403003a400780c406207411a548400005a610b0700800040c0c883c03240c01741030b1280700c400101090b004540103008640c0040341401e01202082442e04410400d03031a0480c030041d455500000c10001c1e03c1d1641300711a15940c1851041c492081c54050203a081d0200d044041c111a40104680380c0c0012140701e00700700300282425544404070040a40f151075000c601e01101e861300041d80c0c941203010a40540011029200104074202440003100c2c42114102e00042c91108104900340c010303a182c004500e81d10603000c1c0317030105644039941581c1c030541e090b1440081d0881000801d000e5000618a10a000c41d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 733304631 1250 733303381 733303391
    0x9012f0d140405061c050408040f060f0e24070c06020105100602120304060f09230123060102030c1608070b040602060711073b0609240904060902010f03 67
    0x7000400c018010b83c00b0300e50180380002240700d003143c44008154203141101034103000d54507180c42c2218040d0800e2080143e5000c0300b40020502500a041e40c0c00154000d9840030100741d00b803070401a4031105118480c42600c40c85c80c044400340281001000314a0203803070f22030042e03440e101000382110402028144420b003102814083c0981c00b04031484a000030a5a5036129259810028010010812404601450031594000700304e1915103066103001840258000e80295941d07940c00d0301d1154590198080382d011400302c0f4000a0b100180d08100d0604c1228200b4401200c0181340c424610240801030450000422014200b001038001404104010609091809201030b545070b001626103c18030002485090125404009607030003841c0d00070a000282032540e0800441070060010400ca030000c18054416604200394851301901d40600390741411b5450000c1541000e03080c41800300c8850507000000e40310b9030341d2140300b8003860061034001a41101c40c8009801507413461010703001e2508007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 733305881 1250 733304631 733304657
    0x120509060307050c190b0601200309060c12070f1e03080c090d05011104090501080a021f020c151c0519090201020309061b0717100209012f0d 62
    0x1181034a41041d01c03420202c1c0c45000f415441410458541009540385c40309001c1d0301d00340130070354544030f024800a0301d4200c0d48000e0304003243c0208a526440740c28a910810881400d0b042841c02001040005070130344440c1030a04814603d2a0701c02c2c031065800380058120041400150341d03640c42c40c0782c500300f50504081c4107680c02a00b101d4004106000340d18001c03072180c1082d2503042952120544c058000c000d9061400d400d403049400034090040317038501e04000420140c20000d511858590000c10740380411108030304040104c52151705a80441c0651510202c403516044100e10645451000940e00d4520380b0644910310840d03104001e20300e5080406025410781040d0346885030f800e4004c00800c11000900060b844c40c4105048140c0080780003c5100d0182c4100034946800e03000d40050b40d84280e038031070440340d030030114040f56001504090b5100c03e041049074024000280103050012901b00340502203268242c2c421502c01ca05000b001c5030200650041c002d0011040503800e003800c0d04804 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 733307131 1250 733305881 733305889
    0x604120216060c0f0605101404060806040602090a0b07030801171605010e1203030901091b14041508010e330f0a060803160b0106050906070b31120509 66
    0x1e284120403c0c04100e10003482480000e46052008503041340d010b00181c10314450041e00300a0b1403043d01c1013050f0742a8004100d2070a0300440044032034443c0249590f45898a03402d000350b00c484003c590148030900c00140700702c0c40c0c001030003140c1e00a4440310280d40c5040c0103051514001150f040903074009811180c00141881520750075114286000003510362600d001c60a198036007029003a036840301008100c446030054000c54802c900c0f44080410ba4404a401c514003081c03640030700c517203109456034085102e0901d40d009403410f8142148000320075549024490848900010115080c2c028440f1020382e01d20340d251501102905846400c400544002c030b2a031424400b81080e07407a85540c9000c18103800c55074116002400c500d2090721b9031011122040700742c4480b81801110240b03d15400010300307a000311306032084001c01401c41880c1c8a1959100c0d10703000740040210b1051200c02001998a2081d030305600c2684403002c4000d0341510403800c00810310700032500703003000300316040098681c1c80e12 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 733308381 1250 733307131 733307173
    0x70509090f0a020903030d0b030c24090112050705090405160f26010806100602030406080402130e06130501110315010f0e0d08031e0702070b0708091206041202 70
    0xc016400e603255807519000c030b1002c0e124503d5510380c5403202040b4020f848015901c00644c90a0850403580302c0581c0c4405c0c00b12941c4010049000301400c05a90103142c10103a006105c984414500082a010f00744195800c41c0e50a81d8160001000443c2e15516400d02d03100303940d0000c0301d17410078080300f4140d140000c0034440c000c80306404005105244041d80c80c40d004c1c1094601c1c0b0080703c159034a68441c6100d0b0750380e040482d00588062031100740080e1040c0040f04441c183c8145998450144d03460760203004031085940030400000b43d6030040702191003014412140107088030380d40b544228080d810201d080d501811240d4480600420611180000d9a040503e04c030700203080600480211042c10b40d030410815000c40d03001034800491782c04020115000714821038584050000e4900001d041c2400c42801b1603007100980e2087c44244507004545000c1d01116109034506842e229400d00401d440065000350894698805420700081220303444080484040c84d00c001e028070313500300816486e911 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 733309631 1250 733308381 733308391
    0x3050a0b030c0d030c060207050a02270c071514070f02010203061c080f030c0306091305070b13050a08011a0303030403270e0f04061a03120f25030807050909 69
    0x244544010f142014000c00f00d501e03102e03410200c1191078000390b04180f9207850a009049200305404008121018008401c81166007000d54940c42d042c0d0707034409003080640c4240e0702901d0780001c00c50400f8540e055402085402c400103154485641020a006442200842c80840c00c0d039006208001040e114003103400c20f4603805005c03411038a01e0608250103584a04548a183c10100008018100e0b0401c0000c42c09500207480000190b40ca14400d0410727803030f42d450000c2c065000000e080008004050103401030495549510b40415510400030b00581b007258050402e80c0d454185c0f20001c1310040c0e0030200303a6641500554a9460165001420482d040400c0c034a0200100044d1080342d10005030305028007898190201b842c01c0440340003800c0501150116800b5043c200c0d03105d03801c42051607503401c2134009070041c5041c1c003441c508ad5041d81c1020701b00c00e1127a5001d114085413050000013110058210805a150400b102d04006202000c01021207091042c05c000c1c83c4082d40b034204001d071b444 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 733310881 1250 733309631 733309639
    0xf02030d020a0e0a1d06040603051f0204050a080601051315270507030e1b060a1214010e0108070e040309060e18090d030f05090c011805030d08060103050a0b030c 71
    0x5070007a080281e64000c3c041da04103421500000d404107124541065003000c400b815805080c40380c0d5110200000d60301c0502008045410002c440c0022a02803049050400b800203005814562100040b81c0c000950350b000154903406140100301c941851060209001d0010006000e00aa00800542142407034860b0100e03400c81c0d4001014254040300f81511012960f600502c032a06082c2c60042c007a01800d86440154000c0d000c0761320084585140303c51464102030845401e1598120066451284a0100d8442d094a600006030140c003a140858041e02c0700540c0810f440d4181414246810074a03001917444101420900003c25040b4481c20200e40303651074200007080d4840040380c1500081c0114103000f0744c0d0241031003c01880402c1c252100e40e2140c0c0d041100b181c0d02c0d035601065410039688000e19410420741c0b03080c00c0d40315060841d94107004040185809580703002080c5803000030000c51002420400502c5500d40c5e00d03014017600300d40c014005200c0c2d441d032a00000d4a911a0314522886 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 733312131 1250 733310881 733310887
    0x509240d0c0305071202032401060e0414090607170c0301090e010b0d060b10050301030c09090320010f0606170a051f0801090c0b030112080306040b03030c010911010f02030d02 77
    0x1007049952481d0040c682c0501564400e554551084000580d5030a08a00c64000c2022110361001c0b150650310100c015038043c0c00d0242d1034801e00750391110103901025002603c811252508501455005002c0c06042c40241803510305000300030031620034224402c01c100c1900040c000c6000c00c0406803815610074040c001240003010801d01e00602c40c0d006600e8100020341060310521809a01401c115001510302d4880141c4e040b40445043c0b20900006107241440301e000e1204500716070000058520078109030302c0e202c2d0103c2c458901c1e6038003103c215015a44565407a45581b0003801804002c0c00d03541045410703000d5400c10a0311116005003880c114540e5000091010121924881c410710f0f41d190742c412074640c44002c014040d000c819416a064900b4810004a003c08102224104c4403101c5211130389246035510300385254005443c0c5680181c503845841141d41c0c0600080004462030000000c4014051500c00d200c44041250b1038140203407002c02042c40c9801104941080e0001c01005035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 733313381 1250 733312131 733312133
    0x12060b1329220518070f030c020a060c2a0204110304051509072c060f150f09130f0e030a0e010e150301060908060903070f020f2202040509240d 63
    0x380300240c55114070340c013606800750400c0b44503e00e0b101ca800340f20f0f540d9501c0f0030103c000c1800d800b0742c3c43d078a40b100016400b00f40b204010452076406900020540c0c43d00141c0c0e22164201c0d48002c030311700d0030807403c80c02e8081940b004616280c07041c0015110700c08000f40c1507281c1030302e0f942d41381c803403808900351001140c00000d400310f0f0052103540043e0014118201d1401d5421a82c0744100b520040403010507100000071130790070b103803d0140700345c42e480c010402003490b10015550440d0b50081d420005410074140301c6445103966005a03814820800203000070303e80580040b02060b209007a241d0354807a0402c0291004459000410400c141c2c002c0c03c00032602003488012441d248181c10104044042c003200201c2c800754082400d1044603210402c071529910707505582610ba100307441f001400c0689040d01c90005040600808091940060403110804071241e40880540612100010b2096000400384414980f400d105604041c800e10400c204107034440a95150750f0034010250700c00c1c06010640c03c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 733314631 1250 733313381 733313437
    0x60503040b13080c0f0609070b071712150f010305010311040b0a0905070302040f0f081b0d050a0606062d110a060c020604020a120302060712060b1329 66
    0x1442e4903a00c0b040407950b5000c2c41140685400c0c04100900359030107030402080311100300040680c1a12048020f0f00d00e000b07415aa1441344660700c3c482c020440c1d800b8001d124a006ca1004080c2c4550b0381c1c8107111a00240366010004401082601d080c18103207480c1c014008184000ba940380d041074103a60014100000000180e4400c045c1e40c001c0c1c42c52800c200802142d15450f4014004845419032104110364540321503820030005802825031039844510304074001d03070070b40c0e0b41800200000740050b102c01c00543c507040c0c1052441c01c81541c400d615032004000c226880300d094041e2642c121102080000010f81c4000d040040415020820586041714400242e0502420716405e030710890811143d90a4180651a00400c5405a1048203161800102c0c0c054841e440c0381040d50541c0605201d40c0c5045040d248409044200122030b1f5590902144403640b01e0018000c5c04184106040b480c0d20b80302c95041c44001540302c0280007000c0c0d44541070500c40350001e80d078100c000030f503041c0c40d1004005246 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 733315881 1250 733314631 733314661
    0x10c120c021b04360b071e05032517070e0a0e071b050703030e0f0f190b071407060302070503040e04080904020f07020f01090501170405241f060503040b 67
    0xb141500020300940104455404101d0f20315500c20380e0b90f100c00fa914182c050f103409461058035601543e00c070850047d011301c42c0d0300441d48054601805e448030042c010880240fa04050640400710703140c4841c2e2501d10110b84e1003141d1100e024545642c084400d180440c4241641d80309507120511070380f0100d0300d040e009440145000d00d018000c090700300000d003403455881003640700507802700b880c2c4140340d034141c1000381c42d180da5120040c0803503940c0c18020040c09500a900b544e01c41014001c850080750b9041803078000c146050160149901d00c2ca00c1154481c10a44c450740170200f0f05104201a000068000c0140c400711070000191600c0c56440c3e0a04c1c1c041d0740304007841503034000d03c00101011114102c00252041e0b50082d6000424402004010348000905008660120350f039441040c1441c3c030000c0c1c2117036000f481003081d81d034075401f6040d0b00c2c8400040c03050104545200c80c01007100a40646210350b182c1040d030000220000e04e0407070701810034400900040e00049461001415000c003001007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 733317131 1250 733315881 733315931
    0xa05040608070501210c23030c040e1314011a0d0f1209051804060b0d05030306041a03030304030e030f06074a0a0f03080415020f010c120c021b04 64
    0xb0170300a01b0b015079001801c4451107000314003104443c005611a003401c0c0c60a8030322406502e901d43e813a16050881c61000910010842e8019480c03540c40400091440f55000706494201e00c000b042803c154030486101040c02e04a882c0209100110200403464064940c1012500038001982d071013a10001100c0320002070304000d42060b0302c0b240000c0d54681c42002180f09500442040040380901c4c030410150204030340000d00303c2d0344203201003074692500740d01401013040a0301c0c0d412014610700021a045800440302030f008140500741890700e03030070244040342c240c1181c04054042450f2620010b4420002c900e0b484042d212840c103060740c4400200c0c01202c480324000c2207520b0703040e05411000b080444440f4000c0c05050b600d5800142d9860000b0400e05a0794480c1d0b040d402c0a0419200d45003030740240300408114400d180410491800a220b40ca201c200180e4030203400b41e00c0440408150b489482c11901194848400004000e103070304c40b8108071000407600851928440300c03600e0180888888 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 733318381 1250 733317131 733317197
    0x123030a030f14031e061f0810090906020a110a0507030f02011214061e010903060209210102030108011803200f0f0a141204030605060d060c08060a05040608070501 72
    0x80c0464081c0c9001c3d6808200d8141176000314603a5182c086c080030604001d100b01e003031414a030000800c03901440c280d5600a070491304483c0c200b5a83c0020384141d0b840400d00703852141d030000d4884010380e40481585024102000204590441641d51580d01c4040b88000360220b400041000304583c807561002c0c0800c2240342d0103111000d43d441007645c03a00d1043c0c60301403042c501d614540c504980500992408250144c54201e80c1c10700e1503d601000c0e40c04406840d0384102c145006030125032040400440d07241e60381000603103a43c10322048500f100c1000820340040f00045ca8440c000980c41424151400c200290400d50b124600d54040d117014000e07040b0700344038040c0301d0021802441c00101d038445940a2054440d400c1d4941d60038035150000021245581102004180301040d036541180350840d00c050201d0765080301c00c0e11184101c0c0c45c8003960800207000711061082c0c900c0e0042c0000082c1c0822181042498a07107080181c0d144228899207041c81703035070700302404414102c0d043c41c0360040d1092 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 733319631 1250 733318381 733318387
    0x1306020f0d0e0d0f0c031416030804030f0306050d26300f18151009050a05190b062107020f06011a090303130902030123030a030f14 58
    0x14520201420b4140344206a030310070940c41410592003288403268800c280c2c1c031009051601610b046604c1d51520031140f07001c1c00c0c2000000d404103501c81510103540d0003550386040b613040a15008004507034100c0e494080500340300c414003540c0c0e540702540c0d0005a01c40c0c0300e1020210711400402c0d81400d14190700c001000c000c240000e510b090056911022400600000008400c8881032581900e00350f858641d0821010009115402c6c2d502140d0b00d103109140c00c48284041105079001400d50848001c0401750720042c1c00c03c0307071440c07a0040a410030301e882001d204520345203996105070781d01c0a140c8008a46c603485c2007401da807280c008035500d203440b00c0314140710202c109031080700d07985040e20700100610440c450864905c9010841906076003040d40186262450310a01c20342d1500030f0100d10358180810800822041d5804200750020100208003580b48e61601c3c0c0581d4042060b044595400300300600d84030100c4c0da000c51a2203100e40d05050010452040c00b0781103901c0d4440041e000650f01c400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 733320881 1250 733319631 733319647
    0x703021006030c1a0708191719111204110a03080309030705060907230a0e0a0b010e04090c0b1b06070e0a05040c05091509131505030a0201081306020f 66
    0x581420302590b104e26241c03801c1481c6501d68043c148541680179000a105100c0c101990b030300e0f2014840060031925142191024902030a00742e001c0c103560510944044007041c050388101401904004000b01c90300741d0403d4041074112410700c200400040c00c840c80580c3c80c44003545d80c6c6040001550b00301d502540c0702d1400c030110682c0d035844680283c0d01362142c040050040f003030024982c0c05450b203034484140c5a980f0700b000a0001441c00c51001c2d8032480703074140850222013181813180703d6071144002190b01d401d00000034007185403001c500c84c0500d04041201c004540041251822180003d09681c0c0e02c0c0d00f9400030800803c3c0301d0400f03401501802d8144038030315070301c40e01c10240300c4011207000c0c866966403001c0100301d4003210a21004580c05122003089440d19a201e04041c1c0c0c0300402141c40d100c519000150009079140c0a0700003e9911001e04108010a0304400041d140680040140d40c44c9034002802c3c0582c000e00400c0240901c00d480000c11a568040e5058248080b031103988400c0341c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 733322131 1250 733320881 733320893
    0x60904200109090c05030907050a0315180204050f101a0a080405010f0207080d180c150903140a0b09030c0a1e020409200a0e0a022203081207020109021005070302100603 74
    0x10544807038400c8d02c58010081024a0801d443c1c0048952000e05031355105024008400030789412a21441380c4044004540c0168503103003d0706200d43c8041c0102060f5140c00110309038410606d802c14030185041c10550b00441d840c2d001150f17202203050070240d001c0c4e5594a081f5015288110103400c03418004220030003042010005040d041d42000c000f03128113107850107400021034000390041c109851040c0200110840c1e505210484501c1d850800a11501c986030040090351040c0e145503240d00c04000301d0305001003038446a4104e240040134510341110362282d0740d0307200c1d0b86010251600791400c0344070194124070810804002d40c00392080c050641241450302110810056240d00383e5202c040c0e070001803400d126010243d50207a080c2d103100d0b4441011200094000004001c0000001e42d51101d0b91031440c030303d1070000c51145007a195610101040c5007501140078000c0000d6a04007035000b4010390f990213500300301445504d0301544920a904080303150042140f4048804c5140400200601c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 733323381 1250 733322131 733322137
    0x301020c01140703110306100c050f06180307210215071d0f0d030809030909090c0102070f0609060804030509060309010603020306280c090806100608060904200109090c05 75
    0x1081d9400c80703055565000f030550603204170602209101d02e0402c001126480d00308014050103e82e480c0a01021603155078113894190000c105001c945d11020401000030b07100183c0000d0951203130051801c000050b91080344400e5884071a102d41c04c8144030912045108004c03c040388054411405800d080c000400340c11041c0c0381320344a000b1000c00301c0340309850424840255030700c0000781c809217009956880c201c07801d01d00513000700390b2404100078803404c0340c0c0c0b00340c0030a0051062001400e284402d0344d001903d452801c1d88620a00a0625010840e550300a1075440840c0d80a0030032004a603100d250854151080c0c00d245644803501100b4052103000540c4110103407442501240c0080d22109180202c03415192140400f80c1c1c0000710080b0042c640c2e400404101e40c09090022038141c941d03480074180442201c4103c80541703c03000400601f948074150b1034210b4020390f04030078681459200c0c00740c480f420803400d0061060100c88109580d01c101c5400c801030102200801c580000090020140d034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 733324631 1250 733323381 733323401
    0x210051309050f060d080a031e0903090e160c06020c03071406090d0905030c06090414130c090b010507080313150608070f0f061101060b04151b0506130807020301020c01 74
    0x3c940000050090406641c900c40c0c09800150107420880700c0e0101b100071701f08491062031612a035100d00c03401c016050003280107182c400c0c0c59501e00507007004549007a40400034a5200803400c0400e00500290700030030071500b04d64001d0b0001d680c4000c094000f0b1710310720402c100200400b40036038525103285004a0058052030846094a61498408004443d4455280221035041e00325003003580d641d290040040c480300102420220b8401e10b51090f00600210484d0082091504900c6400801c040601c0c0c0002801c1242d070704101c201c0000c0c000074141e0188001c028035084001003c030f82c100c504041040040da81c4a0508017030350384130784c090f02c001e4070301d61180c0e201c1031241ca40007040e1391049041100944180a07610a0010304c0c041d03013111a50284a2100201d541e148400715010380820014070103044038114901e00e55800300c03801000100c0040c0410300703064100b10888001440861801d40040f1401c0c12110b042c25141081d0780d05102d00d0000039070561000908804210040d00010104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 733325881 1250 733324631 733324651
    0x32f04060c0c124d0307080d03020403020102070e090a031214090d0323040f0c080d0518100804020415080a0b040b070f02030f0f0904021b01060f050d021005130905 72
    0x2103441991340300d220702c040800401640c0c01c1002d99048070a003903140844940c0d070060031900c909a80f040010300700b115100c07803100000c5d00050180207650f010050b00c0010001c2c4500c00e412850804806622020066402000c000c9400058074022a46400007114820720002d40042410080d04190303a801008204801090500a802402c140103101d0880d40e808403490403030403655150745020144041940c100c0c0c460001c01008119000304100811884a103501d402c1c2ea6100240c114a503141604000c8034842c411094502c0003d0f54040115500640c0c1590045001c01002d400007034080b1041d00520510302c9104840fa052100039400c2e40e00807801a000079000b074450327000858007488003210300070150748108100350301c1e601510300030041c20510704000c0e42800c1c3d0300b02c0018140d9000c04003030480d00d40361403140c0b28106420700c10b81c0000d2058090409840d0f2030100030807035000300044040c2c403c8039151078950707005000c2c1d406c45911900d1007140181807511085540000c1c482602c510f201 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 733327131 1250 733325881 733325933
    0x70203030c060403033207022806050a062108041508100602010e06070f03060510080901140603070302040e070504051602010e120d0e150106032f04060c0c12 69
    0x1180e102d050540c6c00030342c140b144000320701d0200319102000c5c00b0f014007904114854070392a0804602e80140c202e20f021b8243e0808016900345041c03000c25540c0242074080110310b08001004214a012020030003441c040c440c80c00c084104d0300f003c0030b4078040c0d0340c0305c107198101440707610017110b0340188603d105503014034407003101c107131500000c03400c032110a894004503501c400049100c050080f14412813044440ca030101e500c1e0f0720b0f4404551072085075410079006c280d0394014001808428010a01e40c1044020a560145440400207907106450300c80a40260350750300c99030381c01c04003e000b0080a0107010b8814002410108150030140500d480c0701c0c4015403804840003544000443e4103903012000407030342400c0844508001000b05440d01501b01148103868203200340c00700d000400d070b000382000e40b0001144903104825041c0414482d0100200611400301285450501c50a4605603203483c5460071000c820303440c0903502540d058101342480c2850005400c20041b031411100c00940b9030301c0006071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 733328381 1250 733327131 733327151
    0x32909010608250611070306090609030f0f0806010507060608060117100207030914060d090b0108120306090c1c0920041e05060616050105220803130305070203030c06040303 76
    0x1030f08003611060b1020f503c14114003004020b105800010319400d14a05841500350fa981da80720071a108080122805910f542800c4103040e008054444040030a0400c3c1758008400c0000504005004040606000c1c0c082015014080248e01140280580c0e1048031107a584071100100000e0103800300d8103992040049810794000c4074001d46207070303a0341915028000d03410103d0500201d80c0a8040342d400010601c500d5a1000450042481090255100701000d50514803850709244440014003010f00041050107179a843c2c1004c19076201050341196070b1a44100c00d0480c40a003036010011620038100b240900a0203c0074828808884e10f03462090720800907801031000b9510413a80004081900d0b0441880800180c0c000c9940300a005042502e46103d040303d0140c4c2c03550351902135802d80c3d941c0041140c580340d8206901d40750400e001507400d855480341d40d20140c6120091081f43c9000c001084030007054041ca00303491000b6401400c0c0c0c0c2d154505e4a60b44d40d43d4601c05c44045d0002400d01200030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 733329631 1250 733328381 733328413
    0x302040c1403010315110304030e0406090216060c0908100c0807090819020301150b0405091e070f0905042405120a06020f09090106110c1801032909010608 68
    0x2111601d54040c40c5801c5070720b19100c2580181c018400e060001e5214640000900c1da1440214820f07882038451080400c218010320003201d007140c00c106181ca2040041311044000b034410000307155489500030400d00706051003110030388055441b043c15842004044007006019400021031054150350301e4039035956907002112060507920070004546c0101503180c5003503814a5445010ba070010380041450000302c16001e01c200e4980d40940c941001c0480c050009207400145180c0051110301c80301405201c152030305603008009000b1750140070102c400500c500e4010401c01c0000c0100500c01c01c1802c0b0348801c02800740c40c10704425040345240a8020410f482c2c5210702c407160051540081000130ba81d03036290002540302c0814124070364024003141d00303141e079620303000c83c00380c41d280c0d582401807071100915901d0718500d031102d80e10800500950340c0000400740c1040741140d801c85151007218000780e1211010071060359529000f03a4030038003000041c0d04150032003000c840c4035000712454042561088 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 733330881 1250 733329631 733329647
    0xc03020f060114190b0412170307050328181101140a110a230607050306090a09020402160c081e070b0f04171b040c0801030b0a180c0302040c 62
    0x1443d188510a0480d42c1035007004019922040e0b19141d074100c1c015240d842102280d082a4041000c10340307884242001c00c0403009205a0380940052900e0950030110302c0502203003c01840080c824820401e10304041101c0149d41030f0440000c0000c0110740522554000480c00345501500d82039040d85442116501c42c09c004005108400022400e15402d054200c8480e11942e40184861040b240c001c2c0214418694030401603d640d0945070b05040903071941802d0101c014036a50911505000f000030381d41f1203440b2580e0043c2120030000344d0b03049500c002002401040b4a0010411000800d8001c01c031140751030a05450034101150001425180a500e055030440e0420f4019009010104074521809010740040d01c0300d5002542010344a40c16030420082ea402c1011045d40100409500e40e20300742d9062001e124180c170180112848200060034611062000811000030000041c8604031a90711440c81081c54840c000c0703002c962800d08540c00070407400240c0c400c514204240c00038074041c0d803213 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 733332131 1250 733330881 733330889
    0x4030210050a020607030f060f120521221d04020a080c01051602030708060702100507030903080f060609030d0203091009050d1e080412120201050606040e0a020c06070c03020f0601 79
    0x1401305907603130b400441c05416a800c0030801aa1107420206902c1c82403501c240141808800c0c0202e403c2ea541003080ca4030101015052401f403881c1d001e4110842207070100c0700d00b0807204024248240c004418040ca2007404c0d400414460040748400a0481d202030120303000c0c500031a2100e1301544c40f822101d0700c40c081451894003080c01001052140d0b41c01110740c0c0e0034180002c4c240c8e01e0695480e440c0600f400421628600141c12200003000c44e281300b8880c060300564903190030400f00300a40c0d0003070056100607020080403091a400141c0b0340da10001180d9520201405481c9010301e002c00c0690749401c10315000348580142c4560071412403050f0700d0756003222401040a410051140c6803514202003580b14010401c0418a040001c01d1070000141300030f101e0b287d8603021405550421500b10403c48a41d2011641083c003030020565501090303400342c81030b100c03000c403c2e5152140440300912034a440701140c0e00400d010840030139044146080c80764080d4081c0e40c0300707a80a40341c054541c042405 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 733333381 1250 733332131 733332133
    0x50a090b04120b040f080c1e060f01031e0210030b0f0603060303040b070302030d0203040b011e060212090f0306070c032d0c140a0b0703060e090615010207030c0b04030210050a02 78
    0xb202d07101051620b40b0490700311303001c0c44154403140d01684a40b2a42d60160a1482031035005031300400303c000c02191190320401c8013402038079443c10002e019080a18040c400030346042d040070b03003034507084c0800e43c40302c1803095006160009041060502501900208801602c034001c520030018040c100305d021248592801009146060708100784144680c010000941c00c62000344000d100f495698402140200c0c06044008031039803400c0120080e6510b4074014440f1f08904e20030801c50940c0002d40b0011065044504545402c082400315402032881403080c0d40c5485900c003400a4250005101c01d8850b00070703664943c40e116207594003103101280c0076a0714203c40c00140035080b11446150203031826840741414414800c006000b503481c122450006840d2940031038180941c0607017601c2640c0045c1054103616040e450540e01c0251180002003c000300d10f0780d003034810050f6a1007401072501455010620b80c3c10a034482c84800b03a2038001d404102d004003041d40005100900400c103585880c0078a80c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 733334631 1250 733333381 733333409
    0x503010e0a0b0c0f0c0102031005031c1d06070b0106020d0921030507050a20010e010c08070f1b03150e0d030905010b0301020a0e040b01030e060406050421050a090b04 73
    0x1e0364002c5624001007510401120600401140106810080074262102c4001507140e04025141c40806d0000fa03010a100e80d001000c0000703034403e8003280401440c91410040c9407092000d00860070703410103401c0e69030702840c000340030020440d0720300440c1c0c11380e24240d013100c0301c5c0300c42400242c1c0e041004c0d0003408151510795204202203070700f2f400c40000f054070900d860360074201941c1e1400d01c1c03c60510411150042d0100440c101c41c030301400303000c100140c06d1901004801000c070000c3c012604101010300700d030000191480c02d00200c1d0310307404201648081c1c2d848900c0e1240603c414840e44070b000c201da8190040c1c58010040025002c0c01d0142039010014040452120100368000c1590324802c50352552102d080301281d40d4207101414086200f81c03181080c0f11140b1040004480910b0003240c141071808001c20910000051507950056000d400041c0c540c030342d42000d580500c003100c8250140301208498901c1c4592140140c4900c1c0407607110005500d8840c0600341c641d024602800d00041180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 733335881 1250 733334631 733334633
    0x30d08160507032c040c0305060306060105090d0201140702060406021b011e0806040908030a15050406030b0f150306011418010b09010c030c0203070b03091b0f011d090405160503010e0a 81
    0x720041d05044183c8480c500101181c6001003001e80786d80745610340200351740c0c80c10065981014001603610403000d18104d403904510b00e000035200031031600007a042000c40e081a043c4410301d6412a19035940091030140c0342c5584401c007d50b2001c038068a4280341c0090400408254003821503414004044548002c407409002011a04008010030f250f40c882e07110001c11021410340c0340198050a01100c000c1924526038070844012003803580014051441d109040010548410495810109a5540c1415504c8130740182c0104d10406050070b606000b0000006071241d524020380d4843c107019644003034020f4004140030445207092007149400101041066420343c400c440c4007054900c03a0915400340070031500420301c1e00c034050700080a44103002050241840040241401d80801c5130203c4001082c1d00c8049117540a1401d40d240c1880ba10001501c10403007580701c0110350344400340c00c030202c51030f05041032580d90b07603940503021250f04a101d000c9400c1c10103001d658500b01c00751006000424403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 733337131 1250 733335881 733335917
    0x1d01031103030d11130b04050303030408220609051c02030705190906120201020f06100608180a05010b01112e2c1603110d020f030d0816050703 63
    0xc040c02541d07042c002000100001881c910580e01c0341039128448580341c0f001e03482103090386540c035080503000443c00d0008103c00d640020450b540283d200007040c0c0c861a1a4200c4100303103a01c01503a9801c4802020f02145e042d900407000c40c12107a0480b622040010b001805c0c0801b10000c5402a4060304440c2d82440b0b203050542001c4402e81e8942e100003281070380d070071503502150b1054004210040341e0f82d1840041d50383c10011003103010300d0540501523070f00785a946000686400c2c03080e042072042440c0095041d28580070445841c0081c0e000b51400da4909280c01070090414002540c00700f2140b0001100c05170001404d46100354416194040d44101d000c0d000611b6296601010a02d076101c081c244042000c081c502e02d0307041c0500b1094400d03102c900c50321600b400c0c60701b00e250000c003d00000420110328805e07142c0ea061001550011100101400801d082c04500000141c040c403420b181e429243c0d6202103046e12a1098000451501c040d00a0442e00c92081003409400a1480202d002108003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 733338381 1250 733337131 733337153
    0x31009020d12110a051507020105091005060a15051b0c150f07020d080304060c0e0105250204110904061401020d0f03091209090f0c09180f0905010203101d0103 70
    0x8268148540343d01c288403c454a1303d007800e6000c6607550050001205560151180c00340c06c00317000c4c0001c0c00300d03190001070784d603859900c50400d019880d00c0d0f4010a40030380b81c00c100e030406013001900c0c503202c0418020024009600400c188030720302c111b0348a8031000c244003241591100c00024420810916408201d1040c0d0304071801010070503a0800141c001640c0d140000000e0b1445155155100d00c0c0c01c0c20580212141c10030b046080c40740b10160b00c0e140382c0c0d0000440c0c41c01d61507a042c00d07541e800310302c400700d00204008130000c0d00a4540464500301610302406001c03102c004403002e0029603101d0380507441503098112040c0c05640078590045055000b00d01002c000480ca15002428803582e403101152228151480004104120b6003489000c03400c1c0030b11016004c400e08244100300040000401249031442554408035005003018030840e45604186a50750301804207104c8040b2070708140f4000c0d4029122400482d44105001034008a400d9030342b032540210148960f07450386952251141c1d50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 733339631 1250 733338381 733338413
    0x1509020904110711010f030905060402010f02030c0f03030114040e03070206030c0f190f110c04020c07091d0607080c0f07020d0204090c091820060906040311031009020d 74
    0x1980b5500c0750b410228034000900300450185901c20450300c18280050401001024400304045c02e180040f008038000060340c7c4e402580c20700e805600c604082d07201300d0640c0151003604405010314002034070455400005503059841414420031013040c200c08020071204120007180c03090700284103620151520101035a4000940d51131589003400740d4801c40d10b513901040000f41042044c104004400c1c2c1e01001d03c0e80c5d10318460420300200e0007504205070b5200060030605101d190000ba41030448041400702c0001005800c005001c1c0045007030200c7c0482c0018001c601c070500c5084001003800c4e00c1103005500a07403200c40d44034580b80c03040c0e88600c6135070712154091740c010940c0c080580061300c503441503c2580d4000d1022140d4079081c51002001c0e0b43c4200e00c180342c0300005182010110744800c60090400c0d0000207c2682e1000d0040414440e0090035511680000045400018441000c1c1207012002c022030540300030503034288110040351030202d0080e4204500d410b4010026812500c4402c00c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 733340881 1250 733339631 733339639
    0x20a170c0712030204030c05060f03040f0219030326060a031203060302181006030203240d050a20062a0c1f0e0d110907050904020a2115090209 63
    0x402515100c1c1c41c03904001e2400e03980021381c0003600300148000000840c0180c141201c070f9501d4480e40403040a540d0201500142000c0700c03040b54501190390300040c090b80c0d4600259120441d81c0d81e4240500f541c0b101c0070984801e07901e580104200c034281214400d1082308010140c900441c01c540f1203040d09044400c401042c55500d5030040003603514408649005908103405440e145003040d0b00e0352141d90150721800615005000348064a054103c54038149000404010080c000310000200d011a00c81c7c2c0180c40ca003c0d0098500602c008082c81c0e01910244541e551500c13800c0c3c0781841207603c1410b10701a02400d1601440c030780b0f425520708002c609a210811201660440800175a0310700e031311055040549445d14044848680101d908203612130100c44541c000040c81c3c49501d4500d042c60171540c4a41404000034001038050819079a072088090421501c492035120b02070400100c5540060840100f03166940c0000030307500580c031003801c4c0b1840812129103040c2032b40000c2d40201400f1680 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 733342131 1250 733340881 733340887
    0x21051213030b07051e0a021b01080601180e09061608010b04030b0a0f050703020405040605090f010510020f1f182102010f09080a0e0d110d02010309021c03080703020a170c 75
    0x40ca07821210b59032094058449180d491b544824043e20704600c4403006110303400c00403100c1c1d10503138020041300d0380040c0030f00b014880e010103001404841c1d102c0e5049014504528030600c240c0100004895200341000758880444903610b4600369040c1d0424410000c10200412013800055201040c568000c01d50440102d18404180d64010907148121a140006903010404101c2e91429000b402c0040c01c0c2540c500740a814031030744004440005000310383c098044d15100360f0109101b00032031170000e050b050654904091610125460458242104403031030304222412900071f440310001c20080da0b200644040c02000c41d11441410296090b01000359581c0f001d178200605414060403007001d100780001d590f00c0384e070024090440240000780034000c08054034404000740c40014507030482003086030741c1582420903200490280c012100d000f50000c1c0292004020080c11009034969a0310030344071048955a0020210103c0c0142441e5100240e2204082c28a103061580309581114804003c50f00d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 733343381 1250 733342131 733342147
    0x70501091a0a0b01050d110c0d030209100311090f120d21050c1b0c040f0209030f032703160b1b16090c0921051213030b0705 55
    0x10031984140c00030364a40e901c1d0784580700e42031070808078164484800101007001548000008200d409020034100c90250380c0c02e0389407050440c074800e0700c040000c0802220f07000044448000c0c042e400060f442801141e0328910b8101d842d00a0007a102c0103009a062079040c46c40b00740c100220380c0103081c2c07400c0c3c02c220740c2c540c4425502001c3c420661142d03815206e00210841c0300002c0e9503c41820120046000d28040a00c0a0a2001c00031124030080040d038201b180c82080003500d0070001d841c880164098a4082000d4200700203030090415130b80200c040e25004c040030200701e0344030b10071003500803003008804d40c210041c0c214003c2c540c3e071140740c09001c65000811500020381d4071061a00541078005002c203203800d10185100d80400c1c415460f90213000c82030743e070441c080311540701d90051040560f00c1700e15001110303108661080007003088208d0301c0c1e1200c041c0004e120325241ca404041d54036002c1d456851044465507021611281501c0011088440c81d46d205d03080080c20281c000b00c200300301004003038 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 733344631 1250 733343381 733343383
    0x1c1112160c0e270a050a17040b19121103130f02040509030403021e0a0e06010302071a07030b22020903030c03030a0b011209030e0411090d08040e0c190e04020705 71
    0x3500c1110596840c030442c00f2800e00312015001a1802c81d075856201c6610040051740c00b140c10f0503102d51110040045010021403801140515005481d81000120360011844200e140108200b002600d0f8070010396506c0d034404003030700c200722500038442c44200302080c000b44d10251002403950044520140f4059617500040c192034040d5200082c903440072078248150320308490101070a130180400101c10b84130003030100d102c0d60140e200c0e02030282c5401c07000600c143d0080e0126503440364000f07259004400b508580d10049182502c030f2500203403400c5c090799160b04081d024103c440d10252101d400f01c00c5c0c24400e40000e58081600c207905401f0611409081003810070107503011785845c0b0408502a00034a00040c40b07400c0011035011220705004009020030303008002c900010b0001d42d004150200000096481ca1203200d0a85811a0340441d8a106000c204005001a10810403810b02140c0302c80910380c586000790380d400005600400c9001c901d050145900149154015101508203801502c0350b03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 733345881 1250 733344631 733344659
    0xc350a021306030c05010503010e0403080403092c0a1107080310170c011223071412090706030605090a1e020315030105070816050c030c1c1112160c 65
    0x444010707240c600510402c100b0410041c01780400303191590843d03140005803074540380c014001070107200c02d4a012805046c0f091038a0400307010520903010b14010010600d41503001e03010350b03a50b241e420300d00c0400d1072a103150140c1c0041d0288071807403a00301001611403c0c8a507001621528401540340030024661035200c90300349a0030270300c074054000d42200200141001240341c0103c0b4100d843c010b0f0003c50310344070f100007030704543e05c012031042c1a03502e1a800351031100f01650410143c001c01b142c040100c046604000d0712600c1104251084070f950f81e40143e040c0d45807400f40c281d01800a400290202100391b00074800d220441540e00000d40000000d40c080340c2c020340d41840300c1d0301d4840e000e040c0c0d030500740500d640041951410301500c0c5401450303c0140034281c004401005800180411051420001e845e020000c440c1034803040c8400c0c100000c4010303002490031000c02caa075104580d0500010402202100010240a24100380400040314180316500c0480e502000001c01003030001b030403400f03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 733347131 1250 733345881 733345909
    0x6020c2107050105100e0103060f090516050a0e0601140c03071a01090c170c0c0a05100501081203092e0608061801110403240e03070c350a02 62
    0x1a0550301c0c1c0d1142015829a140140031001c0303804029020800210081042411030f60001000a400e552502e0700c01c024100c0c5460141c07040c4192454408504a81018181107541c11550000c42994071104c00040100846d00030703020801c5070060444000c1d41c0c000800340d06000030309480c940415035489100c40161a01c07a07840e408a1140140b0400c2d00d1031007610380c1c500c10350424420081601005a001450040c8007820b1620041011a9048ac0400050002c0d83d480025207400b807402ca00c403000185424821200e55220350540748403044106421a0300620b5840042c0200510300c44030014080800141c619040c20040c10969401d900c520440d006003c01d034010f88803030300f4141418024103010550f039a141c1d914240c2c0c0c0b281556083c034100c9e0112603001e1040c1c1000e005910303201039039058000e6881042401e00d440d98903400700200040c01070b1071040c0d1140e12001d440e1102900c040c050090405601003503e01a103600c49020200b640000700181d0031503a40f00025230100320000140c0c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 733348381 1250 733347131 733347193
    0x70308090a0801091203320f070809071802070206041502070611060a0c0e041b02060606090a051e06042c0f070806031e0c031509030409050a020f0a180e060d06020c 72
    0x1c08d00000501c820354940d04502075103884101814070849668454220b8801c6441d107a8000351846c2454519030103803060590014101c6071a1503840c486107040314403640c1910014081c407140454000d0203014070f02c034088a80402054140c2c4c4a448140c000d0a0a40f011400d020181c9a81c4144d50f50b103004024002d0300d038031209458020181800703803a14001030304803071040105001035111510342c0d080342400ca94088501c0409800b40c0c40060004c051070640c1207400c1380d0001000301e400c0c03070903408110140c103101c1c0354030108030342da5a80c080d0403610503601820803a1580000c68111031103074040301d420000040c2680c0e01104c007400d0b01c181c01111016001c406800131030b5080c03440e14042c005240f81c40704801c114081e504d0300e080381a40305d1085008040807240c3d55808180c6a411650550300d107032049090107a540c0180d1000500505031090125603090784d02d0b070000c180d2175485c07808940582409000c42c101004159070b200c01a420800c611545485030303121381c00400400c1e000044038001035103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 733349631 1250 733348381 733348481
    0xc0c063b060f010501170c040312090e01050a03080301030b190e0d02060a05010614180d081b0708190f0c030c06110318040c020c03070308090a0801091203 68
    0x49840c5080c408000d01d90050141294010083c03642c1002d407086101c00d000c9100e400079a10350186403842d01a68101609809004c40e0496000b038218140b8420b481c4800400e001c103a99030010080c421500340002850902d09000400000304402503494204a4420b240c001013101d401c095000c44440071a000b50b81d40c004031109455980510540d500070f1040c55003071285605005010785004005c191070004030100141c00625121004e15203080c0d08030007820400302c10210700380390030b1613002041850b0b0503808071304281d0000d0400003803010131901010044e194180584141c039003441500c24043d10030b960303062100c01c002044d5500c110040d5204118006c0418100000201300d005c6c030381d0344c100c001d03401000340b10421000c0903501d0311a05011a4040b58001c0c41040c208d04015041180503050b00c40d0300d501100b0000140d000e40b03540c44d0203551001d06075a072035042600b6a1101d1601400f0040711000121401e4400d070402005141c52524104041c0b0b807d0003540d10003440480d040301011940 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 733350881 1250 733349631 733349741
    0xa1e0b190c0e100e060d020d0204051c050a121b0807060e0a030c11041d070303180b0405040506030c0916170708062b14070501030c0c06 60
    0x181c440e012088006103020906100914042150000b0a00810301803106804440d80103954005c1100d5000310741840554540140e5401c0d600030307400c01c4c0030b224032a2070603c514188501c0c000019004031a00000180894891512600d01c0d0650403008241000405040d03401440c4901030310890301c0d40705142d0590f60720074030305284c0102c94543c2a414543e40200c010b080c0440c0d40301c500364282d150881c2c807500c428440f00f40058020181d80c614001c2e540c060300805079100c9270201d40502100c6c0641c4451040c0550000a1103c0081c240100403c40c80d041c00140010b05180c0c2c0510340c420380240c111425403180c000002c2d0800380071240d0009100d4868490340603c0d5100b840c1803410410305d90702c0c81c66403c00c95005820854020105400354140e110f0458005000b0b2040c26500b040e88168100451401d0604000f0b5031200c00c2c40000e6881074aa0015007540300c1e00c21000e9040f01543e801d00c14118a5070f40c03034003404426800d0750405103084100444560402814000880400540c403404154 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 733352131 1250 733350881 733350931
    0x4060b030f2a0d0f060305010b0a050619051606020309160906120b100e0c0703170903030117160b07020f2407030903080a090e010b0c0a1e0b 62
    0x802806103002101c0071900180c080000034031120407601c90012503407284074006052005155030800c0c03104c0d071030800d0303000014003906600c40070b00c00101381d80a46a942d1074006000051107051050910505068001c224040c41100076040e1002c064010500004042e150003090380c2090f2080041604144d82000c1380b020b110004c100100000f04d818000103141c150007115042030f807040035000010300d0300000c444400858800f03010b00602c1104c03801c141441f1583c65070039040102c0c1180403c01c0b09000c0ea140b2010440c40f5440f69400c1d80095145030300b8120162001c009031b00c80600144030301e580004003584640b5284014240e005400c07510780020380100807035641c41d2454940101c0b00400d52121050030401e041410321162041c03030f550340c1070701e2801303e9084406600c0903100d48000f0520b4500143c0c002c0c054021a81080380b40710660362140001c41c0341d8454210040c406a0000e90f480001400090a510030780119000300744840300c40c2d032100c1d094020110384204080303107100d4899105210b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 733353381 1250 733352131 733352161
    0x60a27080919050603040206090402070f060218010305060306131412180d0c14031f0b09010807060c120306050d0303150602010b0f04180203030a020d1e21060504060b03 74
    0xc1c807610800700c0d50b14200c04121305101c0034101074041c10307000610302441e031180e4046480d081d500c074103182c0d44142503042800007900320401a030049038026800402a43c880c1c02204d000710300003000b0308240d0b203520403205c0500d032807588126001044081030f940352850501900d104590400a400d40d1241e194085522541441001502c140903140a4001280e00654480180c820345120340885811342c20019160000420b000d042c1c41c010070403c000d1002090700103121201059428030820398845022036154956401903000003001c00624402048400d0044c404c142c0c0d4905002400680ba4004191400d00740c441c103401103600d546a07402108207070302025006281d076100820104800b01c1c00140c412202c0c3e81090720581c0c460918510011310402414107282e4020f040301e5030340041881c041e448200145e0070b4804034480412440d1710851001c0040060f10a680e1904010a940c001030920f01c0e000010007800c00782e5401010032541c94611400028050380e10f12a07460b4034140185c81c20b010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 733354631 1250 733353381 733353409
    0xa0b041209121e020a080106030c05040b0d0201050f03060120150708070905060c12040e0405150103030804060525051305040c092c0a090210030b0102060a270809 71
    0x501070410404541ea0080026a070f086002c0e4a04103c1d64500020744c8071121500b1440055103030540000c2004143e1003c1401c44000707850900c032403401c0c24100580c0750750000700640412010060600d068800f540210b900c8001410711507011820044000d00c01c11aa00b012500c5500c10008402c2038000c00c08915807020880c6400c1507c1d24007120020913282892003054003035640880d40c406c0c00d507028450744112034056210513445640e54103240a50741c130305950541d5180620034002c0480042086540d041c2d0340c1640b190451511035a5a201c001c00c5c0040ca544400445200c2d41105210001c1a034610300c00d140e41d40e50b4943c401001e020f41c1307140d1241d1002d84070f140b03495202e00160740c1002d00001201c003000c0c0e03018a4032110070005910f44051103046000700d0114000c0000d0100150b01c5000b055000381c51075005502c6405094048403402da401c140541c1c000300c0040d410585541284079451207070882c4120602c2d1480314003c4202c2200001c0b1008000803400d5407032802c0c00c0c0e048131512 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 733355881 1250 733354631 733354649
    0x806030f06070e012f0604120e0d0b090309030a0503220305210c0f0d030b03011e0c0201020f070501020a0216180b010519020d0210060b0f0a020a0b041209 68
    0x10b810075240280031002120001810b0045a034611084035202034800704180401102d03910000b0041981e891302c0e0304003100c0856051074400d075070341c01191007942d043c0d81076507001d0001400300300140c6490805000003801e21030280b000f000b0006058a080c0701c034100844c455001075844000307901072110391800c00390361410810307103000040010440c001039250408400e1880320003d0802072104040611a50401550510070450700021000002510314207104441c1c0c9d04202c0c00c1c208400305401e071103510b100d0031610515800303040c4550003142e100045400c0140001468200c1c0440b890707005070007a5809276003c0e580414002e400d42d80602c035111408850856801c51107060942010b100010603e82100003951a4041d4200e07034002e10440f00c803010683d401003038100c4811402940c80781d40c0c11160005020340100c0c0104a0080d010703031000e489030104050704104a4400401180d003043c188d180842c400c112900000c00c580c404000d001e680a04a1840c001003902c6010700250b4459018403d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 733357131 1250 733355881 733355893
    0x22080f010c110d0c020f0d0b0c2206020d03270b1e0c030a0906060f0315110901050d1a1f02120a0912020d0204020c030c0606031203280c0806030f 64
    0x1290380c8138a00b40d0320164106c4400280450440c04201c4180c0e082d900200790b40c90314400e1040708004000078043c41c20804520011030111500b40d602c42001510406001d079002e945003019290081c0c02400d8000c11005201d00d4a0307102034211480c5901860058804005040c1400789160003c1d115145030400031841842509044950402c20b1100410121609990769280300401c8019000300000700604070581d101641c8030700b0008507002c3c01c4041250042d260249000948080300152021f4140584802c0c0c18401141e07000e1024000d034040e210018400b49207400003507524075014001500f443c0004841150005802a02c0d00349020000d0400038000e01000c0c9070280d210b0305d000c0c2901d40320560149a40b41c03600c00b2038000c01030420002d500c0f9002240e02a01120004040e0030210701500c00c46d600e47e181d01e403d142d10355401d02c3d1045000d5204000165070b820940c0e4840a00c5501019038101483e040d40c0c03640c007103401480c1d010000458040602190340b0f4100104041c6107042d6024102c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 733358381 1250 733357131 733357153
    0xe0106020a08030c1201140306061905120106150314010614040312021c1d0a050907030c0c0503073804120c0c15020f06070522080f010c11 61
    0x2540d075000190040c403603480000080e80940082080d034049000c01d600803245561550924134002c0c82443e0300602a10440c1c0004a55160060441c0d80e6099082d10100140d4100814010142847c110100c281c1d07480303044c0007950041444002126500d0b40c0c1e800540564444850180c181041e4400c07804c101c04d0010044040000303408a0303044030b504c480030000241c03000c40182e040c1400800394207581d05102c84d8044415030045203503110707071400305180301014040e0000c22000501c603003d02500207a400780040c072480d029a1094000000c0b03400e00181408107075443c145198810f400403691b04081d0351001174240340a04500200724951400c41100b0959034001030f100b40320041c0041e041c400d4240004088078000d080614500e500803c3c1c01144680324810f84407040004c0d00003000510a02000507062007000c1485d078058205d82d60783c0d9241110322840702d1540c3c0344400e240e8503000100f8000191304041002481520301d0407400201e604801400081e000010004103803140360840d401b801 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 733359631 1250 733358381 733358383
    0x2010f050c1f090501021303110d0503090d05010b0d1b05010509031009033f0225020a090203090615100f030f0204170a15091e02032509060e010602 65
    0x10010342425800500c1c81074550140c4020340380d00503024144e5403000400140c00e05c00c000341c0c4d100341c1c0c1c0030321000d0f08030b071180905104400c1100f20015125810a02007160103240c1300020806040c050000421030380f070048006041849050760032940802003028021801e071102e4085402400e0908103a4180f210f503401290710356424444034890290b4030001c1c0c20406000d080340c0b00090304c030410b010031400b82d80d1640c04d16618070704980c20041074880e100300a01d003106000315840c0c548200000004c07042805a500c1c0301c100442c02c100da000c05041400701c0c402c80315201a51040c11a2401482107051840c65000d422000d200c0d444c0c05420341844116550ba0840348800021007185030016916480b910030500a000d15000f031520185000c0d0b1078000c043c2e002034034078900c81c011500d080000ca04103c851041350b105070402007480b40704501c846008680c412809450703d00140c00e840000c3c014020100f2030b42c4108003807102c22000c2c2e9500b40960751080c824a4090010b020307003142a541071580c06 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 733360881 1250 733359631 733359643
    0x10b0a0503090f0708010905012009130f050708041101020c06030106050a0c061802031005040209010504020903101d0d170c070317040308062e05160203071202010f050c 74
    0x1001401000070100c0c0c54510108a00000c2c861038074103840c4099260416180a04405001501e956080c41900002c802c81400a0b07007100d100440d0440c0b511030b41105002c0b80602c50a0f254011a80e45c4201880e41c80380d601071030340308802da40d42d5989680f400e840c0040288007280780d10350444d0f00c0404d460361191200e00480341924450700f4240d0705c5400514040300e6420041c10b009050f6414a0740e450303001000d603008d280203148228152090704102103c1c540450314119000303036018440300010022800c150f8010301c5030500280030364102c60600c41208058503803e030001c207043d03c00c01c0c41202071180240185144240710b4940f441c0c0107681c82902e02187d0307201404d05984103c000407540300b0103006010a00c50481111011181da03e428140a003aa65044034030501030250181062030508515003101d1808201c540403255800d0f49500c01c540c00c3c3c0003c1503400b00446610000e001503a810040300c070082c40300034a00c20864010340700040c40d824526410700140f000912440603c075101081c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 733362131 1250 733360881 733360897
    0xa091d150f0f0f04060b120715020c120d0309020103111b07050103020c0601152303070f050c030a20030f0403170306090f040204092001030b1e0910091d0601060305010b 74
    0x46054503030750001800109647c60013034101e10581d0b8002826072081e0001c40c0010b0400d03000c1c4c0d04068400c805020860040000003090380e0461080b0040b1076009030b0220744420b0042c980012602c00001304411603510040c04c90350340603214102d0003d010401c00000014040030f190550a100388900c0c51682d03280180100505054049003600c801881100d0003042814103501801c00180040f81e248030300d500640340040003400b03070750003c1410f901690403681c42107a080021441c249082c88112011408850a6200b010041d4a18880a1001c2015207980c014804089549030324614004001402030641301030f2080e0305004110b01681c5025005074000300003020110103039100e100090042208401c003c0003c0c414120224910244a4801b03413020001e8030204400312106003003001000802518951041c80d2407103000160030540c0d150342d00070100200b8140e9803074132921140c00340d030011a80c106418802d400c1000e0440c4c0100003c500509450030100700950404880e103c0c0d034815024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 733363381 1250 733362131 733362143
    0xc0106150c14240703060f05150a1413260304151202040e010e09070b180102010b060403050105071b081803030903061807060305060a091d150f0f0f04 66
    0x10240703400b041c1c2402214031082542e4001110381e294a20704403003940041c0c95003c000f031b180c680041954920790640301c0c1030b120000e0480046c0f44400380041c8456000505074400c011012400c2c0115402c5400a0180188000d00610f61282400d400903080e180c0c004060f030707061200c018200c64000021044078203550b581c22081e10000c6100e4000e540c590345000002c20f585100240004048282100c00d5040c4d4007c9034a9510030340b10491010f1340c9501d03502518441000c2000b54034041001500005c100190600011071124040c03070000b080d50b00198415186d41c1d446104011156511945407000c3c0801130131007000c0040c140c4c81d0640c250248c06000540441500c0d1800100d507800c20581e040700700700038200c4550b031030503a0f580d4954506003404000107102d64000466154040d0044902c00c802c090030f80319003d4034000c0484060134030340120602605420404000411081c0480462030802d801206220700f0314200000c190003000b0801400c0c2c10704a024460a04110b075485600150804 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 733364631 1250 733363381 733363403
    0x40902010516060603030f0206040308010608340206130b040206072a05090a0e0c190e01060206091603110108041104062c1009051905010b0c0106150c 66
    0x22006031800c1c8160000b500078082040889010000035030829010f41c2c1c4a0390303800c940442e400500380c0c0e58107000e440040105204e840180030030b03841401b40650014200d001000c00302082e0b4442ca103042015800801d0015860300c1e0158040d404018041c1c101c01e240b10301d1401d036926911050300312240540000c1c031800c80040c0c0703801030103003aa804000d607011010410303005518021283c1c482c2d110501c9440c2c0541620000110680660b21030f45440720390010207001960310247c01c2040504c2c402e9012045810081c901191003c041c1e038225010f03040f5a0000c1c00a400c1804c622807401d4041c844000d4000001101440016103085070b035444203500b13082090b000d03151480e04403e19168903102640103441c1150025035821400ca02c481400d84640f0380c100881e41c4c481341c0140e4002c0c00c6401462212108604000d01c030758642c01706a0004a04000c00c0d10815281840c0c416610203a000b0344c3c0a00e00800c030305440b41020b02c86c003001440344c1c2e0124207880c51040b03000b8000c108010780c050500a44170b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 733365881 1250 733364631 733364633
    0x30b06060c0a170f180a090204050303070201050d0905060403170109020310060f020a0b1003030e060c03090d03090f0e0117010c121d030a031b0509011707020a14011a0415050409 78
    0x700648900e12209284107817584911000003c203180540041449000810000a01d6030700760701c211070503124082c1c091403910009030015603c6510400301c070304c0c56950703405204012030400e0019a02030751182c3d41c0c0d0340c0e1708981081031140410040c0c1044040d00e01c10030074414450f1514006a0445900f4200100c140256200681c1454131040f000341860385023100300302c48440500280b03001d42c2d119403548000d0203c2035048c8540e502800507941030540c0100301e08046032400c81000c100700c600c6481d0203101e140c1c40f9150840c40c50303001d40c00384507019441c1006200001c076086030410400091002003000324042103000703181c210043c0043e42da403640c0d40300a0b20409205407564003400c03500ba0440340d1b101d0760480d0080090850f180072001550388003000c12070b0300c0d2140040f01d6803204169a00c00c1d20b40907030f0b440e81b40340d800041c1c041e80640c410559048001a80841c40101d80000a0000506007450049120100e402c21196507c40c62030400d510080d075500e0819101610400c0e50300180582d42 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 733367131 1250 733365881 733365923
    0x3030e0c0307080706090b040509070516051002030f15180717010806090d091505030a022104060608010b060f03100b040311040b0a0b180102011d0601030b06060c0a 72
    0x140e0a0416014042d01038003141e03100c000070780101202d0040e542c00651560310000303a1403500a42c015164489051404508941d105030081c2584078412583c079840c1d01802d40c1e6883ca00350a5800764492681c0100410007401400081150312280b0400401c02c000c4506001541c91500714a9003060180c0c0480810111072064400c04110024110017000350b50316000300a40c0d0781421102c0c0b104510501d04c40c03643c010f00c1202c410b0110392070301884281c0344502d40c005541a42004140d03011281e824801c43c40062451942030020030312040407220b02c0c0c1041e05003034041c4c5100d5041628240c0c100300b401c0c0703c9919490211144240c400e0209600c90f11078105085e003051065014618204000c00e0100c2805480080d1080c900030403030b410404a920001801096461849030a50958040c0001941011040584003951005200018440c0d881c06041166484c00010a6245a02071001071082000303103c1c2581d0440812a41c2e141040c40d01c480f01961f40705104402011900355910801078085 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 733368381 1250 733367131 733367143
    0x15050c06282415050a051617070606080f0c04020c0a020301052e050a03060207051c03090506011202101206180c0f030501051f14041e0905070c03030e 66
    0x1050740081c4800c2c03039001415a4000044880c106040021050009003010821040c208080858880b141000c94444042d6110381007400103401c0e0f420440c0d030103030000d40095090811198a808465140e1400f400c0076411944240c205034072136800780c1e040c0f00f01180001441004680122405680c0705040c01449044c42c4120301c2c02901036003080240603440781c2d5038001d210600c0d01090050035840364081c02c07008840b554481c443d00100380800600200b400750300102256400f5008079880f100c400100c4800300340045040500103651504a0000c214045c416070b401007040407d0b4814840c03160700010b238078044007801c43c428440b210900c9032010649030000c07001400402e100171b4800384a454407030003030b00c1c1d0345a2070310016107068402d1076034602900c102814cc44028040520450f40400205020b0b1348401c9450107110081c1d405960b11002e40c070040000e01110300040c0804580f0103504240a01250811802d5900b84002c200380d50b0392205800401581500e40420048031009940382066 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 733369631 1250 733368381 733368451
    0x90b010c0b0f071e0c1202030c0d020606010201150b090d050708070602030a08090f07061202220806161704080708031e01050a0f03060209120a050715050c06 69
    0x8200204101c551251000c0303072403203182a41c85180c410002081442041c1c3d11340050500801c100745907107000b1a61314800c103020b19481d03004903461301d2203052815290a61408601005a202ea001c20841e540d0a000781c0760142c0c2444040e295241c00c10070920324a002d2400000e000b65400b2810300b00f444010440840280b081c1c0307044c0d4084a03103074a0025125800384281001281822003c181320120010700010580b5090740903040b2941005402c803841c41001fa040f144a40d02407007002142e4100c038803008115059429110300b8549448500d41c1444401040c5031862038420782c4079004503030401030b031a100c001c0c04101c1d07140903511840e02003058000c90703d014154403c040100546e8203001041c3c042c561007925410030f40750380e99008000c4c2039544c5004110464100383e20400001e1201c1d000b030724441000504031411490030780c0140e85416900c60040d01e20741d11000c82080380e13403da40c200c01aa03020602e041c0340f424003a200c0450b41e49102511210800c400e00301c902000c40790440c0703110004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 733370881 1250 733369631 733369643
    0x203030403080a09051905090424140a0c092106150605071a0105060936010303030f020403172101150e030a020108071d0402030f01090c030c0207090b010c 68
    0x41d2000350303002400711102d17010b002c0c026040110304070f090b0030b10640d003a01100c4008000340031b2944c4d41e54407104009039841038040d8403800010003840c0c0400c1400303200d907009a54022400c10380f0300304140a050f10341d4446484144805402d061090100e000e15603101181001c580f00700c611454542007005081d0481e03050240380e014040424426070106c0141800d501440091900000960503003152400078403074107038807200400c128495820405c207080880e0440ca9181c00c0b42201e040b48021001a00445c0c106003854988014030806815206401030141414001c6013028219641c511103942180710b003000cbc0a0004c285101c1c500c002451800304030a080781c442e85d05580d20016114111709082d81500418141c04240000d030900140f405851078050b501c080c143e880f042403d8070041048601d11804111000144540d9107850000b14041c2c0300138079000d07100c8d40c03500c06c0c000d080381c0c081a101403c160174002e8001c410b130f070b0000f034107016180309401c005a1900d0600040c2da084840c41401070031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 733372131 1250 733370881 733370887
    0x1017010b031f060207061407021302120108060f0103060f0e1e0f0111030a090c08010c1d090f150609040f061e08060106031d0a061a1e0d020303040308 66
    0x11840d0614007450080244500420710031114030340000301003a070741c02220010380c440082003100c60702c10300020501d05803d012161400525402140c0c581d90700814140f401138001a001422420289903580105040c0018000030f0401c03211110a0140622000c0c0866803550341084d070140c0d6941c4003072000c0310000202ca0b0307010403444041c030780b082041110000b40c3c00742207884c500c40c00041c01845030f000c41c00c2442c50300c1c40d5214a900c60080c03840150950740412100030105003079030700b486068140c82c40754071030315584140c00045404c003485451155004d0003880c0f040c1f1100b12421481c02d034101001d070940c8081d002d9403070080341007806990301082e80203060105003000150541c0c0540b060f20030403054400303104500b0a105200c2c500b544202c40480d4000b400402285210758042008030001000991800a1480c192841d1000119003520384640d00c4001045682c617004007101c80c50400e4a011950000d24200c02d1242c41806002601480040301c000007155018401c0b0707800303036502c00b00d682d032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 733373381 1250 733372131 733372139
    0x4021c0c05040608011a1e060a0512070f0c11040e0a0b04060c02030f070609081e1b010c0203181f08010609091406010c03031407050c1b0d02101701 65
    0x445103034503108442c02986003540100304150103000355500c0c0905071459060040b4518140009202d41440440300c0b00801115142c01d0380e10350700203060f01160355403450b4480c9544035401c12071500142840040c4040704072144107480d00304007020350041d00b01080310003103049240401c01030b1212042c000002e00035030710083c0800840701c1c1c10701d000da4018181004a400c2101050340c0d64810750b4141c1440301d2090210400243c03054100789032071480b8101c070324102205104182c86000351080c127560000c3d404103285050ad0a1003814000442403000280605405903002a4880c82842d070f080300d07584102c2640b080030ba2a00d403209000313030000c00c1045079aa07400c1900100000001e005090025040e060b0001d02446980907640d5a02e00001400d442ca8541c44019682c0466686c1c0071400c0c07680320400c05030b010200d0b84a05100307800f5502c0e16540c0c2d440d081c01080c00c00e11000120102c1c1c40640c8150000742c2c4401b000800e1a41d41a1001d40c85420412001d580401c00c13002d07440818403030400081 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 733374631 1250 733373381 733373393
    0x60e1f12061503090b09070806062823010804020f1c0206030f1602073002030a03050c07050108010803030f0c120a0c0e0108160f090e0c0a0e101704021c 67
    0x181c1383d409084403070b610f6220706420544400891151000550001c804601a03103820520b01c80903841c1d16100303010700c40e110121865045e00d02c0c1d002003e0091105401a03100307030440b0301c8a101000034a807100713003494950b0004485620002e079982c054030300c1c41206500350808110940310282c00a006e80e0701c80c0340071810b131700c0c44680c200d401515152112030640b4a2500018900050750020440369500e02d101c5404001c2003008520b450302c0c0c20200144030409a28103100c5180894000d6460a91b1020f00c080c4141c940f1005034000d82c10040740314010441040080140e07a002950360a80511940b2034001080c0341b800354490020b060040042408540c58103030b40011514a0b250f01c6120140e0b84900054664510840c0d404040c1448094000c1c034003842402d24010311b80d86400c00f407090f2a19034903184207080e421540b0343c03801c1400140086255800803d444400c45080b20003040d03440001d00001d05000014294048640117140440c08550700c1143e0030182c050701100b080782000b11401c0203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 733375881 1250 733374631 733374641
    0xd1503060e0c0d03120c0e0607030c0512070f06050604090c1e09050f16180308120a020c03071b0e07030f0e160e04021f0801060e1f12061503 62
    0x75405100300c001c1c81250741411070061603c81d0709900d0b44801c0d583c508040001405400c208101044007805c0e030f411856817004c02804203030380260354548003a0401c0c07501ca40f900031051411004c079603003800800c000800c1c0801000b00b6940c010720100301c584609010401800303018074010a2507900e020b01164088030b440e60920300300a03100741c2004103a5140b44500403aa01618044220320841000440b00070f1040500703800031100b80f8000c442c0000004022042201d5a0000c4503074140018601824030301102e41d050f003240c0100030851a100800c1030642da0f80c81040c0f03005103c290030b22203005034900390340c0c25807008118042c10a03082d0b14003c08001d004006a030b80030412540740031001d10b4000c60000d41c6001d0599000300542c8140d090090762903071000d000b8022a403000050782034100c400c2030b07000d0342c0c88000c0c555200e95040754141701c405042e840c000c0c2c1d40a4041c10b445000c034440c240c1807103001c0042280c2e60415034443c040e1035244101506017a0880c0201141c402d00e4011840c4e4180c0c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 733377131 1250 733375881 733375901
    0x50f0102072603011d040201121107060b0604050d14030c010c080103060f06150c0204110706050702071e05040203250e040e07080a0605060a031a07080106050c060c0d150306 76
    0x70200d00b80242808102034042070041003040150702c0b5030350120720002450702c1c3d0800d00505280161007603111703180e02645c1e00300d816541400800701b511002c1007051700900c8a070312000c41d8150f082c42e0600c00495840b428005000d002109060380510200200b8022242a43c0f08003000b80260300100b14080c04403a400e12044416515040303281d600320400b4411141918200c4180e01107126a281042360f00100018090f60b11980d11046600d0309000ba000900d507181c41079001003421705d42180064140403580c3d21105507255840c004c8200940100c00e04070580e003044030016141d846004440c880c0f4054207212404884000050b41c0e451900422102d0704400b04441c2400000c1e5201100e64540220380b00314404c3d9800102c81c8000903205410040c3d1062000d0f02d154050f640c3c949a548100c441e14a14860075803540042c41103d40c0d200300040e02424103400d2062501245041c0c03156101001000d0f020054408212144903e140360085485950701800b03204845d500d0342041e00041050b400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 733378381 1250 733377131 733377173
    0x71b030b04060504140d1d03070b0403050c090708040c06031d060915010b09090c1e1b24070e03011d1006120f08070f060504080304020a080f0316050f010207 69
    0x150380c141000d0300151b505c41c1000f5959a0000348070f070b40e03400c000781045c29000d10755160281c4200802da0b960141c0250000b140118003c013203400059090012901002d843c031001c101c075903020840410040d000d075804440e0301d868001412048101248403080014106041c14091181801405040040d1510034001c045100214907603841c0d0b502540e81c452440702681040c99000007075171f02c684540250480e40076040140d644400b100e140082107602c6034140069422102c0d4840000d410f003006400f4800490008a40c0780290507108039041c3c040041028003046681610120300c1d490a401c401d0304203040e944100e1001d01c403c88415221312084094101d00ca18080000400c3c4005009407580b80e508460b0b210b80d48489900c5c0c0e64501d034042041038030760540e40504000024100c1c032660384035074040c1c0011a183d04091041100013a607503808001d85500484102400c0ca101000f151040400c0c8031541180c00000c0c60300c40c1c20030440c40001412540f0102e1010240040b038020030800e00e075811 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 733379631 1250 733378381 733378403
    0x20c1206090f061308030a090203070f06030b012a0501150f060e030627030c070902040905090109110127080a031205090a0201112104050f15071b030b04060504 70
    0x40001c0340d80302c0003141e0100d40c01189000c410086500300c4010341d0003607c4214041295206500400d180c401d440c1e1140c1990300541d4020410154035125505142d9003d00e45020300500c40303803a039200e1550180b4030703905110603400048100042503100006458600c50750924060b0317626000c00c6030360798510a20001c2054855000a685000704215214886d503100c2e0303011f10322810581c02800080a4000301da24842000b1420350f8180030811240140208000540e8070b9007402d42c128103480020703000c0030585c0e040c0883c0400061a84510711541300007031804204003600c01003074840350070007444040180e074070001000c5914030021030f00513000303406520740741616115001824101c82e8211010841e9400101c1c9540c010343c07003042e8181c0008010800c68000c005c40711143c0210008a03040680b8040b800503042109081200803014145011522109401142800400c05100d4007100070203003400d56031044106203444c2e012030003443e0481d030b10004d07610701417804600a1600382e034280c0d035400c01c04d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 733380881 1250 733379631 733379653
    0x31205070c3e03071208070807230f0d141e090f0613031b0306050a050709060201090b0f090a1a15041e0c020304170a060b01140f0307020c120609 64
    0x500c082c1a40ea40c010700280181403130918400c049800032101180c4802c0c080003810041405040585076281c060694004038440c55004008604201d4543c41170385e401803604000c12100201c0c51091450340c604052100d121000d0b2840300701c0c402c26400c46441000d60303440942041810020700032095058a0380305488100d4030401a150003200981403440c0541d000074800100307004803c02103180c00ca2107c004480e00e07a17a5800c1a10821101d0f2140b0f02d0b40c86040026160b400f200c5c05000704901d0000304502c0001d5141c4e1881c003100100401c06143d40840443c00382d0608100f074130300755600414040d4085042c840070681b104401d41b5412200c030b40c10301007209145400c2c0300b80c502c0440d51089484140d040f10f01d0000c09070540207401e60950000703100016816580000c0541c102c880f040280c14107a186180100c12070b1a59100d03981003003c0054900c000040b01c1045800090700c09082680740e9035110000c92400000200e4140c100115540c5050359003000101c0a00501c09441911100558 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 733382131 1250 733380881 733380983
    0x804060b0402070506010303031e1b090b040b090105031902070f15060e18011407020304091a010c021306081b030d110c10020c0a060f0912031205070c 66
    0x18400f0003070b0883d000310b401040003a00075848001c2642e4503401d8103038192142907142040750b001c0d9105007100c000d0814840b151661140000c0c020b0000c19055030300341f604100790441c05000c0c00e0040703814445c000010070592054001d140e0742c0141c03070301c4081d5914042031614020144d990342040394503e500240d1104804003038040e440039182c1810360351185941d9510321381c3c054030498503062042d55a6401000c90b800b00c4000f001e118480c150011a6260704c1c28030050100d81c003155440d82101c000140d1401c040e071344041d851000503011240f042e03141100c0c540000c0203080d1680007944921400c04419800e5141000c451081c0c0022020364000791840482543c180d043c4180d00c3c0c80342e8011029046080c81c02c540c401c0c007141000d01c116241e1031a003a001c248907005076080b03140440c0c8480c03400d100440d801200c03a0041d1907515114000201203070340143c04160450b041303161054850340052816489042c00c052070903000610211a09039070441042080d03c223899920341d203c0c89514440d02212 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 733383381 1250 733382131 733382137
    0x90e090c03031611130614060702030a0b0c12070c02131a151c0f181a15060703090623040e0a06031a0603280308060102030405040c0804060b0402 64
    0x100c0507000d503242c0811400441260341d41418200d80a801c5810381e001161a01c1c4400e044855000f18001082030401c03030650329101d0501440f034420002081000b0061b14041050501950302005914007601c2d000c05210880c05010582c0000810450410480c182e001050301d4a190003640e60401c03115112201c10b0554240440703030007942c81c40c0f52460405041000d00405c0058581c0801c0703003050001d10141c20040340081c0712040b48c1e51030340b56071034541c0c119100360b000c00c00985035120103144065481c1c480c1c0490000c000c460107941c000005003141c200e000090360341c100051115640e500285406098240c09001e6500080c000040f203071266003042d40c14410581074461841d043c14a00100441798110003003e11403910b46803200000000c24414003200402c90031544441c1d5407130701400b45484c0c1001222640480441da101f0b4580b008040c03508840865018038011b6015640c003001070f4514070460380801d400c180f4001d004103201e984000c015000c0d500c529002d00050310f01100700001c1e40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 733384631 1250 733383381 733383403
    0x603050a0e1b0121090c0911090d020a050307080a060b240d02040e010e10060801060e0f0604030501052403030712030921030c0806030c011b0f0b0c0405100201090c050f060904020307090e09 83
    0xb24200524031851500d852b03203103000c510051054046544903004242003c02d6540801403680c861518001040168040d252406109880c03109540600090007084150481c15901031000300045042454850750125070103400b0300d40d92840c3c1560f4400e00c1c81184482100c103e030790b4000703610300030491500c41c0d601075049a203a5034400104507013050802962101911200d5071001c420040040040d01c280900d070307c42c1443c10340540383ca040f0710321801111603407540003500c01e420800c0b6090008180601c160310b0304034a40b8002401d80c1d504e250002c1c0980000c600000c0342000706a0b84a480c1d50705030002d9049414a50358001181c44a005140d52070015100040c00315102d588041991f042c0c0c1c49003180058003230700f10240c0da03802c00d880b4540c80700c0d01920010328501c0006001d0001d4144100d143c0c0b9040c450b88002c001c0011541ca459071240700c140281807248500341c0c80b0f402d413695440709940010344024400c66407800d01807005000400c0c0b5200c0c0140c2c0c240c081d40000c54022020442400b56 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 733385881 1250 733384631 733384661
    0x307030c020a0506181f0e0d02010605100309051e010c030f0b0d0b190204080a201e0109080f03030f0f01180c1103070b010603050a0e1b0121090c09 65
    0x85d84607800284400344140d481d40015104442d00099040310031420400c407510030100010307021480110300c500b00703c1010995001e6a0421800300115111f44a601201c1c4009140009010240b80b800c18244096034400040e244225814442c0f000419400300c20074003203c0d102000300d00c030191281010750b880500e095620440200051010070500120325610844c110a0700c02e0418041c44444100c2c1c01c070b41c00c107820390343c0040041030401020140348001c42c480014243e017807942c42d900207410f24445139403a4090001001c0039005a034082c0c40720001030701d918000e84247c4d40300301110300c2c4e481d00212403040c16030f450031003c01c000d606080d110384d040e904079184681038042d508500201070200300688030108190112040c01042090001c2c0400e60310503601d0111a514040d4001c043d0740020b0000c8c40c0031850305180078030003840061200400d0401100f4240d14803540c4005a800700100c0380313a0380503072040401c603143c1950154040c42c0c074030f0f02c900040130a0302d0300c4d00c64600844164481036a25 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 733387131 1250 733385881 733385893
    0xd020a090920030a0c031b02070501030507080f1f0b0d140105150a030e07052d0402030702030a0c150e061b0306010e120a08040f08100b060403080703050405060f0307030c020a05 78
    0x213201c3c09402c1400014010b007800704212512680307005541e18240c4194005030042a0280030540c0d05000316600030440d0710308000782e414413155150b0b01c6030020b0302d29103c2c40d815541c58002802d00503200300c000c01b00108401c0d2120851202034000d4a000c4541e08041c2c28400d00200d031074a0306001c0b40c1765a40003c01464103003407810700154001c084800103442244500a00040c032a92082e4056001d221800c03400a0002007480d0700300d060001014010388518018000c100c0300d198004140c0e100c0e070340ea9140a81804010b403c1006000c46001c010700041c1d030600140c90b1102d04001b56842c040c0154074030349090020000c1548005000a942d66070004190a0240c400d5140444240c408820035400361000400c4072f548240c404d40c040c0e40304910501d0035800c10044000d0912214810f40081c04040c055000d00d070b00010b92901c6103000041c02e0b2103011600c0000d140c442c80559015080107400e140d51003141a02202a6400407560040068149440524030f1440400d4000041d6880002810 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 733388381 1250 733387131 733387141
    0xb0a050f1606050c070201031506020c0402070c0b0d021c1a04021b06041211030f190203040909081905090a2106150e090703120309080d020a09092003 66
    0x19240d000303440c1640356010103100031021a02d1803190b180a8914800745595421a500c0003409071401c04090f5004000c2000d400c0085a801241c070884001040720010781d1401a45000c0c6400e1041e074000540d20f200c0030694840c510300550003000d4140400c01410b5007200d500322903505507103806000b005035030f04400070040c09051503005064984040c0a101381d071301301180850b03407400324100d905072125014000700d0545250007a10181490b000c60026602c2d01c140c0d1043c1c14407500c03c0030700c004c0c51002100c0101036054428000e9030042c1000e6101030141c0340300c0d03041c00f0100741c1180c04841002000d170140400800e0090b0200d800300807003e0400320341680350581007540c1c401044c11304840802001804030018040d0700c100300c2202c0e400000c05e00304500309462000c20107002400034100350f00407038003400030601d00d55000580c020701d45004030b82d03030503285810100f41c000c000d0002081d50000c01c40c000303000d80003442103041e50000384040008001c2d040564181280c0c0000302d034011441080410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 733389631 1250 733388381 733388407
    0x3f050414040f090f06050604230702190804150503070e0d05031b01020d0c02010207231507030506010f030b0d1e2f0a24090b0c0708070b0a05 62
    0x380c44144014400a1044074581075030059a440c1003080f41d904111300f600504001161190f19080301d0181d40070080d1006443c01d1058009800b40140509801d601c00500460b01c01c00c0b5000d10007014111090005c512450610800d8206008691142c1400c40040c480103104a0599206a20660791800c000c05010240242d841200c0401c0d1410b00040001c80d41140310b4440c045c41c0c4030304c1d1100061b9030b11000e64206040742c412020650441e4010011000071400380a203c105010302285800005107000055502e003c0700d2500c9405480300c11001c0000543d0154489482400280c03a2040d0760340038850101c04443c8420300865000003498206404244040c540c4d4203403c580218000e00c0041644032610f00001c0b01c0c8500650034415050264049500e401034018214143c4038200307068244440c0640034003c3e4030844000e0741c52132010300f405078400c7c58800010314840c0c5050388d50f81181103020b41c4503680742c040c002032446210800a8021126000c50300303020401d40d510f40c00d01603007103586 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 733390881 1250 733389631 733389659
    0x1050108040809121e030901020c0301050f040209090c090c04060818031801050403020a030c1d0c0405010e132a05040b040b0a140a0c0606120b060411073f0504 70
    0x1d40581d00c41c005d001c00c1c41d403405041c900b100508500045403100249400207140075001c09525001c1c4c1d0400c0d0911102c00c6040000d650456811200418a95103600c541850501098500c85e404401d140a104010503284020000c1d2a503542d980b41c45662000300c10710300c8181d0104d100106600801c42c00329841034000550f24032200501d0094505030752a000907641d10407603042902e200c00740010410201c3c3d40c2c2170300d21034619458821203409240035a01c01c0301901917481100d041c0121890302541c50b0740c0d0208005184070a100d010080300200c50103440340c1103580c508429114001e28824842c660180099400301c945035400c103480d0504202104c84d4503085081c03440b0502c003644420941042c499030107001c0b9801c103031791460030b02034550901304280c4510390b00501d00b6409407040380001c2984600c80d1984124280c501041c1000b040030881391600c9688000742144042501c10821908001c114880104400f10034071408400390103e4480e1403640900d010110b90200303c00c000068292800d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 733392131 1250 733390881 733390909
    0xe160206040b07090302060c06100f060f0806010c150905061b030411011b060c09091a2b05070812030f04120512010816170705120c0a1d01050108040809 67
    0x104d11380c80d942c5d401310b5010781008003030507810b811141c10009100c00c541303d54002452201c01410340079152003c080c00406982d11042e040160100002d907050b401810041d00565002c5124103200c400e0500000041810500403034042c003412011820b60f10600c20000748a01c100420b062550701e1b540d80385040911401401810310892641d40c0054552804070000080d00961004c240c502d001000100f421080f5040400700500e062f441c2084000703900f01e910042c80f016228480d00448003d600080c3e480d0311086008082041d0310f0744010000d020a200c0211160681292940d80000900a00038001102c00c662103a2504000a01050300640452190661400c01c1481c0821018450f01d82c04800d801c40301c0142d00000c070709142ea025035a0301c84020000302404440180c850300c4000d444080904c06c0034410040d02035089080c0070144099102510010600039400d66511740821a00d1601c1000032545406580005915400341c0307101c600c101c0d40885110b1030484880204112981d005003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 733393381 1250 733392131 733392137
    0xa02030105070503100e0415050c03090606030a030804060509011119030f1b05031503070306050702161511030405120d0813020a090f0f1a10020f0d0509060d0507090e160206040b07 79
    0x50a4420040d1509c20240900b0f0307040d03d03503a80c9244c801c240520380500503101d41e010354050340d48000070070761000e47d141d0041d92101000c0ba043e161a03100b42d024101c4017600c4007030103500080500803504480d10b030040551054400b408400c2c503000260003200c2e10f420f951701d00090b2a99800b03610a101c8c100940e4005a60081d890352150800c0200c4d16100641e001142c49542e07a100740310f01d04d501002045824010300e010011484c2c1803020005000c0341080c085001e01c0809060340e842c95600340b007668040d11011384039400c2079040e00b12140d560700d020390350400810900004100b100d1b102100c0caa20f0190040c0c03c0b01d011520b07065083c1c2c01081c1141b0783c0404690b41d0b8074201300b460f040c0d01480c280804195100131305524078a080014030010740b001d040c01d560101e801300803182c40101d40a00c03101c0c100d06103541c5508110021500070302c074141c50880c4040c0380c0020071402c580c00c8041072054606041e00b4003115940e4000d12f42d0341d41a58005000507910007800180080d030810031055204074289 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 733394631 1250 733393381 733393403
    0xb0a030c0215010b03070318050a030f0c0602180a06110a1101090801050a06030302010c05041a03060312040e0901060605090303090409060e0a0b1f0b0f0c0c120a02030105070503100e04 81
    0x2c0d1000b400030300203800581e0340101c000140855198940030750b03442c82800120410091710507030369055462101031002802d03c0144041c410440d80101c0a11b8100c03034011100755a0760003010002240043c2a904941c452124a54081089485144c058169020100040c00207071220307103640361000045028107040080340c01c0081a054000c1c09200d000d03034108600842c65a08501e800781c20350703119103405020814240010421007409014818200d00e0a9003400c0e6240c480002090500e50040c030941d445140005d40007511041101c0e607544100203182c000c004040e141e0104407414811000c00710780c0342d80b0522200103180b8055110505403403182c000002c051a04200c02e5091951041050300d1584c012000c10100266008050003001160149115083c0c205070351f4075aa4050801d030124608400700e061541c5c070100b000412017402008141c502544580e10b41541d461a4000040703001f5402d04010440460080040e2401401500c030601c40807400d010007110040710081c002d6030009050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 733395881 1250 733394631 733394653
    0x12090a051002031e03130f0f05011b090e2e09050a140f070c120e1504170601210302070e04030810080304150c0501090b0a05100905010b0a030c02 64
    0x9000311045031050b0081c60302d03030242c1c01c0d1410000081203141c2ca02a071080007001b09440c014030a9200032540501d0101501c403003410f047c01c0c030100900e0002c08962a004250288102d007200345500c40e0b201360348082d00e041c0c840f04821154202500c5204441850039005507203581a10406007402407000e00c422095550f400d0300e40c007540c20940e181900280c1e210200c84400c41c13680c01d5030307901c1030a00300c0080050400007001801c2103404100a81001961280c010505200b00160801380704002c107890242040e1140031603159011f4030604040740c00a0b000004001000300d40903040761580c5400e0740110000011205401211007021011405901070100d0b0b000182c4680c640102d010307540303040d4986004103070100f042072943c01501c6030768010b12041041d0003240181607444266881c0564501c141850f1081c0540a001e00042074200d42108210261900c0e82c01302d4400d040d101443c44440d5601d24008003150002c2c020000c200908000000a181c000c0c0c00000412307175644101c444044407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 733397131 1250 733395881 733395889
    0x3091502030903070b09011d090a0903050d0c0f0806042c07030507080f0c0307080304030305130806240d052a0a1811040605191b08070b0709050312090a05 68
    0x5608500f0361607a0201b060107003544d0055040005810800420103030054281c002100384400030318400440d6121b280d803074209031058040e201146000001440100745241c00985010340404da2900007400700800680d0301d1a240c0100059481e01c010396400c04907410801084000b100c0b104002948103610001000a100300300c40710080112501400d483d40749102018107200b450441d1b240b203980194800e102000e00130040b14226541420640d030398494145d56a000030b5100d50100019016072000c001e510015605403a5080034140c401019445640e010046100002d050181c42c0f5444503544001e08003c00340340309140d24010801e841018410070000c0e00001c1d1f41d8019600010300d0310701e040a03140703080c004c0c9040314940b503552038149400d00c000100a030184100001d51034021b100b0060503180514052074904400508000411119080c005000e40c8040c40458001a08100180031684518505401c2c0c80e00140a058408194580030b070a42c0c00c0100700c0713a484400d0000008550f92 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 733398381 1250 733397131 733397143
    0x2030126010b06040806150a060f0320121f2d050d05070303020f060c0f0a0e03010528020406200f0a030309260405011b0b0421020a03091502030903 65
    0x1e94038011702691829401f01d1505500b8124998003554200409015854105201070b04281d404e19002030240c14429009000c4190481300c1d01500a0005450440040c00b40e0194451840b0704003601d512223501c100b10010580c41d10480140904118096000c0420b0b40305100415400c1940c020199403103c00103081c1c0070b801502200ca82d400041d0401c00c268040c004102d5040080700504130a152401001085110700e00b403003c0141c0d400102c3c200301c0707401101c2c40d18007604081d0007006103181001d041d0120345003404840c0501407480000b00c202c58880c4c0200c0d4140d85036581c448540d41d41c0c19180d42040b40e228403140301c0354090440c04000e00d480800850f503a8500950300850500c0d400d0402402442102c038555103000d0340a0210301364040220100c608844081c6440030100505200306285040c4034079009201c001840280803c1c03114500c003c0030002e00284040c500345044050a991750081e900c40100070808122041100c7d04104040c0400b6011900507a45414a40400241080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 733399631 1250 733398381 733398389
    0xe100503062809062112140d110c1911270a02030601030513021809070b04150906020307150203040807020315070f0e090a0e07030804141302030126010b0604 69
    0x50384e409003000000082e40b8005040c2101c44140f880c0000107032203c441114041805205020711000050002c091001c1120a6a62400c00402c082c5059420740303041c40c0d000c1d009940e9a03110b401540140f070120300d503c107100c4581c0140b02c1c440d0802050107000c54010190704480f1080050f400b940d020303003550b0390014468002c2030001640c07444c0c4070300050100c0300040c0c100084180c0110001c001038903055001c00e820001082120a156102c0b0840e074a08490350f004888442030125000610168460845c9029442c54481990190b10703070300201e07940d0040d40400b4212030b00d01000101966016801160007901038030000340741031080d401280c6010082002d80c0e43c1c294450041150382c2d6404117400100d141c1c54507040c008402428001348240b00d0161420303004540c0c4107410791034400104016002142d201803003d44442d522507a1102d0424224151400b03100d01c1031100c40c1042c2d282c42140d0684943c03c00002a0340b540700140318000c0480440110030391343c0e0b002c01050550390b4802405c020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 733400881 1250 733399631 733399649
    0xf0c070209040b0103300c110315040501060e0609070c0204020d091a0123040f2406031404030903060e0703170702011115012112050a0e1005030628 65
    0x1e5417451515020800b240c1c080004041841290074080c83c42c00a1041140c079000d01d4003002203805414864415451212403680c140b0a00c000130a445081c0340040d48584c1c042e000821030b9035500da0b11050b000b0022555583e10065038000180c2c420301a8001560a600251006081501001d409011101000c01c00d40c3e40c0703ca600e4500e02c46130004614507006d08070080d0040079404d01c0c02d0302d05000d120080c01003441191554500d00f15403c0d1135208a2451001103460100280354850403841c01040303003c2d42000038140003410120049182420780110b40c11341d00d00390700701e1441d01c0307900050071142403071a258014440700002242002402c9240d50320941c40440d903503043c07440050401283c17401d0510103500030307450720f100c06180303d6065411203c040041c4058003c03104100c500240501c0c0004240186120407500720a600c0741c00f600c0042c10715141d01008007002d504000340013041c0b100b05000a81c0400c002440e03810520392000c6a45c560f0260140d0000034048810242c0ca900e4200c0814 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 733402131 1250 733400881 733400903
    0x1903140303060a41040f060b1e07060513030f02060606090d110a1503140606041e0806040b0a0b010816180909080a03060b03010803120411130614060a080f0c07020904 73
    0x10707450148103415044000b140100840307450300d0040d052341e0103007011050300f03031407110402c49800c4091404c40b0341d980c3e803004040182c2e16128144082003485080e0540024211125034400b03180002856030140c44020a07040c00d00c0b0702c0104100c020120500d044540300f04152842c43c0a84400103558060001418071746480d041710003006044030300220441c80c11561440c10300c07841d600c404c0115000d40e0201060b90400c9295201d0508a0500d168010103442c801d10003008144400480d05602652000d4000d0090405201c0111030040d0151025903420b110401c40d03109040c01055604442e18128207407581c0103598031a42412683c00800c1aa00c80f20b0006081d260b55038140304442c0588020a1258115410f01c3d5607285d0b64024850b444400442c00e40c0810b003440401c890484c0c0404004040c044112103400468029114910402030880300d0048244040c0c0340070015200f801d2140e80e160743c000c0e03039441b03103003240b204000d041c80301c00352030030880c0b20090303142c0292040c8202d000d0700070469 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 733403381 1250 733402131 733402259
    0x4170f06070e060702040b0105120a050609070c020f04200403030903261c0f0501150f1e0c170318070503120301030803151903140303060a 61
    0x824031900400c003208108000c980d0550366955402030f128070540580e800183c8161360401a581803040c0343c1c1c028005041c0e4003c0011441064010b14418001983d00c031020791108201a24000400c5400075801075142245254034142035001450600300074a88003040881e4000007142c56002c1d410503000204c104805105212800e840129056265122000100640000603c49000d41908495444080302d000401908507030041c40650310b50714000c004a580d91050001441d0000d0551000308220030400b00c0018001d402840c00211038072040006a4003110382160030500e000ba041360135064000409600b2402040907600c100c0840d4100c1c511a07100100b80d52400280f50f1115110340d020001c4905d100c4a1042541d046a5100907800d0712501c482d98000e440d001a414040e0304210841507884001d800000c414040768042d048100150301d40a00711030700e074801114802d41210321244204103a40d0a000c0d0180c4402c224540c01d1311407407105a00c6d03542c1210b110804480c40c14691380c0a1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 733404631 1250 733403381 733403383
    0xa02100501120b01060c030e03061303120903050d02071703090f0f06160e040b0301151e05061603050c07030501050615030708180f070f0e0f0411090c04170f 69
    0x150140c01c55803007a041c1030055903110003c00405005040030013458054500c2010f02030800084000b9005041d603a00303141c07400300891015544102600007460705602501d00301221310840c5151901580c6803843e01c11011040d401940c05460f04a80c0460302d10000344102c074422002d50701400c42c2030302400c43c0e0700701c58038040d262903000d15031411150070403820b00c0500707104801d10341c0d01803042e41031568030001014006402460085461a055400e03d0718210400c00d00312200401c1c0c6d9622014000580302c0320215a606d07150501415800110070090700800d010311000c400e14032072080c58000e103030840315130880d410441c060784100d4040c0e449200780585850080086481402950905820351401060040c000f80024080381c3c3c240030f0440d01100c0811003803000708018a4008102e541c0103a03100101c00c0c403880217105030051035150350046208a40340e904080e0040390030142c2d003003080d0440010800021030103071800302031142c00c020009402c01074201e0803d510756000041c0000b02c5064a2003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 733405881 1250 733404631 733404641
    0xf04050f07060806010804030905030307050604030201150803070b0406200913090b06010c080c031309050a0e0615040b04090602030f2d19020f180102060708040f0c05060a0210 77
    0x8a940394000c0c8400703100070b42c0d01440090b0300510920300310606072201d0078240c4d00c000150308070329058000015200c092050010b00d00340114400c3d8005c0182983c0140080c030400f105001d40c001640007004081c01040486944907007250280c0400260404030500c5000c0741040540001d00404010035060950b160200c401291091094000c1c400c0030403da0b40e820240307100a1200f414083d03104140000c2c01017603412344098400410440742d0b43e40384090308003c1124036118400019082c00005414040c0070b0080d0254811800020035598980c12051250310700210780031604260b9400f5030240c01d648034080c403816140100e00069813070030943d100f07485850008102d00800ba8a0030348400071600c1072544034168400090094116440d024403030300e48450808100192280080340f000744081140e40185144c010200601d114884000300590f1035107412074840740812080307400100441d00002c00850014411082005040d8403500061000d820400b00e8000690010342c5030840810a8480c5d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 733407131 1250 733405881 733405903
    0x111b0706110c01090e09010b1504080c0303090604030b18010606030605030d090305100e030d1a0a0603110906030603030d0906150e0606070206161e0b0a0c0c06020f0f030f0405 77
    0x60b00c00481c401c2d0001c1d1a0071841d100d044200503445000810000b801c0d400441c0e881c0000b0002c0e0709810306e004001030707150014065200035000f41503200c41e230f910780007086a00c481c03800f4200c542024a5030311900c0c4101e40007040d405403030541c81390f500b402c0c810038800e0780041d050540f0001085420a070605143c0301d40b0103070800900c80b02080a0001c200006180750b84591540310104036089441c45585c10350050b8000c5125140c280307030514a038113100007900065032805644151195941e0760b0304806a405502d806031103003a081204070454103040c40190350120018044910301941d4170f03180e1044400e400b07001e44100740d0740c500c01502c0a1085d00081c004000c06201c040c0c2c0703418040c00040b00fa1042c880024485c500002d101089014401c013000490782c0c008406007142850112500f40c060307410001215a1040400081e4900f0b15910440e004400c45a1b0b80c50002c0850750344100c000e6100100d01c411b040382c01d00c0084012860000213621036800650418440c1c146490207501d040c0300241 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 733408381 1250 733407131 733407133
    0xa1101090e01060c1101030524150706060501030509030f180105041e090c0c0312051e0f0a1404030f080c1903150504090b0411040b040903030902030c120307020103111b070611 77
    0x24005084400079071054003071007440d0130b202c1c27405511000035031454420040e14902c51000c5111000e02c84a58414000c0720000c3c1c07802d1065599052116449114804112440c68818010650340c0000d88940c1d8000c41d40604040b49040c0d2903e407400d4860410050b8005540085078081c01242c03418010703404024114140101c000c50303542c0c0c02628080d280340000c2051590b40703000400a040510003888030440040c200c1800d4102094074131103080084a0483c0a517050540407100c00d16207940e00c1d40b21b9034050382c440307a03500410f0000f06c40310390020f402c201c4030082c1804034000c2000ba1785a82603108225880006404165001c52410b40c1469408148914a800401c201003540c85030441c0d0301951003015201043c501c10300180013001c0c07030740780c164006180c14090400c05805500458281303000310b0450307100301700040c1045082316034400c504003560400d004001c0113500a810603c0d1070f8191158050401c0641c45400e90b00403040c2400500030350081008000c07060300101810b003d121284 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 733409631 1250 733408381 733408391
    0xe070e0601050711040b120a0515041a04170301060c0506090604171b10020405090a0c02070501050901090e070f080c0f042102180a1d0a1101090e01060c110103 70
    0x20001e032150294500107030410b5107248050180742c1d590b03070240206c100c008003812441c0c08110010343d59403c5021003180d06220340d50600312002d109180d8140718550041c2e185401c100c46080034011848003074002c03102c00032400019140d102c440c802a40c00303802e8650b07500c1900b2400d814034078504030000d0110055174001605100105181c0020400010341c1001c82c16901e40b07800c103480e0540342032028a060306010b03030004c0b09444041d540040045070b00803a905426500c1c4c1c050b441045070704903030041c000b40e40325200c20440c5500450140c050900141040e500c800da40d052407052000c01103400200086a101c600380d600d0381c1084000d5003000c0c40d074807024201a000c00d05480301c0d200c1c9000d400380d00e01c0300101c03515208500d6080310326001e41c00f034041e504152001744030712600141615120082030400090f09240300081d400c03005a070128000070314044000e503c0790000180307028101c034108003403000d0200d40c0003a1000803a00a00711980c810b10141c18500700114895289503c03a41094104 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 733410881 1250 733409631 733409641
    0xb010e1c060c051b01020a08090f0a030e04060b04080304060206160e060f071a01080c03120403110f030a110f0411070b09010609091505160816210e070e 67
    0x14403521103560020000900c9070300303400c094940340980700e071103032041130800360400fa0400b0640290816040329151308185480701980305844590741000e4021a5210030600400300f4400c0d03180d11550f00d005400010415110390b803100c0c10380c2c095001010a0752000404102c4564104092544449210ba20800000c071941008080a06020306c80b44250b501040e450309a00c3c4070380c12503000303e43c80380712079025904001d003080981c4400d01c00c2d05924055020400c59a00380030810f1a005080d42c903a480c503140c19a40c40c101c40303090808043d50000c0b00c4c10600200d51f00c040054801c060301074180005200005c004100d0001e2440c007a8600a46c2004520b40a60648005071040c1650080c1c2d0104999a00782c1e040d401000b03560b101500103402c0800c0e1a041c000c5046180600092021003409182d8039100001c00d44403040d11040c0000d031045000841c0b01032401c841c03148020f1a840c24481c2540f464030b00c8015540090152050150f4448000003070020030004540100440c1803200c00c01e00e80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 733412131 1250 733410881 733410919
    0x1504030b1e010b0a03020d02030a0c0905150d09060e19060b100507060207060b04061d011707030327091406010905031902190914100506040510020a0212010b010e 71
    0x1040c03007031001c5000c01007207100b24203004e9011f4480c1401480030071500e900c1d200044002810b903000c6107201090340f1081c042044d0610103030903200940d40001c201c0c50154800444401040c2c0f9500035102150398500007950b44006004260b2446c0b00200f0b800d00840039800d010041b40c0781c1550140c07240034004822000c4c80c5e04502524061038000c0300040e11150142015406400c42551080d4054079040740400c0e0769602c88810017400d00d130b00700c218119a80f00e4504072041841e8400c007019580c00780784d0810009200300d10b580003500041c940b00030b000800d0f070030800840d81141c008a104070b0300c1c0c4125089400303110510039406802460501a464549000300c1c0e101c1e2603000c03528583e5010304003000300355240e00b4030401e40420414400704805980d0b00c0d1490041003524000c200c030307048080128140e90310508800e01642d600418640c9080d01e05007c000c80016162020381c194002c08601c50056a1414060046070841000109004034140c000600c1000c1c605280d52040008054841704180 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 733413381 1250 733412131 733412191
    0x1202030601060c0f121d0f15070201050d1514061206150702180406060e0f0a091406090d03060801090c12020604050303031602010605060304021018051504030b 70
    0xc0c1c50305000a030f0840c181000101c07190018009808041101c6a1030030707080d030005146120076000c1c200840110301e180c0c100b200081c2500202a4081c440d4a0814030951044008140c0103105040092424540d00d4134641540c110b094540c1c141034020504106075500101140507200040f103450745840b402c05503510700f004001d4290b41c001d003201c1130384031004407041040f20100e64006140c000c541003000304180380101d00f02c41c2140c0e01800e103800021025605201c1070b0249044405a00655580041541c0100340440b015210074540d403c540c2407030f20090103160301961948001c0c01285d1340b90b4501400742c841581c007402950703240658600c040f4101207629401e4070401c900040121600e4000194a8081c540000b50b05000001c103015039040022405400b4000c1c0760024000d0543e0355080150074041118084c0d00010038400118a6501c200c03800003607480c00f428100341158895001c07614503400001c4136404404001401e0003800400c581c107a070b002d20f603c0c441c04941d161300c05410050036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 733414631 1250 733413381 733413389
    0x105031504081204020a09060e100806010e1602030909010b12070807050403030e040212010612050a02070f0204180503040602011a030d05040b0a020c220f0e0316020f06030414071202030601 83
    0xb00310f90300400d04642e240d0105200805002409000040d1909c643c0180090203550016603100001e0001840304c1c40411070382c1c120345d100303004018960f903209032054032402c00c3d4040400b140004c000c103a1080e80c0d1340c0011030180001c21140f50722981c4034a07558103a408044c1024050081001c01c100c1c4a41d440000c0701c003500e0303040c9807408e525000a800705011740100341100c0070b4000040000724200380d00c969609a1200d20040074001c9441d008007100072445810800b900e05401003114401609241c2c1111814080c41d2840c0c0710240d0301078807850f065800035004900142d4440284050500203641e403400c0e20b040c00c034003404a02d601c401e0007401e00d20461161261080c03001c260800d4030b5000740840614100e0103800c8c10003815480c0501c018110104d80342d1600e50785840c8802c8001882d40c0314032400d0b021100010762401414441484003000d40820480c0c2c4500110140c0c11591510303030246000301e1045054018001c0e54841440c1415030641045030030210780310a440c0941c6c2c0000303a2038110303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 733415881 1250 733414631 733414657
    0x2606010f02010615081006031104050108060f0d14160b0304230d0c02010f170411060904020708091005192a0b0106020601050a03020a030b0603010b030d0206010503150408 75
    0x11104001d9015042d030340e201c00c50080a0000b00c10384281c1144805106038020350107000c03e40d4944005404454290740c911348070480501090155500130100150818801080c9114501c503420000b1a0700a4094089403105030100c4d07143c00e501010480e220940000ca151085401d04201007941c0030701008101900320b180d00c942081d00c41c2c800c0254500d032000541e00362040c500b6614000b520f0244d911004900080110400d5104203100d24100c43e0700ea1140811341506803500d40b15030a4000d03002006030f50245080007a0701c1d840c1c0c0d0750310003005641e00c1101425200c5050f07000b00300540440246c040f00b800420050181001607072607800060b001c580c00e00701d80d1014001e450303041941d42c0b5003107108240812210141800207507a1014100d0340030303600320740c0035a0301d0700b041c8135600145110094000107882d50501c0041c500c1a0f403290f12460107400041c840c0180d0002070300d0a050b411070600942c000d24014011401d0034030040403484008803100e00e85003455590701c0580d00c02c0b40850490 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 733417131 1250 733415881 733415897
    0xc081f0f090512130f14011205090c010e03100207060902040e060702060f041a07121a1c05240a0b09070f030b01121e06090902090408210f0106260601 66
    0x203244c08018103009003140914404030203031604140c41410302808036150101e041724a0a11080c940c0b805010312030b040b038401030f02c142503c00c801034410050040d40f40740e05000b07142c02043d040d5290f2001e001c0d240d00941010940016500510003126000d03070318101c5035000308041258864000030074035044201c04081200315542d6041c41603ca21284001600c0d80300c1100c2800a01e87d8461000c54901c048204200300b0083e00c00f40940505900021282d0001c40f003208a1a1400e96094080207450052085c0c40d2403070000a00c000606200c12517200c44c8044c04414010031200f1440784c8840d0f800c06036603020f00d5042ca280060b21441e0f8911000b000c0544410900722180d01c00c40603140078060030b28003403183c4071000070303401041940c1e0996000550714040002940c1c040070b014080850350081c00b143e18031388403a01c07200c09550001210125424010072004c4507500c185603028415445040b14460700c0d410410001e1414a80025203400c21400010382070304400581a4950031540900306041d03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 733418381 1250 733417131 733417147
    0x3020103060b3609070e1216090f1107060603170406141c0c020102041a030105150309070f08010207030e012c03010e06130c170c040203040c081f0f090512 68
    0x80d50355411503c454020035040d040c85080ba40041032583d04410407240b4610402050b03070f05507640e1101f41c0c005c05485403081000c00001c480307980006c66244508601046c00603003051180400c0d804040203c2d0813681c0c4400404c10321001a000740f5099541c0b200c0b0701e280074034040004001e40d130300d818520744010b4002032100e15841e880d06441103907c034004050009200c1c80501074003d400c113114101d0082220164126080000c0046034140c0d034005006500840100c0844c003101c0c1c0000f840304c02c05215405001c2030810051403490020b00d140300016a1b140400c0c60f005028151f0b00c178445040c00482035205140d10040c1d04c0d01000c0c00fa5000220380e41200a0000170b002d007501c51501003441c0151010b20484148409030605c4160103075800c0080c1e150394041c40b21074a0204068901d01c0d40020000401c50b2078a90020b541040c0100500140c0c55100d40401d820f10640c141101108003040d007421110112a0040c40f45c054002d25003080b00c6605070b00d60a407951603040d808014034400041e42c0d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 733419631 1250 733418381 733418467
    0xd0509061c05101509060c1b0806090d0306090207020d020d0201030b12031b0c030d030c02070b040e090c01030b100311040906060815040b0f0d0c091503020103060b 72
    0x24840040741942032007141031085103210340000601824441d03c1146103100c030310034000d88800003102d85540d80c2403281640313070701e41040001d00da41c004d41400d41a05d00011303131180100302c030500804030309014002554203103030080d00b00d0307000342e000031201303801445102c016a441c1c0c3e031f800f041a03406403104c400f00d00071840120f00810340c0d04041d6500104902102d420f40b00000050005640d064003104c01000b6411300326580d4404003072801c2e0303040d80300c0314650320214801d400014403e819401118012910384292400c144c02a8020f186a0700c0c80d40d003004207449080101007000d0100303003400c000030a2801c010403980310740c8000034418580c0b140d48041100705142c04030b41c01054030440c02c000c10390703c80d10300034242e007020b0710703250000c500c1014000c2003440c281c800c80039420f00040c0900d03103528910301440055030714036405540c04200c5007000203c41003180540100c6040c0081122420b50840c0b00144c1204c2c40303604082030259003840104245484200307450200e0410b59420815280d81c03503030340 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 733420881 1250 733419631 733419667
    0x513050a060b03010f0801050c040f031b0315020c1903020727020706380d030527100302040e01061407050f0a060509010207021008070207080a0803060406080d050906 73
    0x1442d524200000010b110841060000107543c0401e00900441c0c481284040b05405640201c0306204589103003040051000e42052008032580c0e11034242c00c0d80d03207403600609050013003d0381c880302e9000583c450307407100148800402d46101c40421b161403c41500c00a50b504203a0049030121503140c03103214851144648001110907000b00195030756616440c018000d004541d5000051110503400000c2e1055002000303014040e0010b842c2c0c0f040c4a4a104124404810a00c1038060100404c40503500c005011a213a0603082001039040e6140409000d00100003820080001007501c140014425401c0303416040703044420030310f4206520312200c0301c1d40e4614401d19100900300d02c10303600c880d50183e41c08112400094000d2030204619658602d10b03509034401c91400070360041c800c206400183d8014049aa00410700c1c0c030461b40c5442d1100e41d00c61802c049000d040e1080c0300f000c8101302e81850b1134050080502034a070068641c200240402030b1447c0502001d4600c6000045030003002a0104100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 733422131 1250 733420881 733420889
    0x3020a0501300b0628020604051b0d080310030b09120702090c0c030d05010f09020f070201030c0905041404050c1f081f240e010504050906042c160513050a06 69
    0x699452030140c0c0c0244e24180b01d00300d80440784112214403030200b80003042031f80c451f64111001c1c120884007141d910314015901000145d002c1e8460300610f001c41d84405c0654411282c02d40c001034158214240f4407103a05d8002c203c0b0740907500c84040309255441ca01d056900c05035060340c00c45a42d4a8009445101e401400d0611680e40310101e0b00555503440e9400940c125021010300c2041e29440d8807842d02a4401c1006240c00100c04101250055200750711a003190500d030314022503800e8541002400b55094080e5441058807220240001c4c400e080c041d100c540e4200700c2c1c20702c540b24080c5e00c6040300c0d00700240218041c000c41d10001500280382000ca41d0814011220103d8065201d1f90010342010780300c00d030075100400200030003d04501036149911210416195035040070310f448108154500b000b0501900b16480381344210340100380d110403e070080003034900080e000e80440c1c0d169103030007601039810f6006028084108a980c46000319842140b81020003c0340d00d9132850f594002078100c0340d00c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 733423381 1250 733422131 733422139
    0x7020604050d0f0b09120a0e010c1e1106120105120f0a0b150405040c090b0d120c0b0a052202180f0702070b0c0c0f0109090f0603020a0501300b 63
    0x242c99010401c8814014441c948a0380c00240707141c540c41c03281a5039040202e001e9580716810080b0f4901240a035034810145581498002c05a0040b5994020300c1104110b83c41046a0fa4401120420044640c41c504800090301e0700b6050211040a0711190501071040070b00178800c444540118010a010032280d002800c0120ba148501510b40040d0400c401c5540c48900c00c1c80040002039841e0900801d030003260007080318501d480c10203070014024104452202c2d0300111141403880080c040012070402800c0c543c5641043c014541071051140400400c403031560f80ca05400c00c800145d0000b101052030200c00049000d501390303440403614030710031041c0c00c3d00100001030811088408007140540304400c15800c2c0c5004d503035100b5a01100c5c0c02000c1c000581c54004000849280c2003e032800d220b0004140b410b2084259510900c40132110f5034011349020300d40f204424810740c00c1c4103280d1001400c081c0b820841c580700305110322040d4803801a000c41d450756110704051000358550080c0345c2c5000010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 733424631 1250 733423381 733423399
    0x3012c10020408030405120a0f0201030e03090a0311090112080301030f061e050a0f02040f0510020a0b0f06040c0f121109180402040b030706050d05091501060e09150607080702060405 80
    0x81602584c0ea00144030302d5204003036a1a42241844000c200110155402204941280d00940c019030142c26040e151004a100c01d0007400d103079035503081e1703064000c50040345906203000080040c0072403480141c002c42907203100005440000745045046904694110903030b859220b103607103442405020b044181c10704200e6010b02c110003142681c0e0209004100c40c0801300008688184144164080c40c491516036418244040005081000b1001803410352441aa020140c455882d14500700c0180d901d4081141011300f040b00c03c1c00c152086002c2c61701e2a01f09050028036820000b0322141c0c1c042d18541d4007039102c46081ca003100500c020f8a002080045c00300001940011968110200c11101a4442d030b003032071150740440c100403648100f510303030b0395507041e2511050b46c10700700c05810094044021841f4101d0000800c0d019026070034040c241c5551a0002d12511408004a882018106d01b1a00050b0307500c0314604c1d034426003140c041c144d10003011a2140c5050002404500645e40050340100c940 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 733425881 1250 733424631 733424639
    0x1c0b0903090a06210c181a0904090614070c290705070203010f0203090d08131e15060b030603010f050f24032b02010c1407110a060503100503012c100204 67
    0xb1400c858680c0403400d4140914070b0b07941606451020602409241c01501088165007900380764114800c4140140c40c0802e40c0910cc0d51f2107840e090049900000188003001400300704440303200e0702ca030700803442990403001000b074042401001e4809000901800400030308201151800c1d0400c01086403104021912842c02981d20390300c0e50040c0d984100010b52400010700d40c0510f103e42070503101c1d009030f03400404070b00300110154004070245007075039024803c14600100220030700440c0060031000d20020b480b0f080010a140c250f640300c210100401c2d08010801001a200c3c0c4903496008903048485408981c10300c1c81e1301410381c0c002e14141c0e01130151100344820007150f40542c08034407407604210075448103502c4040742241e0b043e0241800003140d88039054103000b031900c00f03040d02078007528a4004080d0203000051840c14580d01060200384003108115050040940c264011300c400c0d0300900c03080000840300e8801e0a40310349180c2c110f0840d000b0000c0c0503201040801d8141c01401000c66440b42c071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 733427131 1250 733425881 733425887
    0x622020909070501030c091212091707051c172209020a0e0a0e0a2307030f0c0c0f0b04030509130204091a06271c0b0903090a06210c 58
    0x10b03e004150100f428076000d118035a01c24403840049035001d5602e1900008a56158001e05c1100302440c030810024400c0030035210729050300204400c0313100c0d00610201c0d16110a01c0a00d0341e00548141200b0180b0b681180411400380d0b480001c4498100c0d4035503602c5104c02c03c40760019046800820030403002e4004160084903900a010b40c002c285c40f1080207485130400c11080d119140a4100d10001420202c0c5191449400c02150f04003c0c11103252a005a109101035020048403420002920b03643e040107a081d06100d00c1c9940306a61400c08200c40c4951a82500341e600d900c0010003071081000000c0516126000313a40041000402c26040927200041c0c0d01c0c041d40050242c01c058910b0708031032204403084240110450040500094103000d00340e421a440c2020000ca014994081c2440d0b1014540c0c2e00c000c02803a0354041e4213201c4441580d07003482560164010076449803503104001d513044564030215414111541880c0c0b80035694a001c00b0807a0040d2008120520745041c0300d242030065030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 733428381 1250 733427131 733427143
    0x21302130806010302090109230a02040b0a0503180d020d0804060b04060e24010e060702041518050a02030c0702060309120a030e060601020105070e04020d060b0412020a08060601020622020909 84
    0x4000c03200c46c0300305d03600c4518110850380042d0107012811102002c507064611000003030faa0141e034804005007856aa140c07503104581c8883d40c88000200000b0410109210b1140c203100401e80250091900540d60100a9902c4008107120780601c14010001010810b480c0c200000d481009041440050750750480c11140420a44502c0c0d200001c40a0059000300658a03151604105a4660000600c1c80051007802e5015200503a0440e071101444078030100f400e00c20320002c12040541d1201d46400300c83c9081110000b0b0400d02c0c100c3c1c010824001088581015a10710a4041351b0f0a0b5072919a072610525016490b0f480c605404404184076140982503480860444444400d507011544c40d90012402c880040306c0305408640f40303c1501c1010b007042c1e809042c6490002c400011400d4491120744510707000b641c460491128040c0d50002103080403503855004103c40c4004118070f060000010b500c80800031300300c90300e003000c00380c1102001342015469100d00303401800d00200342c1041c4403250b48074a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 733429631 1250 733428381 733428383
    0x20a080706023412151401150305040c0501051309050c071101080403120f1503110102011803090e070302070206390a0b07020309211e0a0213021308060103 68
    0x141c5450440b1402c110742440d0300040034854103c4841410301e40c6014100d603215005079443c0c4000403175010007907001c0c4101d690481401c2004640c40d1700d05005205000c1921007030030109410030040c803000895a001072000c0d071b5000d082c1131b07841d81080b040349400140941d100d222020b04240c1401340002d03107800144801409194840d000020680055502c00d80c00c0d18010009005a040900d01d80302ca640540f111140c82400890408a002c42c0340e00815010340040c6d4013170b00311034800ca45640c0c0901c20480b2501140509c07507081006c54402428000f16480748162031205100040c00c041c0c404e504660505500803e81d81e00c80d55804040590104a039141201c2c40b155100c1415001c1d501f07001c0307003072091090070080251001c01e0ba02c003240c102001c0c10b00d2080d40300a00810743d0b10303a00c0c091044a0000070520300300540e01c00c641e850385056641d909884031140358a0340d4080403100403481d1103031942c05131805212542c8050111000388a09060282c00d034a0001e800b243c00c0e00c000c18618103c0e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 733430881 1250 733429631 733429663
    0x30503190314010b1e12160210060e090f0d02060408070203030708120612060c371707091805060d06050907060e090603030a11030f0301030c090c020c0a12020a08070602 74
    0x6045e110421070414491751808203022940e44d0005a03021003c020100540641441618a554403051101041e9042600103500310494403040010841c020000c401c10f0003410300040180145004c001794035130402401c0540341e9100060b1120554404004448060b54020941c50740c0f405241407034000d004060f59198030442100c0f601004c0484009403481c080c860305a0003528094600440f000300c403014100b100b07942c1e100130002a04000079000c841920115a4450b0380f20300840c16401001418010a20010310502c50f4061007138604410f60307844100900761000489449103800281d81110122009003203c1c1004100b148011001c035504040b204d9503140d28681814100400c059a070341100c0c00c0d80c140c3d0040c06020030081c0300b01b4000d003600075205d003568902040032060000c103900c2600181c1316002006000c0200141d035100340c0c20104e4407031000e440b084510314002810030b0f40340d104001d01c82c00b4550701d440655990013808002407120804903900c0ba03580c0c02000c0e4549040d00d4001640f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 733432131 1250 733430881 733430917
    0x601030f05010e0a02070615080d0809010603030e061b0d020f0d08040b0406050711010e0105060a05121f06170d0207210b150409200604030503190314010b 68
    0x3003160003254142c07400c80c03d84007155910508114000c3d00002c2d400e4400da6116a64586412300700c1da041005080c40701c0283c107007450010320103000c415002d0000b0100c2c2c3c1c540303041040802d501114100403640121082540c40000721081485c85071100154001801200d41c1950090340000340c0074500c0000d94250f44400e22210382c00d8030b519404440140c00840840700060004016500c41980b100480c01c0c44000c0e00070702e0b22194211015040c0c00a920ba56a80a02217949821444074000300001c4a40c0d038140e440f41c0150301c1e204c10301c0301c84c150040c944080ca07202500403183c012401170106484c041000d01030480e21559903040070100309000d8040c6010100b0490703400c140c0b40c1c4001c03c5e43c0310f01e080c4280c05555803406c1071000030002c6103001c09814000c0c600343d0382c5020b41500f0034000c0780302400303204000b1031540c412841504128405d02c400c02c42000018408001d43d04034000c2000c0c0700e4400194244250082e1022a580100c1034041c01c00100b14960700d8005002202092100d03428 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 733433381 1250 733432131 733432151
    0x90e0c1009080712051501030c05090f06030c0904020103110f04090c0504030f0f0303060b0315040c0e0d060b180727030c150e040c0f0806060a0c020105030711100203060103 76
    0x16200109010b0040b558004540c24410000d40c1204070504c28412000c4400340031880044881461003070b0021595000001003c01003841e10b00241d6070411103060042c4024102007001075034480e20a2050303400b400c1d07403500080541e80664084c0603d8040451203035561580061000c060351301c11b01030307000b01a02e00740c48038588032321400c16076080c3c82d80680101c50905494542552404000004400301a2206000304030003803000c02850184c030421044640c0e410b0100300700f0040d0740484800d03000300040c5406451941c0d90781c0031461446504a4000a200171070517000c40c0300303400640b5203458000188c0060050241c0d205400c2481c0041c20135000386e00c1110303030100030300030403961102516003400041c0c00c2c000541052442c088c0002e6034140b00c01800a180d01090546c0d2208500c0301c007185d0107000c440c5102d0380101038a81e00000880d40d5034600490b107172000d0408101824082e042110110008881da4000c4004440310400d9804680390380403013800560281d84121081e03030009040c81001a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 733434631 1250 733433381 733433387
    0x140a050402030a0b0a0605060d0606020c010c0b0610140f041a030106170c090a0e1905010e01090216060e0106240e1002071701090212070f060305040606090e0c10 71
    0x80e019540c0140070780f110003003030f03202c03525030203405010058041d980c0c0034006900e80ea1007008048031003000700003061081c034045001c2d0404146020840c14040c036500c4c040c000541c584210f50f4810812188801c08443c10441240c0004148110303042c044130020b209002c0b10180000340c41110703204080c801c2d4500c8808041d2102d40401c0c07007032001185058902e030303100003102c64696a0040f5600c1c1104e00300b060a00c0014074400d525405090b0a052031001c2c0000300044841100d010800002c062015514100c5c803100700040502c110303c041680802c0280c0840c0a05110f60401c41d08502c0500082e5a00010306008003241c0c172407550729045035031280b101542c4620107240d54a406480d1044c1c444a000e051241e002284812402180101e181c0486e40303007000c1c4500d0011482d21400050010054814090b2495030b12001c1c01d045d0303101d814100400881c080d0408169819450003040c10340383c038603210300581210341040c0c0c0f07040d0604507854054000021941038145080350140c10001c0002c90035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 733435881 1250 733434631 733434641
    0x906030b101212050729180102160609060209060708040e0a09031220180f0102010e0712020d02040e010f0b0901120320060106020303160306141e03070603140a 70
    0x184043d290400b0320054501400c0945841c600403a003510203050b400600303015080d080000034052026002c14400380301541c000325044400000021864404902c500e81c4250202400c010b00c1e007900c4d070300404100219501a10520000074159a44070142880c7c920107640007800741000c1900c4c3c6000052179081d0502a800509402d52650045100205216005400c1c1c40d95200c422100311f520a4090a0018000384650500201452031901458080100c82100c20f00f04904582c104400d0304a4082c010a601003150031151059501c0341842c0b010601d00a60b111000e58000d01d0810642030106040d0026400c204d072114040208802d00020040505803c0c0944501d041e406201800064047c1e112140805031200044a9024400d000103181110903009680140c102105124002155a00c413151040440c181480300038200b0406c1100f20010039405403007064800c07402ca0304d08440c680c041629010150660702110384458019000d040c1d02440c00001281c180300060100e0b80c14822 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 733437131 1250 733435881 733435883
    0x50606040b0301051002011e0e010501080f3004030b0717102d06030903021504110d02061201031101090b09090a330314031606020f040906030b1012 65
    0x125810b40c2d00f49420b0002c507a0340492500159903890342900b01c00d464890031f25020740409400402c00001e980681070030366030103a10403846513101901c940c00203007000c03801002401154030341044000113005810b0880044d001c02c2c044020001402005000030b4406c541e100c0d594a440c2d000c08401e89006070f4145036000c81d00c0c8820f584c0c0443e018003800110055079900500b04007000300c0c91040140400d103e40c3e200f0740c08040406c1c1d6400c00c05040507014403400f0250a82038490500d14070b00313500c5c8d03900c18000c1c88500c280301381c10b0000703d03004665030513044e60309140c01a25103407911340e101c1c502407007500900404103012650910000421a0184086400341040074256203100e44031a07410f000a01064240d00000414030050201143c0308800702000e6402c4400040c0100e910354144568034a22086d005030301900104402d503002031518142108480c0d101200680d20089231002002074040c54121400f05428000d0002c2400880340c0c4803402400c04540c1006034550390b610080d4420300d5804 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 733438381 1250 733437131 733437149
    0x1090e0a0c050919020f030421021b010c05010c0806040e030408030f030a021204080d11040e07081009021303021302191b2102060604050606120a0f050c0d05060604 72
    0x305009a0501503840794020101603810b01c1c4d12041c0302407180507a00650340c84400050084100024090b01c1461510024100e59140558036a441002522800b40d14281d2004c0d400b03c0f106000582d20a0344100c4100e604103000300704840c84c1010007400c1d0381080d14034501c07460070311801d81410503010081707804440c02c040086183c8150150180300c250402010744070411742c2400588c2c0c4022002020a20a5210342c080d07554942c81c80d960401120886c0c13141541c0c0310000d0006000f409000d2002d503410103024105040c5907600e03040c81c17490150b00d41d0806041a400880c4644541c0d521001c01d00540f4030032664401c8400e00642584101c0c0940049122301d14600d00c510f508050152945a41030105200d581945900301d0300c0310000c0c0c0b044c01c1004c940e50700e0303a0001c4007511a41070022a8001c042200c05100701d09200c00007400c035000d07640e2800c4d400e900c804049441048250320101c0c8510300c0340c100317001e545054104070403107400510b840c241c0c050070080000d10074609039085409543c4520 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 733439631 1250 733438381 733438403
    0x9040809090f010f1e03081b06010e0c0301090506030a020a1217071a131703040b06030f060610090f060503100611060114010e0301050a021801081b030907030f0b01090e0a 75
    0x1040c0781e9869245e1070000d01c50420804c0e0202c049004a001403d40d6100c451a6499040030880d036985000390503031111002c1e8204c5018005400800d00c00c503070445050b030201003901c4d142c90000034105080100000c1d4061000030002900c1c03a5401d03081c0d40d0f07907030095807540301c048580c24250b02c141c4070b038000040006d0030050581e0100810000c919801c0100141c1c1c40708a0001540c60072100780038004203c03441580442004100a81c202d0910780c0400306901602900a0003009180ea804016110a1240740d103003104410841c454080c6400800e9a070700406121565280068031641c8141c5106c1c0003504603440106040d03008460201c0c5c92000c1c207000f81590380c03810102c91146090024524100468160072402950b403d02486004211072800140d80d80c0b03170322154200d14210302c10102c0c1403003c507100f046155440c02c03c98285d600c0240398102e0b603d0380c07418001805c101c96904020440d0b110b61210006200c022013140c1c0c140c46031200108681081080d407980d45809040008000c20480 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 733440881 1250 733439631 733439639
    0xf0a0e270d140d0f0f0f0905060c0a0e06042903010e040314040e100807080c01050d0515130c0f0e0d1202030f1602030d05070b01170c09040809090f010f 67
    0x9405070003842c2070a00d80480c14802020010000d45200c0340c1410100f60b2a1000402d411980c2e2007414141c0011000411041e0b0781647c8280c0c440b64010010307040c248002c103a803142103004448014215800a0070b207503503603844084c0c500700450320b0800e281911056581901c150b038000c4e0704480c180e91559404088580d10395038201c0306491442e00242044005200002d0050700d04101640660b44406d41c0000650609074443c0c03602d18283d00c050903651088160b41001d9170841d08484c41c3c0c20310010085210f50300c140c08007203640303429250950040d0700c107002102e0340c20140e4840210054550350b400118045400c007111100e0800049541c07141c850400c800029480010548449071180152030030201c604100950356000742d0322901c5403a07945483e4008500c0e007401052901e80060501e2404d0080c5070700c61510120703050080c142100d500c0c4c41d8004000742c003080703101e480002c000d10516403880e040c0713030803070315500160702d520300414000d000f02d11680705400e1194103031026400b01c000e1080c50 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 733442131 1250 733440881 733440887
    0x504170c070b0a05090406030b0601080a270c08071503061a040e1e010f06020106090e0c10030605030d11150f06040207020a030b010e011809030c0f020f0a0e270d 71
    0x4100114400d0000c20828030145d0384031801034a004500520003601645051310000d000f41100400000c24249030404d2220f00905103042e102c5010288404201d11150520380180a5040c940084031184180400014113040030a56420703042e104d983c050001e19595005a05400c00c00d181c01a11020f0a0000740050031410303240d030f81e000303101c4041244004032661811105030f50030f030056208944002c0003400219024003542c3c1c000c090940b81003114118104400392071300401c00305184a1340d0130074240403105103e50442c0300039007030040c1a144107940001c40030b441c0a41e41c07601031500740522054000094407440b1012b2045c00b01e0510102c643c0d41d1241000002e42c0141c0c401c0383d220301140004000715040b003031079034041c1003883c804001030350405002e06501001130101064440c1040c00280000768420600041c40383c0c000c040d400110038600c0003070030f0b03484031103100b0740c0048402400180c8a411040210301519240200201d07410500c80d04822280401c03640d8180d603070103100d84c0f10341e1b030b48 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 733443381 1250 733442131 733442137
    0xb04080d05180907090504150e130206190c0204061d0601180305070b1809011a0f091c0605070c0218070207030b100617071d0a0909060504170c070b 65
    0x920b101100700c060a00004400b40c40a031803810008440c0403050010341014442c201f4001e52501140010a2401254503041d00c0c0041c03c040640002d0042c10045445200685002d001d1200e10385800f481c05140080c000d41c10307003d0076441207007041c2d03000410303021400c0100d02124001400c2c21282d41d0365001507510454140b000016071041200020120b0800c2c841603000c1c043c4940c01d5503a600400031036000381003490003031622501c0d58000410590540400d504250380c00300e0465510352200a4041d1024003030105240e4000591100702c081c21031201c2e0464051034400c40e41000a621005021584090f000c43c000303400c50004c04140090029002803e80d109107030388115003806840784d60340c425030709069804128055410506001c02600705960581840e0441c034411071516001034020200e1440c0307103a00040608408904805444462090000e00b1420106000098661618000504c0f00701d4003505c40703065041400031900d0b580ea0031108018403032801029564109603445400354 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 733444631 1250 733443381 733443397
    0xb07110304050a080610080708030304030e1314041a0606160224040e090c060706020304020d0b090708070504020f0a0f090504050f04152702010e090f010602070b04080d05 75
    0xc4010300002901e0780c1d5182c42030380a0100309003d0301080c10802c40302c84801800d5000094030382c01802c1c003880120000010b03240e001d034143c580310920b6800900410801821800d100c0f4401c5e0400000c0d486196250b029140124400c040d007003c100d961004090454005464207903000c04100a0821003444400d000c0083c140000c0c11340340c0f6060030a0850150a40c1024031100c0c40c01c1c0440c0c100000508081c0c0c0b10f81c000300d010098900e07030702d801d000a0358500c542d000c0149005d0303022011900f503459100400a807558003a150300001e017001920706944808a1042c211144640940800c0c5401e040c0240c4000155000c405820118180025501a911080780c01d0030000c3c50304c4002205d030b440c0e002e0907000da5401181c00d803132410542020801082c44411146001c4d00b40002c0d138148520100d0080d000f225504038059450b0082d1004a5888801880f440e621501003802d0040f41c0b0ba01102e114104c45a640031034200d1907035842100c3e018011440b0700003e0b904040e6007d01c1e42405140200062 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 733445881 1250 733444631 733444633
    0xd0f0201063309050604050d05030c010905100e0f0c01080403020f060420090402011e0908120d060501081009050703060b13060323040f0206090a1e060801030b0711 72
    0x1e40b02e080c101d141e4820700380d004503034852507507000840350b00b5003030725448030300c01803070001030701800d280c040307100c0d8481c511a250094000c0e00148041c81401d000b0f40304c4d051440402401100000c2c281943d460b4005203801161500d005950700d10203500050510481155501405840f4842d00066600713040041040d41540034a4040a2400380d080c40510b205510030030030800014000e926582103040c5000302180610b40b141c05210141c2e0b0803000321000c05105d0000d08100b201c030007500b03c03042c846c150f000784200d225920041c0120b207252805480c1a00c2106010021950f5540046820302030a5a0810407160130321000c0c0a0100300f60060b542c009860f06002c64859560540050390740d20810f01c151412581440c00e2010035890b0007000b850b440c22901c0100031010035041d80c910722101420040504021035161021902c501c016542017140c014160381c64159601c826a1100700c0e0394000d1b41c6000018034000c01d12500940c0c801e4140c0350002041030142c2d0315400166000c580c001081191 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 733447131 1250 733445881 733445891
    0x605060402210f01060f0e1e13091e080a050d2307020607030e0d030504020a0e0f07021c0801030f020a1e080c030703030f0f030e01060f180e0d0f0201 66
    0xb05089004264540650a55079081d55150103504984a1a4180c11640420442d120b90344000b42c0c0c440314070120076a04465160710490703d0090024004042c902c4141c001007413070009807120220f07900c1060080e0003050404181010106406079109612500800000c0309001c0420100d2094000d000010b08149000609074a88843c50380b1841c02482191b155406681c00c0000643e030500440c0e4100000e4203052080050041c01540c82d1804a02001c041560318030004080d99191074a4400030311708400864034a05050360a02800304040754844094450f16061091550301c0c0110f00d1240755455503113021700d07400c40c1d40e00d680c40031450700d040c1c0c0d2205107a1408140c02c010800480103029040c031146449034034007400c083c00c2c1094800041c0c8a81c001c1201000800c0d0005400c000d0091750317103040080d004506409a0080ca400fa204c500198a000000300f51004040c18040543e890b80c1348250b109240154503a0545024280340c194a400c2848096101409031070740d002410000d00011035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 733448381 1250 733447131 733447147
    0x40b031e03120c07210906230307030c08010e010506040e060102010b1f0f020c06040b0906041710141603020a020a05150105090718050f060903010207060606031a0109030605060402 79
    0x18428109a40400c500f80c00050b84000300070b07005e085140c074425900d02d804820309144c180603105101a20862007800b03888031400c0300c1c58402c4103c0381d84007120b148400e40c0f64108410024001d00031154180041003490b4000b00d021040c00c0034003412214020800f0380303481e0810f80441c40348640942050305540d2151001c41a50b91680c0f00e0400c0c2c1041c84e00100e01c3e54a00344070040c20001641c41c41c00541d003101a0011242c2c80d03078402c0707500350381740b61000940d14070043c80492030b03600c00d5620410070042c400d0b540b8040101d011841c3c60410b45069810b020741114100c03900b0050a0544900e48103690150300800400d02a401038904000d00c2d0041e030b1010701440d101d6500703010300da801218003101c07042d006114520703190708a5134008005103002061600f413100211440c1c1c1e114020701d4441d850707511304100355646500c112006602c020f0029500c8008510f0b201c03026085502445011a041c40401c801031001410401003000e0305a4600310018915101c0710020007003d4145030f041380e020880e1103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 733449631 1250 733448381 733448407
    0xe0f120f03071211160c0f05151605030a0305090d03050603100e01021303110411090303120919141015031b09020301060c120314220b090c010e040b031e03 68
    0x3d400d456141c003008035000e10702c5c6c900981c14403500136099100082c42c00380859101c00450003074101c20310040c1d03581c500c1c5440300c02101c420510001041403100240c80c003802603040e08803034001c1e070100c011600541ea8071002641940c504581080c0c040e4040d810456000794190407080c100c4070060001440c080340b210181d1040e01c150307041500d85c02007141c020345940c1460300c0349030840d0840405240c03c0c5641d81000a48034441d070860241a06280804900140018000c0780030580364022040039400940c58001125503008005d802c1034018001244141010b030b0044150016070880c04607511410b5503680003040c0d40656001620001d0381c0404161225144005d50192200740c0f00c9030381007a0f80340b400d120202005048007080504003900181203220b0f00040c1c5800024030201e03522001d149115007039902c44503100252040c0c00900c05d0120b03031071001c107003046444000e0340c0307810410300788405000582d540c4110054041e40038510303001d01c0d400100041c4a051190405403840c00d4000882c3c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 733450881 1250 733449631 733449637
    0xb0d1104051e071808210d0e16031406070206071d0604090207020a1a040e0603010b0a090b03120301030809011803060c02060712050708040b0c0d0e0f120f03071211 72
    0x4401040c1139008070200503046002035401452880b0007066914000020003950b8081280003001107200810203070b422100c20342000d800050712074102e407500c8404445d01b1002600c1ca1205507103e03c20200f10300300c81800420341912a47d282c1e0000c042640700c08070111101c2c0c0350b6440c03032000c402d120780820b1800e9969200030001801000380250700c80075240104805032016034815040041c1c810400c2140003000025501203c0c8080ca8040e07407595000046400340c015031a41c1644400c3d030ba5404940244140d12070b5883d1403041d411901000001c02d4a400c2c10b20003800083c2ca00e05080c040c0e01c0c220341c4614514550045d100881d40030b80b603900d07683c8205881c04d00400c2d20150300242c04004009a000000007a100407000051189040080d40501101400390001c0e00660302c020005440868501c210781850701c0c002e00400401200807070064940f4035605a03061240140b20090402c3e13801c101c240c0707c00c03102c040c01a0340746403607924041d11405e920f80450300d5a00e131552904007504d1110302c00f0b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 733452131 1250 733450881 733450891
    0x60a09170703050d091a13050904150c020d121802030706030f180b1302040e161707031e05150702031305040e0706030b0d0c080a060b0d1104051e 64
    0x51a001d400c2d840e0050a201820340340c1002c000e900f4038108110b28010b4060785030f0b002c1e901d49541c0e555141c10003940c186407442d000660017405020031f000c10800059810800801c2018082003e42d01c03402003207803207207400082000081c000080f4080c0d4241c450303110b0b46854840d842079582840641c1e001c03d0502446921038400300c1c0e0380d0700c03c803804030095000e01980600e0500c440d0a400c1e0890792004d440703082c007514200c00b950f8005058070854882c0d500494079a0386000c01c41c1c50203244080141e51049580c010145040401c2c1000d0341c0300040000c40d0001d582e403145440c200c0708010400100b40c03062061b0103542034880c19011807040906280714500402c500d5000c3c5075251415016141403d04660149008614041010040c40000b0441d101a94424580850105c16000000750700403950070010305800780c003000000b05054001280001240705003c284048030151041203000c1f40c10700c40c080e240452800c10031801c2d250680c8081d8ac005403c0d0f4041d41481040c140d4100381c1c440443d1307 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 733453237 1106 733452131 733452133
    0x10506040510050a091e06120e070302060c010216200a08070605210a050106170c121e01032303040f050f01051210030c0501080402010e060a0917 64
    0xd00d1401403d1b0080850000c002c0500c42c09001c0000348140804995400103146131480c05004003000007100802500c1030700d281d03801388840c1d5071046107004480e560030022102c2d40e44031203810522045c0a1515a4850240085010481c1d0f81c41041d15200b008160010088031a0005480d004e50705249840c035102d0008200210315030506200340c1c040000e90504201448902c0c0e40194102d4031941e4900b85a00038040205e1095082503e05c122240c000704004900303217000c50852a001054103110290410212409600c003071000c0e0001c45001c1c6902401442008904860745800610000a5484d05190041c03200303082c0c0f01e600c900c0e4044c4688076441940c5ea8007030015500d02c0d428208043c07a0318a49110038400c086424001218550900100450907520030a1030714817441c0e040e10b0b0b441a0307240c118100140303600262019400c10485c204003003500e503d0740e00c0201d02181264 = true := by decide +kernel

theorem cover : BRFrame.Cov 733273381 733453237 := by
  have h0 := BRFrame.cov_init 733273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 733273381 ≤ n) (h2 : n < 733453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
