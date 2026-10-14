-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1807
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:45:09.828977+00:00
-- url     : https://prove2.me/submissions/daedbc59-1bf3-4f2d-8df6-526c41dd1847

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 324820143 ≤ n < 325000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 324821393 1250 324820143 324820147
    0x60319120f050913021315020d170f0c03090c0a062006070e120a051c08060405011505160506040506090f010c0801060507020303160b090706020a02030d03021614060f0114030c06 78
    0x10205151340c1c015920002030748200115030101207402040c1c12710302188a03201c910040000d080301d260f83d040c2c21200441d02103049000900304d90300c41e1000c7c5070407040f071004803124403101c800803540e20041d40d0000b20202d50a0110104c2030741c041f510182c00c0758480740140a007402c00b05c0001e4090301030f080000e441100f6440f25203408000070444003002a80200490710752221000792100c0c6481c500a805001404c0040001c0e514100380c010384e03048a0607102c0c10100132a080d081214039804c80720016110076862000b000105000f003100c0d5024900030405850705040c0f200d6a64034007050700e0042c2c01c699051148100c1c0740c0f900650002d0468156040103907881020b440000e06510a01c118001d11951407000901030010005c4410702c5851300000b1a03c4c45600c8405c160f0f43c80400800095142d07205008000c91203100c2d802501100394036200200740100341c6c3e0b660420f132410410206106070320442c204890041e50020b554010281078240210b20300358400860344510f50010780d28020480 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 324822643 1250 324821393 324821407
    0xa020303120403140301090510090e120f0705070b0c06090703050706081008010e06070e030a0f0809030a23070509073e010603050114060603040b060319120f05091302 73
    0x44030b80284d01c04e49542142e96030f40c0c6032508800100310542d00d410420002c0d06022034005d03040e01ca24864911844014403503100d081242100d1540080c200b030440d95424088800003840c02c001c10000b805644405035114004201010302c0d010700200451456807100c2010804203101140d2003054a00034648a0382da5901d4006e0160314040c20362040c100f6606c0c20200d000804004035555000b0356941c2d4401d070b103640b02c0c4020142e03511071880011304000c0800f410000054119802080b9600c00078050ba5400303503c540b039190280b124440d200e00a0900c4107040c2c10002028458140501411601c00780c6501b02500e0050002c0f508148690445210b203c50400c20300d10543c5070040710041c1800511034108400c2270700d01030300103803000f25201c0d803e280d092400400c404100922800020b404039017541d445484007508001c0242c00a5058010341140702919100b41f64103139a49800342c0300f40e120301818902c00608940350020180301308a800d00080c40d43d075a81440440b81c07041941e00168481c15 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 324823893 1250 324822643 324822647
    0x1e1207030f09120f11010606171b0406020a11090c030103060b0307030501050c04050102011109010507020d170720090106050d0c090e040615140a0b0304030203090405010f05030f0a020303120403 85
    0x21803440d0141034420724110700c208103580f020606081e0f50603a5200709013030a178400540e080c1d410b54040c071004641d10130118242400f041204950084010052642c903a128001d0404150312903040480140c1010805205205c0b0050081c00380340c0741540c02c903240d0b14047c6102e000602043c04014007094480d01d820f16155030401040019540140007040141046a01041103600c03500c0391501550230041481004004801520244d46040e180d85180c80015800c000c49119038500031552410104809400c030f0410358080e01115200341070503918800c00003040089098a540c0c040c0c405c0b400e00c0300500c45030364044142c1e42c1c0100c0940020940074030005081e60014401e400584031280349408210912440750042d485030480800010b2006840d100b440c8529040c640304a50004844102003101113180002035900500900c107681c24501c40200045c01c0d03940a03402490604034084042c0094a0180003a5560bd11800d004108410a50380400d48a0150340b506045000b00f0000260a140c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 324825143 1250 324823893 324823901
    0x7150504053102030601020c01020f0d050304080c010f06140f01020a08180301050406090b240d17070309030b010503030711041505211204050112052a1e1207030f 71
    0x441c1d691000c2202c807034032081400094004a511500500c0398600081007540046040560341c14810040c2552403002ca80a035602c1d4400b501c1125200030402c4811240c1c1400e100780c0d000340c03000b2400810004c4c6844421840b0440b82061203104081e450a0701c44540c0c0c00103140310070258065052512080c11040c0c0030b22a9569024a980550070401003004020f103a500c00c0c44040d108414450301525404184400307008617611001e07510903031100e400c809141c60207000071983d100b03585980031030710300c204c807a0145d803c01e1001728003142c1740d0481070081020782c0411501501c1300b0f03001941400302c10388444a1102c0c00c8a0020301490351404104d000b40440a014405418083c3c81c00c0701d004541340d2900c1d011034003a02c1708040c5014804400002180c00e4085801329481650740190540c800807141000308006040600209115454047d1245031001c416004e503004200072034071503501c2e200c0c2d050702e0041080480b0714000100200c05a5041c480c001d03d801c40c2d844d00d000a07403107010b090700d00010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 324826393 1250 324825143 324825199
    0xe180309060c150a0603020303071e0c030f17030606040306021b060717010608040209041e021513080c061b101104150806090703090c0b07140715050405 67
    0x500005440d08200e00d000982d40d07450f246420041455030b41c2c0600610840311a8040290706400803c4100d0104116448950014000540d81e40d800c240c19940e82c082e94050382d0044400745011410340c01404900004086840030a215103495450880e000842a11860100402032503005c60140d505c80100503404802000c9201207032040d0604810145c08002c0c0c18105d186840c10b188004500c40744142d010790301035540a41300380c42544442e940c011039640001d00d007180e4100075040d42409a6556a40c1c0c44000006054660b07494015102601d0108016003001007180d00544020300030b030b00c4000854080c50701010740817215a034500103075030402280c442c240074001d0030051b1070381c80e12114100900480d9089d4080d1010040883c0c0c1c141c030b4544044424a03404040c1000161140780aa00444a501c1c03117002d18460864682a01c20541e07080b401c4141ca546ca04c20036080380d5440300304081d070060700050500b210713003074003c040007000c1d44503a026990084459403005210401005925104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 324827643 1250 324826393 324826399
    0x501090623040b0c0f0102042304151e05010801030c090c02150c0904050a051003060e0718050a0c02030c1c030b030f010b090109180602090f060a0323010e180309 71
    0xd02c0c1c0d65101000981c0e00180c04048090180f480070411980051003228100d0342c6040d44a400c242c1600d0450b906040048082a000791310303a58045019000220503601829507913034401c03200c201020140301c00c0e60700c0750010350500980d500103102003010300e40805c044071140f190210741d01104c148100c1c01c2103004c1003280c881e55100d0091020000301640a0400d080003550100016a500f00c00b40040c1c54068a46007034050040c1418008202e09412001c81d806030001150300460340d41500c0c9283c0a080a90b030101903940e941441031700c00140c0100d0003000b03544d100843c141000c00c40d541381c0361b655501d8611821030008003504403c40c0a03400805505c0c000505489100443c140d02a000e004801c6109110700d113010300100707114445115034086914411181400c0b81403d586800003580400c0006a118146103499080e60707a5110081030006d005039030101c0d03450901c07507003104000103403138480700b070040c54034014051400075001c1d896202109080e60b522002d1041200d90443c800c842c01250 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 324828893 1250 324827643 324827647
    0x7110901060903020103110f2205100306050306010503030702060f070501140a050a06080d0906030f0207080301030804060210050f1501090b0d02121b0301050d2f030105100501090623 80
    0x20300540150350702e41100d0007a2418403040d8407005040785148111400c80001090500c0401c0d0010900e441001c6110552000084c83c80d440d100021980c00031010f110b0002500c644060001e81010710801d801000300b9402035051004c503500041d114014911264101a408102036040c01001d40140d6003143d16084151200c2c2000d1002a000e00800c81c1e19000450400c003000428620010b011f0840d201315582c1c4041e61420060101c019144484046a100e50240a010301040c0104000d50085124aa42e255101e18104001e41440c0c6004a8400600e01e40004c1182e0301a4690281e40d010300005615810348100f0401641e10705901d800800c070184010506440480e9135500030a082c100c1081c081c0d0055a038400c0d490a811081c4800d14500713841800104000c2c01c052400310b160900c0781116414050688003d60080d5038500301141e12250409054240b43c1020301c01d8a4018018802c000cc44500b01030019180344d40728030852040000303118064000070404024000b810012801d00307a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 324830143 1250 324828893 324828899
    0x3120a270221250504110a02190215071a0405010218060f0f2a10111204120215180c01170c1b01020d14090d020a0807110901 55
    0x1181100610350100d01a0100c1d401c403680b44418240350784082c510903070003806142c51003405140305200b0401c01a098a2440d00080b0700c595542c011042450f00040c0c499450b0b4401020007071601100c081802c3c03040310500c1c2d901016031944000c1001020642000c0c3d503890a503841c2c0710395a6106003e01504076442d0400744005c202c4190024101e5502400d8044a10400304040240521444603900c2d5089000c114044441e0320310005011894041121205011000409014a18421410503065401800d0420310350706041c41800c1d100000100302c0390030010030b035140d4485110003410290850031104550a1f600f403080000c1c08a480c0c002c1c40c0300e4031a00300b00c0f100c1c4086a103010030762000c6019220f03000740154030520b080b406001d5140d55060080d03c1d100d500150303a502c4440c4400c2c0c51000311000e4034012a00b40010104440741120000d400c0b960801d1010510a01901e00c2c4216008498030994007a0b0009140e04c0c900d40181640d6507a0707031030345808200200e071320b404190802c00070700c000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 324831393 1250 324830143 324830201
    0x71b02040911040c03020f030f04020f130203011811121f030c031406040f0f0309050a06050306030c120d0323090f0f011b0c1a09030702040608010e03120a 68
    0xc01640703682510309004e4107001442c19002d80c0035241c0c01c0f07288150240f000414200200714000e80150018164401200407140420807d0b0482a151000d00d03800100400084001c010840300c5100710070f004000010003041c90441c05d104000b507124001c0c42500c007280c0c0c0ac01d540e44000040300082c0c02041d840d646d9030324000711f5041e0340b80300070303221100075003200c0b61b09070310100da41403003290300c0090f10540070503958802c0c3c03000410f10002d8007004034001010680b40c81c0c011001000d40625196241c49251080c01c01d45006d81e0001d0b414000c0312a000e20228115002074011442103450070041079248690401d4074091250031400801d0620740414401c1110000c07548840c1420b50f0020f5450b1081480c4e0070a0907907080e401031301e070342c403108009016106110310b203880c00740c61003580f00052421030080017900920065482c1034103504001a9601103281501c40c11000344190700003440701340c442e00e414035142d00070102c01458040019001440303803000c60740000c08996401e200011030301d5681100c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 324832643 1250 324831393 324831413
    0x7030603020f0a0e180106080d0c0519170a1101020a050304120e030c060a12050a1505030f10020c0307050a03120509061006030b03030d09050303040b010617071b020409 74
    0x100340c0c000c20810380d101109003003036801c0f1000c2d112041d104840d551150744c41010346822084505142c3d569a41002c12008401d1006070465015951141411281820b2290400800c400e505400c02104485500040d83d90b010715074414081000031030310317108120401d817072000d14181c1030311181d4400030340b9030181394108000d180913034010404018040b000072003e60b1991101c80c0d15607070540c1b1000c410000b030707e00f000c0101800c075010724003600c01c6841d0015000640d074054420804858890200c0b0b9100903080030b903807005010880090044408002c030142d10b861808124245180d00006c0e40302d8608420811680c03c103900c0011600308074020309008103030380a0244210700711428500415103841300024954082c0c4002001c0b042c4040c07400000b03800610740e101506400d40010f01400341c0e001d80c90310582502d140244083c0d5a2072034580740c001003542c816044841845104c1181e54003600c9a0a0382640c0041325040c000b80c0c00e1280b07514644039180740d40e0000e502a05000707041c1d0400001d840 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 324833893 1250 324832643 324832649
    0xc1e030412170c04120f02041d010c03020906090d11030a12080a090201020c04090215160b06040c1407050a0c061d04020406020d0e060c01020a18090b0a12050f0105070306 75
    0xa00d441a1a034240100600460b0507910b580304400c051109104034001e0003a000c5800b44181c0c0000840b40031a4049400c1d81c08c0c500da21300036030211203a555082c007070070f00034021300110510701149410340703000000e24103003d6940c082c1e0103150301603400c07070070400074061030701d034001c0c004040319100a000c2c44c24071504840f8841a400042c1c42c040410701d44100303030240940f8a42c5c141c001d48101d801e5242400300600344824140d0344001c4840800c4000c1a520000b460b4000c2010288216124a800c0030302c0010400b82940c2d0085180160040e00700f80c2c0100400c083c07441040615035103c2103410854a4040005006882601c4100c40001d415400c940c0c980300300c0320819049546c040ca2401080b01320b004900c145030142c0c1014a41c01304e100d1084404090400c00208070030300b00004512402d003240c2110ba800d07804281c001d848003c0c052100e40c0014000c000181052140081001c049414915184200044803804841910030050144800c03441412078000800c40d900d09040001c01402d030600c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 324835143 1250 324833893 324833897
    0xc07020d050a120c0317090a020a0801090209060a12080c031306090501021603150c0c0b0c072a1401030e15060414060a03110604080106030b01051302070302060c1e030412 75
    0x4904043c480e01030300340046138a800da101c00714081c000141d02c2c01d40000050002800e4001c001e41e82005a54540424024288142c0001021110741c414441c0c01500600058442c005d100010440c82540200030600d80c2d600c00e0344980c85a07100780030540345018002110400c4030720080083b0341558800c0c0721070b08444090342152a411400c019101c03c00806000c09402511008025800f605e070301d030441510450b07541b5140c1035442240e00e0303541c0c941d41c09882e41d04441c04005841000d1015640392207100c15445000844110340d0707160201503d103024850303242c8082140c06c01c440b65a020b50b0022130312845020503980302c8500258140000d0760100d0f41144228a0540380702c0316886807c2d69113100f4480900310743c00d403034215250f4611041c087c2c075130b0540c010000c000204641400b0b024400095102d1a9401d50a5050108024061154441200700d0a205200910100c2e078001801a0464800c0035a91340e54066121a0000e002440c8a001c4000c1000000d200401195140c003410002c015 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 324836393 1250 324835143 324835163
    0x8010510090902180c250b060f0f0a03080d05280902010c02031b01030509030901020c1302190309050c04050402010c14030f07050f0705090613020f09150a030b22050c07020d050a 78
    0x80c215180060703021510107410300c80383c0c90002c2c002d410013001c0f942c9c1e07121004014203680c0301b0715130000d821960580c0048a00180204403518400369038001c4a1308181c000d180b0302180c1c2d0740d100e02440300013036140000300319941703409420040d64040c00851815503000b90a45071142888582d40d0041c0407400b00c0580040e00d0b260000713402003008810396002c15416409061008a11810001c4400d8400c20000500c0d41c204001c65061025400540013030505840200d8400e41d0b46c00d0444c01c0c0440e40b0502802581071008210043c1c0e40b0001c00c403519940098101c500340000741c9294030f03501a04152041e44500020100180700c0c0000e1900e03200e10144084a4020b41c50b0024072441b00390a1f242146c0164900b55000041c0704681c004d044455034840d012030800d03a0702c1001941110a03428080d80c0300d5000107034410403e03454005c1182a05050700c3d40b4541c004003003410032001c039450400c003c0565485010804405000048480180d0000c151a80403a29414119224000c00000b1600040d507 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 324837643 1250 324836393 324836437
    0x11070c0801150e0c0a0804060b0d0b0417040b040506072109031106040501083c0a1d0c01030e072d060c020105070f02241308010510090902180c 63
    0x7241c0c203900c0c880c0c41390481860400c0740c0160246d4000c1c401800031241b1036212021192903449035000325600500603101145141041d00b8180c03084034586186040f036900400062008103096011a8200c1d01c0030b9601d55614042810000d1000b4241c04a203000e07920b01c03c0d03585290580c03020101c016a4084c2c03414101001102e002c0012030300c5580b0545010810b2000000d0319503412032140e00740c00343c003034200d0b040c109071115248400800701e80030701740400c0d940c400f030011400144c4502100d1940416a003200e007001c01d1a41d41d40c40001b80c809c981010b481c5c00c03501c3d12030281070140c1e6000b85142c2c2c41003d0308100102c0f90003440e554104809582a03404000040d11910078000b0500ea181c06071261072426446032543c3c0400c510303206060307800038558042001c40035020900445848801828151140c006140b030122460321036000c507415038108406c3c401c42041204041044074510040018013040510104000800c442d0351184140780f0b140800070000088001030103140000c946480201c56 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 324838893 1250 324837643 324837659
    0x5030901020f03121302060d1107060506121b0d0606080d020d0c0807080702060403020d05010f060503010b0a26060108070e0601030c0815040608030c0f070e04031211070c080115 78
    0x42c40007200001d21318200844c1201480c2d5520009160020385842c0c50203548d01040c00c2982d141070040121000001412b0301032007100e1181c5500100115800c0c00031020161000d562071034aa020740c064090316101c1100c40c0d58641d000a042e01d54070030024441c4c165103420444d12904000391450140c001c50705050078482c46029001c4001d40c3c4000414100710003504c3d244c10a030800041240c20000030000400580d1365000010b40940c4254004500044031400c0700041d00c2c1079510a5019a0510100c500e5a503038145101060391110f0f02200c15894840540c1e0174280100b03220700c140f07409030900201d00400b01041003029181d1b5408004265110000110708a541e11603a800c000380403200030540f107a11004010100c00c40042010840f16142c4001d9801d6a0000d03006440503071000b03240e510035681c140800001480c030991415028075003602c0152a40b180240980d07503095807a0b5140c3c8824501000783c80e28035400c4000004201c2c1c0b600c44140c02001100342a11407443c18507000940e070a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 324840143 1250 324838893 324838897
    0x60901050103030207141c0b0403111f05190504080c010c020309010c060b0109030203030412051b18130f12230d0e0c040207060b100203090102070509040305090a0305030901020f03 79
    0x2e98541d0050054610f03160304c03940b90030420050345620030500b01180041a03000c000300d649150180007064030750304041c900a000c00c1a040d0050030079400c0780c00c6074484052411b0701c0c00b850601d40c1401003166034901103180f4410343d8a40100b01e400380303014140030500034518080c00005801c00020041d603980780c1c2b01aaa41e010700706100307002403962900c0c4000100c41c0e800c00740c0c082c403040c10101c2004d44c4030307400242180c002c2e03006802104103201c01003080c0201000482c2c060030760500418158160500401c10b151042345054141c0c545c0100481d800c0841c0c412084045034212941c0100c140e081d14154070600d59070b880680020321000c1c000c020b024181208104480d070581ca2840c036044031030080031b014103480340d94007030035014030907250720303940c030740780010080c4900c61000019111145020009001003140004007103510500101c100c50740c0004582c0203440045540701001d0751140340031116031141c504031035085400d4403000020010004042d04e91100b098003990300c080c0b42e00f401c06a0740c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 324841393 1250 324840143 324840149
    0x302070c03080a11010509061b0408030906030627062107030615120c1706010b04260d08070201110c061825050405011d04022206090603050609010501 66
    0x154290304100300040701070300144500c00c168200821401c4400b50100d085420484191002e81c000728100140000506001c141456241c8001d07410182403046450b983c2c00342d110b86034016000000414003564900340b80c000044908032521404002001000f500c001c4156034071802040450600d900322817880031300c12184d6690303000502c0b60b64a1601ca06000e44002040d6405001c035180c0d01082c641d03100502251414021682203402614002c45207600b40c035111903150b0036421007001400140b5218040380c0442c0c40b4079000300c00351940541842040b50078668000780901c5026401480c281d0840c85041c0304440a40007000400040100a503031403181c215075845641010300011001c0446805502c404500780c405c0790f800b80343d08424020030901e428480910b030300618a0410181c034183c00f03001d000d00219020440380010b810b0242c43e1200000c1e0000303104105226841c80c54070104414000200007914080c848666a0141c482c01080305000c2036405014200000d4041101402100d0403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 324842643 1250 324841393 324841403
    0x7020f1008190f11090901150c0f02220e010501090c0e09090a0b0420240d270302070b090603011a04030f0b070e01030c020c040209010c02150415030207 67
    0x30719520200800c00c080e6901060524040d07880001080c0a0303d2480795010031000d9200300c907540c0240900300102c2c404141d008114024400c0c100210003940074000c1038005900444007c00c00a039480000d0000e141d04024115148100c00100601c0c4400d40040c4019038500000700040d0762103450040a0b2540086440b0114500b22590907860510700b8140343d004a106064a21042c83c0c4c0d964080400c0d0281e4003a40c1010303010350040b00000c0c0500104450712000c4401d14080d200032002c40e80c140101120f0b2000043c0042441050b5480c540c120800ca490364070b040010b180c100007000c21003002180c1d0240c00600c20080007080d60300d0740b101180d603d500004d04480c01c40c0c1c40d260042e8400d102d0780c500890414418000000090302e80400f20002900c5240c80d42c003146040b14009220210b244030040c10035040c8104d40800c903401207145545418141e802680c0d48110a0040c1c401080c2e17100000d40041d44044010030718922003000d0b04c01d503144112100007040c0c0d1844220b003640201140504 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 324843893 1250 324842643 324842657
    0x71b03030e12030405040c030207051501050a060f020114100f060513120c09050403020703060507080f1603240303030c050f090105030a11031008060606180f01030605060a030207020f10 81
    0x1210b10700010380e800d0003000407040700c0c946038503800450203807442409840046900402d0440c104001070021042d0404d150030303002d0702989420002600300340184030700c034240004414500b00451007904500d070700c0116034916108600b454050520408581d00c100841c1c185100804209544110b0481300c0702c560b50a2050041401d045212036813180c10a02182c055000c030078000364445c0781d40240e0f849680250090304030a440d5060110940b5070080c400d8003000203070780801400e0b2403a14032071600301041040841001030f28000560007002000410343c904044640800204800d5440719001e40f40300b65014445c203c2501815103590280c0003030150144000d100024a5510407006503900c405200d0b00801c01c1000101d030890254410344207281010020541400080010049182c0011003070f200c01c3e180c80480d48842a03080c070700011603440342106118202c00e0740e11030382050f409864011300440d40e41144840c060000d520588049000320b1140e40f20095610745001501d08100ea240c503501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 324845143 1250 324843893 324843917
    0x70801140105040b01051e09040c0813030c020a08120c0f1c050c15010803030a051501020c04150806070917010209130203070c1b030b34020a0501020d02071b0303 71
    0x80071344205202a4104107090220403130701803140c3c41c01c0701e0300320800070580d945d00d002c0000d000075141820422424048038a0a206041251a2034800340b2905807806030001441440020350f002441e40c0590b03090f100f5100607541c031000d0b15000300f011040c1c1c1400c072030311281e90f000303404e4560800180c160540700c9041502981103000b50010000c3c40e0b05c0805540000001c40c03107604440c0400c0e0008201c940c0007108000c040c120511030075801000032004181c0945804c40000d543d80c44801010340903d40701c9890b034541c0090500c250002e000003000352191403500001c000e014035501c0c45516011002c100211100880603c203e6612041c050303c0c0e0358241120108450103588060944410804000701e050046020106001c014132903481c80305800c0c40c594140301112000141c20101e41c400465012000103445d040f1608403680b011407001e5600444600681c10942c92003009401035000181c02c4201e58681d13030003403007024400c601c900400e17080080c581112054030b01008003c40c4400000d5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 324846393 1250 324845143 324845149
    0x31609020c1e07051509090420032d150a0c1805061209031e040828060902030307050724080708060f0f15090a0b1201140d1211070801140105 62
    0x214591700f000e10307440341c81e2843d58808140018400c503815034040c000f0303d05000d41c0d0010b117154199003113002c600601e04c0d90700341c15050050310721758100001c810258400e20060001c0502c41c07802200c0801003075001514101c10100040c100c03400c0c0500016550307007512881036080d02140c00607920b02504040c10002c030000148035200c00034001c02003d100500c050642d00180341800c040d1070420100d12615a0700d080b011506d41400d043c00303110407038100c2c003001d02034000f0340d00700c284001d8210750b0220b050001400842e0a521406c80301400758020302401080301c0000c0c50812840210444032540c1c10014503000b1036142d0f00c142e56410004211364085030302e606d4094032500489030010515a420646030700081c004400d407010b04826110040762452180c80c180c0c02d020f0007084440e01640c0303403000303100306034036003032414040e01c40e070b10910f0321074001103445030004552103680c0700e54241d003c40f400c21805880b856009042c0f00c91445810400b05032124180140c0a5440c5150032020700c59003020300f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 324847643 1250 324846393 324846409
    0x60c06020306010905030f0106030c06030c1b061509060e07030203040203210904020d0b040b1c1502041203020c12010e0a0f0807051911100f0509031609020c1e0705 72
    0xc910b0401204e4100810613a801740a0300c400b5084110001828900d545403030148aa02d680c8a081418605017808001a81084480002c1e0100b0105541d440c0d569140c041d00030600c00d0840707032101b0501000842c8051403940640c0950b0311a04e103450455540c0300084042c1c0c031040784c0007501608a0b0051000325000981042c52142035001014108003410380031078100e81010484101d42d9485188040716400c00b44980420b6030020342d00d11030594600865421261140c040013440d02d0351700601f0090090442e4180c03000740500036080510f1010600f0000e542d50043c2080a01c121501c0c24524071140e0148101c00c521505800030b000741102d03c2d240c8100c000b441c1081a100082c040202c03400042c014030038020360f003940802c813076840c0c0300701c0c03d015104000d10115680545070040d4505401c42e04200d51030301c2c402d11803400b190382e05250342c0845e0900241070150140000805000304800795540c02824000c0c2856049500010b116201c8401d00ca844a117015401d03040710f1001c0c00f060509402d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 324848893 1250 324847643 324847651
    0x30a0201090b0903010f0c0507110904030507080a1101020a030506030105060f092a071407080a2f0d060519060b040e040317010b03190209012703020306190c0801060c060203 76
    0xf00000f0010b00c00861b41003521600c040c002e000840c0022144104481141001d0940707005070b5680c5001d1810303a6028001303100d0508054458071000c104d405046200f5810445e803228084d0003951280c51009001c0e0142c401595800d00c81d50038600003d00a08080362078100c4250000c0a2403066241c1010580526140c2ca5255003803042c80b800301d030350003c80040100175552085201c401480c0c111401c1c1801d000e40d0f0380000309640c0003040e920021500d0019034440d01030340034860304581d050610a555001c3d13003020780d0799000080180c0d41000e01003581c0c8214452000491805c000a4050440c00f04480d200e000c1d1800f020000e100c244a101c2c080b890042c3e11502c00d00b0706440303c8a0032001030010004c26440008a15000400c03c0400c042082c3d4011404016a4081d820140d120001a21280340c1f421001c52590307a6a803c1c00c402440080784034011600070302525034a05040d03c1c4864a800e140c251740320341d541084098503845101c0c0b07000e981250080e40c0c0d488000741d256a9040069030001d8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 324850143 1250 324848893 324848899
    0x1d0109030e0907030b0603010e0a0b030a0302030403031d100315080d120f0221040318060f080a06090212010f0b0f04060e030a063308070b0319020c1506030a0201090b09 74
    0x5201792409450b00001503000e000020303103180103031070004170880c02e44a5840140c0c1c02a0040001d03100002d4000058409980d803508000302c850b9035044a1041244180040301c0c1d001c0c10b001d280091541d0142e00c21b02c0144101c01041e00155107a520b816942e0f000080000d0026203200007515042c106a4040003c0c0c20001101510308200014003034400540300511081000c2c080f0700380f004041d0000a1801203d030110100303110180307008005402251701000c0314003800003280000700c0150340b07a03100002400b04d400f0210b486403000b08400c1001902409001ca11a45e8090041038034004002581c4402d41d030281a140f401d410554112180d11908018a42500c100c141042c0001d132680541e401d413003000e00151400307246c4184070300c07586042c20701012a01004002d09215681010940c48180c40719148416a66200d4040d0075201c081c034158040310b1180302083c00d0120103004980004564172400c1d1207240e6849120030107440b6049010024003003989400c041045526582c081c0071101001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 324851393 1250 324850143 324850151
    0x30a020403080c030a0e01081e040201020c060c0a0b13050c120307021008150a050f120a0203010e0a051005010b07060b130507120f18080c070b0d1d0109030e090703 72
    0xe80d150b8119030480d01103650181c202250002c16280d0200e03207040c05070380034a4603421506110f0724020010000c00400050440180001029a4005c010004007120058803540e60703207200700b51042c0c58142c044000c07540e1a04110101ba00e04400c244121545074201000c0c2903403030174400801136120028415801716003c18001c202c056640c0301284074001840751618402458018803203c80c000348120014811a1808030920032038849c0d071301007036840000362005035812030111952498074001c82c2c07000754990b081628041142c10301240c1c01902c03522603002c56048820105070301054440034040c80141c290f0520003140480c855400170100c0c1e03800034101c00b468008003680002510021680c41c1e02041c491350311164103000303921070400d1408030b0580400900c4140640c00d08007048035070001d40300000214007104040401d1008000134150012031940c0d8580ca04000000b802170080300301c0c9030340f00c01601c94852160602036030340869030665400707241e10134100401880c440e0103803a0740209955 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 324852643 1250 324851393 324851399
    0x70803010e0402130903020106050916020c010f05040803070f03080708130803100b0a0806030706180b090f220c0e100809011b0c0b070f08010b1e0f07020a050306011a030a0204 77
    0x300f44141780c0914041e600100c1c2c02c85c01c00041c42960003001e03211742da403100301d162240386066002c120b089015009181c50302c5d0700350f004441100d00b402a6000000e0500000034044100b04040506c80d43c0203221307850740c1d4030310b5aa104040e284007108458641c00c00b204c4905403000031b2558001141c0c00b010401c00c6908080e11040b00c184c00740c000301030010101d005401403108600d41048118018061440c000651301002480001e0342146807080a05507040070517100042d50310002c4820480d00007919105405440d130412000484401c001d5001152402c3d02120074944103805884d40401c002e0300700021040009801c441d40280100700d91130039540c5810341d050254220050700444400c1d59600c4e41c0403526420009080d1801a01000511660211b11001280c01910640c1151690192261990440003486014003062044940c0031403000840040100c2c0c0d4402810404d4000c0d20741829030380d10750b41810741d0b50b01d080c01031709410303200f0001d8502080300c0c440041da0300c03e00c000c4d40035003000e0b9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 324853893 1250 324852643 324852679
    0x105130303030e07240c14030a08071101021303020907090915050405010b0406020a0201050a05130e0414010501030221010902100930292a070803010e0402 68
    0x101900200c1c000b07078407001011410102080b00c94040c03c40f002c446244641d01d070703044e1504000d41c1060001804140a980e0b0203010104841c1d050030240741043d070b1f40ea06007225000344400300c211807600100380c02610390481d6042c140700340c4280b8411901648142c90440d0200b185189000b4492000c212007901c0204e114502c43c05007428042440b484041c41c40d0508003004181c0b078050300300302c006010034002040316980c0061055440354080c203040b503a9040c01c00048400b849910400540202d201c030001412a01404480d881603005891050b11031041c0b0442d5403d840d82071002940c01080070141000c0c8500c81410b000e00391600900008490b0166408542e0303c84050401c0c1001c103200d14810055150a514440342c2d862030700100c66505800100891b03a481300b4a0400f4120241541c004910000020b114030043c0c0301a00101042c4c1c070b0300429a800040d651048040780d10080c00078041c11403002d01c2a204e070947d01c07209080c20b580c20130315a0208004001c0c0140d0b8806419a90790607850 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 324855143 1250 324853893 324853927
    0xd05070b04051c05071a0c1204050a052205270a02040501060f140703140c010c020c0a0b090906040902151908040203031801032d0f0213030803060105 66
    0x110402425449070b1501042003405914107540301c5001810b46080c00010b14045400300684101124402080101c0080104280038243c00c488143c131440c8510090210014060411a0402c44800000e0b94444080c010230703505502410340c1c03551f8502140c03078140300c45030441d5a01501d50109280d15a00041c542215070302c1100d40c100b015004101c07a0307025400c003800340318050708460030080d21441603400c0003031203000541c85c00e1100710808135050702098400c0d560018980c08000b03680c0d45811180078114001c1451441e140054032039a201c05a8506091010303d0465844c0395030141000d4226090180c1e210004100940c0950764141e40401070303544812003d40c5405500080d9254400d004641036000c0c0d0056190040c8403464040000503507000040710345a07240c0b00300240c94002420b00580c0600400000c960351000010800030394009000d4052100c88222030043c096007a03001c01c400c0827480790f200c3d004000c1200b8030090022402440095421150614015140101c110310130740c1e0750 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 324856393 1250 324855143 324855149
    0xf0634122c010203040302060f0411210709060b09190e0f040507060905090601050a0c14030c07090510030803041e300f0c1103030705031306030603030e040b0d0507 72
    0x14501c8008501e50203940515101040060030008500e18181a02c002c0d60720742008140b56641200b89000400700800910700800c811009041c45803550040101d001103c84000e14102d00c5224440c00020042844d00610781203400544c145483c00d9140ca0030f004110703091300380d44c03000600f901200085001c10913000038440c4080503174201b05414030740740083c01c20070035038460401c202004c0420300540e980d0380e00543c0c0144007401d00c507035260304001c025241c0c2a60b941c00601800c01201c0200d502041c00300c001d03c140c0b40b0f01c04c15201d8854031140608100ca4065400c4c501c400030840701880018468030003190080c0c016103100411001950344101041402e0b501142c01c40c9041c85810f2022001075110380304540405e003110303c10740544600901c121384104c0000100030081205c002800b0300c00b007031906030800242c1070341d0341e0f240f507030074459900d510001034500e03001b0b08031100161262180c45080142c036415651003c140203220100b1019000800c8003d5015100003005400034000700480002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 324857643 1250 324856393 324856421
    0x30d060501091403120d18050d02012a1110060f0306050108030313021905031b030705180103150b06070c18060b030a0525020f063412 59
    0x4814240000104040115030049a000d00081c245251980c1d0200360000601c0c5000720a548540415000c0d0002e0568040303102c200e0b2411045c1041401004140a04100c030903030002e10000101c80304c690000050603d02c5c83c49100c1c00c0700e07900d800c2803198100c4400b2a411104813003040d40041a82e1048a00c40e512000c0941b240100820420a1902981d801005408083c509620701400d00620307080c465074000b88103c5040411900820032420307071002074003001d8112041c81c040c021040d008810704014143c070900c0340c040005250302e80740e11101c081c3e00c14040c0500e116403031a40c8130549900c2c504921009651100361000351074071240044d0005074080e03c0c2d00b494603454111480c2a00301e4001030410041e060050600c18005d0a0040700d40000d48000700196943d02e4034035584c07441c0388159034107511340390003000c61400301d40c000307044400180b08506840f41e42c0c80301501d000742c47c510252111080e00d02e0824107402c3c4402c40c0d2000800d0815410300f00f1008442c1605802101c41c15811161 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 324858893 1250 324857643 324857651
    0xc07050a0b1303080c04120204090314120a060f0602190f0f0f03090501020304080a020d08070614040605160e040b010e040203010807080c03010c091a040b0307050c010c08040c1e08030d 81
    0x18544d00250043e0440044035882d0f142a04103101803d05013410300c4040d000d59100d00b0a0420984614264035100b09243c01050b00d070034490110300d48640e015101251002d08102012509203a5802c61200303d500b16001440300701036010360040c6c00720000a040d581c00e00c0c0c41c0d038420701040c2c00e003a40c941110700c036403416107a002c1350380742c090009410307034200743d04541c820710040c010304038002150741415070112241001c008035460300e0034291284440c000c01e2a07040070310301c1d2441000c0710b1555000d144100f07130500181da202004041c4565400399010002004d078516110325041a6110141250041c94201300c580c00c1d400c007245c16a0300a030b01440150344145810441e00c1ca09101c0401107a004a000b801031f144810801407408030140034403500c0d020b403001c2440c0c1581306113044400603d00800d0040c0c40e8549100084d20701e030410a03401c0c820f942450043c2800700c0c411380e503c9200d1903000310010b00140c105014060140f090b51081400304610140224189100304003030480300c0da88070700c00300d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 324860143 1250 324858893 324858931
    0x6010c0b040609020301060b1b0a0c1707050307150f02010c23070609050c01030b010c080403030807021903020d1b0c14060d050a0e120408060f0a1119030e150c07050a0b 74
    0x2401c4401e0512212714140c12404080000918041e2070404445001c0f5841c424400c02100003030a198403a406907174148a0a180007820104410100101140c03645903c02d518010003001e9081c0c8040c1340f4184002805262401280c4440a080d4926004500c40711810041650342e03200459154101c02d0707a951b170111000d0314803981d15001d001d0050b0030030710f030414886226948600c02c0e03000d24003008060000e603071f000603a80ba20800440c20251040708101132800d40030300b40a0f40f81e02000d00f042001454112035000c21210282241c2d1b02198081d907024249450000e1032001c0f8050040c05a82c04071080089100c008428080c7c3c0d40140b03500d030340c0000c0d60000c220030a440c2c2004440b091807044014042080102c0f4041042540019042c90f620525520901c04000410141581c840c0c1c0d20b5011800240d080c0c000300c0c91000c0d11034a03840170801c1c034054400c0c0a98450610500000110b004000524030886e110007601003580f250302160000c070301310380d00d404108200701c5016041068503c515 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 324861393 1250 324860143 324860167
    0x9030206160506060d050307120c0807080a0801060503010b1602040b22140f01061b0804090e0105070306180b15040308220e181c020a1a06010c0b040609020301060b 72
    0x40d80c2020301200c817208502200c1c1d80c2d00b40c480c020040080e01c04106100170102c1c150041c20008040ca5101d403007a0341d101c505140a1865800844011002445040000c0f07030a03401070b400c49041e07948468100d0305041d000146200000008601240c1254440300c02c071000c0d481d00040019a40c2172449440c0740608080202022607850085000c44658520240804c91803052041030540b03100c0d01d00b81c0c2c0c4840205102c1083c0c0d80e490b0341d008107071400000e00040c0c011610341c8444500c0c210f0a00900c100e49a0b04000c0b420369500b801042e60000021140f0315240516030f0000b106503a0284c00c4d031005000d220003203151a081940140d640039000180d803c0d810b075501242d01100d00c0c003000070300e444608203c81c0c250041c1d40100a202c0c00460902e1166000c4020041515401c00c00e448820031600715050094841c8480300048030260a202d220303103d00910703031461234801c13801070f510a01c483c0e1003a15610000000076100f5a0074956400034080542c50a0203020042c105583c04036580d442031041c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 324862643 1250 324861393 324861403
    0xa080d02011b080c1e030c0306040b090708151c050a050d05040f17010b0405010609060f02031804090f050604060603170c1b131410060203040608040f03090302061605 73
    0x40d8001203403051245114464200c0002500041c0c00a00c1940385c4812200003000100c010801d103401d03a40c00b100b04800024058000c500c00c80081d035043c80110b100ca4180180c1c82c0040d203800020808042c00500801c01840c94140c0d401001406d0460261145c0814000101e80c18019035945d00201003080900408004010680d8210318042c3d00d41890600040316152240c001c102034100411500441001e0940100442810042081140c2d588d07400014114030071920503400410f04060b4500e107503500101c02d440d4010081c11030000d0414011040000402143d14222a0b980c43d104e03074100410000c11400e03104610030200007070ba407401e500300380d0303070f400070481005041390070400c50030100d6800400c1e807a02c2d980101e14420400b100483c0003545c1c01008840c40306615180c012240300300405140f001d40160744004648a1040c0c556031708036120b00c1603026440110700c0070b00100f40040ca03014904071b00b0700d009143c5025a5616a070001d04140d02230340510542c403185040796810f004003840 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 324863893 1250 324862643 324862661
    0x120c0102280f0b04061b1202030a1e050403080a18060e16060801060e2b170a09210209150112020c010911010305151504080f0609070e060d020910050a080d0201 70
    0x106d224542c031584400404000043c00c0790070020340c011004c542d003d801d0340c0152a1180154003040103400030503400c04c0003403008131010b400007102c1601045407250640306072920714030142c44500308071242c3d444420143c120600c19a019224003a43e0242c010700c640c003408083c010035030710030707010313501d05100180628003413681248104202c4845403481000d500110811400140c41d14050321201d042000c1c1402e40494041c848a400154200805034480454400c1e684100f081407aa8450f0300918985000e9241d0025082091200804d44c0c0204455030242040320524044205030300d036041ca030080c3d1b000109100a242c0d110092403007041646a0074202407503003032800704558a806a02d050b041d00d072080b1400e00030405203803145010484201100c024012072400c460420703151034085541ea03c2e0071600100203000e64200417841141d103002280c06001c0003071030360380c0c50f2000d5020041c01003409088040e00f03c0340d203280003070b00e5150042004020484e501c050041d651b01004042d0a56510007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 324865143 1250 324863893 324863921
    0xc0c0c010219060c02010618020d05130209010501120f0219080a0c1b0201020c09070c020915060d0b01030219120c02010506061603050c030d0902120c0102280f0b0406 73
    0x280080481000c0032198100e07802c05004200c0c0c1041044c00d0380141f516402001c204041d40220240710380050b0001e00c0c0c0b510302350a00300f201d50388114100b4601010014002d40c000d10340310040102d036101d21a04500c1c4401d0140010300d695104001c4001c80e440348501380c0341040c19003a40c0e107005401c0baa019612190344107051126024010009000c40c1170340c0a1040b514500040204c10b592081003031440903000540b500906040615020300b0741010710340c04074800c206801c00a8075901d004070201c101480050852030601402c1c6403100c0140040c440e500f070405909004031400c20380d44804065525040c0c1c0c4464080060481008003581e0070b4041400540e81405c090004a80b41c41c012200000312030044910100290b00c0c04172564802c101400042d4400810b100f00491200da2015000034821240c5080c10000c00c024151905c69031a84d65025800c001030240e136006c007100c22142c011640e0414189031070343c50796402c491101c41d082d09540c1031103d40304000400030507100340524a4401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 324866393 1250 324865143 324865153
    0x210051b072d05091e3d030b06010e060a030c020606030a05331f050f01050a0804050106050307030f150e03030c0705010f020705010f0b09150607050f060c0c0c0102 72
    0x68080c00b8015001e40300755400b03000d014000a0126118401204100c0328100000c03a82c0d00b007105150003500412604017038441454030003601d0090a203049020401c0c1042414803c2c940f4540f41d08001080003010b241c103100340c00100000780d0340c4000c01811552095240000c46401407040286401001000030340030741d1001914a01007540004d9405500094003504580c50613181d100707410045407200c40107941e0700c0321010701c0880003200c1069a00701c51200c0703201484964038010042c140700b950301110b0101e441041140915072203010707003d500c54040c03400400c40d11399400120340782501981c025a540082558076800300484000300b60080301181c0c000340030804625000c1500c900c006001490104000101402042003e4000d00004951901c045445105504106001c4c0c582004610a55440e250140c0060300d080c01889004840b0002000301c03845291040c002c450f40710413003c2c1d401e0301c2052041034281070204101e600c100d008502040d103809407046c48900d0891911886030540d040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 324867643 1250 324866393 324866459
    0x30303050a0c230c030f0a09030b060402040b0307030b03010b0a060f03060f080601050907180f0509090f060a090503070206030a0b10030207020609010e0103150f081005010506070210051b07 83
    0x2d030984480600c1001045184d44901c2207114626611071b0000c45200402c0204d1181655a000603071082128040c422200703842e40d61008100c103e1050340580f412046080c0082032600b0f200b0b87c0204080c0201900004645200c4800106418219880703580040e02c1c0707040a0160036814002d003002072400c4481038552608040305c25031a00014081c490290514a0005100320b1140d402c000c0c0c0000c3c08000150a0340d12294400301d81d142ea400389500039540c88010800c1240c001500603001c4443e000545030039269805504080c260400080e100d40c4000d00035400542d403a0b600460007a0300384000007450380901c02c10f0094595403600c584013818414855040545c580c80c046506051003443c0016464403c1001a0014001882c4a480c00d280a40010600358040c0e103001b0141e400040c200d43c1a0b6011301e940e5006d4031001d0240320b800c104284848801401d01411481e514101e0342011030411411a000300344140e40b14010b04083e074030090042144c15201102c0d22601400c0c29003012000c41c03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 324868893 1250 324867643 324867677
    0xf060e0a12080901090e0f07030c0f200312150a0506030c0702040f1803030b0a050f0a030b0a060e04110a0e0c0702130204050d0b040204180515070e0a030303050a0c 72
    0x416241c001e01051400107001881e030b03204011110150010700c200c4003090900c400043c06451048506102091404010469581c041c0400c0940200a80d540b41400c446104a88074040384e8100c0c07990b00c6100c00e105c069805022241e165208542e243e01003001c2c45100340411070104c0999016a0043c54100705001c1d038445034204540820360140d401103683c080401d0700300c0041003042041c07a1440340c8019284209941508000a031940444003080c40716220810440e40c1c03a098100941e00c04040d1800b00001155519155480303a8024030018810b9941c2c20703400102d420480b000c58040c442c0da82d00d0542d602c1c00c81c5698010748450003684d039462030907400c070b003410344100040a88190401c641100c44110260112006070901070020062500e40c3c0c601520007c41c2520224482c60a1140c00c4480d03001f0800481180354000c0c005214070040602560810200a452001007140110300a0740d43d0701c2d41030b5010003d5110b56000034040c80c00003e8102115082e10010007040881e03070b104c4590345 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 324870143 1250 324868893 324868919
    0x11805160f0902130b030106020a061413140114040b011d070f050d090503041214030901080c0d0902030a210806031e07091503050d0201020c210705070f060e0a 70
    0x396140c0b10040c1d4407010580c1c0040c42040d69031200304403180010022800c56408030b1070f000340510038401406120440100c40c54080320031a0040300269607004280e0124034a000d209034004c8280c0c0000401c031111195220300d402013118291205401c503801000040b032a414401e8240d42c080c504071401c1e00f04410f0050421441142c800308115010035a02584002e56010350521584402226030b00d95880c0b86000f52110507000c191032044e4041c18081280002004481890b0700507550054159508074001d4815081645694070280e541c4a0800040e03d0400c070803040070707001d4071242960601045800e607001e895101d0707403070800c11403005000c0305072000101140e0382c5803034003110300d11030724108080c0745408404d502181035142000741d02503044034020006e4060742d0003a0103070f0300444600d0500340e0907403045000350501c030b43c84681d5a000c100c0e080a42000c00500710340e0000d160406680b5101e00c0c1c40c0c059082658a040d001d00c08010316900301c4503190391518180c9040b160b00e45040d0501c2625 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 324871393 1250 324870143 324870149
    0x5011202030105180c19030e070f0f0524040915050f0d200607080c0c01051201120f02040f0c0206070e06030f060a0f03050601090c1b1101020f011805160f 68
    0x10003044c101140e885d0003501d0a440305000c801e80f180ca003e00100324000c3c003900c80c4106c80b9030f081c0502d58001c0b401d0760070600700c43e0545100c1c00e40c4140305403a120a02100562030030707640340d00160b19014a07a6951081000344001c07c00c0d60000f040e030104101504142d01101e500242c801e180100303807a201c03600c0c0c035003450a030f054100b0060341141e20488001c0e0700e02c00344641c103158051000038516040250300d5000c0c025100684044403c00e000540c01960b0030f01c10a081524401400001041005080d060032800c041c82199106141041036021405503182d2415840c0c41c1600c400c1580e80003641000401c0d030211462506e030003400200d0300826050712000d484401a07503102000540a82c0700c03800c0b000001c222802041c613540b99a800c00a0300d89a0a009000c0041c0c10b024141a106118180b40c03420200d41113000070f24903800b40e95011889018500716410760150110130600c540084c412000c99540b60008840400c0e2180f800c00e0401074600854410301910041c02d1000b28040001c034401c3e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 324872643 1250 324871393 324871429
    0x1409090604032a0b0109050a050118150f261c080a0605060a02030d050702010b06180112021902070801021908040516060e01021b10051606050f0105011202030105 71
    0x28400a00d01c91104000e0f0100900d0608042c1d1201c030010080b1001c1d1042c100c0788107000030045516000a81810380d03800384514141d810240c0506516044c0c294800302d0501c520840014180d40d40c1d100c601210040781d44040b449a0395071100c0c5aa08194010500540c03a02102400102c40b102c0d480018219040d02041704103c40c2c60001820001d0390750240c00500b20080c40745407100310400c0020764070361040031103910103400c2c00c3c04141aa80140248031000400504842c2403000300d8080284484003140354904222a4091481000b04984010492041d01080c00d01501d207a00c01b02900d04045507200c0b100b113138410022411b03041d000f620103d4030b064452410400540740c0c1d0511318030f03252403070348078800500f800b14000440540020740191000001c4e020741d02e101c4420b8185048000302c0c40003064000717552004001d6883e1048004015440800d090a00c180d020b60300c4000c2224000c84101608120010050080f581c00141c0c00404000c1c4000030751071036041c0004141000c00c06601018 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 324873893 1250 324872643 324872657
    0x506010b09040e0105010b0307170103050a0602030408090a0807050a0f0f050d1703252d020f19110a08030414010e030f01061502010e190809090c04140909060403 71
    0x224a960303680002c64043c000030003d101e2540c44800170082c51b4801d948940200f01d914094408860010b00e185049070b8120340034240382c003c19151000650b0004000715400c0c4020000d51100f9a00c103040c8001400c4402d008000441c04d2105009120200d608054102e070090071041004040501540060f03490036681017604140d103140c03c076811500ca10f040c1312200008000c00c003115a010302466582d07400d103580a40e0504111006403203115141182290070b180450060404001032820b82607030321000e1048030344600743d4007410b41c00d00d080d02d075074071401d02c069070440c41c14400d0030003c4d50000c0c681250005512480e040c8560740e00e02c114070915954000d02d281e990f40036805107400400e030b0a800b409641c805900c014095000381814083d0003401500c131800414050f105108005003c07103058001c0000c03824550f803511074500400809c803411103041209848030744038501c10754040c03a10307801c40700c3d1914100700401050101e8012000d002c0c149501c20000d0341d00b130000358036801c1605030800348 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 324875143 1250 324873893 324873907
    0x61b110f0a230906030a020103090311070801050103050c19090b0102010f020c0f1b0f090615190206011d0708040c080d0e030c060a0905090a1e0902030f01090506010b 73
    0x540000d005100c03065000005100c0062100d0350040350740c1a803240e02d0050001c04a040c020403003d64800d0300da55030941e1100c0c0b050001035000340d004505103030007424182c1e1880c2e0042581c81c5001c46507042a2400d035101c83c010001c00008005d000c1760084125405411007001c0f08a0030440d0302a88100d180581e207a0540081c0380e4003e600c0b60301c0301000640195540c8440300e00d0f07180c0d1515024036561707144c4911809003800304402a8044059040100940c50100c03c00301040b011400150289501098030a92840e810131000018104800c0030f007144a0791001d0600003a007441d005034024032624180c12802c80e408000100c885901000c2c5003481e07032658946040407442104c039034204030f905118071100d2600040e004a46004d8214080701150004010401030200e20b00400600d0303000b184100c01e040c072203464001c0a084d401007200d0000200c010800661b904012250000c420125950706080710550409119104000518100034841c030b6030540c3c0c4859455005100c1c64a5011010603070f0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 324876393 1250 324875143 324875149
    0xb131a0607081e0405030f010903050f1e030405070f0f03050303040618151a0d05030306040915050703051e0f0705030a11030114093912090a0b01061b11 67
    0x3454003a100720f03002440d414071050710000750b80d00a00034035110340701c1c444100d900307140d05000700c00010b54940c1d035181c1440d0440c02c60100c03a07048481da40002a03010710303469052141980145208038010801032140918000e44a8000d22441d08907809982c205102440411000011650010f80c4800f000800603003400c03080840c1807170520010200c1490000345120b4031032940080c0071102000700302c8586500d8203410001c01c4000164014404e42050000400700d1400d540204045800f40742180055030b44240103504a0300304a50307a80100780d0350700900900c001280000400090b9012030840341d42000e1781407460248005050400b001000000078030301650301d802c00c50080a10000080d200e5866608020f00d00c541c800703211b8022202200010342d0944141100301a0700c2c6541d080315000401002801c036002c3c85950b080d0b40c4524200405060702101c210b800e4895040c0d076000c2e050600142c50840b81c0c50a060b030002080040c2e0101442d4400540450031a0407640401010003031054103003c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 324877643 1250 324876393 324876397
    0x2d020904021f02011d0304051503070201090807061a010c08070b0403050d1a0f19030b06061b0609011d121e12090c0a1802090d14010b131a060708 64
    0x212000711400394114034500383c2c054000320945400d40c0792450010380c080161590320700961090981c009a50710b42d02c03040c2da80c01c3c0000c54110405100201750034403143c540030f200c0c0e44a148203c980075600c2c4d86a0343d50220070100560a0341091030803881d900d07540c1e11511554091002e0191492000001083c01c142c01201140e80c0462011410712920070000491a41d10b40840001401004000b40313000f054500803007040226000a004100b01a0964451180c540c6d4001c0415800600400c0804007401100618102c94a0404010122864003021480c01d4841644801e50401c508e100c0014a052001c01e0304010081d80d818595110b000d841e0383c03c0f4030360140080300030141e0000940510b6030081505031178411400300d4101d40d08013004034207010801e0b80b0340c4104240d00e102c1e4907940d514040300e17400078502d03040020004d000d0a800c945620000081c11400d080c0c07242c0d9540200500342c1040d04402c2600d0080140404c000600c20020110480d82483c180d8864080005e60104000030765013 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 324878893 1250 324877643 324877669
    0x81611100c030b060726040f0e04060c09180b040b0402030924010e070806040b100509120a0210030b060712020a0314180103020a0e0306040b042d02090402 68
    0x80319529020380c00300000034102a4480400281440d29043c0320b42040004c80d940c650780401c001000b0030804540303001242c441c0c00d411514400c200400960b4464410640002d444004020406d48c2814074001c0204c07a49000c2a90034003981c00401c0140648002c45000e143c544031001141c0b04101100060042410070402a401480030007807081115001910a00d48540b40120400c038100b01380316600490b8091059244806c0f01c00d00142c406403113440800d402c840064404111268804c0c0010207951482d201c08000901c0450222114030740100038400e809030000240001d104250040380c0c10f0a01c040c0640141030303ca4510422540f600c404450341541c02c0609030100c211a80c030025141c0101803002e03800200d001003248440c0220404503050000c140c0072020450328800015406034100001c82c00a108903c45540e0082d101401440c0c880c170302c940c4180d012840c00345442065004007035090056224544500c00aa80403143d20b1040307150100d0306c0e02c0c0960f031a88001603803004154 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 324880143 1250 324878893 324878927
    0x40b0a0306060e101205060604111204050d080c0708090d030509031525081f080706051b03030405060103060905010216150606021c11011407020703060b01030209010816 74
    0x882c1c0002c44101d400100c038061030461010760019a6119102c1c60f604a036000d001e05503402c901e01180407454154040540b40b9080d5440c80c1c02c0801e0f401c4401c03900c0000b12400d45451700600a48030704954081c030301c0c0c7e034410340c082d0400307090807015143c43c13800d80690124107019400c250392240a140c007402c241c070650348006003128540d6100e40030000b01c03034009440c440c60400800310b070f2421407009030700070581100c07541c1e0310316a03981d4803440b004050341c6651843c0c00705a51400000700342000140035540c0544040e0700c1d41d41e03680d403000e00c003050b80c500389003041813081e002401400009000825030904480c1c01071404500c0403003a003402d5009109074500d640d8100e0303400401c9001c02508902c0700241b490001410402d255681100ba030300c40407800445080668050304000384a405555085030b00c0707113280c4c00041c40002070201c010031542d054030050050703408000300700b0030030040b1300404102007020300c0c096081c03507001000070b007010801414203500c030060840d240b0407041c4142005501c5440b90 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 324881393 1250 324880143 324880151
    0x3070f030b0f03010903090303020d030516230406180906030b0c0d0204120b010e0603072405040e010b0405090c0a0219030e10090f0e060303090f01091815080c010e040b0a0306 77
    0xa0301e4080c7c503590f80e82c80b044015004440da082c1c00140288507080c8901d61140007160011400341c403c07103a91182e04d03090324420011003d00d01070074404074050320107480d80b610350449200343c03007000d50000c00350b5074803a20166040840a100007605644410f4110401e44649500c54480201a0340a40182c0d007045124440400300c0806000e08503104d14100d07140c45800420a45440c002e242d04c828840c09039440110f01038940c0040e600340d00be200703141c000c21440d02c1410107440d0044000c044400b03a024000e0b11030041410302c16460031a00454001017842c00300c0340380800111b0003a440340780220000c58448100040c060915002e100c22010313078040103040301c810007520140030381141c0306406266003c00c1c612202203100003a9800c6030f8010300c0000c0041d070030103031604104900c0e41650629a03042000d9544005245200e00d4041c207528428100b02003010120341400840510440c2c0c0064615407002c0300e60009641c00100455914905a6020403002c3e101c0000c60080c90313103540014901707460 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 324882643 1250 324881393 324881411
    0xe07030b10030b19050105030f061f050916020f030a020a030e01050c01021c1b0e0918030d0c0305150d14030c070605120615030a0209030111070311011103070f030b0f0301 75
    0x4c0001d01110a404003000c20242e41c941090550720026021040c805074400d0003c03403d04003410240266841010321410483c1b52a0f4011541d0203805854280e00580710416244c1d01d0394041c401e51107442c0b840d900a40c10701151180c02955149561300c085d080c001031405018140e44284120780d0341c0d03801e007402903580340907c594100458084132820322175a4076142202000e10040c0c0c4140300c0c540c1256884804402c1d41404209070b00c00003074000ca440c240b0107502c0e09420740302440030382807242c00110005104107000c0d1000d01034130002448803004001400f416500350b80c954004040c400c1d0442101c400b601e5800074800c1c034511426880850034800e6080000c0c20790345c01801001c10079000710303a03400b01e03848a80900507800901901d038148003d05000148404009901620700400e0080c004210741e000503610310340660107650164002402c020903441d500c0c20034000d44c1c1c21150010b01e1741d403440c54254401007205140b00b044208254039540350045ca555070518201604100900800c10140303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 324883893 1250 324882643 324882661
    0x1005090a06083c09010c0e1e0406060503040309080c150309010b03011802120f190c050d1a060102120912010b0a080703030809010501030206040303110312041209090e07030b10030b 79
    0x20450f00340c4108100030100140d003d060602400c90444141e4442d030000d010394100f0040408000304210072340700040143c000300d558640c0101d100400342519115502e0400c0e0500400f2400c481d001048103038442a0400030946500340c07820300003050b054000d516510f459030b55070302500c5000300c10743c1c1c59800d0030401c00c05280d03407072800040244211000c01d4030311004940e06884d04400b401d0502941c00445581c95048419115005618854040b0f4103480c0d07102c80001e950900301020907a240c00d5030b081e240454903095901240c10035001d00041103110700c004500d609602c108000280508031940b1894800902500002d0804030010300c15039506480d04000e5655207618801900043c00d41c00205465101c180706480c107032a0090240e5107010704540701951103001c014418015444204221030310b04004610907030203203100340030307032a80c08400c003100a0004415030080600d83d8900728000741103544c00180b0004490340010b4458542d41c55481c203980300c5045a10242900e00c00c5410822005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 324885143 1250 324883893 324883981
    0x302070f1406011d010e0115020a060e03040612020304020d1401020409140f011d0c1b0607090f08010606080412031103041a010e133306051005090a0608 67
    0x4c0c07007040500088801e241c100035901c00080c4641100b4410758401403144004141e1421801c034041d00484040c01003603600d0104907146120701d41600c3d000400c0c140304240d405005140d90010031007040d400c6007003d40002d1103c907a100c1e0018440341416051801500382901910014801a2810030690007505038149141d08215070b1511560300034000494078208a110a00e00000068034245e095503965000100940c031049900b130345070540c125090300218040111500c02c1a8540d50344a120f46454601c036010001900b00c0c40e25641007440620155500c210143e82c02a08050b4101440c2030300c41d020740c000c0120783d50904045000000300310900014904c1258115681d0715119681c3c2e923034001c50b00c0c08a400351400440500103840240c0410b25100c03107091142030120050704e4424081400e41c54554241d00405545501c5003810000c520700409000c95130f00031410424607200c45100011802100c1d40160400c0c0907007400172503820841c0d50340c4c504a00c0f0000b6040c02c00c00010429140b488 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 324886393 1250 324885143 324885149
    0x14040f0b0d1b0504201c1e0f0204120809060c2b0c03050a0f030e07150e03060103050c010804050c15032d070c0203240f0a090309060302070f140601 65
    0x30000b1030000500e07030815104105401200d1804101c2c46a00d000c0042ea2661280c1c3d03120001c2c43c0c059601d40304030002849100b8440c1204410840c421400800300703020fa4108001b40c0c07407030a1041c80104240c1280b10300e81014154029541c590361150500040c182d8010b620400b45640700d4a8241d0301e40c028040070b102c00c0c0000646164402448440007150400c41d01790001303000840504c60145280d00407800283c182003d428007050103070b0305403a1986406215801100c004450324408222580c00100d00c005820055002d0320700d960554541039a40c14036001400d042000010000b0284101404001c0c41030500a04043c0f21030070b01c414540340c1d5042650114203c11601c08460358215089032155105a06035440710300360ba94014081d06c070403018490503038050007403c4d4441900e800d44510746224a00d0111080325504000481c00c44a040c001c086000c55441c012010021941261005044441c0d6180160780d4034070514089544240764400241100d00346c0800c4503081802040c5141030f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 324887643 1250 324886393 324886433
    0x7051c0b0702012007034b1701050319140313060f0c0201120f020909090a1101050f030c0315181603061202060a03090507270614040f0b0d 61
    0xf5130200f2220b01c501d03108000009000c20405061034541c6c5003034480005000502c02c9940d544901c3d403041c400d00917803c81454180c20006500c229103456049807881642c02400302d9502c1c031300d60420000c0b903074900e80b410300c03007417030048011041c1c00304501c1066480c089407100341030301c0d2900307100100d444100c1c2c100c1c010940441e4042404000700c80c4640c450450f40f640595540000c80c0141400f00018542650141203003038081103200125180d03890180d000783c1c1003c00411582c8030908251240c48113846816041000410901e12210260b00940340c00c1780015000e69501c0d1074581503150302013000400250451903c0c440008955100016284160724900001200d5080a001142169140e01440c1d51a8044140c0310015041c108080c103078100c1c42c0e0500090200241e1281440c6c210140e02c10b0000700b8890321902421210303500e0801c80e01c2000207052020f14203060303448003608150888140141c0d40c6060390340900c40079401651003440041d10b928040c1e041800c010710202c20b84544402 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 324888893 1250 324887643 324887681
    0xe0c030d0909110a0813060f091103060a021c0b0d1a09010f020901020a030c051002030f0a06050d020105090103151701020a1d06030103030c06020904060e04050c0109050307051c0b070201 82
    0x4903c1036950890300036a0256503040010b5a8004806105054180003942d1a46e91044182c0402d0014492099501d004045172a07020740450105460040002e040c0d41d54280140526142d502c11018890403183c49a00040340103e14a000300b0032003900008040c0c5407091103030000080c451051075060003242200003d0101170000568035050744549410f070340c016409881840b020a1103030101d40340c03981c8544150b1351241c641c400c1c803a0590b0816030b10040d030b050042c0d040c407554004621588001f407006031030114003543e02e900040d0960240c0d04043c3e0525441d60000d0100c1c800c804910700140c070440c28400300a142441c66a4000e4108007003035004103003100720400780e000c0700c502803090014005160f00d145a0a507501101d030085078100c11151141c0a02014080b0703034032400f40b20050510740301c102c0400c0c0b506003819850544900d8107036051100d55102071040c1d4401043c07050580340140d84500380303031007580301e10300d10303141000400f404104002c8248600c160341034003e0216521507000d40300e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 324890143 1250 324888893 324888911
    0x4020a0c050c030d091503020c061005030d0801140f0f2d0102030f0d02130305031801030605180403050313150b010e19060e01030608031303030311040305100e0c030d0909 75
    0x9981d0712a40f000c0300005c1001d0700420469115001520005c100746450003504148200c0b0701c0c0781c58101c0644031120052907044050200e420700300041030300000d2601d0b1481c41545000e4042e001c510b03285100c43d0082d1340c000c9078006036448103684410b95010190007920b10700920307201d140310403601c40c00c0070100026410420000703604c00810341d500d0151810b590351410342561140e100950110117904050310030303020b00002080040c0050218050f207819508240390342c20b000103084580d00c3d003015100d0003841c6001080290b209801c0d99216901d810f03c00c0c1d0701c0d203c1040050b860012810000e1070005066115407100300150030800c2203201c02c0e262b440006030074a08210700e01d02d00704091265034800b407000f000080d00c15024400382e42418140018400d403034501d0242944d20800010060011140c010002c259041c49485103181c60401120b05050956407207d40701c0103190050443d03962100b41c8030f0303803103001072040c04043c50f001801c441d01d1800000016080f4400303845602c0741d00b49814444 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 324891393 1250 324890143 324890149
    0x71109070c230309040f09021f090f060c022b06020714030a121109131a0103021305010305040c05030f07060215070c080304050115090209040b0301060e0105011b0204020a0c050c 78
    0x802c0d014411002c0e50030324104c0b40501000703020480700910707000e490707958090241e26001c50f0702c1d81032100307440e240b09c543c907155002070000b120580c0304165030b8400c40b0003000003e52003171841088590441e2a511301c100b0340b103441011a03010b524521750203004000040100001a8014000d0741d10031503280c0ba01e424003003040b81d1a80220507086012075075120100a84401c01da0025540520010403d810040c85d00c0c08a202c1010080c01511a1a0341e0050458000d200b1144a541c4030424a0107501e002d02c5160000114405882038606041c0ca1300042400c01c042c04041d0f4000e8000901115a000360708642c0315511402071085a0142c02000e45549822180c0514a485004c19445000e810421035580003059400140182c42c19540d800944205000700500180101880040940c03610131030b0f0100011184e00703a2455110382c0c5066010410001c401448e98110360003420510040385035042c41100d4412500d400a61043c40000c0e9540040c1d00904040480c40c040c6044500400d401001c2c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 324892643 1250 324891393 324891443
    0xb040c11010b180103171c02040509060a0302060f0d020c01020c03120f040b0c22080606100201020310090b03160305070317070512090301060e16170708060105071109070c 75
    0x880c4054500001840421000111b41e149038030b1510a962030003160f40000e1540f00c000700d4000104c036400003001c02840c07911801f080d40000c02240c2d1041201d11b5a4000f0700b84d407183c00f0900400030340100d0001403803c06035041d80e002d05154402036550300b004d20310342a220b41c0680020000b03166000c0100341c80000d41110188201d0b030000b0240400e458440e902e254541017010095151251801d19a8079414514400030040c22208010310850901d001081801420441020300b1a8410300c00c00c240d500d42d9960181c00c0f101039850004002c06a0b2000c40e0a110a07018001203606041c40000204800010003000302c80c06240d0300381820600c41e0b41d0703190510030764901918a502c60485010508100001040d01d43c00007030001501e00d588103920301c0005022240001c035615440440c3d900d10344c020000c081c400e040545001d01600d4107040182c03140801500c894100079000c1484000c1058601030702da113051005203146604e1510b00401005d401c85040c040710304c4900c035010180740c441c62441d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 324893893 1250 324892643 324892669
    0x10810180302030a121d0609071a07060b0d02030a030e03010f020910032711040c090f030f0303020708031314030a02070b1623060105030a0320010b040c11010b 70
    0x809549044e030040c0c01190034554071000c0c603400c1c503a11500380c100003019074240c08008080901811651800e120381e00d061065a51000307078880d10507141c50290000c404101c59609030300000c00613454071640041000d4180302c4200940620880440d40181500a19100600f25044000344010000f4145131001e900a01580704d810050b409880b190f000d000b50081d41c0d0b20740c12203601036413282d1032100c00e541503100343c0001c1d248215030b0080986a42042d00031000d800c4030505103840300d075103000b0790700c40074058610000e443c0f1602c406144040620940480f0300090304804082d4982c101226101100301120b0f10403038480c0c3c00c41420f44601c503c080165a0744a0180e0007910180785011028102a07210140810f0400407a06007080026814161a140c55845402d120b082102c10f1000320700e06101a00201d200303500481d540c00000b0303805007030b1904490500c82540000d8000c441568050201141c2c0103901c10308009441100031752202d101402185140001d10031400000305110441610399 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 324895143 1250 324893893 324893897
    0xc0606100507110f04060b0403020913020303030f1305070e0106081803040612090506070f120b032a0904030f090603140c07050f030315040e0f250e0108101803 70
    0x300c02c2d9030101e8405425001c0400c0e000d80041984955940001c0454516401200c00250041818015030802c01d52071540803000c010300504101c981d400081d07036070100411015040c80807000040500240c1580090502e62141c21140c00351307110800070070b03011802d000c0c80001815404c001690b0341550100e00300c01d800410f0185241501b0100d089600500040003144025280d6a612001a5041080d40d01c9000c3d42d945541c00306e2440380000b040501080304003c629403c04a962605a4000c24406404014461040074000e07101c2490300034004d002100d280e1220140042100b45600300660a0240701c041d031f1202c030025100d002c10780841700c21a518030320750018100054042a0002c0050000758050700495841c02d5082a10300e2565004403103049005001030b11401e110704281c003a60341a000180301070701c40c1e0542e07599180d6843c040c076030b14115441044110310201b0b03000100303c4c1000c0c09071401c10501560719002059a1024000c00101d00326140500d90b041052140b511100c900c5d50503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 324896393 1250 324895143 324895147
    0x5040c14030c010e27090f0c030d02070b0a0c02060a02070806090106060e0f2101020a09062115080a0b06030c041803110102041203030e060604060513150801020705030c06061005 78
    0x2401400301031041600d0241c00d4a24106803202d01c0e141c405c000520842a5400408502c0c03c0b0310030b000c1c24803081c91000784c040c0d4071a2041c00f10017600420b459003911100300400f511250301100403100b215062902a400210008ac03c510725075000c121041034a00ca031046440584400c2c0d05142202c2c491310507903000071014000c030700141c54882d01220ba40303000207212241c0451400003401280802c0b12060005a50016a060102c0d030004085401800c05052200c81074076940442c5541d07003000e66034030b1a441d81d43c034486c4808090600002018001500c1222142c1c20146480980b1131000d41d4009d1091041c5210440180350034010070f500400c54900d06182c3c06190713139041d0381c00602c40101c2c0c0c059540a0001003000001d40c40c0343c28070306019540201c1d6400d40c012201d8180039002e01460b00460038aa0140000d8035001c0e101c081d5071803810800034184880030312440030048035411241880d4000514501400000000b618a10201c01c080d035044d5220841001010f010b4601c28001041e01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 324897643 1250 324896393 324896417
    0xc0501050c090f0f030a0507080610080d05030105060904090b0702011505060c071503091e03030507080906011502010b10181d13110a0611150903040e0702070905040c14030c01 77
    0x1004140c404eaa11000c0d049880081c0d103a5203890910105812688103607010a003040340d016601e0788103000030320002e009041d04602814000740316110500519003d88400030350728445898640c00501001e41001c02205c00d4108280001d010700700e50014140c00e048402e801282ca1300d0004101ca4050035500010405546426604070060010605000a143d506d1b00d1050100b40112034005890400007600d000000c507034640607040b250701a10b640e04000c00c1d5030400c10002d900081017810340b145c0380030340445400140320407030250240c00d0314036030408182d000c05011103070499045224140f210060103c2103440701a151003600100c0e4031040c204d145400800c500a0316448141281400790310003900c50303e03c2501142000344a50301c402c0005078602440e40c2103041c1400f0703010498044151a5020b0705008220304d54901890082d150218600303408615000d000700180350003031084200500c2030346090f060003405080d00f4031400044410400000100b0310307020600701c070b40313280c140c60750006980d03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 324898893 1250 324897643 324897649
    0xd020114070c03060902010f0206090a150e1209030d08150f13140a0501060c03020624100c06050a0507120b01050409090f051207050601150309020a060c0501050c090f 73
    0x503003140c1001020040008802061000351154003840c0140b2000c00d0030354040c0700050140344d40184a501b1900711070300340035109d440030030035200c1c86400c400c04981c00f00310b0010308802000302008980b05440b07a0b039030400d101e01843d40500901e003001c80544140c0820007100390340104088405550b2a128002ca4080900e44940d100064200103040028407110081c00041154500030b0203641c2e9020b40c070308100d82c101c124091030340544603603e0300c05142003080c1d601a43e1528044c01c0f14082d402c201c6017400000454400c204c0350b903031005220080e4501e901c0c1015144a41e405002c5d216642000f00107102d1a036103000380d6010f8010360743c2d10300d0210b1090840740e000b05003501540e810090100000240c00700c0e00e0081e00505805000040c44130342007072070070318a015580120711040c0d51091010b01d001c64408101d4504445401e541901c2c28041c00908400619400200070b40c0f01803580c0003c1222503100c5d1114282501c10002004903441d034070300c42c0f40c0300e000c4c4445560340003245100c1d5244600f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 324900143 1250 324898893 324898907
    0x7030504151a281401170a0b042c0c0a09020a03090623011d070f03090807031e110d0507020a031719050702091b090907020d1d0d0201 59
    0x300300319a070810340e032441c00009901003e00046501240041d440c642000b4100304205000414041c44020041244600041c100182c01880d40034502c00950001e41810b00755001880300000041041002c3c1c2000ca07002c0619291138281c46817002501d40e0000c81e65800007441d8076aa2200400600490789000c111102075408114040f00305511451001c0005182c1d01440c10210124104020020050030004000e9141640400005080500c5c0c1d51602c440008a13507400c04098580040503150100068000c0c041000c030041000e080014204103050b0f001c6415024102c0c2030803080c95080314000216480340408240e01455080034406100080c010300c000c1016900c003425040c01c017607480c1c6a040d140082549002001d03800010050586185810f07060010415810418140159600072400c400401401c1c5203181c0801901c04440c0300401c410741d14885801440e038502403402c02d4000b912401560848004179414040303c003640008103060558602000d072008041e014180c004690f00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 324901393 1250 324900143 324900161
    0xc0806060a0c0605180c0d0b0a02070c080a201915110304080d0905091005190902160b060a0302060706020a090b0a021501050f130e0c030f01050105090703050415 71
    0x1c411210001070008189010f001d1041ca01781100788144040b00c03040d14244200c200195114680c103070510070004503580c08141c0c1010130100016107682851400c0c94542101d900b00900310300c034038101c903410071004081c9040018a400220403140303244005009200380c00c120201c42800c0c202c401401802840011081e40d16040e1900401e0180340500702401c661064008450a402030071824400682080550b0014582900c10303181c20324003411072442c101d0450061910507121859040448035401d644400134014071541103645507544849403940180b5010101c0e40980c410b80003440606d4034400707030400c49030054030141c0307032017655618540254010710401c001d105c952903003c14048015406420f1442258000702200744c1d500d5940403540c2d01c1640f0040c498000010f10003880e4032521003120710030b9464540460820800030000381407103c5a942c103501841205a000d00342101500205c4c106c400989001c805620303080c00807401c0c0c440c1100c000d0710345058042c0c16007013101540d01001c0360b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 324902643 1250 324901393 324901397
    0x901062c0708060a0f080610080d020a080c030409020d150e0702122a06011a07030c030e21101109031504030e0303030103141e060604020d0b0301021b0d030c0806060a 73
    0x450f988030300d20745c05410340c41d030008089548940100848091b644442201400300b000040c00031001501000355555600c4000408410307012802e83e101c6070041060b600901410102076445805465501000b01017030a8800b0f10040f000030f00203081c00c40c00102c2406010307142d000e040300d0150480d8591380c0354840040903c1d4026151701c500d048003404141da21202050744003400207940342c51012020741690310710301108440d0402000b00000d81090303144c42e5080e4982800012442208005075101d00d0300080b8052101c0740c10210600d441c07021908518038403403030750100203140401100d0041b5008054859825501c102c10480642003001c89096000703100c0c1c42d21503030060003407010a066030420303881101d4201a40a0400c5185130030f00c00e0003903130345021f002c080c04210000d030007696815018142d24040c070380c00154026480c0c400d4114940c10040034000b07650303074110f00301c0800500f02a00b64500490040250303201d2818403a0244c0c81d030440d41c0356a441031640301e500403c001d03507020340320041c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 324903893 1250 324902643 324902659
    0x14010e0c13081c0206371407050c01060603090804120c0b120103120203130311030c0604030f020418121d03010906050114030307050312070e03060901062c070806 71
    0x92440e10802c1428030340f6202d40040c1d940452640b1010b4034000024180c0046a90400035446008507140e03104000601c0e4120300d00102c4143c01243c3c0014160718000c8450320031604200001560406c0c014404600d000d00200186641c9840c00c03022140e24407070080c606202040708100020300500c0700c201d8980103024200d00d01795128515550340d84005030410301014550010010b1040c613070242403c0780424000f81d458421042980c070348030802c3d800020070079002c08090b0032860b2010445900200005442e507503440c3d480381001903864403e240201c0c40f0300e003840e65900c00098200c001d020240d41c00001c00d8100c407809a402c2d42c008d503c504420038a0f4038a07401c40032543d9424000c404545009100001e8103504007501a8880e0701e10a1595009900400850001810010480c0c424101e016040321498840000403034090a082100550611410701032014030081036205504a5102e02241060044a00114400384074030500114036041800e0000f0085409400d1071540404000e000f94 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 324905143 1250 324903893 324903899
    0xa0b030a260408101d0303100f0501030c120c03060503120301180b01170705090604030807030905090c04090b0307031a0a05150906010f030b0306070309020f1c2a0b07030314010e0c13 80
    0x40c0383d0740040b11010018060f4230003c1148200780d0010718040d0500380380502088080b480d010b0403603d80c0c444101c1943c0e40c0c1c2c0c8029000c0b0b6100303600071005050000c060b900101880d8520b813005030030030302074110070035824862600304c01842c0c0b01d040a400c4043c0c507003030892402c04001c0200f40c60700400c03140903c0410841d0418070341d2010010405903100e1130095407550001e09000300701800750380000780903d260805101c030032060107080d00c1c101c8000c15000f1070491600350120b424194036510080c6802c0303048000902040c0203480e01d40c8030f411204010483d03507440301500c3e0801070070100ca003034001d031140c8045005544641d6884040e4500d40c00d000c02d0700004040482c0c5019001c03a2000d00080c0e54000e420b007186400b0140c0308100c4012501d81c1c4401c501c2d10602c9071000710000008185003450880220303545581c00b803001021f50340720116102103544d41031885450380080300841c0001d162071342c0f51054050207515181a5001d020740c0c10500c0d9540381c0c00049541c0800004440005044000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 324906393 1250 324905143 324905201
    0x5040302251e0915030c12060603020d08040314120a050903030c0a06050105011211030a0207021203040608040b1e010501050a0c0602030408040f0e1e0a0b030a26040810 74
    0x81030000ea034a602d003035040c90075143c6811110074104100c12510000e5013040401d030851038140030b40790031036411106442c181c507001c0c005090301e07440290880030308103091081c441c030000a801101e004040c840300c0c00d070040f00366036116201401011074030603060200f0580e10b0711070720280a02800c0617080f40e00d0800f090030500c2c9410180c0e10304030703030b0640c40c0c4005000c156400440d01300b03070181030802400380d44a0302801c002c03070b03010040c00c9400203540458400d06554410101c1005201c0c0784055990752611204028040c0c10100c1f4180c0300c404031100803e480807000425108002c0b6030204082e41341e400c007401150b0650158402ea0208030020f41c808000c54118401107006a00c00c1500c1a83c45182c81403401f4052855884050101a894100206098190000340001c050400c0d0400503586810403800108040c051043e0941301d0700317804d1410062405801142c0f070b00040300548480910f21900e00e2a840341340610344041c0c000a84440144080c0d81081100d9100b4192003100c001100460b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 324907643 1250 324906393 324906419
    0x1609030b04050f010c030c050d02030a02040f03060603051c05071403040b0f090406060309020307030f03260a05060a0602070302012607050403060b0a031e0f020616020f040504030225 80
    0x400c0c0c406803c04502408601d5091007000811030385410240b01055007207074080d020b03005400f250415250001300182c0c0d0885640d0444003d05000f55846042c1364403070a01030003c0c507050008940c2c82c819104080505990361807112000c0c0c2c2c2c5036075050314001155840101c0300341032100d403550a01c001d2001044000c414400341000c00322590720307a034a0b8040c0204000a50320141c0c40b0703500385840e09801c1400b44c2c8022404000b070301c0c0c203d0019154403085103001c441d2100c7d00d041068080003c2d801c007a60044450000d240600c0701c018051000f901e521041190f5820903100b03810141e4006281040154000c820760f001043d004800014510400c03040343c0e4200c0030884400c0c001680004060080203494407580340c240800380d4001016604540d500d1840311058840d0740f40c0d2880c114030300c03c108200e1051510369268003804140d1649011108095495a410030880c41090241c440d5601800c080c0304648c4a244c050f0b000b44106082a240c0b080180d49800680b2940c07480590007182c0d0015580e9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 324908893 1250 324907643 324907651
    0x25030c120f090b03040f0b1810020301060e0f0619170f07090b0c10020f0c160501090902070503040614040f1e0b130303120e0a0b0405010507090305061609030b 70
    0x80e1990001140740005100342240d80286501d04030500500c0f0204050585516405600c410401020344860000e003c10040920f070003455407041244500b0203291030340203141210016150705025130050020090240c02130032017a5007222081c0685911a03071445425401203c25041c0b869a81003101c11425003054200c80c08014024544203200c104c80d0300c50181030007041e42020b01402c1c462010302107515080c00c038503a036085980102c0c40103c0b071a60402103e00d0304410b4400ca89521186000f40b82c04912544074150100c0e03030716000011804c0582c002c8a150319070100c00340d46002d0074100241c0c1d6045140310302c411f1451043c003004c01c04185002850028007013000750004040340b5228895071041c12034000c1d041a180600c014043c04034440306440549a040c100f0301c031000141400c450081551007044207061041d55400030900c64440003450145010300001e0215944220702507800071160b10008056501000c001468541030a106c0d41640f01d07186050586140da0740c5503406c8280c030981e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 324910143 1250 324908893 324908897
    0xb060c010203010e06120a1b1701140c0403150207170f03041e0f0b0603120d06080f0d02030a080919050c0f011d2b0302160b25030c12 59
    0x4018840f5501141810381d005030101d442408000d01b130007015440c2c0b80c00341d40040a0151458034602d40c01c81d80042d020140c4034041c83c1404201e40317070b00c045010307020182132044504c0d101400701343e2840e4400d040b1030035030f03400c00c0084151800e42d031742b0f0400a5100410646e0b54541c001180305840803040000c040d20701c0182c1007151a0301305403c00201d040c00e03203405100d90002c0748241d44001800c5030b031086a0141c01561580c100c0da200c2d0042814000d601200034114040003411007425801940401c3c141c50001d000c44a10b00c3e07a4002c0c180d5120280000c03900583d00c284074541040d80704001c4107900822250a43e800d444052460360006200c48104641c2ca400900007114207050500703c203130054070f0902e440840501002803c0c1403010303240d10524000c104003c2c010030300c0d24036903400e162500d51002c04481c4030580c90800944440d110810030b6480c0707a82980c0010083d43c0344040d6540c4a4007100500c00c01e080e00240714207042c002807411001e2000d000e07200d04c046100030340c1803520b241c150f0b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 324911393 1250 324910143 324910147
    0xb13031b051206191a04020903010b060d06060e0604210314070c09050a1103060103090609050a0b040203070b19030f0e01050a0501050315010e06010e011701032003030a0f050d0b060c0102 82
    0x1844e1100130842c0344044c66089585801c01d003009403c00034520403640c4405840050392038602a0100740034183c00c00d04075801c284000380700b00002501381e001004070303040c03655100c0d4808250760170002c0910a9219804000768403940401c0c44032000c43e507003d8030610038203040034a040505090743c882c0d0800d113005e44410400301340801000900f400340c0703076110101c00d404015080501700c103540e01c0e0001030034003410141d03910040303030802c6040c1d8007030404076801104446032070109190600348410225800c078000e00030001c0004002281c1c6096805142d00c2920300071002c0c00c0d09400300c000f0100f0155180b00d041e00c40003004070512003845001e000740e220380408501e542c1004241468060310520214544078400010000a141d81b060b16030031400074642254081e440c4401222525095513070b440e50392041e00d000008000025006840c5141c40d04040c0c4a145000402c0503101c2c000c0070403802c04202d80c0d8143d000c14521400044c10340c540c11010011b203100043c80440d0341a008404000620781d80 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 324912643 1250 324911393 324911401
    0x80709020a1b0b01031b050303070b0a1404030c110622050f01180b03040c05060309151b0910030e03210109020406090b0a0e100c03090b13031b051206 66
    0xb00011000c1c9285207180d195204aa00f0396a1000003641480301500410040841884000c0724003000002454018102d80d1211410300f40701c046200f00765000003203907241c20901c507a9142050300700c81c81250141c60b03454502c1d24070344624240c03413090301090380e00c450f04100101c00d44c5503103049681c012040c10464690310f800c001c14031960b40e0600c40fa90341400040481b0004c894010b81801003641e01c02c0e40d0701522600c0b1807030f0500c5141d0550300041c0e405880441000004000080c05a074100c4c02d0103101c0c1015100c125600c48038240c4504c00744590b810401400c00302c1c0c1000c4100002c43c0b4854900001d4081e000b036402d03030441d04440c008140301c028540c017040c002d10800c903a6038058001a2400c40c50705181c45000b4003c1086485114186440852601c41c01070189180140c100009040c100340e00e50350510060841c013601c8011000f151141c40701050240034281620b002040c007600e203880013403c41e2544003a0f41007040941c24540b51440700810943c07503516020000e504104014151400c2c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 324913893 1250 324912643 324912647
    0xc0f030906191e090206043210050306040b01090f06020c01021005060108010302190306180519020f120a05070f030507080f03040302151e030a2d15080709020a 70
    0x10200e03a694040c54141203104240d1031528145042c003440321400004c698a90b07101140c407070301852303000c0500d11050b00002c85074200072108031628a29188490340c82080c1c15401c00580c07013408091000000c2c400d01c00035001e23041035440b03181b0403001414841c91103941e800c404102000c40781c1144005800401144500e560104044c18504042101c28045407501400003480d46005100c06481004002d84071000b900300100c0d4078000e07640012041c007400d0a91107009200d14102141150244207841282c080303028000307400303500c481e801170090b000c424803038040106010b1211000410350050b88107000000c1c50812134a4014010341e076a02c080e0b1859400e02701d003801d0665010345680d403c16041807e58620200c11a020b81c1c1c2c0c1107840c005501000034040080307000f0302000a41d540c02400c4101d98006a610246108088400b400d215001040d1a4032010860302407006801c000111000c801028460304130a004004001c1c0c404c1c0701c030b81e131010210307d048000d0380030840f403a40c00034030400016 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 324915143 1250 324913893 324913921
    0x10608010e0d030e0a020d15050703061d04022404080f010c0f08090d120b0910081c0e3601050306071e1103040512011a010e0a0b030c0f030906 63
    0xa0403e0a0422803408444c20490300d403000008001d124101d0390812600300026820b19140007003549004200c4c0b03243c51880680106428001d190550110030b0396030500c4c80f00d100c4070760303c00d13a4040c0c1120b400c0c0601030300d0036045658151200b244203100b400b01150840b800c0116401c1800e04030004588510001c00180042249010950410502e4020400c0c1882e001a0030480480c5074a401c50400000092442c02400d4120807158884040c4040c01048014960220305407808842034880e0b81003e40030240c0002451007990b03022540011294409207415142c4e243c4c2c44203203030030f003c0c5255449200440e1040902c2c0309510f005280100505c510b080401159910030300508002c0348543c4860510714807200200850410080450441a25483c0a00c00d0350010980a00000640c06492901c107000e00b81b680a250400000800c02c5c03201c03903100e5900300309681c0f0003829072180e0305c0c109220030a07954002858000040b6040000e000168610f40003140706001c1070001d40120300b0b241025805117 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 324916393 1250 324915143 324915163
    0x1902010b0901050913030e03030409140612060912090f030613050d020607320d020715110405091005090c03060301050a14070c031202030c090a06090f0620010608010e 73
    0x31303a804000f007090000b140c40860b009981c150501000a00c410400079180d4861500720642d03450900f60f20202e1100c5d2240c0c1680034800860b85000010305260800759541d00407608002070b94410302901c80f05548640050152000c06030145420044880100389010800d603100203080c1e01c44042c0d071091110910000f552105644060003650a1a2030028a03030404040c00d146031b40d03038840212002c420700b5404d9400e15280c0000c00b0f5228446201c116009400c194425506401040f00c1548108100c0c1b0401c0134040405607001c1c2003501306810b000300e80d0030003028000c609604410110311951101e1420380304600804580c2d0f640d107010710900d800d540025016484107070910000e00120040345400c01e902841c18601492446040d09044885a032884e030501000f0784000107220840c00b07090f0003003d0f43e110641d0041d680300d5403424202e07110400341c41605140f40c4103034018046c40388681d00d0800140306422a8080f802604a205030844034940d20130011a0f54035806500e84c1101841215a6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 324917643 1250 324916393 324916399
    0x2031f06080f0c03060310050109050703150b19020f030d060306060e070e090903220501020d020a0c0e1302060a020d0206010b040e01030b07181d0a0504030f030903051902010b090105 80
    0x205052020700954002c001078200703a0039503008800103c0301e071400c118004a5094944013807104d03581d20340d0040c000b0141501c2d1341c0700103420280040c101c10000d210030b1003152441c100b440c0c41e000026811b020080c2c00602e00f03c0843c041d010120300c01600400c003801040100e1000001c0c214550b00d01402214903540c010340c1020354007001c0106c25a0012809149100141c030181102c0c2d413507081c014154803890a03070301c1c80c040c10490183e030001d01969040c8180c2e0006e0b001c4848200c14900113a03170b01c0c2115140104400f000c18420300841c08194002508034207010307441507550030168000f034402d4003e84c80441c0164000700b61070310304503410403095005000030000c2a10b002e0900c0019240d4000500005d000c8006800100311618803078103141865041e400c440d944a02e490b410440d0210310074120840c04e4001c942c0101e640702d9114441c01d8010b0b541502e41050856102030306901901c004042501844028005030f410868440c0c0c01048809240e40002000d880301c1080008007503040c4c04c03040c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 324918893 1250 324917643 324917657
    0x3050105060a0c050c130621080a030c030603210305060f31020f04031103060c030708090a05060a060e010b09030a03050d0204090c1e020c030c010c08040902031f06 72
    0xc0d118074044803880111442c04078007600d40750820b0f5184c40001d00c00342d03800c013200f4100a000440541e100c2000e444010b010381f5404450104580d118030381d0018040c19a510402800440b2070280d88a08070b0240c6504001c150650743c1e44441d08104420b41070341410406c40406003011a91600c10554804003c4940c40d00003128040410301641840100c01c40743e111004000480070000c003061210804a20030644d6100c01304a00c42c2d0554000c0c2c8411184840510700840c0d0038940458070740d20556403c2c0350182140c0c0c509104480010014018000034040d40008002140e81031040c2442820581004078003145011050700c40709405a02800c810b80c02844112700a6401049486000390149400c4d9121200c04111400030b00c035070ba00100d81d071071030081c45501362508074901000c0a2a12481d001600086120036601d4100182d0425495000300014911540c0207814401f10207002d004003500701525160f94404a1b44165100480c2c400c604040703046500310b8000050141000b440c0c452 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 324920143 1250 324918893 324918899
    0x6031204050d0602090915090a05010e0a0507030b030609030a1409030318120712060f051b0f07060207060603052109040207060f1a0405010b0c19020402070203070e0610030501 77
    0x5180610701036944589041904201840381940640308a41e1004041d41030500702000c000340004081c0c113410340544003010000f05a000148202c9048072034188424000d66591110a00185402000c0400b810340d5a81b40c030f10f03a61001c100031f91252001c0c0b001140d550001700303000b821035181520303e826030200c102314004080d1004400c1d90460110a901c10310492031003000211500005505a203c511911038002012302041061110050090404100c1882032a60110031b80c1e8044550f5141f1044840312294200140001040200d0f03c0402090400100c0c0d902c0c0c0050b40d009103410ba501036200c010074024080c1c10300461000b0200c4406042c04041c2050040300715004017171042d44501d41c041208810b00015801000020002070400c01c400420302c003040842414514415000310b1401001042418000040b1f6012000d180001c09442d0300f90820b0038624400044201d07000380d000d01001005072000c100c1000684283d50417800d0510b000c00c14060b0078100000354404140c2490010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 324921393 1250 324920143 324920173
    0x6021b071401120207061409011401060903050a11040225062403110112020a11070609080c0f0a050d080a02190308181203011502010e0c0a0506130e07030209090603 72
    0x10648140320f0399000360300c0e007101d03007440d40060a82c0c81742000b0010401c030070403070110410b600c00380004002500e541c4c11a600d641e0121880f604900001b49203900880074140424103145603011480b900400144c506000d41041e0407a55442c103280c1c142000f0086082d600308030709400391104289400c2c001c8110420000001e07445040c180c84043e02d154461141248240d20405e802559404013110540d560a00042e0003031030410500340460640c003603600007045551085141c0f1049a108900900400341940304001001c0340d0342c422660b00011400c0c0000d000d8807100c0d00940c2e00c0d405a210113844100131607001e4245000b08400f090b21112004080c0006600076000c4d94021026503c2000085000b12059181400c03000003005045008000000d8503000d10307117894441c032090b0340284000b4140c851021b81c2c50400110803940000e8504c810300c00c038203003140500743c01000c1d4248080c11541d540091290590107a03607400003c0e400040d440d206041c440c060b01c1c1c0101c41034006100d8504101c8030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 324922643 1250 324921393 324921407
    0x5040f110906030703230103020117010501081603230702060117030304030c020d05150105030705030a1a06010c080304051b091605031017060f0717010501030c0c06021b071401 77
    0x101440b0300350120110740c99611a0f8800011007a0241c0d43e919a825181062144817000340b000324005a0124841c20344580ca511859040740e6042e1140901500c803007030310241d0720f51000e0040d0209aa070740004049840c4519903a4282228404042007604000c5d50007070034460142c214030382a05807042404a12000003003103030f40c02501464a508020f5151000500d0b613010103102078100c0c407813030900441d40f46032022000d049513021821148000d03520402d16032619801d000240ca02e080000b102d1101414498225900ca60b05240200c4080381136503803d86030350400c1e0b41c2510a5401380d00b003190060003049112100540c201c070880c20350300d0306140c1c00c40129442801c1408000010012550600e24800b000024000d403101511a001076001c00554682c804c813003c554074030342e40000c107107020f029840000350070600d03112601c400d81c244030055000e89801c07110f01c400c2048410108000c140c0c00c0c80a01903121a81001044016444072202d03d002441d800030309808107101c440080982c2c00c240 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 324923893 1250 324922643 324922657
    0x50705041503020906043318050d050705091812090609190b040e0f0a02090306040f1703070f0e010201230c0705070305030318070605030601030504260405040f11 71
    0x1c2c1c090781d152040e801040742d90040381d0001c928807011308003000c2150408043d10114115003400d8003100b42011800301e030f03a401c01d40703030b544d5194058038418480c81c100115000318040c0a10200c600b4070341d607100480c602c2c1e0803c0728076210500c08042081240311051103a181c0381c1c0141d5034524100011000020894441c001410b071064100c040f48410090113802104001c1030908007464503190380d01701c0010400c1c01114035400200c0300718001030750600c1603c26241c03000b0b80034004040039030310b5540342c503068210290180e0714103000103403040c0340ca07159070003c0d0320442495650b914000402c0f00041d2039126101d03007040c15641010703810100c81c01c0d04000c920642c04126040c00c455211101c0c42c407154456200d002c0d00728000c600740403003440310020042d03020b0038121200040c4800d00404050f162000d40c024100003070010408500c20790310039080560082c2c040c040d8602202001d001540002100980c2c0403d10700d40410304009510b05840b4098145500100c01e0082c01d60307142c0383e643d10784a070074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 324925143 1250 324923893 324923897
    0xa0801090b040905010c0f031401140607050102091e01080603060103030206072006070e0114120106140d0c180f0b03060111030d090f020405060301091205220f030302010507050415 79
    0x70305480032556440d0001501d20743c200c0c0080000700c150303400c000d042c5100d610303920380421309080c55000c0e000402ca10f40c40c102e90142080c12442204a0200140d0380e00803003043d641503409000c00c0702d1540c1c407501c07250303241000100c0e200c10580415001410a00c0300803c10b0340300c0c0c1c02020042000c29004170702c26501c0103180c0381038106403040c04010000e40c000c40c8000c0017284240420881815000003240c10580310980f64020003615070480c104183c464003980c520040d280c2c000420450740601c0307440541c007603100c1c202420030140f841410704940354242e40500003142040490502400c0c032410030701800103848030640b1982044220501c500c800f034541c42c10440303004005854030300300744142d0b1a04440014103012500d280e04043da0081c2200005074492840c00380070031010300d07051003111030300d0f580a01a03070003018400c40309680d44e400c988503015902001d40079a42c81c4102c0ca00c01c0501504647c00d0941c1e4260650034001e0844200408540c1842810003040c400c0b00103290194035603c0d070074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 324926393 1250 324925143 324925151
    0x72714040506211207050601050301050121020d03030906020720030309010903020f060c100905160e060d0602160602031014030303040f03050f07030c150b01120e07120f11060a080109 80
    0x3803040603d400c021040300039840c44e021030007008009020501c541210310880c001e0001c1e90701c455424200c7c940b0001c01c014074148c5d4030090310042c2083d184103c640c50080c140000d05402c40d40b81c84003a40d00c504c0303040b6082c2020858104000c00420500001081c003980298140a0803200103030124180b07010191154014180070350700780c1ea8a03002c544003882d5400c262020340c4900403040c009800c2d100720444840c042d0f040202e1207840451030f00001c548521840108a40b509020702450105509041d200b00d6020401645075980d44105189178a11624005a680ca0319040d05002415690004039110701a0f4030b110000380d60000c00d403030f002900243d90003003c007000c1c036060b80c1510500c0040c810340400851781038145504480c006200502801c43d0340051880740c021041120788014400340841e01c1c2c10240b8191110f0744d4404070680302d50104450401b62500e0108001d180d58143c100c3d07030003000041c14406c00407540c0d1b14100d03101050702e1480c01c01c2c01032070300504284014090103090b240e079 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 324927643 1250 324926393 324926449
    0x1020618120309012703090b0712111015170a02030303040305130305070b042603030115121515170f041a0a02031005030304030503070605072714040506 67
    0xb98030280d17010700740b01d200e5001d545401d80c9185114007203250590104810582c0007a01082903402c980045501c020131160204625005862001d0410251a014801c032000144107090b01e00c1841000c05015410352102c5103404000320700302030180900c081e960040d100000043e02c0000580381c03c1a85030804586a0401c4d088a14a060040d48003030514441e00100040022f20b020060040d11082c042501e2501e56410262410300040d12814215903c1007004004d022595910821002c001d890301c05094041001c004041d0758080050388015101e00d18100030300d001c0316092040696032420006040604280c0304803815200400050380d0380020b5000908202c01e900e400d100f542880f03820741c02c0341c0c10416140c5000750406c86010440408203107022031540b400106a9088030750140003540b41c10345581d80d01000c1e0002034604410311007505003007480070000c5c880000c480740003030004043c1c07640390044842146031000d400038040d5103001c007448610b80350700804420410130a0030420010203 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 324928893 1250 324927643 324927661
    0xb04080c06090618220f050a02030f040803060402040e15030f0a0302070b09060412060c09080f0c04090303290a050603060108150a05040c020a0606060503090601090c20010902010206181203 83
    0x485c40d40411210320b02d04028034643c190941c4000e04a50040808016583d00c104440049100540300c01c50709000e15000500041e0401009542c4101c01510140c14680d0792040c0e200c5220040c1d1b441c48040c44010460905810104152008165110001c005e0346003107441c0a0344840031405445c0400200080c1d1700780340c5d15003004a60080409041801203c0c8560900034000e0440340e9924000910b548400150441c00242140c1401222009013017541c1c18041000018010300404405045c3c0760019099440700404503039184403200d15400c50170070150402c2011501e450b812a6104103010b105004469a01094041c0e0141a804403c005040c2c004006580007036030b40e00240d402810645403100700359010a40320304052140105000664035000d0960b001d000440d0496001ea00510040203c215242c1204804030a02d0400d8042100c0c10014201c082c41042d1101400c0c2e074403801002c8c21541d040203120340c00b292400f00f45200711042c050700354407105c14550b1800610300110205010b44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 324930143 1250 324928893 324928909
    0x303070c1509050d08270307060809071203110105160c120c020303030c040306060b03040b0705130e010f06020d02062205070b121009050405070509040f0605010b04080c06090618 78
    0x14010641484038600c0c1c54085c1d55940130045000c084148145014080c95011002291112006004d01403082c03d00d030701280d04100c002c002510f1072040d0745c030003d00203071625404100342d4000d60764005d0903000500d8981c00d542c800381090544030203020450500d103a0042c04526815400001a4400c00710458211101e10090784040c1d4580800014000c045001c1002402241e1043c0303024000d9950b41c0740c00c00c2150100b00c1d0080c3c54042c035140004c550310705c988010122242c10280032004541c41d00c0b58175441e00001d0300320740d4884810f4075040c840c00d070b0104940803221048d44001c0c500d900d003900030480c0886000b0000b0305003c40314030b5103a0800c0b0f0144108070280005c04592601e40e01c1c13a111181221805072111051010000d8000c111481d00e4020a032007150041d0043c85014074003018401d458000602c20703034046140001020000d403c601400c0c0c0280080d94000362500d05210b4207a0921a6a421081c0305140c02c100940c0f40c2d8a8080541702040d000d40c100c880768144510102e070b950 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 324931393 1250 324930143 324930149
    0x19021507061a0102210f090303070b011401032403170d020d02071209060e0d03030902030a0302060f070c0c090203060a0305070e0901150b181c1406060303070c1509 72
    0x15600b0102240e03122204600401d403000000d034210b45503000c00f940845201d01e55001d84842d052810056829090b44030300090611250103000c892910b8925143c900c0f10903020b03000440c9188200030007402070760741401075031000c070588509862402c004406401d00300f00103100080640c2d40b0301c0400801c21002d8010380b46000000341c015551008803060070710081d07000901c00c586403001b007040a620b04e4804e620042c10740d01c081d00c42d40c0070102000100409620941c804608050f1203003803400c0162810302c6140002840b980003080d06003813520a079456820010194001c1002440f907500100d8400d50b002c2c01141d82c10100182d4036140d900100740847c480d0f400183c898403402000042060483d505140304081840003082140700061042104201034401d404025005105249441005c0c512048230080000c04c58510403047e4250708488010105d0255030800e03004060342c08656041c810241c0c851001c4003d540341c00c0c4940c3e1104040034090103901140004c49510b9032405028103000d50203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 324932643 1250 324931393 324931403
    0x60f14010804051032010501022a0a1d01090506060f070519031805040b010f0305280f1109030a030c080c0a0c05120c01091427160219021507 62
    0x444480ca0500c60b0840c0782c401d0404c88040c080e0380d0f82c0c126411581c40d1450598405030f001d8082b24210780250004c4800d54a031081e022855140d100406540d00d00c07005000308030048003100341d422401d541c6c402c401c3d01648010942410101001526a1f0b00000c60f100e050700559100e0701c810241c2030007032408140c616920100c07040007281009041d0401c1c40030b0f403500c04076000c014200340c8030340900054591000c1424080307000742c2c0c0900701280c080d0308203a03407262103030744041d03a40034503246074000a202c3d09041030050f95a0307512803000b07503405000311900c9400020401b45803a4400d80420b0b0b4808540d4409010006c1503400442040703410f2040740c1d41e04040c0c00031543c5803086414145014070039803052502c01c13000b068962040807400308080c44c401e00142c49410410349050103900580000c2c28925034409030710040f000d83c0d614548503203048440364869145052a02558240d00c07032194071010400d646c070803980c404070500742e01c1c5500c00042c2c1c15222414042281102586240604000201 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 324933893 1250 324932643 324932651
    0x1f0b04020301080c130603020a03171306200606061213050607050d140f070302090a0801020c030409060506030903070f02060c06070f0210090302030409090203030403050d080604060f140108040510 86
    0x1000000022042c07004070049420550000005c65943c08907112884000c0d0000ca42d0002040807481c841c55128030303241003005081c41c20310715030045206440c6982064010504114040c0302c020400c2c401035031242c036800000c0071035051101c001007907400381d200500c4103041c00754009417480d034852000140e40e5130702c042100c0d100d09201c0c02c042c8c210341040500041440c82c03d882c0c0c2440d115210701d001e004840000c2060b065490701d1000b100658003000d520364100c40d44140004030032800340300805131503c0c00c00c05940c86c1c5062495540c00e0312180c1c2c1c05948220014024024111804411202c000354454001810a4518800318540f40507907000d50035280a103104000d610754001040f00d24072051703030f42581d45500714190310030100c88035030f180640140d200b44800e002c164040c0e40145182d038002402c403414565255116071a1155607480c0c100021440c4050201b507080500400300904058240c4c0e0f5125400c208608810011070395509040299002c00b00e001d0001c20301950601d0807014200b40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 324935143 1250 324933893 324933899
    0x170304030f0606080c040203190515120303041707170c19060c080604182301110408160614090a05090c09090c030403080c07170a2604051f0b04020301 66
    0x500401d03061080064601030b9405e08865841e151088a10580c03181d06191185044101d6000061030001c08039800c00080ba60180406c0d03561912a00c00d410b40d003001907a4918091500401039040c40c8502c41510005000f0100000c0b500c044d0310b10008241c814580d203840401c89800c0c80d11440002000301120001400000e00c00e05400c90707400f0005984a00d48542c07250030a0004903110300d007031072000c2e00c08000164000b411508800040072000450b2070540c2540c0040310342110390b20804600309407000501041806d00034001031120039801108003440a00c1c104014091015610040c20b82400011b000851540d4204100001e840c2c0984a01c032146004004219944d01010b06640320712001d074006000740c1080b0044038811645035540c0902d540750f07a41c2050540d00b20500031112044203c00300413080c01d51101030005802c441da6000b0281c2d248903000d0706600c1c0620071021070320f410b980801000c0361000a1203402812201d2010302a030400c100308800900f440e400c05a84540000000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 324936393 1250 324935143 324935153
    0xd0c03050d05070c02010e0f0f040b060910030605010f05120f06041b18120f1113050a050106081620070f030b060411250311060f01081209010801170304030f 69
    0x11002e014030031303200e440c4268204010030800518410744964003100c01c9c40354101504154215100f0b03580080c22050a01c01d80100040307028001c510070340c00291340c801d8200a1503900240c140c009032100d08040f440c210b80120070248244008040000484140c4003140d09500caa03400100070707a030b41c2c0345005c480e5521880010058000d455514074040d2001c2c0000c95402c28424481d000c907903114090080e10f40d00c982d24030184099142c12280c0c000529a00c031000902176024440c46000c01c8180090a5130510102914588001c0e040040400a0031540301031960800d0240405c0c0d001c101d0554504e0030752860300b0340b41403542d400c82d49980341140c20000c00c0090400705070b03001e0b4408803800d0003500c0f40108003542c240600c024140403040c0200180e1081200201d843c26058001d03e414815218242115071800c08280c4030000c1d070800a5004204201e0244400c0d00303620f0042e101c0074a020075100000380401c2c018040da00841800d586040c4241104008032130085620528100004490727081c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 324937643 1250 324936393 324936407
    0xf0f090506190201050c090102191707050d030609020f09042705060108010f09020102030d0c12140a0b1e09130c0f0906051801031104140a0e010f0b01020d0c03050d0507 74
    0x12402c00756080c5004103400140000548580350010780c000c100703021107a003d6421107986040c05498001000300c40e500d040b00030500404000380034500600304d13001c203401d0040403284203501003918144103004050413103000c40111458a14103c2d00071440ca11000075242809410104141c10103040d0080001000380208103641211001030080000141080d070303260603241920b00003401604100b12990740b46c176a5034011854400036203802010f08608900010440307030000002800c04482e02c042020341d0641e400f031442c202d903058501401040c00d0446800040200b060410300ca0500d120009200e0021400a9102280c203c4c0411944542d90140d04030443e01a0181c20881030900314003041030308007020f020341100249100340600340c0c80d54880c200c0d0340c11421406a800f44c0c0782c0c60109040d03030f50304c80054054074918200043e065041003050f070231124445000380401c1c0c107000c282030640e0f070081202e120050450a100e107034030901c1c0c901128184210303001c841c801454803080c4408541c4c070440c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 324938893 1250 324937643 324937687
    0x3031306140307080c031807060c1211030306060a0e040c08090d08041a040f0c0807051207080307020f06040305070305031201061107030201140c0a060b041b0f0f090506 74
    0xc0d00304800040641076807940c4000c6416002041d03c80011440c0c2c0c1e101c1c600103551000c996004000203103070030f41032a402d00c00c1e55801180091000801e1409100c0045031900442000742425210180d0001001c0d40f6804000c1416109a10100340295000c4c020b001c2c018809070000c01c00c2013007070340003200a44207013019a4590004c2c8201450396801070701034541140166008519100e000401140a034542c0100900c00c840d080b0683c03102400207001c50026401030041400941003c5003024140111007105001d046141d1344000750802018001000f151030068055401150000d50039010400c580f01d5580024001d2003904000401d1200c0807019003025070070700c0d0640c00a80d0360703681c5c01c85a04420f400b40b504076800200017000192700560f141039204907040c1000717050050380002c42d0301300001c605003030f00d48607151000f08010745020310030210038082421601079000820078000382849000620741003030150078048101c0c010f004010b410000e1000403d17060b0344005054440043c044840 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 324940143 1250 324938893 324938897
    0x4050c0f01031d0f0f160e0601090e1009050a02091c02060c0f0307061109031507031b0210270609020402040302150a0215060121020c2d0d08040605060f03031306 71
    0x10640c1c28045105100e6240c05141031b0405030800e2407800e408000a080641030101e080b000051107020f2102140c03103a81c8011040e00014507007032402c3c068940040406500b03d10400c002c00b00b80e5a5142e030451150000c010707203c0400c8140c404942d00344500480d042d07076481000c0ca1a0820080000140b242e244118003d125811a45d01002558054050099856008a00f200c1c140800310b00006a02c002e25190202e80e41d02124000e554450307011204a0068110381401d8985803083d0242c00115040a10300d22118200c000904c1000251000300401240c0c1f204142c0c419580c807a01603c000d940c0051a81e4081e40000301041016840420f10700094080c0034080000310440c5c82906100b000103844124540c9900704142414018803031071451004da0030b0080c076441881c100140304039004034072050300c2c1594038003d805c141080d8244159441c0d134400596603903420380c000356068005138420000704040c0c445000140356041da51000b00d425100c040303040102081504001001c1b62803517 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 324941393 1250 324940143 324940153
    0xf090204180c0504020f070609170a03060806010e01150f090305060c0307030e0615130e01060605130803032211040903050904060e01050904030503060315010b0310050904050c0f01031d0f 82
    0x1c0c0061000746e004460380c6420b01503046c0640800314285403c021105403060021010301003050317610391a03d400c440c0d000d07400aa84c941040c0601d04003000400d0240c440921030042c0b561400c900c0031158203e500395141040b10003200125198040e0140b2009154480b050b221a46000400c2c80700f550411140000005c1c14504c0301d481072035001c01c19074001c13401842c8a8017000f1507101032010200e040301c070119106540302c0181900003401e1145102a001c6035586903540d100c101100400900ba50700400c0340398108005100b580d425031806c0c0c041c040c0e0f403110701604107000b40c28904407210701005001d40150a00703000c401055881001030050702e030216002c016880c0c403106401c140c2c2c9400d02400380c2180501d004200400d00400185500c840001d04903022900c0040d40701c0d0303090000707a000c1021308030007105200c2c0012072364000e08046e0100740c90300031043c6080d03100c0c41da032240600c2c0c580e402148103010100711648a0f800040880d04840c042902d1801c2409045a448014801440250043c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 324942643 1250 324941393 324941399
    0x80c1b0a120b010b0a18080d0206341e030b01090602190206090303070f110f01030b030d1404090c020708010b06042402070e1f0807080d030f090204180c 67
    0x410108560880c0c1c01903128400c1d6030a1951a07540c0754458038103072007401410703911031702c00c000c00306e00b1a000b520901010f40000000104041d18041029064040c82440b4a4205400c0380e450410300101070a107465030400032200b60303401e50701c4007802c0100a038140b40d680090803181c5e40503000b0b201101c0080e030720800442e40d980c504030b840711041c1c1c012110351568504c83c2e001502d0301c20044e104443d0001c00792480c0024683d03500c80042d0500e03804891192141d00400d85c1450715081002c040c400030f007800d0100c1c0d0031201c00692256001070310002484401c0c111004984d14100a0300e0103001407030f10420640400d001c003e55241c20303e1082c01c84c10f40c00c00d80c422200e400c000007540c0849005066800c0070441c5903a10409c0000000001800c502c180080024001c0614080074014842c40c040300c40744101c881020b2414071803c1c0c01070301c1c0b603511228041012001c005000e4040c07412519001483c40603400c0c240000d443d0340d440c040d50240c20407200300c203007084102c60441c10502c12003204001542d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 324943893 1250 324942643 324942659
    0x108010903200709090809090f070324090c02211b0106050a06050d090209010617070e03100b04061e0602070e040507030f030c02130f0606020309030c010c080c1b0a 72
    0x41d02c692142c0301500036442c01c011510341c68001d0980e0314032400c891403c000e00c580c08944208412a9504811100360050201558161041e41344080040038211000c6034014080e0000c4c2045101d080b10070303541c074030051185030b00c244010030040c0310198622256034082a010460343e00702c580f07601d02071050303428058007030841485410211000070f0043d00c2100d10340340b41a651a00308202038400320f40c0784c52000006940c0d034241e0301e019140c81e0b00c40001c050000603031144048001000801440750200300058544c0c0e0014000081c406034400210304421048085009001282d0050940344c0104003d00d40c3d5100001d0b581c0283d81003582120062079a03240c007240000d806031006000d0b031b0800401480030611031182c002480b40a404c00385003502c083c0e400704486122018040c0c3d581c41d0380b041060b040312854000d9030018800351000f1814411344400103a01e464080345118140b18282c11420200000320040d16500e078422010746500010f00348115400d683d8546146118011160020032020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 324945143 1250 324943893 324943937
    0x6051801081b03071d040c05100207050909010207020301060e060301050f0417071a04060b030f0c090f130b0a0c02120c0319030e0304080a0b0c1204080904020708030108010903 77
    0x154040c0d00030894a25070200b401000c80b0742c0d40300c450700341c0a10040441d0200c90518040d4006602e002d4010503490a0b05104c0e0400295401651244010010b4505030590014458041e40c05c111a58200c40c1c0351441e07400e0080c46981c0c0029095400d0290005010560041c00c0348100d20a03402804540d07a0102195103100702100d0042103038805070f0341044c1e180494005031003400d11a1001c012a00308000c03180b40d910804175000c44943d511072140510078181407203c10b1400a40f54000c04a08100c2c400090101c0801082c001c8405084000500544803000701c3c500820780214044145040c0001c003180545881c08203400544542c030103609100c1036410454003524982000707517081080c80030344040310f1000c9150f2803040544030301500090390070510082000f4000c15004060281291401d0401c0c03802c02841e0041f106024440b502501546000c1c0941c030503404000d45559200820004001f400740d041d0140c550a0084004a120ba80560020070903034080d407108400d980c20444200c40c0340d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 324946393 1250 324945143 324945149
    0xe1005090a080703380103050606030f0f0705010c0f080f03040c08120a03050a1b11060603010c0c2a090212060904020f0418060c030501050a14030303010e0601110f0106051801 77
    0x10f1740e02c0914080001021a104030745008600307017001e425813404a84029003803c01e8000303442c1604100c0a001c1d00d49020403502515a130300401400b5800341c60f000031034a4030a180715007814003803400a1002000645104180c0890f400320301d998840155007018001508111003c036000b522079840458203460009000d00c211341c03007072110b0f41341042c065000c401503c005808100c03510384a82e90700640600505049031100442c1d40e520b01500415543c031480d08201428150103039151580d080c4140e54010480e0000c00c2e00260f81c581c503002200310105050260301c4c2c0c160030500c0410300c003049100e080d070001c1055828515001500d03449400410407008070658000b503108070240750342d4065081540003290310324484004201c0200503521001c060300c2c1405220000265030320011b00c40c03454040b98a6000c0e14040d1a0000650f01d090301103580c0340700c18000c1e0f4060101400020700d5980c45001050010300c0043c040d40d1414a10011480c0a031a0710b0041c02c2c0302303030610303042c599408540c01015812 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 324947643 1250 324946393 324946403
    0x14030403021215071d030f010f0b010e0604050409050f1c0f051204061125020907080103050619020c19020f04020c060415090203070312120203040b160e1005090a080703 74
    0x450f1503100b0305542032101d12454101015081c5e2980c4038640d001d20107110420039040006c02c030340c00c62100d0401198031000c10130303040c400c0101c0306010a86406050324203549040d40d0026403214107080c07080c43d1261500350141d103881403030a0400d0348807d42c4014004190030752112680e50102c01002d60301030081c15600c5090348502000100401e62980224480321100d45d00540b9050420072001d40c802c00202030143c40023010310340c4500310f05290030071660010700b0345003180c150b5066503140c64660402600e001c000101501c4413086031507080e0304541404908804507082d040064084000c40b15110806a1050000303030481c40c40e6040900850b1203030b00c2c801c03010b00019600c659850001c04c00d21282940c1c440d640361130040050301c04012003800355014140f691b9540017a10300003000c000e01c007030280d2203090041c014880010054012140c02480c51441684030720340c6004201c0d159089005215803060740110000c2c0c445401c100245030319101a50348140b09910b4406844d43d40d40240b10042c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 324948893 1250 324947643 324947683
    0xd0515060d1508030406081006020a0302060c0706060509011806050402092809020301080708101505100e0918010f0c05030402190306020a09150c0308060616140304030212 75
    0x801440954002555007140480ca0a50140c8071480f1902d150015045040880c0c0e18000f40305121417406404801810b003071000b480d400e80260360083d150b42c07028010814bc0640414000104651038111402900003d404000c0039a504c090f03d0b0110000c80744a007401600d00030000c00d0a0606008444024001605072008110b00600540207203e680b0140a581019050040b607443c01c0c0e030000b54000d010750001040a030b0700380310301e403400c046090240c1d0039040e1034a205994002001e1181e0411180110340b2103500300f10808040d030301811020225030784505010200000400c16005100001440c00020404401024940300480f10111082c0340072820a2001074014074112002001c0004028954004141d40707984103000d0381c0115000d00c002c81d1224405008081882d0880560b4103030b00d140c0040030811a4070050020080941207138010740d00091500e43c101010140b03445155400401c108140004088813600da070014002248294581114108108800501180f42006c0154200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 324950143 1250 324948893 324948907
    0x6320117060d08040e010f0305070b0403150507210c02010c020606090406020307110a081e130303030c201c080114060a0e120a0209181002031f06050d051506 69
    0x40082c2001030801c40f21920208000708403c1d1920f1200b0f4000c00150752036400040c03d601c0c1003414100560803a4888601c00d00003080803c0c4561001d43d0b0350140341f040051941ca4121045500c4d940300300050b41c02ca40780750200269004a94008050743c072069008001055020208070b031030b4001594965404414000868040b50f004c2d070045800c07080b60f09200ca100a00300c5100750a001203001c0589038100040f480c1029520740c6a4040c00c00c1d51111051450601050000420f41126000113001c0566030802c4c000c5140c012810f40c410080715405440e08a030180e01d6164ad03980400341d01400100c000351940500b580181002e905035009a141001106844020b1100681080f40c0c042c0400841038070301d004a4a0b40340205c20020b03000f0000e01440c030040e00602ca144840070380a884010508502620041030201c3c1030812030034440b1003d03a40fa21a00e114841160240c502d122000d094070030000740d03298000e002407821000c03822040c40950750300512146c103490040c90450f00041c00300b10035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 324951393 1250 324950143 324950149
    0xf0105270a080106062c0d03021507050703020d030b0319050102040518060306280f0c03060503030a02030a0c0f021f0f02031206060307090806010f030c050301060501051b010632011706 81
    0x100080f06c20b80880c03c2c001035450015030070019034a400d8000d81c128441c0e40800203a8500e646620503150f044c04d5203000131513070b0300964403074419103440101039503084000c1955806004401c1c240300c80c0501c0d20840020b504205000798032501c1080d00c60302020040c0b00482200c6c0c110144074010041c0034000f140da80c1c0e12240640704204061b444c0d043d079105030408c60341100c2c1c8680b1070b50340714008000032100c2605002804079039154024504c280e2003400443ea1040d4000b00312440c6a03a40d26040c18072143e51700d41051620304640c402940210039910b1a00d80c100395045030700300005d00752b8031260600c14005040c0c0e101c0c816080e4001003400c03004001101c0382481c00045410103250310703004064580d0740a0860525600f07030030118083c5075042003001401101052400a000300301c000300122481c00300081c100348183d4469055480620400c9090340d1000e522150080c03400c5000035600780c01004100c02c01d01c0b21449000741d1320f61684800384542d441038409c00d0006001d00440c8140381c84000c10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 324952643 1250 324951393 324951437
    0x1050607110607080306011b020a061103040f0303030203040209220f11100206011a12150105070605011d01080c030604020f040b040912110313050f0105270a08010606 73
    0x2910507040009140c8001e44440c8001c100042c000c034400b9480c2d0400c10001041c41072903540000c2d60268201d040005640c40401040480b803d9050201c4440054001e06041d0300442e8005035410b6100700c03002040c160950010b51256108440b0020342e030361450440d1040c44199043c69070483d12031030424000a040e41d1908201c40e0080300314840740901074000400320b00c2099402001600084010458019403109001c00c91003018102828016120520f2040c001c0007003140d403103c40c3e90101040f159014408881003150070030018002d96840c0c0740c14164491401c4a0f070040c4035000000046d40510205800c00848001800340045413202d070200b05020440940055010741c4d580d81c0a0030031b40d143d00c00c103002a03102d071201002041038102c000c3c016400c4084240840d420070481e80c0045e0031076020b02e10540d1821101c50324031006403001260300d4060510860750100819032410114045085405081d03101218000d04440d03c40c03800d40e00342d806501c60170300450401e001c49010905140c81c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 324953893 1250 324952643 324952657
    0xf030b01140c0109030201050c0a3504060204141c020d020402040b04090501030210020d1403092107150c090306050619170607020a0b010b031009111b0a0308010506 72
    0x15050110010401201d0080e52104004020b40e0b99110030b26010103030280140760b44088101c150f242132081040000e0f000b02503a041c600100b0900049881d04002c034417070403d2400070080c4859030940f4103480c080d0000d501c94007036869800c0c001401c0311507034035001c0345601c14410b43c41092a801c1c4407540c20f10280c000801c2080360703c19000c0c000450484a1b85014000820008001040e5945140140f00d0308040b403951100031504401456544550800f000301406155a041250380e56601400036041443c03e240c0f4040d001208038420100c800000c0207005940c0c000c1c10903585442da4000e0080c102c2d07114101c1017000c2081e900c0d0410100b200c1e64881907000c0b1002c0c00d140303400d003c48610960910300a400c041140070040a04c402050410000307198009100d000908044103a5101d42100d40380c144540c2c0784440001000602d06200d80301c0c01c80060112170024000c6c000008581100e0f0380240651240030013100e004007000e00000a289441030b905078a42c06002e0342484140451303035102034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 324955143 1250 324953893 324953897
    0x180b0d0f0605030d03020409060e0108030a08090a082a0607081803091302070c0e09030d0902040b041104150201181140200901020a050f1510060f030b01 67
    0x1031070000d40c940b414005060307011040d550040e5190306103440c010464142c3c0d000384004000c8400140903001d1300004503140c240c01d9090800d1155030704014145003107007006004005660114194200c8010420301d00420a0192002c044443d10b8500a55450f0411100200000c60030408100c45103849000007105800c04404e8030319105035000805c0d440c2030254407407517070113034002500014030201401080141c10501d41100c170320b0402080c400e64034000e01401160803503075013140108542e03c80e4001024144003500c2403005045400448103660002e110710a64818044417240343c0503c103204281c0c109403511a400346400c1d0a890305161003000700107140d000124080c40c40401124811030345405014018162940840502c030101c010441d140010100350a05110b812081c0303a0301d034124072445c0b080c90f184e92180f101c400100d203003600c050000381090044100c40d554810300860f880c02c524000002c150f5558440d85030444c04500c1a103d02c400140501c0c0009240e18829084481180814 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 324956393 1250 324955143 324955151
    0x1c0c050706090803070e030a05030403081c0c02150921160b01120507090e1509071a12100e01150203040e0a1b090b04121707030f180b0d0f 61
    0x169260700c102c0711164010344100f01d000c4100300205e940072203c000214070590240a6041607603583c242d50740501d000c02000c6040c04212001d00150305004040201c01c0980240002c4a02000c080d490b444804034030030280036010001010340c1800210082101280e01030700030303040c1901004695030380208200701589590403111601141d82c2c20b0020f070203002c801100c80400a03442c50312514040340d9a2000c100e0504000707150758040c2c80400d0b02410b981200ca85c0908a507a0314481904008150b04907004100560f0706000c030b0581004042c18204140801d07025071601c3d103815a0080541600c070382c000c200740c0300d401480074030314000d07141d00301104d50300407a410261100c03854139041c03604440051406548070a01d034802000303500007040c01c00d41403c00041c1207003031040440a92060307008807484505035118042c1000f0703c15460000c0c01043c0b5140586540040c80d004001500000d030080000b108580c085211340d503ea420300088480345c0c4a42880e06500c00403c001400d010300d09542e8050b52 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 324957643 1250 324956393 324956407
    0x30b150301081b090f011203020109020307080c0406090203220618032606100c0302030d05010608011502070e1504150608100e15060c122703031c0c05 66
    0x281406180640301d40d02c05403141c200440381c03e2a0901c0d1010040c0c0c881c400c0c420038012010884401141515109420010b6a00440c20107071301500c81098000c0d0948144800000c03842c101142c1c1c0140c480c000c84003808600d0380d81e1a403009901058480d4000b00e2022070401c1e4414500070802d5000c0791240c00c0208500058091454a010f41154198085000b032070407004040c10100c000d0a00c103e540c00c6600107400c006000c070708022401c80701902840500c082d10002d01d4001c005441440c000000103101960716954001c003450750a224041150103e843c034a02000e0001c100d480645510009060380c6a503059103403c802182c01200a03042a83e4131900c442825a034003c000142000707071211482030078011421658031045500046403142e9000602a030780c0d00200f901c000c0b40b003044546039241d016070500390b0700340003030700b0607040d5581c1c1c00007408046880300081046040403110b0110820120700c800b4544c4900c40c550003000b00040c8000340340c640311150360288080300003529002d820142 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 324958893 1250 324957643 324957679
    0x402010c0c060203071101081302060a0309082205030303010b030601200102030f040b070201060612020a030204170d08010b0a0c140f160f0609050102030417013e0408030703030b 78
    0x1941e006540103030400240b081c21b01981102e0070050803000c1c60000d0080c80d0090007810319400e40030340207215020000c1d0841d159031181e0031070800c01d508484200da039140408610100e1030114894000d0b412940000002c3c80c1c9004019607040300c2d10180c5d55031450382e03007400458465480c2c0f01d001c8504400c540009206c03240c00d2024522030100d101c403200007402c103420100904d80c0d00130504411a03042c60700030b018166118103620142c1c00343d1a030250315000c1080c019000380c091b68010a0700000507030f112841780c100c001380414000c01540c803008100e90303c8580c920700b14410b0036050350110f40200b586e440012407000440c0400200c038029074822450f0b0041e89030134000f441c00401954078188a0500859101c9910340c030091000d401c1800580e80343c0340000c1c3d228025441030010802c43d1401e0b0b07181030300c0700703401007201c0e40740b20b4003042070020001c0d991100a03011496914507403d0b400710040515054902240c2c15034880e40021820592965003c5001d4603c003504035800200741282c0007201d034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 324960143 1250 324958893 324958913
    0x3080a090c09090501050f06100f051312050304150305060d15200706050a090b270a080a080a0525030216050102190512070806061204080a03060f050906090402010c 72
    0x44c0c4100004903640c140000c4021501e8009401988156050300c540e190171900000310354072078455410401d464001e00021114000c6280d480325119a003003001d4442049800b000600988103201c200c022200f02c94a070171811110120361158109030000005008284ac110300c1003a06080d0b0380000c15a01d20702a2886902d4103582d8541c040e400020541a0400619000d00c030f52204001c042001200450389a0b0000f0b81006030170000b040f081d5454583e000003243c500c411002c005001201c552101612704418258098400f40300081e0a04000c20418481402000d0017012890321103201c1d1100000c000b412400d0181c0c014050642c00c2010301d000c10700d902591030119020310001a01c50803200040342d0388240b9030b189141048400c000368112810074032150f90700700751240b906644d6503552a0205026100c0c07114011040c00362981040708200c0850010b000c5180c1c01d50b414801130b81e8130807012510321440d016899101d89400d00090681c28031103213450748079005142000101085440b91041c078 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 324961393 1250 324960143 324960161
    0x50f0d05030c011e0e0c0306060427030c020405180d0302030a270b01050102061e04020a0519061b0c0b0901090b0a030903020c0616111201180203071203080a090c09 72
    0x548952010408035545071080360824540070006e0328960a0b04800603403034001c01007a00e849250380e02c0400740c44624010500d404000e80b500080385610361070402404001e2000c074200d100318100741c002006901700d41d50140c02504c00304000c021400c0240000c2d03010b500020030003482142c1d61540f1010300c4c6201c0b01c40c1520385003310407107003004025040c070542c000d005801050540d80710700c044c08510324600410500c401d04401e40440d03503854500c006480c0d1210703a8080e59000180d02d0702d6a0b006120090031001711081901c0380444040f654201044400c0e5150005c1d000c6400f81d8020000c103500d2400400703079640c05250485c03105e61144408032580d0001c21510700060342d240c410710200341d01000002285ea000f00c0341c103403c2031003001c140304007080e84d007000600c2d01a018111011503280c0410903040c54038940003e0144150110b010006111030000c183c0c802d10030f22000180308081c40c0c0c4540c83c1990103503195409075881a5140700900b141c114125880c012114001070000d181c4c1c4100500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 324962643 1250 324961393 324961421
    0x131205102a080901060902040f1e0308040603020c010c0905030c04200301270203040c120c0302150904050a0207021f14030109060e060102010606050d0902040e16061404050f0d05030c01 81
    0x70a09000c101c203401c451044c1c016006c101e02c1000244019164203034008115a0503260284180b15456030b06044184c1540c03000344101c1c8046408110150990050a0b00e586004020094050207881c201c800304030350300c62250140c220100852481c1025002607940381d00c0410305a2a13002022866842c42c1d1007640202c048089401003c9800c0c0414408002c0f0800110710030740c210b0520f511100e210744042d102e240340b00d40407118004100215001d41c0c40080d500104920f24030303010081000345503400998031a105c0c070b00d8200019140000ba20a8680b12a00a89803100202001d0084541410f4902e101018050b1145d9403030b4400d010750000f03501918503c9000720381c90f80741c2134454940c6c80001d006141564100503051006d84d0b0b001094810440380220081941105030001c10000c1955540055140c015107c1d511241e0030040c0803c0d0440d21166103804078588041008070050069000b07641d40550717610389059441c90141c03011901140100140c80c6480821081a0308564160b65280a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 324963893 1250 324962643 324962657
    0x2040603471e030f070e1303030b030f010605040e01060326070f03021005131205031005060f07030e150307080604020d02160b06121903050708030c131205102a 70
    0x1100c2c3c2000c1c005544138a20843c001e280c5107003891b2001c004070400408501803404440303900e4051510a4010ba00902c202805554040b92210685400303810344d1301039140100d08100030f0380320524051284608980d0001d02030413120308819404100594000280458004140003000200c1c000c04403401d13000c4d102e034000f0320307840003802600029140001d2a4040320340036180c442001c100703a10303103d9455400ba407131300954030340e54403400b1030f0303060031903001103802031804a80480003c04007801480e040740030392240c6100540e0341007001100701d0f54042030282c0300784c103001040c42e2502454540d50071501c02800541003c046500c03200807604540e840d0242e0701207440d52001441074058549400480541c0c580010301c0c4440d00c000d40c0e400079010098509030080704884107051046095440480c1c4c0000e80640e64100800b0103c06a0412008601103c242900002d50480c0c4032107100e826030b0340000940803240110f030402000b0b00300011315112440c03000c0f809119040340507040c16420310f8282c80fa10303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 324965143 1250 324963893 324963949
    0x60e031b060604021204020906010201110c03031e04020d0f020102120712090e10061404050303030106080907061713020109090204060f17070c0f0501020d0f0204060347 74
    0x14a0720038003505542c00749204000c2c0820190b60141519407080c1c0581d140c0495440e0000100c0c01402c00d9500141c1a000208020641800c040015401898009003200384034440b2a40c8800d40d01003501e00170361001020140c500010f6170450a9241d007401401074881501d0220110621039024400c01c40d200c0c40e42000c1a0301c0c0300c0d08480704e01c01401702c02030320310300301d00c2c000b800919102c060340106002e000b542c2503800c541c04030301000c48000e00b0001d800c4d01c0d140c2d607580c000a4500c000943c5c070101c03a0300404902080a6229003402e1300d041e0507041c1051a6510364008104608110046c20703030402a0642d07021801c160326000800042866544900b41403911010041910029007507980400141106000e515540615000d035150b030000704141c00100c080c984140284135100d100070100c1e00380500c2d060040308582c064002c65070540c40911494003080390560340540b40b641c2e8009004041d0703450601c1c03103200014850305109071040c0120340c45600c4000401c0041041348407a100c41a0a40070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 324966393 1250 324965143 324965197
    0x9010e12040509100612020c0709020c0304060206070f080103080c160612060f0506091012141815012303010608071e1404050c121005010f020f07090207060e03 70
    0x83c1c0d4420340010f10a8900e80c10494002c050b07590710340c4140d42d51a004030f00080f640d0001e000180042c44500c1d011580c0700702482030144c9a400921401c0301500a410001300118018a00c4050311260340c0ea44040903801d542c4e41400d5504400080c01043c07007410034a2a1038100303040ba61003e0011515030310741602c203c0c200c0303405540305600000301d041c1109204110701d44400050b24034a040840e03588903110617114046079112102400004c006003040700c0c8002e413940340400140100490313400d0003d40c400100080359941c0d081d5801d041141c580c140108610300e000c1d4103c001000c10900c500215203d4400040e007912130b10f41010720f01d50032590080001c02a1548242008049224004c0145151403c050305059001403110f004e03e89034400104c0d402e0400045641109007801138200c1420014840300c07000c051406598040354401e405100520b0001800c54195038a40000b803540c58284610716008c0d42041c0d508413040354940c40144030f1910144064049030456010008001c900783c000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 324967643 1250 324966393 324966409
    0x9180f18020109050402031e01140a051005030718080f030306100c050d050f04150c1704050a1a120c2d2d0d1517070e09010e120405 58
    0x214241036015181150050360040c2030002111002ca40050700c1c1d6659a00083c02000315075050681102070307100100b022444a842000e80302000e465440c1400e44400c2846600c1020b0410304020503010700019000d28403c2407860650151017104001c41c90f51740c1c81144c030b00030442005400540000c410403145082ca801c0045401c0004e01e800100c0c46041c3d00c1c2d5544560550720110200100015400301046c18202283c000300b40780c941115104490b80d00c02410070001400071540000200c040c3e803119034180c000d840035200010020b4880b0791405901c0e201c150048100400074039414090003484482d8039061a10a002082400b683c407400c0c00c01170716400d1040c49070503219800301c09040c02105442d10580c1e262000341d0002d615410a008460311955003000200d80314880c0008501d006c05a1942110304118142c81010900710380b00ca00780c0704901c10300001c101140d88031440030411034400560894004001e071000007960101130311141e00b01301c0300c44500004510001410000c034108114 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 324968893 1250 324967643 324967661
    0xf02031302011d0d140304030203100e060a09050d030c0c060f0c0f030917090d0203060a0c090512031621080103140c011d18010e0609070503160f09180f 67
    0xd15200b03102d0101d00040000144c608041c0c01d80d0703003a04008941c2c40e000c1044401031a0000c0845510004552440000c3c103081070001d0854020b02001c202e40003414001c80c80159800380241c03858980541c0118001c02d60101c0c04401c000500c1d00d404085801842041d075031080b201e10208e5545400c0e00301030920503c1d8001e20003010301c5d00c004180410080d40360005a20390208101d40e07240241030002e2015810b24102075410301420b4140b103940403c41d482804881d5003030f19088440c1e940c030303000c210a007220140100140d8108000e0909104800c40d40305842a11504101c0c8000343d03042000545103850300c4141000c02c050300014424042100340404c51760031000000c0640484402c002001c401040c7ca101140a0601c02c91881684d25180600b4844a502e4424413242d82d603080380c9a461401540c550b0301404242c000300701228030038001c90788986001160071540070081e420032124070700500800700c10030109200c0800e4100c0c40d81d601050702000920049480a46044078004a075241c503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 324970143 1250 324968893 324968927
    0x1413060e01110c0108040201260105040609060302010c1101171602150403170405010e151005060906030c07060f02070303022101050a060818010504030f030f020403080912010f0203130201 82
    0x2440003402080020f0200242c0200f8600121030340ca0350310051340c1910942c14014100e42c1e01604014840d41c900e800c03117040701e00403201440625501c841c454100c9241d0b00020780003451000422002c00e00400c0d0360034140c40c0625028140c01e080016402001c1c000307646424081c1807400c803581c0000d90410030541054a8010540303014182070fa4094800c000c00414907009000315030004003440400c0d400003d00b00118025500c2c8040100c03588403a441e4203d42801905074001030210340e5041003800e80b4000680540810f103903845d0404411041d80101108587e00350304c40507850b8286446001410485100303860150b00d8400710101819040a00b4141c281900303585401044aa0b558003c14800c480084c00d00801c184c8440d017044000c00740d00c500d46902c0e9800c100900040541c840000c0700021140d6034200300c0002d01002000c05d0303200e140b001074003504003440501703068501011003040e041801000050081020700d2840140d07001201c298503c140746030201d400b9940c0207805115040c81d01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 324971393 1250 324970143 324970157
    0x706180e06370614120a0b0301230108160509040f05070f090506040c0525050a0309051005030108100c0c0c060504090c030204080d03050405120c0105040c05010c021806011413060e01 80
    0x644e05580d0700681e0910381d200040d04010404d030500b02e500c00341e80090060024013008602c44011040039000080580c410b000000c00064040700c042139061039074200c0b0101400841c42c0004105ca00d00c00071b841075520080901c950000980104240380c028001c1c4140b140b0b015180140f4001192070052009001c0e90030701e0030252145500804648085012104200c1000840007615100c88048030008110384602d889440525410410b580704413241119015003a00c5850000c46603800300b845810344039404080712086103110390300700c6a1591201d241128500445449000103e00c0359072104001c0703000000d0512614680d4040d42c80306104038107041d4a003138607101c4116651101c0707a81444c00c1550312001f0604001060201402030700c0e54241c002d031504140e80e100e600800f815502281d800c035101c03200043c5540155a1034010640040ca0420180e0324140000c502400062003581000219442d140360241c1d50800350a001861411102110341004d0003d40000c5600701680e06100c3d40d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 324972643 1250 324971393 324971417
    0x2a09080307030914010c030c021012050f0105281203050c01020a08190e06011e05060309060601080f0f040308040309080307231216020102010b1806030706180e063706 73
    0x120314071010981c9c0c1900c40440484207c64115011000c03001c0d0b4640450501c814002801100100181a101c04845910a0401081898069810300010302040c0c10041341e08108403542120b403420124002e041840c5400c3c50b9454507400c99001c3d20050010811240030302107080b1060040360340402c007030301c410444a15074140c02952003405124001000019040101100e0106c407080c0c0e0061002030006516420810041525600120740c800d0015080c500018111030780c0a4485d0b020b43c0801d43d2008140e200d54a0803207088500500550a10030304800018864004000800c0140c0c000c1c5010030b121400070902c1b10010442c18065400740d030107510600036100ca11001c8800c40d151800e00200346407843e01c0141d0242136401c2595a002d0001c1111540c500c038201c112910951044095914242d144c15060703d40c5100f81724800c111041049003400060404042d69420110061540c80003032075452030101c291a21350301c040400881c003c40341101d604001454006031013642001c01080792 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 324973893 1250 324972643 324972647
    0xb0106030e0709020c10180b160905120109020909071e1505071103030d06180c02060c25050a0b10061704030302070c0314102a09080307030914010c03 66
    0x940b43c0103845865074002408038000008005141e1550311404007030003c0240a0f035102c2c2145814502921140301d00000500c44281c040362803500184551500c1410074101000d201c484200004080a550f507030340d482d440580e5619000e02e201c0da03120801000b0150600901c0c104185100d2003406194180143c10b1013940f01d455000103200c081c6291442e1603020714144100521211001d158040c0400a142d6002c036080b90042d00682c1c4801411500a20844030540102c1d84c606003450010b80003a00450003a400f010002c00b003400040d50081604000e0700d001303040c070052901c402c8501e607004503441070401000850701c507030101d044055103c0081c5403810190603001080100c030b070076801d10700028040600990644038000d030000f1211103203644900d00000d070350b00c902102490350301c111030b05480d41c51494003c0d5005032203610304900d250070b00090032071418111003c081d400c1c403070900000301d074440302040503040c100e019503281c009241c035042010000039040c40419042090710b6541c0303004a9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 324975143 1250 324973893 324973903
    0x601050f04090b011e03060606030b01030b191a0d050901020702270703022802010914010b06090409060b060a0504060801062c130903030506090609040f11040906090501090b0106030e 80
    0x1a000343c0c1c1500844464517088044071386140c00c018066480c020003c160f20750715511549604000b03880400081005408108603011a413541000185400005001e000002c0c0c1e05240c41c3c1d14005100c5081c071480c11202002d90301e044429521f1030398003107503520561400d89624550040c0012188001c5405004130b01c8428200070918410306030001a400d02c1541c1e100c00c40b500c0340000190b107254500074180002e01030480010f003511510340c4250310390940001032103900c007803110017020640b030103c1030018000640250138050761403559820404d0b0780c54458100400c90720b2a0380d5181562203040150141c10b00310103801c20010002d00c4131210110200c000d07440160130348609400c4030b003800c62000081c035101c880080320324220f080c003544104240d090303080940034007422035800ea40c5035582403e11110034070440d0081c111411003042a000704107507011041c81d0100252000c80d500101d51210802d644902c00201c0700343e9543e004290a10042810355405043d5601e000d00400b803c2e04101e542e03607 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 324976393 1250 324975143 324975149
    0x182012010603050705070b0405030d05010b042105071a040314150a181b06030509030a0f3b0102010c03111e04090e160b0a0518040e0f0601050f04090b01 67
    0xb040d9940003113910366002e05d050302c6444c0d6201c2c142c1601890649801502da402101422404906107000811303140e5411041d0780c1a80c0c042d52107000c0030501760005508114080b41300303482a0180040100781001000028008245c4841030310303a13980e2840c07402450b040d401406034000ca4000d648a103410b1018800680e80000d00f00d00085071011604498440d00402030f00d000b011704001408401c2c100701900e40700000c8440684040200d40d40d0240e04648038400c41802c03000042c14606a20a041d005120700e100c44042541da587c200041200468101910f2000c040c101e034209402e80d81c4190b9090280394101c940f10300d1b007032100c4604042c0208850103184080006502122100c02c203560b0048160741c000d04081a043c0503851292603580e403a0008134580c0408014056070208061403000202c620030400ca035540c0c2e2909070390001c000040e188803049075600130380b20210501480d10070417018550140c842d0240541d549007800b00a002841000c1507409941801445008558036030115411 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 324977643 1250 324976393 324976397
    0x1060627150818030915031e040b091902090703050c1b0106050f1914010201091a100501140307120e0f0706020601121716080d0b030d0c15090305041820120106 70
    0x7e0340c458140c1200c0404010409813003204819041000f40b04ca01c0242c0c0f4000d0440900703580012010900e0302040b00003000000e5007111050001c1200c86110f6441641d000000182081c02c0c9141c21700c01141146141c41c68143c941c1d1541e8003400300d8a0004081480e2150440b41040c4054030403407103a608062a100300014681a415840507a9000390000c1d038400c0e0b030000141d6110300c54803030070080c15003041e40c00c1081d40c0c3c4101404a001e50043d42c2007041040c4044c089400c582e18114110b6503a042c0307416040c161929440462902e031010000c1c038198202841c05085024113240c0003c1c6002c2c3d05030f0001c50b142003c1c0c0c001d071011680400340c88191003200d00c0c0380382d030f6055919100c440382d0f240668010541c200009200305000c10a0b88a101c3c1000204c09036841c8011202c000c462000d8074160203400d0800304040300c103028990383c1c40b040c251340c841d041040c2059600c00d1102c0a81802c0b5100441054455110380407213400300f00314140c441a096441800c00502240641c6c48010500412003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 324978893 1250 324977643 324977647
    0x30b09041101260a0c02010b010c0f03031503140d0302090d0303091b170105010e041518020402030c0a03110a170a0207060204121401060627150818030915 68
    0x24450b480b0700703a101a610090039110303002055100000c841c814080f41c4800c50340d4075017104d0780030941c070602482d11484016902c45c16036407680c0d101d000340046501d4085084c140d8901d02c29400140702560800114024001c803401c66200700c00c3c260030040b21010200c100340c4100b0400c900c5944a030601d500b4150140f5001a00305101d2914207981d000c0800e1860884e0b0002d000050366401000141c41b1a84e840c0000f8020350f60f136000b00640d0040c0c140c80041c91908041030801840d260382d401800c078139421400720b8800302e040340c0214049074020740340b040c807000d8000342c072590154050141c04100c0e584c01c400b0a00d00300c0c44038030040200600c03036082c042d98808900800c0c03108010750181c90815400000440d91039a440e00c3c03003100c180d0000411540d581a103000310b155420188140011144580c98001d0088182000941d01c81c9501c030350246c05841102d408200c0015050415040390803d884a041905020406813030b010001e04280c1910740c000c00407029252211252450b03602c03501c8102179 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 324980143 1250 324978893 324978923
    0xb030c0a15110a060209011103090121180506010512030301030f08030c131e1d0105151201090c1403010b04050f130203071706030f120f09030a030507060606030b0904 73
    0x152403122052030801948a000c0f00101401300d59801414011403d880b4000410030254403039460b4042c3c0b01a945c0414860300c41c81c28400250000417440e85e030003141c005442e25217001c03c1044a600c600c02078038181d00650044c0700c40d003000c080300c1a0b8820700d0001141950314581e6401041031840100a182a901201051600c106030090794460f49000801c50300241d11b5003449070401d050b414850b841492070500010b03080d50460b8a20a500706441c0341506184c0c00c160900c4281d056a15540403424000c2044800032029521480e002c1c141265012421485480c0001c180001802d10b00060500401c0100003140c00c0008076003c5482c00d8a0001140c40c100340021142e4040c0740485040c0342c000001c01010a40c0074200c05900040300501c01e40540740c007424166100d40c09402070710117900600c280104030400d00d01420841a0f03e80a007498000c0180101e0308142401d8070490100302e0124410b0100601406220094041450108071013444d5000188009801501c0070b0300840f5030031216 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 324981393 1250 324980143 324980147
    0x90f050f070e060f01170a1b030605030a1b0504020c0102040311041103041b090e030306011d010504052806051206040b0f06090a030b270613032607030c030b030c0a15 73
    0x81b1200d194070850500c407441c011900c440a8034544c0c00120341030070f050032007c240707600a00c103a0003620703001b40c0101541d4102c0d99800c0c0401031107800c002000c080d0301074005455a1240028111244080005616203145240c09801c40502a100c5072180342040b280d001190303803110540f540725401031400d40321456480b07404000d842c0150040d00100f41030149501c0c0d0340c0000401140540e03000c0c1c1e0ad190300010110f80388101000c1141146000407400c0008010600e05004404044041000705440f403510903800000c1c4071072941d0180c2e01140d00802c002c44c611021b8408198001310981d414001c480001c4c000608008001511034468003021520b00c3c0c281d11280c42120186607c1251404d19040a070100a52001400120b240e15518210408034096010583d580078180e1100c40c960055110303074081c0c1e00c100c01918189000061001c45004002c08010340c14050007481c0c0300020200c41c9910020242c40d40540194002d910100c034243c001d49801c1d20040c115401c40820382c1514100c0102 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 324982643 1250 324981393 324981407
    0xf070302040b2a071a0a181526061003091a090c010c08090108041505040317060f010917010b090117160b0328090f050f070e060f01 58
    0x48040c0000d00440c0340a40d000040070f04a40007954250b1010509988881c182e90381c5501703001c2e02d900d1501e100b030060a41d030700190180c056000b00f420100311105030b0482c0d4843e030f0b0710715500682c0c110180d404584d11030b540200719048440403004400b02d005c00c407085c04140c2d0340c80c003920650042441d01c102042080c800d9001c28107081e4005401d441100900781480d000c40303425102d00c0a5802580c00202c8190300481c9000605ca034002d00c0a828a00381400644003080700070419646541c180e406240e41c40f02d6480381da40b00d503100e500c5100492054040000c2c1514006010034021b45500090a4840ea0002e01c0b02e42219040a1100315404c0c401c80210b0240111405a0b0b400141c86d20000c184541000c3d0010140014141240c50141000c2600d00c140c01140c8076036081244100041643d00402200e050030300444c0e80c2c41100120502c4540c807080390280c000c1520480401900502000b8040c012408108001340081c08100d040c0b1030217413001d85001c0d0009101e0614443c8481e1664010780c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 324983893 1250 324982643 324982649
    0x9181a04020a03290c130e060607020a08031909180f02090a080604110402070b0f040f200a0b040810020c0708070602030a03060518010608090f010c09030212030301030b0f07030204 79
    0x8401c00c241c03800c8003007544c0306402062080481042e10001d07103121442029250f400c2c40a03d20030701030a1908032640381070301c00500420b07080303481084601c000d6140e002e00781d001403402400440e80c40d1403110a00c000c2801c80c6054000b00803100f14100f000001c0b045d010310172555902c20025030740c044010761000074032482c40f4860700080241c1c00050a804081050783c41680100309061207103a507042044101d1140c080001c01c030110400225002018424506031312a03c0f52200c811050800d840d0100c2c0d400302043d5004039590450904605414402240c40040c0700264031a1700f414100050192210940550782c0d03a059400310300c0d6001400104000401000c42d18180e5818544030b0000a469071701011050020078209200000c01c0d007030145803180a03800445041d160b07030342803402c211880100a0402c20740752003048080441c14070284140501c240b403d45035420003c0c994410702c440ea003584402c43c03009420520040000c03603419500240d00c0080041c00810310355822b0001c1d00207001c2c2c0c0d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 324985143 1250 324983893 324983903
    0x3061509041b0c0b1b03012106061202030c040c09050f03011503080406091202030604030302030a020c060c19090b1b0304090603081e0703020c060d0b06030a0609181a04020a03 77
    0x808000c040c1d50f04003820748102c9000f280300d40701665035070822403c000c0c24600518010041080100300464904001c0200486c980120300010f944a80f255001e031640e075008440c0d80c20043c003000341149810084c0301c07074403401a10b0a00c4030020003c40070349803694610603940601c000024081d0340b9942940818045c1c0800600b005281c0d8690605105c180c00c680141004515240004601c01e100002c10104603a802002081d0070307641c1d0350b41180030350070180181c2c440039003e0110f00244c2e642440414403800c0c809104030744883c00e12025448504180e0500f005026211704207002da038141c0d20807511602250000407021007042c4055078514416a444a02d40624000d1301008205190005054040301e00300940f00d6101c4d01024a00188141d100040c00360307001d85462400c608011016080c0325900c6900081d030342007840e0208540740d0044882801c0b207903a400c000c0c002c00c02644212002c40050740c11300072915045175551800f0b100c020042e10281d40d8560001411940e994040501441c1d03c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 324986393 1250 324985143 324985181
    0x71704030305061206192d020702041404030e010f03020a090b030402061c060302030d030506060a08060303040f0611100b010207090e013b06060117040f23010608030306150904 77
    0xc60b2a40c1c2c1d03001c14219001c10654180483c1c504910000e00308400d0410b1007140d5031041c7c420103600310000794445d000c00ca800c9038903a484400080c000f00040b900c100e0080e100da400c60503420300010501940d445d4404141841400140d0000c0e9103c2441c03420750319444100380c1d17203888038000035400740200718514148024034140215000b0003034100600306c038402e03011101c07401040d05007641540d0088036059000001841840350380c6101d01d942c20303003110000d403d0b43d00d09034882002080710304060300600d002c00c0e803100480381400020020b034490201c1a13039040050f4a92540000c2d1180300034441c003020a502c0f03da880031000d0081d4001d03210302605041411039001c0740001c6a0342811508035071501d51684d03050000002d0404105180300c2d002c160346015440700b03001186251018058001e5941c078004101d140c00040c070010620f90005408100200c007000085c48450954403075401440982e00140117110480d195040c1400082011203007232a190010000441c1c000c01040001003011036030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 324987643 1250 324986393 324986401
    0x11030f0102070c061115130f05010509010b0a1a04030803070912032c03060a0906060504091b23040e0c090a020d060603020f040302010f02070308030f0f071704030305061206 76
    0x1e071000640890304c240c1c0300c41181d400b03002c041035252010f119414881c00024400541d00d030503045d041c428850700c44c8003480c100d20704540310a400c40d58100c0d20101142e64903003401041d4580001c15100520600440a2100c80450f40713041060045102c02414600048086403000303000d124018090504411110300340e20090500400c1c042c01d62030302d02011000010707915104840c4800d40c400042c0301400501e090f4031002011002003503030700d200366032403581c0c0c0728046455074a5000320603d01e4050450b03240396500904249039110007560001c0c06c0f02e41c1d00c4032500d90103603680d030560246090880e0f00150300500415814100000c08904a50022185041104004041d4007034480c42018140402086440d884142e040348220003015101e0001403100300010b6116400740001c1100b1441a2443d840e40d9541e2a8515041900c50381000e92107401000000c40c110b0303d0300340d8050124070380400a5941010500024000504060304041c2c035440080c066845040140075000c1000080303540b03030700d8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 324988893 1250 324987643 324987653
    0x50d0510170604110f0123030105010318030207121e030c110d020d2a06030207030813080711061605011a0906060d0c0c0204020a170a061211030f010207 67
    0x400d00070311455180502035001c0d1a000007a61510480d4410028240b104404041081107014001990304104000d244100c1143e802c692002c560f100070703d0200d0312075040c0b90014090301c443c0c65990f844201034100c0d400109900007140001c031401383e06000d0b460352080c281702c49602861411841000d030b581c46030303100700b660000c00050708600650341b1a081b142d0203001c0003103180d080540698814403801181c40410032981000554107410580700300f41d130700f20f403280d01101829a440072010030307404100482030507005100c144e03100e0901016001c0194155079001070364000c440d00940160441051010962100c1c1c00322044d1014416004149141ca454414082d041064034450030b50340c240043c02c1a410f101d98424056a03000344064103140344032103088000c000d8030b0310a07020031045140e58009a1120b100070021807500c0d64964496000e11080300342001c1015100d01c01c99841c1c9501004a20045125590400d60003131640507440000400a407506564200c0b45250354400210641006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 324990143 1250 324988893 324988921
    0x120b0a0e0108160506040f0303110f062d010510050a11032d0c0a030c050106050604030c03140a0804120303060506040905062e0806011707081f12080307050d05 70
    0x410400f01c0025110384840074045a4050340c458160a0308011006100103030103100d8000460388120304964168041c00b01d510702d020029507841c0721903141c41c000c41d07640e011a0043d8080e01141d1300c0c0a40100d524000205482e50420800b030030812102180a48045208410321038000310b08800310782d01c5801c0c1c05d04002c82d684003044030342005148044840c11740b1201c03a06551140308814060b00460300203072010365402000c14001c881d20755a4560210b603a0351004054030155000d4a10000320f6421460169160300700000c00b90129800504c2250009803e18119001c0d15500c2840f038941c05014641680540400d412150b4028008140410200340c030768042d910510003100c8540b80e00e00e078400c207610440700d03c058024684608600d81d5a00c6405041520740210043c075180000c4d50200170a120f42c3c2005445400000d401001840a00c0c060082101c10f8042d5903c034150b04a4138040c0300342c019a2041c0401000d01101000042c14503024074141e402040c0c0010b8148090718208070b00030441 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 324991393 1250 324990143 324990163
    0x804140106180b01140405041e020c0c0a082d010b0a030501020702010305010f03150c110619110f120c070807050703060609091109150a2403050403120b0a0e0108 71
    0x14900680240c0a40c4030f104e04181c43ea8880d02c03402d180c2030170001407002410400e41c03270030b100d04004028580d80301068802020000e1034a4054081c0b00012030030000c85050981c8440c0941d40805a0107910311940e00c07038202581d0014038480c0040c00ca03500f0345809850b20620841d80089112400401d01070306400804440d4401d0744d0401c0340760b8032400300301043e181500018204025001c0000c4a445059200385070b06030075403c00703051481c410310303c8a16180c812910040d044280b0f9003007561103010342c0681840b80350808035803070030000030b00c7c00034a050003190822085444050049084080350340221100d80d500503603510303aa400d00741407072030313403071103141710494800c0e123400400120380c5c0c4607204c1c80c16207581c0480038034050030400342003001d45e40001d00010010800054141880e40d07803440c0000c010b00307904d452164060803140840520200800150090600780420403001a80c03004014040c0c2e040a4000a0b441203918085114203209400c10010f0074103580003c40e10720f0002680d4268 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 324992643 1250 324991393 324991439
    0x613060311090f0912071e0f0c0e1e100812040314060c040302060705070f090c03050c0a0c02010c0c0e071e090302150a0302130f150207030b070804140106 68
    0x10a8071043c1629108020854040d840c1e80c0015941da80042102402020103a0003541a09012140c5031441503c181210500302d5000301c1d41005002041035609040c001090f00b60060100d502d401054000362011801e40d017200c041030040055481403610381e0f88805001141d045610b0000040a90301079540180000d54550075081e0300c039882c2603000150540306a504900c40c6040510b5582842580d401c0401d048440c1c0c001d00344081180e09540f18180d004041c50800850000e080b070311301038200c9402400540c4d000004121400e14642c02c071194180d940e40c20302e17207140c402560b820701e4486c915058110a2510039038006008000c1c5d4440745104080d0760001444588000210040d0b42a5089120083d044009500c040304043e180720050000c0e044c1909002d490240c2c1070076684500200b90308424450f855004080c001c0d00c604640079403418000b4002000c1660a64903469580440141168200721500380081c08010511660b42000d5501000904c145503e40c801c40504414800b12245 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 324993893 1250 324992643 324992659
    0x10203010b031f2402010f0f1a0609090f0601020a211b050a03050d150326031b0a0c0b0f040308060103140c0c1501030305130f0b0904050613060311 65
    0x640c00044081e0001260100030626060304141013540008500704c1d12800155582c07240c5420000e10140a20001d0240c00f240024030ba509050505110014441c000360084100b481052401d0321007480c1103070402c2e00c042103090b080c2c0e00e80004030710708800d0440081002c20780100c80e20b0381c6810781c0d60072800c1c841d668450715200080c295683d4280e0061503030140450380038070010b0012a014000400403280d0b010008204400140c1c240300300c0c0300e0268401c40d00200980300c0c003000c880740051400e07403038001c0900e0303c1e1070350030301210982a6011180b52011811800120602c029009100d1004800d901014402061408403900060140122026800b280702c040000e10150701ca8440e4283c0d600c1c180c001c551054032100030300300c1d0f1a08042500710484c40740e40d900344104c0c0c0c031654101d8001c610030740d2480d985e0700e040c42254841d5582a44010740c5e01200820a204084e4800140e8825103415203000801da03541d500042c9402030714842494100d031800e04040f0038090a807140b40f0b11104180d0f1099 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 324995143 1250 324993893 324993931
    0xf0606081504031b17040303120606030c0915020115180e0d0207170c0901080d09090b0a050409030905040501060c02030c030715081b0a050c0114010b0a0e060c010203010b03 76
    0x165116600700da005000500a000384d052015120641c07481ca0b03409901c506084804800300b03040c0e00d500540054010980c400c5001902d46c8242c050040601514035051184c6c80d03030750380e01410044c01e0340505200360a01074072007401e0074400d42c440c2e180400900500c03000c2d190b648003a6105514040181c0c0c60103402c06c3c41c1c0b4a490a00080c0300c401d4448940d008145d45031415440106083ca00c031000009802220700f00c8240380c0d01c0040141c040d004c0703040981015412581e010701601041d074840000b203820280072880d6641d078602020300702c4105940c01301d9144018a0100d07002c40702c0f900031a620510345000424090784c0042d540c1d40c010b20980840320042c550004059803001d65100751100700340f80c00805542244191506908403525a00811852001c0e0300d440d0116080020610001039000c100340c10302c45803d00520901c2d489281c092a04c5506100541409100703601c003400034442c03900252607083c1c950b00304480804a031a0000c40d00c070b58642e40b44c10855401651803250701e40081e1100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 324996393 1250 324995143 324995173
    0xf02030d02010506130b150d02090319020108010314011b02030310050613120816051609020a0206010501030e07120c03030e1206010504050c071a0402090108030f0d0b0a030f060608 79
    0x154000e010090040c0c0c1c0303500d10001700c0c42c0503092001519402c490b049094000028101c5d020b401929003c8502603181c0e4110300604d844c101c80c0e441034003050485141e0202c0581d8000d00c4650559402c610381e560510050100070340540518801c00300118510a800d55030141e001c009180102c0c00c3c1201c04400b29901d0007080018041c0710b6031300c403091034055420003800203034001041d80307c0c0c070400c000740c1490054020116250391840c1c09640c0d0360001d59211001c4648544090042c1030080011410301c444801c0c000d64402050090301e05140d41c40c66001c0c402c0c0020002c420082940c0200d00842101f9841c1004405101d48021404903800305540740052a148000d8840c01e42c11600400c400d03803a28003008013501000d07143c00300d00b002c10801c0780003064500c0c1c80099409a1116604034900342441030240642050340000c841c0e4006000e5081c0d01c01030f540850307865007005140807070403141f52000203d81e01995031004180010f4444020100f0240350000003c458030701e001d84802d011000c000c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 324997643 1250 324996393 324996401
    0x7020106050f060d09020d0b0a060611060612030c0f030409060501050c0d0f0c0609060b0102060a020408070509090708010e0d020c090106050304140109050d02150105041a060c0c0405040f02030d0201 87
    0x5400e52298448040b090740742049006020002000c480c041801000d503004140300b040c003030006403a0580d101c001c01194002d1401000d00504003440d03d043c00003144100c482d1203036006040c56204200003a2030805100b01042174407040c40c0e2800a544c08a10003080c82983c3e544a8401c90000b142041c1c0001199170041702a24038003a00c50b005003483c0e030080c1c42d00722540c504440c032404c1030000b14003400012680601c14820000e105036800580e1040800000e40781c01c0d401415000020f0040000b800340d0f40c00480c01908a0701c0640300801c403600d6001419050444540240c022503203090340106651800045841d0160015020344103285013140900148178800d014000108004001090004255842c52001980241c00008418255580d01030600301810080c400590111541e81d624104030381c40580107081c100d9080102d0307024034a20103002151056118130885010a401c41c50403028040498031520003041041545020301d8803100800c82080140d0103803203080607000c016801442 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 324998893 1250 324997643 324997649
    0x6060d0506041403070f03050a1b21020a0203060f060a17070b0c0120090a09051509040f0f05100e034905011d04080901030216140601030b07020106 65
    0x301401540d40e8607154101108050911820584000c102100c0402d1a482074850742038800d0350745542d203140fa204020b20030500051611105501e8100e000001140c568031000940500c0008901000e10240107a080881c030910194140c081c520821400341100003103d0721907002211051459500c41d070f20340303680d80104940d40700c2d203500c20b5006208084082002c1d2001c1800c1c1c400220307940f5285101d61042c81c00c1004c0400d20b040700451819110b00c1c0c0000c5940142c149003030100424a00440c603000c08a505034940c6010b1448c4001203000d00130b80307201c0210215080399182c88940c0c42403402c143d45110181e101c44c0c0c0c5624003880c407507010101000b03d403040395140003009041c01045a0205407010807880c00052064040c2d90018504144140214541e40d64100003525615002010b2481000c100c851200d0413442d00811000680400c19100410000c2c640140c44a003408401850380c028030401038100c1800f980d10060704080000e1050507a40b04410102440e150000107a0980b60307280 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 325000000 1107 324998893 324998903
    0xe10090b0f06070308150f0d02040504060b06070b01030515090c150d0f060305160e0c07050705130207030e0919051509090a0b070905090f04060b0915010206060d 71
    0x1200e4400200710a684040340007454800080c1004c11802e0300074402d6032f0b50000300d82800481d42c8001c0002e01e02500c074a035230752600d05060101400c01d22080700c1e54030822603422041d95800c42c01705e01680b00f050041c0503240c1c0e8401001a110705844421050020606c00c2085001c00d078042c809881a003a41c00048050641c1459410280c071560800350740400f089080003100114541694042141e6114a0300d43c00545070031b81c01c0c00400c1d446168030450500140164007030310350003450814402e484007103040506100703001810404440526507460070407020900d40409801c07095003d907089c02e203450b158440000149074204107075624106a48903403102d0301046054889150044003900b819415507141030009a02d00c1e500510000a000055001c1020807246030401c0c01c0405004051220525003d640041c0c0383d484044058010710400012840178240b0034030040328a0742007 = true := by decide +kernel

theorem cover : BRFrame.Cov 324820143 325000000 := by
  have h0 := BRFrame.cov_init 324820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 324820143 ≤ n) (h2 : n < 325000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
