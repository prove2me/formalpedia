-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4719
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:30:50.83329+00:00
-- url     : https://prove2.me/submissions/f021b9e5-b077-4500-a263-4b221feb2339

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 848561151 ≤ n < 848741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 848562401 1250 848561151 848561173
    0xc1205010902121c1106040f02060c070f05010207080c06030703150909110f01020105100b0901050c0105010e060411270402070b1320010512040501021309060306050106080408030402090702 83
    0xf591412152400340010340003091400580070842404503050000344407054400401d045000b01d038043e44140d10914003010b85d446400450354a025400e50a9064464580c1c04950308140c5042c01d000c9030001d90880700c00316203911906484100f10f1a000350445414004504068001d030004151004050180d030070741680e031210141a0350f8209402d84d0007001c0b030b0194061794100400245480c10003800240090b0801000c210390450700303840380008420000c1003006507a88124101d8800b985140c7c0240541c0d61281107403201068256030480c499860b04419481c40c08411090350072005800480c0180300360b03041d00041090101140da039602076401c00612002400c4810580d00442001103041190364452900d4203241c840002c841c0044440d40c109034005a80c04011640e204820070207440b8a0b0311180390460181c01451850040072619502c082070b2502550b200c0c0084a0103007106022699035080d069890f140155000b0f0111041000001e01500300000b1054114625104403244116a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 848563651 1250 848562401 848562409
    0x180310050115260a1b050c21120621160602011e0c020106050d05031b0105010b0913060509090a031205060d110d0210030f0e0f03090d030c0206030408070308130c1205010902 76
    0x4000c0c0b1903001c07885c04a08040c1d5050304110b0034107408400100e88d0041c03900c94140400902030901d010a40c04640d40000d95291140240340003081300080c10303c80300024119800b61240900301c50740250b28482240010350078414055440100308001424243c07600c804898409064031240000c2035640340c1c0e0002580b51559090a00c07528010400b560f00d6011040d0586440c52041203030b2440d036030408006000d0280e021044a144540440f03d90040c0581c00d0180341c0501415401240c2c4601c5000400000c540082148284a8800c0e43c0c0d4002c1d60031580b40c0c95044400a940103a0462400c05804000480d0701c84e0b10502c003000140140b20305445070340012681c600b5005100002a191034012040003103600134032509118080c05804480c0038401902e40c0c9016600e040c500c11b941200c030041c180f6000342c21000c40c503030f0060150b40c2e5030300e0142840902e41e17100c01000c400081410f000110440c0340c015075543d0b4158015581d801040c906105000050180d000c1503030350355a40e151480040e61 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 848564901 1250 848563651 848563691
    0x90803070305090301150806070c020d0506070801060807180e0402040f060611010f02120f06150a030203040b01061b0b0717090a17130b180310050115260a 68
    0x1c46507407656502c040030400d01d0309451484c0001d00040b0182c071806c0c00640008142030b0b91100c5149813003c04403807240001112802c40d0800506036000c1e94040c4074505074462221030681c2c541d51a842e0081d2550042180e0260092010007110401d0030fa00f40600d14642042e2600140002c2000c22120b4a003a00c0d032048680342e0303000e480880d20300c4040714400d43d401e00501507803203007407001107080021140381c0c00350501e001800e0ba82402104400a141583e50180300043d12420015081e00c0b19074000d4050020760083d00c0c19a941d0401000014090b841191240c8007111708c50801728a4a03041ea0b9a1020010090540014054403941d03110280c4040c142c0e00f0f11402c0c4c0030380200030700103003400d091128018814280303406c41010072244030301d014020241011507054a0100b913481c2c602c0004c01110b0700310b003000903a150241800591801c60550041c40c16a0552060700d80c002c4c0469000b5204240190050500323450030004000c1c901c0310380000d4507404440150042044490b412051520007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 848566151 1250 848564901 848564903
    0x70504050c1c09030801121104180f1208011a180307120f020909030307050415020c060d090515240315010806070207060503010f030b0702011103150f0f010503010e0709080307 77
    0x1c3d07a9641c3c1d40185075000700482d004094140805031140d44d103032180c600555000380e034140555100e1552000481882d400012100d030460b42c00c000580351840d180008079550041c20001400d18000403401d0340727607606221144d04140b02c3c0c080c036221b111001c010301000f010300c00d00d606004030000002c015002c105040031076841601050b040403110b2040051075240a00900d0750780e8000c0c000c01251540260881d0b0641e440c20700514a6550200c01c224500545004210740055022070024100c10b1181c2080d001c1520070005d0f0f030048408100524a00c0301c0458010b80081c0049440c0341c912b407040c0c1d0000854103806416112140c00441001c4003c0300203902c01e101e035902031001c202d0b00e6913042c4100d00c041d1101e407500b17520f55490807108880d810590b0002400d04880c2c0030201d41c0d118002d504c0b1007a0249800302040c3c8901d004407070300c0000c07000b100b08a0300031050f13151802d0080c5045031104800490503104d40342540d080003003109048500400302f0061048040001c1420a8100090b011003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 848567401 1250 848566151 848566207
    0x1206010b0901020f0c0913330b04050c0d0f060f060804030207080705060405060f13030813090b09131707081e030601020601091503081b0c01050408070504050c 70
    0x3030710403040024609001920484050341152100600d0303581d500000c1500303c042c05800c09203030b241505044001042a24030f01c1c1c101c0341003642590a20a0915184142c0c029841c5d00b08011401d1078140300503903c2c21200d2030340c4c81d0810056003a00007030507841305901c0e500203107000812680710f000d0140d18581d25040781020502c10000c210800d40e04002c0f24000e409030074081c02e07910742b4000100b06540550700805104101c04501203000300d01500035610403c0e0110303080080103a6904040c0b10030740c84841410507000b881103010808100d58042c00d0f0540ca8013034100b41c01c035683c0500106040c40ba9020840da0000c440320110209100e0310301410200d40102c0303080760b503072242580c0d40d0444c040710f0340b0040f1060014000c00019031380115100d41140c40048000c82c074207034003a03001e0004e085540c200401542c40070921070042000b0140c5860040d018200325544207000720300542d100d01461160010355442080103020508154001c80e801800700c11250b402e203400f05504110348400c1c01c0301e031151 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 848568651 1250 848567401 848567407
    0xa030e010603260a17191a03070801060810020a0c0506040809031c02030d09260418061212021006080d08060f0d03030506130c1e03110d0b1206010b 65
    0x14204a6007403ca8644000301c9510380b801d2403801c40582407201c05008000b140400d1000a0b840810707054a611469407690410001c070b1042440326400946c10480c4035000b445001e40104010390148107810a80340010001c104060003000301c40043e610140d0340d01c0401008010030b000113030b010401c142c0568032501d0305944500400c818185000c1c1d90b05280316813544902d040380b00060300071046401c190440719000c601640340e400d1900d9104075030740d40c00620842c400c903542c4c40103404001400c02e41e40d079020300c5519402070b060b00c3c2090b9a079500400080c6480740001c0f40020711005084518030b03124bc01601c0c00e0500c075505d441c0031110740764070280c40c541041400f10301450384110300c01e620000481b035100003242884085500350001070402000c2c590740e1008182d041d40c2da694903007244082c41d44180000c3d44856002444121a1021402d50003809809030700403500a01510098400088460381003c0307080760084040c003c0045c1c540d40007541902640b8202d20b0600c2002d018007001509156 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 848569901 1250 848568651 848568683
    0xa03060606080a0e0304030305070f0c05130914060105101d0901090606081e0c0711060c0a0c06020a020603070e040905251a0a0e1309050622170a030e010603 69
    0x3d44054004c030b00c0554001704070602c0080d4120003651f011a80020800050b4912883c14011085c065041298070085184000e4030744081038128000142c4501440d03008000d020320283c0c0c2d82c880a00640350301110844a02203000d10030411103d640311146001e5081040020209601c01c0080c0c2141e007601c0e840b810240080e0342c003d040c3c00d41100340c01032000e141034841d032181d90311040c1c080c01a03182e884001a02c041401183d007800200040c00803c1c43d561804004689541c60340b40c060101d564150321000041c0b210f0010a44002d2a60080d00c150703e50381e200842151034009500e0426800365540c203002c000700b207041000f851100c10302e03070201c1e001500c5104428500b1039103910146c00304078100d518100d0303880000147e1700381004908124028101e00b20000e400c515032140c2591502d480c03c0342e07400c18000c002a4150142560704100301003007000000390a003100c00f8807800340000342c400030914074588611700201403c1e00c407854002404000260078509540c580e9000380c50760b042d0f0200c154 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 848571151 1250 848569901 848569921
    0x4090e03090901140109050609030c062802060408070b1012050f060c0a0c020d0f02131e0203040b0f070216060215010605040e07120209060408011b020c1c020a0306060608 75
    0xf8090060310004103070801c40600000e00740034040c000d44d40510070104286c0c0350350b2400c000640840100030101500c41700f02c0c10f00901d0f8086044400c03404503820030125028030b400403078458000c40d0045429880c122a9440d0407060081c0501003d4600c40c01c5d00d40010803101c20f540041a50344a0070190024060314004203140c0705003e0b00346540c80c01c00b0007007280e1080e044030703410907441d81c15035040030340526a042040e071628003a1400380d04495030704a0003107850030740c1e8890305812a000da2841081005140e01c0c8041340011640200007001410104894602d10b90001e07500103a43d20460b120301c3e0303a6100c40b0710310460076444a070140e0720071204d0355120000e8035060340c0500841d14200d03060034504a500c44540d00007a2210050080c00c10310070503180c640f034040352203801000c0c105940d11965218051b00800b40169901d050203205520410040d01c00701c0e2014101900401107210003038840141101e410034500220ba010504101c000005a07480c0200c030014186601c1d91004c62030501e00c45 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 848572401 1250 848571151 848571169
    0x302191e0305031005190608041a07050408061b03010b1b010e0d0314070f11030904060609050108060904120e130f090507060c170d091406180f0712050304090e0309 72
    0x291b115402000c0b03000540c0d20700490f40d00c04c50346585440d41450b211402c00420b802c015011000e00c91403c40200441240c005000740119078007001115441d60302c810707212545444860b103441066100300010800c08100b50081d00300110f00d01c0c590181756812087c45403c440f44004d4001081c0c0002040321003264240c070130107055440600303c4032094a8014001002002504985011b001c1d0781d0b10003a981c02420401e8400c224000b410812030340d6100c16000e808610148039642c006100c0f10006040c0d1b052800c1e00500071030f8001e18070000d50701c40368000e80b54484c0c148105030b08102c505032209107400040c09003180380100c51100282d455801d041c89810604182c02801c107000400c1003420004007600112202600b81e500150b444000848101d0060580c0c0c00001d4142003044241800344040441c40c58025041c082c6045480c020000c03045803100c4050000e07d5240d00480c50800541228069040501380310b041601c3c5815101c0703281d402102c7d80321031154040d900104100072107081502d12 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 848573651 1250 848572401 848572409
    0x7030c14060f0f1e16060506040902031005060321040608010e100306090c080618100c080a0c140c01050a050f06031c030f06060c1506030302191e03050310 68
    0x100358a0322440841d5154280f18a50711020141c000041d54443c400701040d05055030072030f43c22403a41d29540001c4004400003005425a0980c1c40c000104003185824460034544550203400307401d1198003070795880018040100700a8140c002c16212008103501d00b010308500410b094282602d0303c3c01c0c400000e10321401600010f468100340e01c28801c5102c2c07a5545401142c0d44403401068010541c17070444840c0000d81d0044103c0d100300d0040c0b08003450641410104411118100c4050004000d18181510039009148012a01e00c42c007090b00810030350001c202008083c03d215035080303c3d1103000314095120601c440e0950350740300c09104408031140070b40ca4001c9c030f00584008030350038100000303074803615007450f02d281001071414401d001900903085024210308100080003c01e0f640c22000c1c03d00f032855a01216414880286021201c0d8280300b1300302620b416074000c2004d4400410100ca030141c0084064074071001c165040c0720380326410002244020301c40d58074a52241800c021205e808007250b04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 848574901 1250 848573651 848573659
    0x90c020114130b0103140109241104290702120312130210080a0b0604080a150203040b012601110702011101060311190e04080403050f030c0c060d0b0307030c14 70
    0x900100d0200f1000d00d06494024821300c0c1d80307000c8041c0d800e005218500e801000b580d8140182414446540f2981c4c046404086c0148810050410001c5041c801c5024012106071740340000c00d40c1d18640000c100380040724940302031428081c2c4d00050026404100e101c1c98a610018207000b085500180f4160401002040300380380c0c1c001c5a00051101000c0d2000c5401c1050710000a14036080300d420140820740007508041e40d41e600e078582c040c0c440020440c01d686410210a46002010152003120310072034101c0c500e03040603420000140c81010340c1c1c4d90904d1100d06140200c0703080d40c07400c3c45100c07503062501c80c0050f550009803002500c0001a00246860346c1d25003042080400c21b408844140c036901140c20314544004851f40c1c0300007420982291020308928020441003044407801402a280543e044944a02c141580c1a9483c459024040c00c40c1d005204480c00a09141018020490503c0e0003c208400c140300800e00d400b0301a4015030301480c00c0207081001148070200b41e4415031082e1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 848576151 1250 848574901 848574931
    0xe0d0903051e16030b0702012403020120060106050405040e03132913090509030a090b07081c05010603180c0b0c0a0c060305060109051e01080709090c020114 69
    0x5214152604941c55240440b500d120301802c030141000e01c01c041c150319020504080e800e40700d08041403002c1d012511040590300c1d103a02d620f003c0c1c9500c0e4a9051200060180c0c000390b81c02c0d0303401115040e11054081000082c0c13098280c83e5031405028641c003130700c2ca40d581c00f9101d0f884e0508000645014190402503504204160100c00a010002009035138143c28460110816103031201c405030405a1040c0480e40c1c0491020451040414803001b2105010010b11440c0c0b80c00c0c1e9242e0b220312038480c42001150040200b00081c1c0040350103410000c4c001d15441e402c100c005105070a03518015040701202d1a0b4400050241d540c161080300511413401040304a18883d503500d403a44170a0f02c0c015186010000b045a0620b01000c01201600a60042c0c600248595030030000d000350400340c86050220b2120500400c140c2000548283c05c1c00709100c8000d40c035040d01006549211001e80081c08000f4641c40100b40c071a038034091440c8801042d4000610811002540005c0e44400307400c0026045800c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 848577401 1250 848576151 848576153
    0x312030c03070806060c07031b06080124030902100201050709060206070f110c100f080c070f06020304020103060f141828151403010c0c02090a020a020f030403060e0d0903 75
    0xc40140da6102c61103081c08200340d00c6180c00210a405403050511052161210100c1040f07000019202100c0a41144001e01c68a580f000d4507020700c240280204c44d82200104440c01041002d0301c00c80c0055800c1c001594440b80d004603016070956000480580c0d190814004159032003401d2100402d0a803000d41805d0501035402800d403100280007034204070312410020071040c130502c40060000002030504041c035828a501a04185820003920085191000000c10803041c07001156100e6501417184101d8000c10741c0d031300d402504003030016030416a03a09000b086019511642d04050b18000c903c05000c08070308800c01a0700c415200c4005540342c85201485900d8030100403206119000104081c0405540413000c0c000b010010214002443c0301c1c10000340300141d065540c10720303c1095009210780000c03c2019030b03115058000c002d401004440000f11451000d40c00340207101d0315441900c100e44a1652407078950b1700a50410744009607245182400e448003003041d68540169400d14841c26455 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 848578651 1250 848577401 848577421
    0x30c0c0320210705040c050c010c020c1003090305031303180b0c0111160b07020f01020a0e0a120308070e0a0b0301030b090d02070311240c010902030f0c3a050c031203 73
    0x1113441614050b9889124030944503010354141d401c0002420000c008041100400a540d008034801641c002e820585e034148400d03209000b20200700350548c07201c0d451519040035032441101c070b0b03039001d808028000e0741d004003452001100c03100619610400d00d89481c41640f409007140c00d0385454a094500401c041c41c1c144d20349004850044c0d40085201da15607075007003003c0c1c5c10b0400140c801c0030036503c00a00c1c0660140c1044038a6902c0700c0996444c086941c8030441c510151104081c0500030403180d0300042c418a100e40c6801c008203d0103003d10600313035902e912034402030f0800e801c1101d0a401c8901004208035007044200b40c0d14810b0720081448600c0c688130002c081c2901714005004024580600089224410706075600e05071059000d0b80d07d40030340b01e855000784011302e000c0b80320f4064150407020b90080040c0d4229034683c000e02103100c018846078a800480c0b00c0010240c503051820551511034823a460700b4044a0f07010324050841100798804260034542034428901200e42c1c01e205020011803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 848579901 1250 848578651 848578663
    0x1b040f0e0a0206090f060a21021c050a15090603020405130b0417121306060f060e041a0a060507170301060f0e180901090506060607050307030c0c032021 67
    0x207010f80f08a0b60312015680130521070080c14200c40d410510002d0b003942d4859204915140c2800f813540b5640c0c1c1100c3c501000c8003a4441d0a44618112442c04114084111241e1110b80c102290b01d00020301840c070b00e0101404400301d980104001555107008106604180c05403a901a4130710700f0340c50707246000307945c1c0340040100904041c001c08080305c0001c01c01c0f8485000c5505140040c40310500714034084411495810700070b80c04a03011420aa40060402072490081c02500e0654a820035550b850100340310082c03800e00158a00f80c4103a01c1021020b40341c1c4000348016102c3c03a0754044d511511810f0a90b008145039640301074160b0200300400010303500840214881400d803600d00784200001c030000e6840b0000340c1120f00303c4500c0f84280420400158070081e01c407031042e803d0355456511030f02080414055000c02800c1a00b0030020180000d01c14070500380068482d000c232030485516501c03036800a415000d50301700301c1e800e040c1507082d0310300e8114080410103c10036504000005030b2030840b5200c1d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 848581151 1250 848579901 848579903
    0x903053f040b07080f030c0d0b09090d0c24061d01030c060c230609011a0f09040302120703020106061407020f06090a030b0a020901182409081b040f0e0a 67
    0x10b0000301d03034141003100583c1101e520380d10102c0740030f4680c2400781e11b1030f25130781c00190790000040c42c1c500207a286091a45d0480e01c6540780340302a1100103103040e0b0540e15850b1400e000c584a0601d410608811607103145103502c550543d00c000200c09041c101d036601c1c82c00560499103d491211001040041c5046610005035040c40c50602100300f814070b402c00300c414140b0304465241c141c42d000062180400104148181700340c030028004d40401c5500210ba2003400443c180d0002c480307041c1c41841e0300b4079017101c42d0094841d204803a0464600b0010005d03d80100004400503510b903d0100b200961002911f50a9402d030441c180c0307480403035400a130b03c0d0590310440034042c000104010f07005072703101e00d5000020354014600150038600920040025880303848000e011810703c02021f148036103141028000e542c80c4ca410040c0d01c00344014550407000024003014108042e48d00041096402800400c80c65600b2400780e0b41031a030600100003d507089101010b60f034034034068802c07000c1c102c0090011030701 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 848582401 1250 848581151 848581169
    0x6010810120609020603040302150a140c09010221030609160e0118120f051509060f091f0f0615020723180702150618070903053f04 58
    0x8940c040c0b8140d0060118860061740c4140003000b04002d0503004500c04071b0445522080c844203965001119045903e1140c0075181c4144545c001003114180000812010a0500450711040f14080000b0001c492208201e00d8407000441840305608058a01540107003006030781c0004d00034040780050500e042107510604000340c40010000e03108461740701030041d04070108541c0512015050410320340c820b00178100e4030761084103402580071405007084e900560701240940029203a201451032a0240584960603500035800480d500c00080212140b40550000c030200d00d10611040080450703020b98064000301c0440010231441035030125900b400c0d14500d8940d040710200709840303440503112800090740c110118011640643c0f00380900d0f00c2c82808035500311030910131070002c1a40c03940d105681d900c1d00121100017815248401101d415800201440c110380d5003030b600c0c0c0310145000c00c0c4108244000c0072881424620314031081c05484003c8104070300d2141c15894001181d20792040344900701b60 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 848583651 1250 848582401 848582429
    0x309080f030306092e0f0302120c060304020d0512040e040201180501050d09080c0a1a0702070303080c030a09021f090803070c060305090703060e0102090423010311211506010810 78
    0x98030f020100c0362100e00300c00d02c03000c44000d031652155a007080306c50005a00c40d0003800c01c0d61080c954000f910484001e0064500c07415601c440e801d20120480b419411122030203603907200d22510074070001901c0100b072454034031182424540005000c3c11801d0302400c040c0c84201500380b0490341c00c0304c1110075011240310b00240c45126410010b80d10300614500c1652405041c00c08014404a10461a056480030140ca08251a9980c05a955082510008000c00c010b1700010340a0204240516441903003980d01003507240081d800100d10140006d6186070162139031424121007a840941c00d0098100c2e80d005504d0411151240150b82005205040c10140c54200040403200240f003444019a44000103000400b030050340c080c081d401502c40c0a004603e000140c0f8116146510703070300d442e10451040c0146590840d00d4040b000740350202c81580042e681e120601404c1ca0101c400c2d01d06031800d80141241c507172400341400313540d80c0241c81d07107040040d0b04007442480d0314500c045800f111031121000c14 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 848584901 1250 848583651 848583691
    0x3060906231b0d06080111070515090d05070c0312090f0b0403050c091005032e0911040c090513060905010806061c110915041d0c040b040b040203040309080f03030609 73
    0x409132506402865140d401e0411200303048030200050980e1a108200384c869402c083c00400e000604100c0f5010030300d5100042c000115070081c4000c3c29011302030345c4208800c64494553300d0110440c50f0100c00061030552082010800307004405020b040c081e80301034905840c41e142d2981e00d501c55038a9910408441010500700c8100140d030700000c240c00780c10b84001600750030751120080494200c0d4140d900c86002804250b400342c0c07040804c01f6034804502c040c40c0e43e805042c0300c01011076421080503c85c000c00045030940d91404007400300240000081000c0c0d0508451800f5554181c0c0069041c0d84450244035080d502e41c01c0340d4018803040b862060707540000341030030250055041065a0020010310a00044440c407011180240e40b0580d418042c90f01050080034140002c046400d03240e40215200c4c520302e192a82181d1502000100003264400f003900000381240e0095034114085207020380200603400b810f014440c0582c070340c000610b0a600c0c0150210300c0002d801400e81a16190403481c0326 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 848586151 1250 848584901 848584927
    0x6080915010b090f1306170c0103060b0304060207050709021305120109080417032101050906010c0510020c0c03190b0a0203060f130207050a030f0908120906070c03060906231b 77
    0x80c1744504029003801055515a0000030800e010303640298903000d803081034400d55009004400407221034003460b03881d60740c0e152900c20013504003400c201c506004a0034006902d9040b030014240341856902c508108600d4007081005080c003a8412401a90405086102042022f4103480480381107120340100c7d90707440b2003414290f108010031840c400c000824210304040030307420518180c801c10348908802e42c48150041da25408090001000c80c2e102c20484c00c0300b081960090903c4220a900306c681d10482d25000a040885001d221620701848804a0080c040058901500580070000c01c43c0f942c00d01c200414001e6106034080e80c021a011030108032556065412281e0590700311090b10b18030000783ca0010000902c01c86900c000a84201012544c004042201c060382c241c0c80812900d044140006d203c1c1c1030b00030083c282ea020b006079034000049070150040c41a01e0f4481c60b40010b001425844005060002002c040d4082910508000780001c0c8078145c038402c043d020140c40d40300c2e41060030318 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 848587401 1250 848586151 848586169
    0xe0604060902031005010f031203020909070e0a05090f10121e0809091303020705010f0203092b060b041505100e0f0a08070306180c06180f06080915010b090f 69
    0x13038070300518220002400e5a02030718403400340c0c0c0c480c040481c00400e5014080703040c3d005500351590700c8140754000c940072030700588000c858518040c044140f40d994903400242040401c84a800c0810b414000f00705100404c44502006042c03c0c03000900803440903281c220074058420b038054814000c002c41001480303568815203100b03002c010300300a80c078038248000003030001040d10120058418a40041910344c002c42001d2420b03181c580c01181482034150811170480081c49200f0700b50301e40015075000040c02268507008290044e000410410903050501c01200d682c0042000509040344003482180d5941501f00c980100a180c4050b050303c030f5100146010404c084800e511864400c00003e9421021a80c0070841e4010101040003100c0860f10010355401010028000c03000190180b112500500100100c44003c403148500d0a07104d09002082443c6070b04804045240f82c4c080020744481006050541009209082d04551400d000305a440c011641c24511a800349469800192641015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 848588651 1250 848587401 848587423
    0x304030f1404173007060902060705030a1b0b16030623090c07050a0b1e0f19060e13020103140106210b06070b060d0209090f100e060406090203 63
    0xc6560780d00c0d503801d00030b002500071070051240d40c050003481d2005a01e40d4038070048900860180060a04c0c60340001a40a901c520700440b84d682c2d4864080c800f40c1c079888040c000035446000210b0382c0301259000600f1080e001030b00c07404254a0a00d011000038002d40070706400018043c040d02c00c00500318420790107810310b40c100920741c0508050b5069645210007000f840b00100742c81358803140d20740079030358015032041d84405441c0d0b80c0541e0303000c8001009c440000c0d41c416442888034001203011012003140200545085000d90395100070322000d820433a28510052510140c200b00c0c09140841440113003000800c0c4032a01901c80040900b964040c1d001081c02c0715020745840180d40c0c650074045d00b5602d040c0c1e416503204c5204901c50000c2802c034401c40503003000c024100750616106c0c0d81e81605000c1e0007001a0740203541d0116010041c0c0b2444034040c0200b000001600c9120b18100b00e141c580040300221090850a02020841038240850300c140c04c81d400100c081005012800802d10b0140748240d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 848589901 1250 848588651 848588687
    0x61d100302010c030c0326010f0501081b0c0712081c05241908060a0507022407090918030810050a05061e030f060a061115060f0303070302030c10060b0304030f 70
    0x8021590072030314164032305a07282444080001d548031001110380710001c0f51b041c022010b41c20304024410f00c0d003001507c166000708044603c40c1e6200c01400c40303040d00e04a0211500d40000c1390042444e100080006400e0b40e4184c0200134500d000100343d180d82c070500c964035540104511402c0c2c1079485500407601c00d5614501c500544541d11100386585d00c0088a500c00755600e0b05001c08c81d018404190200d034008000b02d81c0c1d4080a524050711400c0001030031080600c030a41100042024980c02145010b03100e03940d040317207211090305000c2c008007401401c3d502d04611003042030000ba80c1b003c00c4601a14015145603894951020980ac2e400c000404801898100401003118000780b000010f44030324419185c418149075500c0341900c038240011101d5005d074110110400281ca110860698802e0004140e034035a810603401090940c0d104000940060300005002c00c1d014104021003401100c031030701c003000036915000803440d0174000170b4401010405044610b4050611070f802a90003000d5150b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 848591151 1250 848589901 848589947
    0x191e08182103121b0a030c0c0c06050a0e0402040f090e0f0304080d090b13170a0204050703090c080307080906030a1410031a09060c070312061d100302010c030c03 71
    0x14840760ba0766000900d81507a000d0107240010b450031000c14040195181c4002601d08004030200f080d800b5000c3c520750b100c204491540b03001702180040480350010702d4180c0380e0680d03c1c16000c000500c205030344403455020b54010803041044900c8601e603001101c1e180c1c1c03400602d1080d10f00700781d41003030105d808100580c800070402040a0300080352070700042c82c00b51142d400013541e600183c0c41034003550303400704004422000100501c01d004440f07203c181400c03c0c1542c81d0070081750f0005084600c02e88005001075a00d400d900c0c10000095552006092440c008604201c07140e5101c1ca090710500303000501601d00400440e8104042d9004140c0415403c1e0000310a0b103402a8504402c04092105444d001c4003142c2d103040c1d8010204416005403100d0020b00400c2d40e418440c44005d40c4111400c03002c014140b4188140f440d154032840028084c400d801c0c5455122140d0b802c01d05c1400500380314103d031034103d010030045c1e0b00300315040407881e81030820720030b1180c85090550300c8461503890800302881275 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 848592401 1250 848591151 848591209
    0x1020709090803010608070201140f07180b0c070801140c07020d080408032701270b030c03010906061403060114040b070f03270302120c03191e0818 65
    0x2007000f941c10780d041a950840640d5075041e04030f0998400600300b203c54140440800e6541d0300034031921f60310165078100020349d007901d81801c0031900c4103a800854400804202ca1581c800c050040e0401000d80c04028000e031000c80c610301005045c0500300792000c03140082e0160840d240ca42101c00351a4120494a8507103650f00402901c030380c45242805c203031030401d00302c030460801d10509c191409a0b041c3d440c03558070964000340004442c009800320280100304900014041e600c071004600c980d542e0541180c49514058442e4180c4041d0b4020307005102003120618104552141501c3c4d000310240303046d90708202c8400d052600d03407141d80c000034603000001604405002028040038800f42c400e076190000c0b41000c12001c0c510061304403104002c003040600c20400b5140801440b021914040d041d43d13031101103070340000d241c1608030440914414051401c401406219907003060b200074000300c920700442050340c03030414078815514035061402c10a644100103890f040400c0c020f642d0440d0404881ca410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 848593651 1250 848592401 848592413
    0xe180c030a05013809070e060c010608150c0a0e0a0909120e0a180f020904050405302d0d0911040e030702092d15010f0905040b0102070909 61
    0x1800180e29403104d0362600c0d0080101001ca420a0812201c000310b442c0c4480c500403c1490b201c041c0041c0200310320340384891150350391800107000e2413883c0343c00040c7d03c6207000340c0d903410b00e00301c50b20f441c9510400c64100070f4010400011200c507900240b030883d1074000c0c84000a0940070050300705885040c64107490100f041660912000085425140c1030350340c11210080001c850340328064400011007601640c0495100c9030400b035160f0149910250400d8085e0010070102d0300c003100c0503151a0301416400b6030b03c4040050f40419800320030460b1591003010000150300d0b105085001600c030104041c1c110800405818076002d014015060f1642c40f02c1c2014100c0c054204132109503032120883e1001c4074035103820300c290324118144030041c0d42401070f50340800c810b1400090040040300490003405424051340b24030070f404035520700008217042c00c20100000c06420104c40386418860040034028200e0703003004420040380c004aa000c20a0301c41580101d0515526034049d0b01d04030304103003903a010400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 848594901 1250 848593651 848593661
    0xd0501061706030a150f0608030f09120604050a150905010509070504060b0306090703020f0c070e040b060301093504090606021501120b0601140d050702060702070e180c030a0501 78
    0x45070384580315124442019110007008400601c0d02d030b440700f10805501000c2d0800b0080301042c01c0700052440d80c03000c200d42903602004c008100c00c10f000400c0e0603603180002049201c0307030003034005080a10741a43e0785a55140c110001501c0c1c036240c040e503442422401d40010b00b240798024001d100d10b0400c0d40c142503441c81c45014143c801c904117500800c100d0411000e0ba403003290b000b80041d5164507040000c2d40258020301046400310010095906040700070848440140700c51907802110340350030706001c2240c4401409680c8241d05045103030001c540c05482804082e059401d803045500c10f81c0c950b5182c80c1f460031260100c100c03800f040002d21030101d5485401110752580030342e08180000d119810ba2104240266400006040da000011a1454040d00d074011018107103207c4d15401c00840484c80e80110403031030b45154072081008181d0713505000c141d82003070890005041840c00c05001030011301005282a100c2c988109504004140c10441000520809020381d489200c8500f40746000e45 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 848596151 1250 848594901 848594927
    0xa0801030506070f0512070203090a1e1505071407080718050a0212011503110304080309011b0e09041704080f010606020a031b060603060f020d06051e010c05030d050106 74
    0x80540760004051038001e42c1c941c4007000180d0345e92450308044d208501e0545c0406030400d01188414000841caa40f507006448001c0c10140c200c00403003032401d40700203020403c0e5800902d07100c0008018622059007100c251081a0f0703111241180580104a0261801405901c00c030418403a5450000f0003651401d141030800202503814059552504120340c180d02c103880500710160f14900042100c0110a401c0009040c070601d0041010a80310416000c507400c161425158214000b0074440c004000348104c40801c120100c10416400d07100d00045e02c0d0441c0c84040500032240e0340d0000b0704000d05060761100c100800c00340d0a171901e071280b000e40e588024403264080a0b610b40300b000f2604500015079040d0b4a545682c50110140403481845003180c400c6074115400e5840e004084000340d258007501076a003040d0031006848070381d41c04000c0241e810750b51120740101c50307208149032000306411001c52041004e08041800c00300c1c1d403600f1407451099105e0120f000d03103040008100c3c181c0c402149076800b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 848597401 1250 848596151 848596153
    0x50709030b091b21060106080901240b0c0f0703030503060102160f03060c11060711100207080f1e160b090c03070e0604021c0c020d0822020409080a08010305 69
    0x40d0303807900b0340c09a84100e00000c0000381e11002403541100d2902c540c0c46206100c10440042c2410000c0c14494682042a08074002080c0c030035040060088091049280315000546296003802d00d0701582c100c0039020b40107134246040d0009002240074820480034080340020400c9900c1269a070a0080050308207448182c010701074003091000c0e00e024050a0001d03512280c01c540802451961400d005041e00d90391201400a9200310503007851042c041c042c411f06075522003000e40a2440403180c02c0000e100c0b443e00416105101c00030100740d460f802d4440030b4004422065450364400d0071071030741d03541c2e41800d00e59080c80041c0c010038918900c0d049010451181405038001e86890f40c0b101c2e214105d540d072050701a841080204180302d0400f00d07664108101510052402100650b140010480c02460f07034881922101d03021a172983c10408184010b82524010801d82400d040c0c90300f0b140195070380601c2055100f0007800a541d252390041d20400d0380004116070f920f52081c0041d003000024403003541c03d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 848598651 1250 848597401 848597423
    0x90c070b0c0301150e0d05160e01090e0a1401110f0c010506010302090f0409142b14160201030b06040905040209160215090f0303010f0e060a03030512180105070903 72
    0xd94010503041e24182d4450301405010425074140884580014031780c03a03940b00321003c1208000c50024845183c580d11070b072a8024425040440d4950308541c10780c464049586844540060340d400458003086166000c9001c40080c40c0103e803241c098241001c10f10901880016041003900070070b0014203071881c0e01002840183e58460055040340200c00400340c220706000c101e2003252074140d001004152054401520003652810b4480c601440c15400b20b55601c6158001c503c40f10b040710721952020040d00d48003031800d0510100802d240101084d0000841c03000c1009021a80070345c00a00c401003000e44403580f901c5d9505101d0000d00420b98041e8041c83d44000810740300410002e00d20700881c0190001c140c50a124a1040003051005042110500410f680104040020f2008500030550345030400c15403400c1c88008032215074040c011a204030a006410800a5008030959000e030310005a41062552130307604010342003922081039070b084d520f0b1400f0441d0003600b055451065901495846035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 848599901 1250 848598651 848598661
    0x12370b0721060e181c0c05010f050c070b070e03031c0510050618010201181208010f0f0902180a0608160801050f040207140105040f120f0e01030509010b090c070b 71
    0x21901e007402210418010398002940744074062003500e066064410403100da91401000c0400b10340401c41030000002c008011646c1404030074014060300005071038081119040c01b40c5056001d2117202c1004090328140400030b040c49006c4e280004060783c000c2c06070780c0d80316084840d1850000000c10750962030b6240102041c04160002d00100a4070005011a858403604c1244144c40c4820949181c0c11503407207070380c0508550142850030808501c940903400d0007140015018101d1007058028819404d014081003009058005884c002c4440100c0016500d5000c2081074008146601d12241c000d4000400000d402d580302c0141d510491040c40400120100d28104a403040400e1240c50360296040030b00c015503181c282e00409401e84200d4008000c012003a01c918292402180c0c01d8400115007103490007400b41c41c440b030641c85891443d28a0816058450180c0401003500c0d0b5141059594400182007103401d6003c240d001100404190081c5092417020204c0d0b4414003088a9030000707500411 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 848601151 1250 848599901 848599967
    0x13110301090c0e030c06130513230910020a140a020604050c0418060e0a140c01030506011b0609050c13020c0d02030405010f0309111e12370b07 63
    0x2c0030f24800140500881c940803070402c1400d4100641c42c1000050f5104002101c1c0d41e45180e02c501a0300c2000089900324a0800d1090250f1003600703a014a0300b81f8004201c2400300100c0c02200c2a2091100141c81e01c4001ca0101c07035a0744003038880a40c036000000c0a005668002a01034441c902c10011a104a0700580a20064860013160300c152140202d5021000800c43e8005241040401c0102d4105000d1925080741558507452180d84c00d40121316000f01c00d5130700d40115a44108203081c805410054040c1390318081c40501d10140c2001c3da100302c240c0402ca07040c0018069140003c0c8205140c4070717100c0d030f203400a6000c01419a0f05202d049801035000d400841900c048604c161200b24507808440710544c00b03000850300440b40c24407a21403d02c10340ea2810025850f061100c048444000005814004250319025003200e2a501041c035019444091031201d00e00b4124a440d42c0751285008029400341441c000801801c10780901c04010710355510007141011300742e101071500300c90154a4460 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 848602401 1250 848601151 848601167
    0x5030705010c0b0a02091f080705040b1b070302030319080603060601170a0b1306082103070f110106140307060801060504090b0d14071a03090c0f13110301090c 70
    0x30a0204501e80d42c0c460114030041c04a60340103a140310098507140200d00000d5040c0c240f4406000700988540c07202040d02c0e40424442d90080c080c3c1015458a800e103c0300d10101d00a01c0100105c0da0202d00f0440070081c0c05103c4030380219030180449442c0d0341066000691420001072900000b1941800181c2501d00068078a0090347c0603118201d200c04a41c0310355607640e2004081020795a12540d02e40c46a40300d8140034290201c030300d04006005410050080e0410030001c02c1d42212110b0b0201c0111135a54002c1140d4104005040007800b01040f20700684502d81c5503000643c03c0c0d407a11800281f031072034101000542210443c1031361311480c0c40700f4040c1c4901c0403c0c02a417001420600003400340c0070701c42d44050801d05000308001c1101174559603031a18030081d0261005181c0182c18104240508652640f880301564103400c0d0440c50804e2500d81e98044c030510951162101d40c03036042c6030352110f0b00c1c49188090203181c00e00086070078030003525a41d802032140b01d500d2407415086818652090500c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 848603651 1250 848602401 848602409
    0x9101d010c201203030f2401090608060411040902070501290f0d0605190c05120411010c0515061005030f1902040b040f090f110307081b03150901050307 67
    0x148030b11646410703400c982c5120a01c07a0075504015510412021484200055403050000516040083c034140e202e51051260380f60684020340510140d201141c0e8000035500142e401c10b14024541d42d03035074000200580382c1f0811801c5521000900480c211305640c00603d1700c2802070000780700c4115403c0c0c0e4280c00107050320b00c2c1149100d06214041003890f000c7d0505200e240003c2c03a00b64480074a4558000316001503031403100391346030380000f0142c0c00c5e06d5020780c07450702255050003402c0440d013040c1d403052584003d10050680f44203940b85452030f0f004900c1c2d40041c60b0440220f0744500240e812030125171000340d507c1c61048050100612903180300b0821207204d141d40200c41601602d43c8400c03c0d4541d19034002c2c94280c5a002c1c07102040c410402c03009000240803003c00603e40601c0d2201484c1191a026207555005007001504400050903000716508450749140c2600140d0f03c40c1411a850000701c403803285401000807d0000503c952081445d14800403079640000340d0740d82e41095074411052003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 848604901 1250 848603651 848603663
    0xb090108011401120c170f07020307260f0d11071104050402010c15150e15060f070507030818100207061d04060b040303021c020601180209101d010c 65
    0x40c08001900301c102d099620381030400603241121415003c0a482402c0701c5180002c04c0d1050138500a04010100d84d04615100c008503c9410440d0000303440b0700c2113801c040c01d540320310824108241c101170400781c545082c03118443e40780d6200c603807483c040794400001c200d07509040c040441040740d4404100c401d616400100100160031000511029140082c070903814020541ca0400214009800e00c4408407461000040c02d0141c00c19243d121020f1500200801020841000324108030304500381000e0008841868654010107585111846825002003d41c080c1020000c20800c03050041c00c26944031401e40b120403040c10062111404017003046400583c000380041055501400f00306000200012001404d140001c010034291031a66104101c44000010704100f4103505124400b40c2c58041380c1c9030705640c0c0c020780e4004e66495040c040c0356510713002664501e0850207264111030701440c01820418000c0108007010300401e00301198045441d00d503070100801b540c4152140050302d54004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 848606151 1250 848604901 848604917
    0x60908060c190e12030301170c09040b0c04090213050a05010c0309030809181305010b120d0e010918050603010b06041d0901020c0601090c030b100516051c12060b0901 73
    0x1495410b6585040c0352210184500d031104001d413520368851519800340141c0041d9502d5150040009654000c80048100d5800540024980340e4981043c2a0840e811100c8440c1907210340d07001040501c519070010064520008943c0c1440841070703001d00440300c01711551135140da907981c01500e2540703121400a00280c60f05200740f0028405030040e180032607010349107020700800001340c03d0045c0783c1030324116204602c0600c0b11040000034001c07001c0c08401070307034040300e403021444000b681c40d00802c00300b00902000050781c203916442500ca0304014507101107509603070300c401d56a82c00100300c140c4c0c40b03c2c00b95007402030700f0125060600c21038040760031080401402006828103448002d0000e0728080b440d5401300300c00074551208008950103040314190000382c2c440c00c0c00000c1c0131244040d034607a026085c84424a81810340003070945a50b2815030311403501c2ea8105140081c24424034107a400704c030000006203017001a521801c2d0001c10503240c4020450035031a440d100ca254007070a500180091088 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 848607401 1250 848606151 848606167
    0x5091006171906090203040b060a031203020f07060f0504050d030c090605070c0b0406020304181505040b031005010f09050108060c04060c050a0b01030609021003060b0322080301090501060908060c 86
    0x1911109600200b802485080c1d0b4258144550541d1a02d51040072016008400e100901c1040c0141c50f0300214116007003c003183c950f5031011a18902a9140c0c41816400700303802c40f18030000000c4231441907215004011103002546481c5c010802a1019280c0b4441c030203000171110701910441c01805041d403510103606103080306c1100c0c0355004210845080e500e084001030002c40c4840500080c100503000f464999050040c104458200405440d803900c1c1000c0c2075503502025946084161074042c2ca011984000d41004203141c021031101500745c0b00d10b00800040d40900c59011182aa81074500911003660784038451545c8902c15180340340d0f06001040104070250040791880792103407040042e224943c0654a034040301e04c3e000d034015140180c440c480c40c4c04501e010425110002c10b0703810104a140e0500745e2121103400010003071039400070070910342440b48200d1400d01c51124dc0c0a82d40d242d80b9030311503003498041e03c802c0c4a9000030800700e09000c50540404120307648600400c5082030b0410b128 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 848608651 1250 848607401 848607437
    0x7060b09070929040602070e090c09130318060306090b030304140d02010207090204060c12050307081518040501020d05010e0f070c1509030903030f021204090504020604050d0b0105091006 82
    0x41052012401c03c90011802d4074a4021010380b009244a4028201031071410101c40b202d00c00040c046080303600003191081c60382d41d030000059004924032510440d101103915081d45c000240c00110003150000e9540010740a0b45a0071000903224410010b000c0c41b00460285603803809140542800306042c0455006541466198188a540144100c07240e09980784402000c80e0b015400410009021081103024440b038440341d40041f504502e425850340c40c2c0a08020504d4001030440c0305030100c94007040c2c4203540d501110580003140e040d0603184078281031401d28001d511024494905500b00341c000140004a41c11440c0300d19000c0c82c440410341d9504904551450119008903245480349002d0075000c1814411100528460b4841c680c0c8a411810068110080002c3c1c250856001d0424100743c80c03018800e03201100c4001e00301180f03035220351000800c00c1c01950042604600c00c40200b005116030740161504840059400c0c8150381c551741400c0c4440d0407a0b00607100450f02800000d12040c0d2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 848609901 1250 848608651 848608679
    0x2100e090610051201030c0317030c03060d061b020c0406080a12030c1b0b07110d020a08070c0302030d0507110303090f090403200706120501081c210207060b090709 72
    0x1526103000d524003e42041c4d10810190280c005a0781c00c240f105060081140418810824801a10440341149801106c1c524184001080700c0d00950198420801f0040707a500404040140b01d510307648030409846009507074000b44041244614186000000c4000303010070780080482d00005c400304400a80c02d029006018460400410031002801c9091003011850380783c0c0a0358441c613845595030801c1d203c0280214024000c520049e0011010b4121507a00040d16044455100403a0f13501c52013a42462511042c407540040d416028080ea0000c500e94018010541e00b441501c0001c402c000020601d80d0300d00031021107c2d00301550a00c00c60640c5040003200c2c3d4424485d16100070131043c0344684451100f0416401e101c80d91002030184000c0d5000750a002002c4c0305060100b18039032400f480159500700c908482594842c4180200c6000340c4100351084805002d403210b001581c110340c1c00d40000307521584058641524140041100c3c1c0340c5042d40c0c0380118825981c0c0c0d030312103007401d0b10005411 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 848611151 1250 848609901 848609929
    0x41104060e0d0c030c030f060b1e0f03071707030302160f030303020c0a060603140d0c0f060507180b09090f07090509090118050c120a0c030320010f0902100e0906 71
    0xb034003c000000741e2008041401b8510510000c2440c034014079180042d41e8151105500c211400c201080f5038042c002c0500c24002000c4a088080c1c100000200741007610a400482a1080200071680e2040b0009090411a8800d9086400c9a99500c3d401c89000455014400d031a40e50550100040f80c03194009d007405000306025030340c08944a50b9524110341c0c0c690300807610150001d022441d480d00520074007203404d400d0300340f100c443d801903070b1015a803009100000740015034070b1011038142882854a040310000b03080141da0f5003a01d0700f4000c10a03810006009200d03046010014a242d5030280b0910b010306181d4403610500c608050401260901c02015a9500e41da5400e500c030020724035600791240140504050100600d1460900c041091b10400204290b03000016640010f50240c0e440400c42e5010700d001001e400d4030700cac840840c008401240010943c28440301540da035405500c01c081241c400c8641070a189501801519030340c0d034044880e03174030a4440c4000f403068144111580d1142c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 848612401 1250 848611151 848611163
    0x40e0a02090d061d0c130510151806050f030a0e0f03070b040c0b04051c022707021c02070605070f140303100902070209041e0818041104060e0d 63
    0x440c03201000318107280c02e4100c0075541103031180b40c00c0340d01c10240961400303108600c0f4003400401c02c000740445d0240e80106004844642d94100294040c034030046400701034001d480c040000004029402410700b00c0ca48042c030300c1a02d06103400102c0d60300800c00c8440340c5904020040c00e66450314441c4000f40000c1034840c80c58000d0030034a2034404418001071a01c14410300d031074600c42c20903041c2110454681e40020420703101c201303c2070160f81d071001ca2220203080402200765403c04184045010415441009641f84040c40c1c22024482018004d0038400c030026030855110000b201d0390581c216455070a0000589c0083d4402d20405208000404200e4000c0e414903150740c40b1a03541e0844582c0d007a9001c403184d0004410700501409004409004003075440c402c2d030808405400140701d4000c040d000608407903841d01d41078162041008001c080640006079a6120798040c1882104102184501c074800c501d03140c1100341d004041002d0300c0903100265514407070303688072109000c103001d40500c0039209 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 848613651 1250 848612401 848612407
    0x21005071b1104060902040b0c0f0604050a240f0902030c010c1104020a140a05070c0f1a0307021f020327030a0f120f0c03290103110c0105090d020f0304030503040e0a02 74
    0x2903040e6070000b04002c103a001a4183c1d49d48115201c5801c03d00140c05a0030990482c00c10711002c10400900d0410241c1c0010b20413000030032080304180001c0840f185c443d0b10b581003034240580900c50764008039840c0d000354242c4442e04100801120018007011000b0f2800980344020f9080b820183d010300401d4180341002c0301d8846e0315059122454006011036000501300040708810000c03162140001444003000e42840e103420014088d50b1039401d45100a0402004400101d0382c038400c01c42400510800f0203904040303140311750200c020f90f2007101c8050710403958840d010101480203081040584000d8007540c10302d003803200c2c02c650000c01510450708005102c0880c4000000601c100d003070180807400c6c0048d0003290380d04090199808040742400000003200300b1108149049255501c42d002443c0c001100307502140a03101c2ea01545030030111661030034040100782800003a4114114245400b102d03840c0d4444001c0550700c3c171550000400a800500007000042c00226805030032481944c1c0240c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 848614901 1250 848613651 848613659
    0x5070507050111190504080a17191106131a1510080a0605040209060715060b0403060225080d15091a040515030a0314040b0406021005071b110406 64
    0x10039610395100719160120005a84d507043d01c039000304418120031030b00f8000e0401c4c0c680107206455592003500030340700b240d500346681203407a9404112511a034040742e00308180c805180c40200004000c2e11001464440d0001198000c440c0311b84040c1c6217544500a86903980320a0b02820302190003030460200a0450052400e0036900c1585c02681da103426a94864035150104000050711083d0348441e004c2d900c10400d60b00e03c0d8859000722800e05400500041d00709007010020700080001e41c0c0405071101c800b141c048100315040e0010510f1254443c0e690b1818200c40903840c0050007443c800804050080056114241c25900860b8007003900440810105503280c80300d0082d41c1104414102c4003210341414021803416100d15a00081c0d511707030b080c070101c40000109a403681d2814000d41070006040554002c401031a0454018000d80040d09848a0792500003039540e4000200f175404290600700040e00340e51060554850000c0d4035040e414090f0030a0321052040171102100340d030400c0d12240c002c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 848616151 1250 848614901 848614903
    0xd020411070b13031706090403110c03031c0509010b0a030f06060506130306050f0f0c0d0e0a030e010906030b21011409060105032a1c1a0f22060507050705 68
    0x910403c01c8502514180049103802056241310550080d440318060f0f081c05256240c1e4080c11394419458288481403c0b040c14040d454682c1c01044154107110000c0e0309049150040c12081c80710350054000d00158072120403590a0741d400030001600b210003443c041010494001c041c908107401030a0005540d41c0314000300d1002e80c04420a004543d084040c20400c00081d44951a400388600345508103d04101c114182c1e010009030501d14000c4001c14406081080c90780050322800145045902405039890040c051030715503443c050110340b1089000418031b009000c0e21664040c018000140d41784071008a418100105041120b07540d41e0307110102c0040c40d105075240c05a40598001c191a6241c601094034000d1001030007a443c00040d184454085844e48841400d680c080396003180795040502e10280d60702070900060300351000c0d50145000c4005002409d4002c4105560815055075450000b00c0500405078600e11907000c1d07014031002080c4245e11140d0032089515000c0d02c1e2100c552141 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 848617401 1250 848616151 848616173
    0x50715080633120f0c19080a1401031a072615091807140f041802060a090612020711040902190e010e160801150c0602040e190204050d02041107 63
    0x8003000000302c0f002d20240c5074000355450341c070030b01c82c40c5010300d400b154503541c041c20644500094244040d10000c1003010351940c0081b244030601d000545002d40e983d08001088401040d100c1d0039000200021544c1c3c580300d88400817201003014820b5600c01030041004d008071700020407a103511641000e800c207507035580203800e40c0071b61030743c546908a1f42001e88282c0d0401006500c440c80907141c0d00e044100d1030700c400038400d5603224100d40010f07101009485040f0308411120b40254040030018603c00d040d604019200c0c1030b215030707075140600d10003100c170200700324171030800003130111b0642d401041c42078503143e0410303c1401d20207000c05403103a86501c85a0344c6598070740c00500206502c0c10050000040c0d20000b5980200303d140240b01c50101c04901034081c0318180512000e240010154107425409800d25026503540f02c03000b159036a0351900000101401075072080290b80c0410119881c6080a00964042c1c800042c5120105100e65080100038085d890120418080034088180401c0d400205 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 848618651 1250 848617401 848617417
    0x4051c050703090905071b0206090d03020604060501081906020a111209010215100506070827030c0130060b030406060314060403050708070204090b04050715080633 72
    0x595034075080c0d5407801a2500c4200d401420100e40b802c010812600e5001880100181e0f00c0075903029203030380e51700101d0241e101d80072581c3d80251541718817408059000401034455402440c040040781d8a80364020384a0100900030050048081c003400046100303a0300402c9245c034a030501c44034494503007844070300300415101d2481c900e00005c24400030715601800b607582d2008842e014901c4603d0200c0c0214000c0060f8020980030300c401181481c108512041160715009a2501241300d4480c01c40c3c21a28510b080c0d14054001d0103405441129075018032265440810090400b128070310150b0030f56002e2602c1c01d000c1c0c900070b6440c0c090010b05000c0b540011400703a0301540300850500d0450911000d07804c0c0c120f03c09500350707000c2c0e0300708008242d1000030340e02400e034032000082c0d540006000081c050044078202510350208007090004200700003c5040858a0003070341d44078400220001503400d0032003110003035045803145141c00711100c1110180140040d000c1010006803d9002001282d074001c04a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 848619901 1250 848618651 848618657
    0xd08091f0f0216050a03030c02060d0906050103140f0a020405070c020a031101110d0f03020f040305060a140603010c0816020a0c0603090606050d11040b030c0439080f04051c 76
    0x18200030210b90510185a41c9510f800510080714604000316003200e0640c80b02a04009400c00920115030710340c1c1c115520f501c2c140b8000d1005850500f0702c0c0008040030b00c400c82e503100c100100c8801642d4046240c0030b40200303117405001d25201640078007000d03002c0180001c2c20480010003040050783c0d11038920000d1030080400d406128a50400500706402c5d107401210603a010041010a0a0348002400031441c090318000d44c448408807164190781c0105d400c01070460081c54200104c0305015445240b094a01c6120040c039501c0ea030003810b00302d40031061500006000c04001440340c103010540301040c1d8000f44125100043d03284c030350303c3c50303848241c00080c00251191060b000340803032401100081d040c2144e05e0004090702d40e450381c4040030011941401a03485101018207690140120751310b43c18050401e000c0b20100c1c14500c4803030003960340b000300d04da103031031300d5070303064040e04584d03098040200e612404142c3d1035500741e144203020014000c9406110709200000e401507440300502981d42261 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 848621151 1250 848619901 848619917
    0x50c0d020a080412090305030d0b01020c04021b07060305151c050a0b040b070f050d150801051005011b0309120804050d0b06010f210b0d0803010e061c020d08091f 71
    0x1203130500d010a000144401040300300f460500110340c000c411a07004007884400025a00c0c1101c0040c0d061060302d0314500c1c6d1080c07020a1044140707907107a0001012148220503181c0e5151034640030380480c0c1054540461101d401c4c00c802c461814560800c600700b844a0030340c210207115983d01c0c0c520341960803e089402c10035035020b101c00c200169110303941090081c10800030000314004020014000c541c0719030612503c80c000f20759141001e040e8030001e04103000081c4682c3c43c003038020700d800396401d10910740050a0650b0b40c22802c0030f10340510540aa2681d92a91010b140c52252094881004001d55910104000018450341c909924007a128486c09824210303140250001d0001200ca60b1407005100c1d5241705401c0c0b200038102000c1c80000d0380000040e0940402001c02c2d400500000000d00707030000000003003500f00b8005202407103600101c4551080381c5a01d5000700d042c4105c2c9100941000c0e10920300320002e940d4402070b18020201500c03000c402c507550700f41c1501c241106181400420703010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 848622401 1250 848621151 848621153
    0x1116080a021206071b1e0303051807030206040302060901110f070e06030d08041707061a031606090608040602070b0a091e0c0314030c03032509120204050c0d020a0804 73
    0x20902c0b041402e03000034004510b08590040c0480401c0c1502c10681d045908180c8208a0f51514014a8940705003c80c004d514452501800918040d80d802c95030400d1224501d81a0030b001a0b1301064235405003406041501d181d0074400c0325000418100e0500c845140050080c03a000c1042181640c00c400041c100c0c0c80c5440161462080007410841c080c0e005080c078011403540200032a41c201b41d1100b000611039080c0c2c41c41c4501d1380030790b8070006c01e480d092407030503541c000072108004a03201040742521030140e65120461800900c510035500422548001005540d026250306036003e80070744405407030020141d83d0098503810032541c0d441e0050303607503450344103002035000f90f600d1803209803215104805042c1c6039084000c903540300c011b0500c40309000050048905009448401d011241202e4980c10701900919001440400900481500444c80b0609900c50000c0381d040354101050381c164003411780c0a10014100040140f1011542000b507807003c0f900c0e510042280016540e2060494141 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 848623651 1250 848622401 848622409
    0xf0f130302040b01030e0303060d1104020408060414010204030302060f040620070309080f0c0603061801080d110c131503080a09080709050402060906030907030c03060903030b0901060f1116080a02 86
    0x80c1c40f90940c1010301d4503209184155002048a4202e8000c9640c3c480303214081c80d00035816903908265580040c004a80007420010003c0c029007d6841111042a000e9036044840e080340607034440030b00103910002c041620350148585840d08280926400309007a80f01c1080c081c141c00c4036030b90002c01d00303000048810916611000440c040c146c40c03805050200c8040c00312564078085811854801c02001000c2490b03561500341101141c2c0b440d0380e007a10b02c0d60303480c1c40c4651900d01407a51030020480605c21521900008500078860b0300c4002d0038501b01c0f0070140c0b45a0000e0504601d66100900e80d907001202080211000e4001c03d40c01e40c0d514950107007000086400d11100740c0c041c00c852424107050000581e1524207035441c0031004d071030044d1240c0d06c8605c0203140c00b82582c400f808410910b2404014460180c00002c1018002c0d201445003480b82810f0006c030300000d00c11000010503036a000e62910748540700d424100c00091048580791b0170bc85001100000d03840d03001c5440e81c0e03c250155011418 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 848624901 1250 848623651 848623661
    0x50a111c0519030b010509060a1205040c080d0504060206010b0702062106130b0901031115070b10081b040c030609150609050324040309080105040b0103050105011401020307080f0f13030204 83
    0xb05203424808024050300213041800b84030100352041c40e02141c880881c500c01d10700b409a00204030000c0c407080c00e0134207200d840c00e80140102c2071b040c0141800402194040c208407802c59807250b00401c8107a103041ca2184c1150032800d4101d030b006104100d00c01550028882e5100c010b641618500c4450900c40100420400300005c5039585d107050000c51a40e41e654040c00030b044079003003082a11019051000101190012004021b46034004500318060125400310940f1800d40c542d1403401850300c440a0070b540308081011810060210f40c0b0307000c21424240c200d82c01710340389410046107240d00da05030841660f40c00142c04280d9080c28400700051544491250b0003400c0c1075000e000300e01c0030050103ea00082074944090200c100401107804c05129889600040c14640001c01070350905140c001c089000c203202c140d845609010000c2030119a0301e800558811058000f180707004c2280d44d0310300301034004c40701c01c9511040600c0703110381e0701030510010040b44002c0aa142807041c103600c10030003211 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 848626151 1250 848624901 848624947
    0xc1506031905070e0c090306010603061e051c02210a150213060f12020f03040b0603030408030d1a09040b01031203020a0c080d06091d0c10050a111c05 66
    0x440c00700d80c6900070500114034141510341103d4038404903a034410300588a403107241e1034035405201d6a000058410342c940d102500b91039808100d528180512080005040c41c14081c5c0703944110603110800601c2002c01c40d500c07680e480601141102c4007412211691340c5058650300115403c550746000400c840f02900b046002502141103040c4502d01c0d07030301c20f58500b130390041c034043c4404006200001ca01806801d038031609224001e55481c2840e400d2002c041c3c0081e9003c54000203600b002c207540d80703001b005640944960b44011810468010848800780c101118400c202d40380154169000361144100c9a2155001d0100e42140b03514501e4014030384081c0508480c109407040c4080e0b070300039510511013a181a04801c0740c90b1540d01000403074000300705039840710b00424580300b401400700b00800c483c80d081c0748040096800c0034404c541801600241032441a00084040180c0c02e002402425041c9912101c07004072516040d0140102c80341a480045402c0400c00118074030b483c1c45500da640c070032a1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 848627401 1250 848626151 848626183
    0x40c0f0206090307050c0d0501060e010b04140a060203031306090203060901020a080912090915030a05010e15040206160f05030a03020904060b09010f030e03090616030e0603040b0c0f0c150603 84
    0x501c05172106901d5518004c01144035040e02c2d0b6095040c007009401c484060480303048078500550303681b5a644110b6001e840703050f4071203002c0c004052441c54043c86480480d02c01d9000b544c515a1000c51210349904100742c01c440d896601c600807000358408000051261804000060751486150b00180070311000508102c003c2d400b051442050111040644076406015200007810b80c440e950f800c0d0b0f820000180d503d806208a100003024003405400c00520300c010101941d03002100c5102d1207407014403c40380a50018010000c2c040c0190102c203070344907010b01440e03061103050a50390b201415035100302074400004c2d4021a01304601e00d454494100184440c10015260039100c2c000a05020440840c0f0f00916540d004000010007052048403041c5038000d04140d901c00c022805044545c03108030701a030000c1d00703c008450250600d0000c07280515000710b1040a81d0b91000c1400c0c80b240c1c0704c0081511400700070300c140c070b541010070804000c8481d51a00007242d1854000300b4540b918034410405a48 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 848628651 1250 848627401 848627407
    0x9060207110a06051804140f1618120c030516080c010806030a1101020f0a032006040302070b18040207081206041104050d0c051f0318111905040c0f02060903 69
    0x820750401c1c00c0b690820b407041702c440140c40c4140c2c0000c008200441c0700840d00351810b01044602a80a0846031042d07c2c00380c9141c0c6c41040d94a0304540e0341d1600e002e50085059031440a00c109504d0740035100c6414483c0c106d43d60b4580c0c03a070791414200300d85619100d0500d0740512043c45103810501465201c0d03c03080c6172400b40d0b031600d98002590303402e42500c054000b00d0101c132440c613603034070030b01c8003904801000086030221041494010100f0030000c44060424000b03c80e46141e03070034085521802203400d5401003506c181000e031183c41580c040740441c4903070a01c00141c1c1d070f06901c560014040c150b000d80103031602e42c0c0c41c007246200e8014004028038030882c60860b00c00b00c607010b45425101500c1d0203035039441c0c100d98640f805001d0f52400303801040d8402000600229500c150410418241d50b03541e070148501c3c41d111500c0242100704400c0203140102206401d122030400044665080c0107440881140c03541e154045422200349184000008021710701021f40c25804011485e04882c881006501e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 848629901 1250 848628651 848628659
    0xf0f010b010e0f010c06060302060a0509030f01091205030a2c190c15030e030d2702010c0809030309100206100e090712081326011505040e1009060207110a 68
    0x300d8092880f10341d0501004044840a010403540248041e5901409032940d62200f0318011384140c005007991446845040702428680c074040c0100d507000d40c0d0205802c0a051607240303003a202500000c0030400d0040d030baa0714000f031200100f00307405000c1c81036035050402c01d40b850001e42c1c10030740403c0c4420420f000d5068000000b4081e04111802c544820040740740191030b10904801070700381601490500d110105560300c1000c00f503401100f031150003003c0c1c225a030110004072010704c42440000380c0401d030718280c0071010400ca08004c040d0514002d0903079143c018403c0004912240070130b14107006900000811802280312055103028007481c808681086c504425015074030740c1507000340e1140310094000d15042240742800da0720580e01c80c1c0300b901082500e03012031900c1c00000c40d0098a200700000da00e00710070f02041c8280919200c0300300000003414280300c14080a4030590b6182072651081c212270301a40601b81c07041040c020310560026a9540850030801c4809001c942100e20800031180700700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 848631151 1250 848629901 848629909
    0x406061d072006042907081f05090a05040c090e101a090c070b0f0f07030c120c080613020f04030308040c12060e0d030203130807060e0f0f010b010e 65
    0x156015400b0302c1c2c0500c42100d545401c00e0302e00d0014103a05128402c40050104100c88000c5014071104d24121203140c03a81c103020032425071001542e614020902040100d1a414800e011124901f01f1248904100950b07aa0100300c1c2c80804035060074106555170309000c20480f0072034501c03006000c82102400204850343c280794407001e0322082240e41039560040d5a41c0c101004044180d5007034014003241c400d1810100010303142e444110122581203012002031401c0d10503440c00c901441d01d641040c1004e5603048070075002090400925010700983c00c2c0e4881c44155540221580b0b021a0742c0d5100480c1811405d2184500c02007402090300c500501131a0900d500c08020354007140d8040c82d08802c5a160390801d9000d12000e50004071507551010440020f2000b51341203036151002c1d008c102c03207889502c014110100d00003510071007a04e240343d2800c0b00108542c10090700f0101c1c0207010000309089020301c01840d109040018445580080042081701c900070321903c0c9880c102800c1840340c0881420000b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 848632401 1250 848631151 848631209
    0x5160e04050f0105012d0b0403050d020609070e0a050702010e1c090e07080c1c0c1119020307120201120203070e150c190f02040c020c04060819080906120f040606 71
    0x14004ca00075a170f1b82c10307100100c0508940c2c014201020942c2d9a15201e040180d224003c0511790710140c410413000c9890034000080000072074006104075111515103545e61009005d01508040031513494800f41c04da0490184070120b0340c40c02103400741c04800110400581000401d50041100411200c10000003035001074040360b02201c4010486d5581c540049010b1168801603c04940c0e10314090002800756082120007030300e88803650840d03040504945102d00040d40002c8000d40641021508124405055404203003003441410294161070001d0061422a00100c507408000340c0c1c1010800002d00740000003072030007000c2c000c6040c60000103040e055038411025014113004c0c00c00c113403084103000d090b05408400d00c0d1b008206019210319440002e42d2160203d440500c41c0380340900000c1d0440d00000d03941c0419040c054209500d000d181c881030000e0f0030844203103800207001c100c10142580c0c0b0f00225441000b404802c010241020300b003100444d0642c0d001083c1082e45030703140c090034054154413 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 848633651 1250 848632401 848632439
    0x1c4d1902030f0604030918020310060e0609221107030c0215091305090105010b0406080408030a0b09090f010b0406120219090e010b030d14070b0405160e04050f010501 73
    0x115460a50580c40030034a8020718030300100301401100c05020405501c60301003002c517002e9510701e81031a60b80e840741c2c000700d1009a0341074031401080b50042154a000b81f00c00c80d1400b1000b411107040c2006540880c02540c1211242c0e114642c0c008a41c2401203030501c19003510b11050705075207040074150356000d0300d1501540c6000e44242c01011030300010800c4003084401000000d864000e10034221150040580000e0780d085005509050000c900d0f00142400e0b24129100c60359001c810780c940e038807000400e91000e000b81e482d003901c401c00c10015403940d140150150909070010b102030680c000205084074048403003144030354182001005804c0a8003c0d1310155501103901028282c50179402002c0c07011580d00c84242c403030418040c5000c09030198094100d552060307090b115540058141141c000403023118100520000703103d8980841c0048465640c00f610a07000c8075020b4401d81c6032140324502c640c1c011080c428481040200b080800d12081441609504c024810b55040801221102060302d031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 848634901 1250 848633651 848633683
    0xd1a13170f07230d1e080907050a0b0406080601050720010c061b080603070312110f060c1b1f0b0a09050705030f15031c4d 54
    0x44504407002100c04a0300c0203940101c409101012181c00d00301e10180074150400c0704c0c000c0b40300d002c040070300515480c044000d070781a1050114000305d200342c40c20040640003030210720a4080c0410142c45518408002c2e15010781d090b6100c0e407600c00b006101140c001c0555040100038001c860002d04c031100f42d040b1040450905500d810800386c01201c00d001d442d800644014102007030628550142d142c2c000c003c4005907602c140c50741c1c6241c20f03d0b0f41e03a1440d03c001403041500980d229022485485075000300d05554055403005a21040100d10300002038400d102c600c10002000250f011001798a1903540100c03001400380344025004143c0304180350924052169283d1028060541e502904600035014aa10402a41c1000c090040c029001110010314521254010492207075628031080c1540b030005004000d601100003034141a0010716a480c014040040c402660850142c41c070103000841c40030059401c3c141068421003085080c802041c007102c440d541018008501141c05980c1e140009 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 848636151 1250 848634901 848634907
    0xd03051603020a09090209190f141206011a040b030108010204230325080111040e0906160f11010509011e06080304050906030c030a080a0305100806070c0507050d1a1317 74
    0x10010440d03180b03281ca0510b480023803442c00480c1c2e203107000d42d01c102500c1070624020030800b0000d05000700d45801d42d0440c04103034000d000400640f0500341c030174042000b845d40c400e410715640d410400c40541003a0401c0d52589d402280034418034240001c15421075103116480030303900d15400301003604d51114200e001d0910b001a1601107450310741c0042000140741c000b008220f23081403c020120680c015018002949588402240b12002c001460a004010b801120380e081c0032280c07419682c80004002503c144407400880e07044000782845280e01c00c014210011401e07114100b04c0c1d10010484001e42c080d80d03403503c1d90070b03c0340100020503601622015900809941c4907000000c0c078048222428560511a10448004102d01c0c1009040741504544051186072104001c90b482001c103801003030500c0d48080300294645205980b40c04800340500c0039264466121030105580324110801983c8950510900b0000b01c0c5142c0c440715404071104a4800340451a0356a00400072a1900301d014012008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 848637401 1250 848636151 848636167
    0x606031501032118141009080312040f080301170706021c0804020a0504060303051c02040b0702090402130c0c0506010b0405090106140d0203040320060103032109050d03051603020a090902 82
    0x4400d07480761240d010340300031360750755039070100f21035030303200301d41c500b4014480010b00840c40c1d40903025000a40310f55002950030036610758003611035484028026030300443d004e024007010410a900942c040c000b02c00214500c00110f05020745094080e9011408640c0721070010308030403030181d1405414038030b00d160130f41054841e400000d00c110071640121380e01610f81000002016000381c000c1071800f00c840385805075501a140c119049010f10b10480c1c01004040100d1401803520400b1294041e200801c8070450101c4908a04200c5820345010400300b940c01604500f4000c040066600602c1503143e400d180505001c045900c11506108000506c01d06061481d500140b1314140d6070100c0c503a84c2c00715180d20f002e00f03001300040308200401208a280075002c41e448040413039580d050f66050740340e41005012403a03440210401d40342400c084a0b07600c01c001000100e040c01a00811011682c0c0445c40d4144100120060081d501c1d4a90a252040019414180d00320b0740d00070454001240043e114084 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 848638651 1250 848637401 848637407
    0xd08060d0f021e0a14010801150c1401050601110a020a06051e0309060406110315220e010b010801081504120e060a030c03060b07030e090603031b06060315010321 71
    0x110780d000960084104100c0e002261003003441d158241401c031241c0e03071a20780d01c81030300c01400ea60041c1e450001c0c124100502030080e42041218110042d4a04800c0500c59070303c4104004c01d40990306900d5135150418000e507581e000034944002035a1101520301c418a0382e00145601c00148079000038044042aa01e0a00884661a2000401c101c000585da03207040000d1070380340c50085408480b9149041c0f41c036134046d207850040d01c0c0319600c144a11860000002e013002040441e080750081016007a001d9801118440d000ea4010007031102c00100e0340c4001e40b4005441100140c200c0f040e81e50200007007082c400c4200c52807070340040e0400d28420380c130202c0783c030100c400341003d03080550404000200a440c0d070b64160b01110602105035410842162110000d1150348a542d40107000660002c10b0000c151400042d11707a0400c0004086030b03d00b041840700c10844561650000495400420802c5198181404482803044072507441c6074996043d41d50b020012085800c280b400c03261014010315207240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 848639901 1250 848638651 848638673
    0x40201021c0201090312020f16020a08010609060e06060304020d06050c040e1807140f010e030f0114041407060f0f03060e1f240f0903080d1b020d08060d 67
    0x4000c0d910320304800001c8020b40640848201103002881c02e1580784800e80a070310943d20001100194a8035214034010b01e00030289494038140e81c81200e40d080042c0307000c400d1050038014040c3c0c3c0804603c040c03a00036030507a02d2100520b22400344100300200001a03994100d4450040d0340301c10002032030b441d200a0381c081805a03400a41c41d4085810034880c0380600c01d030809440c0e0110800300c0307a082c1d4481c80b038011108440181c064002144000030321b4650301801449030480009000c582c44c982144459500355121004c80720802c3d00700d801404180444000710613081c42001700203104d141c0c03408100814040521842c0010040241450b111407842900814020901500340308100d00f07041035034881c03080320800b03c92012805c91500050481c4061080300305a10050307024144c281c0103480581e80c2d02c101e01500c400700b14618601000050800f8050803400320301d1000041d1035070202c0f100740701c4034404802000030755000c2d0004214650348140369a034041c40c180d400101c070606501d404140c603d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 848641151 1250 848639901 848639923
    0x160b1005030d030504050d0c021c02040f0f02070c080c090103060513020d0302060601030b040b03120705070b0a180501031a060901091a030609060108100e280b0102060c041d04020102 80
    0x40109902d540c080d56040e0040c80c000e44c05482520035080500c00290342c034100181c8001c3d0490710000303411106c41c0b90076400304549030020744045003d9804400140803501c510702003a420544c0840e8030403c0c044002d000b40d0140210300010240044203c002961050051000a000a486000160500c012043c0c008001c0e58003410300c10008220340303806500c8400403503407280081c0c58091000707034901d024040c0307890840000d00a03200090080e2402d9000e07a00c2408181e42912078844002161201e110040c0006245070766010402e48100c1c07103144a606055120ba41051b05115184004803086030410601050455000d81e840181c44016502e00a1691011680382d9415030315508681e00c00e0001c52013400c00f11001c86007940d0b98001504d80700000c1d1b904201001000b281807020344081301c003030b40c7c001d400d028501c40c00c04e06c804000d0104442c040580d07144141c0740c1e402070816580401c0384a42004181c1c861900301400d02da428400039203000b40b5a10b06142c040040f83c00e43e4000e02040c0140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 848642401 1250 848641151 848641153
    0x6110c090c090d052b0c0b0411030f0d03050109021219230105030c01030e06191d030a020d0305131502040b210603031810020c060301090c14160b100503 67
    0x501d00a00301191111090301c4010340140c0820106601003840c642800c5c0e10013903035210b642e803603d29a1074402c84a10020011139208040d410030007201d940400c0b02c0110366070264010110016924001010307194181c1c0200b6030140107001c48050507032500d85441d44503050104089107098241e1030340010708a00c00b50401240d41804100314807110030325085058071000d50445a94501190045048074803003010490141c12030000705280c0e46003100030b83d40400e500240840d01008440c40144842180001d0032040d40c8005800e080d155010300a20040300c0c2e07607040070411490400014840c0c00c0d80c0303500c024800c014240104884041a5040d00e0141c1a1088800c0c2c450f9075008404044102520700c0c017644082400c0081d45074607001003202c2014036160408880d802d00c10f010302c10003c1d460306001d415406817006280e0750340c4940001c0c5000700189403001c60081010721000d00407201d110300d13940f0015010016030252650140f4400f00050f4824640d981e695903000310091500e400da0005545 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 848643651 1250 848642401 848642419
    0x60f0c2a1e0f050112140705040f08030703050304150608030412061b02070909150e300f0f0712021e03040e01030b070909020a021b040b13051b03010f0f06110c090c09 73
    0x407465011003d001964401404112282e442cbc9000aa0301c0c00f0790400107001480800005e00014048040c0000041c54030401145040d141e07904241560015005010b046505129a03801d00c00540152110300d150070258205200e030107880203454285034000c01c0b51168683c81400100150807800020310082c0301810040b44121951703490310b5400c06211410940304441801c080810b5101b5452004000000d056281000b500041c0d401b80d04152104109404148110000300b02000701203401100300380e000c0c0c01c0702d50450762000c032469241503001809a0040c0414040c3c009030f0141036054a811260b0840f40d5a01d0132000c50b141c200581080f40b1082c00814903020642d00000c0d6210310748080a4440c00d80c10b20321003803000301c80030201c90340d034080d401c0c990a95001e80c1d15404990042e90034444c10800310303810b110204441d403080e0300203072a44407100c0d01007144100346841e80010348903502d012101540c0740c2c1495940c2c1d4201303070003da1140b04c3d400c1c00314000111610890780000030280500c45 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 848644901 1250 848643651 848643661
    0xa0201030b030a06180302070812030402010c020126041b0b0d020d090f120201050a050c1801020c0a081005010501020105040f033506010f0504060f0c2a1e0f05011214 73
    0x170103040c11090482c0944034200010501000100d40c4a12151004030130604640d595001100d86409090043e0b06110319281e0400305412010240c0c0b4a02d041c182c2e000c9100d00f00b40c0b0307012355104418a00405001048801442811032000450341d0414444001584880c1030603047c400806450400901100b107030320600041200381c0080450b94001c680081050b5562007650300b0550f402100c01c107580403403c10405200140210100a00180c10700c1100e966084800114003103405a8000880c47e45c00030140b04070401260080701c0c05898284000d1281c0d040c2030740c0d50703000d6a541000017801c0c003e40b641000d0007200c0c0042e248a4407400514481c81c000725418100000b103c055440c50300080b0720380503024407103004104a40132180196030300c00783d0314a8041c0131a27554180242c200c0300c440802108041440481d440841102651514404018a0301c10007403280107010756045c0826030301d044104020a6020001e0701286c00070b007060403039424080323451402066804201d240c0a085481031007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 848646151 1250 848644901 848644931
    0x50f131715010603150b2d04050a091404080705120315010f08100b16050a030e100801030206090402160c06020615062a0307080d091110020a0201030b030a06 69
    0x72000aa10301d0240341ea40c030b031034048050328041058010000c07070b805020014242c10000500c1d0f061084940c00441c0c0c18215500b80000002d110450700d0380b0408070f001d2015141c02e02c03001c00200b003000d0040183c1e214105514001402c0140060006c1a01251001c1413120038071040c0702025081000a903646000b55246440c81d0000303c4403800074410b50b441551140c041d40419000b49003940d4031641062400d904058603a102002c0c0000311030300c094078540010005c0141d21361642c40380d11011407a1408006000381c450600e0741c04010030003282c004001584a00f81200c040c10019140940d0750108203440c69140a025500100290881000094800d5000c112203000d41700c0040c03040b480680031401c120700d40c010f41d11002c0d100d01070404504122040c40510030071030321080c021303242450303400d4550190a80001e1200400d054480c2c40140801c40003284070b2001240444000c18000403100009580f0084510001c0c18955030303501d200781c9990200a90350a1541c040810700c28501085008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 848647401 1250 848646151 848646163
    0x1219050a09151707020d020a06021b030d14101d0c04170a15020f030a180b0403030203061f120510270b0409051b011e020a021206010501050f1317 64
    0x14040d600f1400482ca0551000c11142c0c910304a682c02404025806d4a401c4000d5002c0541010030811181c885030014800340b010340028080820f00050030344501e00d000d444d001d0020120500350800100c00e21030840c03000d130615500e00805c0d06001c05503640c0a1211524452600800c0742e411310a4054003129900142d4150460322640c51001003d12951240b030076401031480800b000d080500c005007884480f5404a410b00c14240700c0761241aa5644494086810688050700001e030008200300c1181002044502d40e90740c04c4003442d0f0444024a4002e0042e02c4000981c1c18054403000030400a035044075080025041c1e24284406012005000e405064072404800000d00e0601d40070007460701e007d129000000350400d02030503a1035842a200700708600f203058040c0c14858003481c80d201040f610303102040340310382c207070000c4c64092000c2c010401070103103815000d0010340c040d20042c0700a0341d121041ea80b40d04040c0103100d0700d80800f00362035801c80c00c0075007000c1060002846000c04882d000070742 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 848648651 1250 848647401 848647427
    0x20d110d0b0109152307120801170303010b03040b060102011b0207050910080c10030207080a20062517040506040b0c07020105040501050d02090a0b0c1219050a0915 72
    0x140450266035010742595403c10000c200c0214114a82d03150310180075085c01506443c40c040e0503464401282d491300f80c00a4040c2c00b0500050850005102004940e8900399808034080021420f541c5442001046840010001085c0c180d0300c0d008a00a42d0003500522031001800403040c5200c0b00c03442000355115140d00c5098881c1e00d188c0046130b026102806400c090f109401c0c0605880b080ea281440441030b40d00c4505000c1550802116012409243c00341c1200a80c541d1391042c1003040f050100a4000c000d5450805600198140f11842c1c00d440241c248035829204400b0982040c141f054031542502c80c290075860141001f008208140410868030652094510710000e032207141d8506c0302070007049002404601c08102c140009e43c015405813210104507440903240640301c1c80451240030103980285401c100100f0505141c41081c0194201d010301d1b11006810304001803016a500600754425205203c070008600c0640382c480c420190103003000091040b14a11143d100414009071700138 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 848649901 1250 848648651 848648657
    0x1911160608070e27041514040204050c0c0a11010c02040203090304050301060f45090209090c031506060c061f05090115080a0b031b1e030a06020d110d0b01 68
    0xa5026100d14080d869080161540f00d00325042c02442413400b0036910002d0010b80320301701a0304e03800c9071101d86409034560641c2450381c000858141441803205440c005031140441d510180941c001240740001c0700e00e1b801c1d800101c00d00900c0d000100598024484c000c1c0650890300002c10840c0c0420000300400031604154002c0222a03520044031451131501d00402043c4845800c8000d0100e180e0481408400307802c0c00301d80014285002d10b1914600360b5040190242d403682040c2041d49000301c03070241c0c8180300c40068151452203800194942036640c200e401c1c0b0071705040200b2555202c0200307441409402030704880740e03820840c0f01c044001c01c850410302600047d0b0400883c00d0700b00705a1160403224909065040340c2420030040d180c2e04001815048500c1e5200385031200c650f000c100308d458050008a0f82007001c8201814448212603070300488540703159226012409460006904440640165006072a4034000b03091201800340140515600351000c6640b0107030140c56489842109400d803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 848651151 1250 848649901 848649917
    0x61513080d0c0305191b060f050f060a03020d05030918190c05090d02130204090204061701060f200a030e010f020f0d0c2612010902191116060807 64
    0x2210458290020102c0180003900a00006601034032003602e900c0303105420b0500102c103450000c1c07a003038070302042801070324070f0340c1c44086c100000d0714148501c0c1d82002214040a2a0346841008101001601d120003801440421132000a01400380140d80d10710301c00410080302080150f0212208410590395040350881c0725484101f81c1d0a907105030480291180c80f85410229014100244611001000e9800c03d15404e40250200001c0c8020006002c06990050b12a4141000200070024082890071011448401440715903000308604d00d03d60468030300a84908000907210740b42d0034205100d00100e01c50f039105203040540051f00e00d960b421080c1d0720316081e41c101220480e51003941c041c903107031107410584120320010321403180c00e940c00f401820380b511050040780c0440b15150070065410858140130440260010081608a005164442046d03050070000c1941d10744101c03001030001d090052031852008255014400307144958900d162440007981e036030001a002100c01c64080340007848030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 848652401 1250 848651151 848651173
    0xc0309030516081315410d0905030310120c09150e0a06150302090108070e060c100903091d01060518031903021c05030f1509130302070e190506151308 66
    0x405011200e01410510f8452010344106d001d040c40c40c074a51310f0315071607103003040500c103924028003c2c113030f40b03521070002182c0d80c0c60b144c0700c042c6a6159540241d0902d00d0000e150401140c950300310b81090f0b52030800700040350461030303902d5842c616031030340200391281448007048103283c203a80c0900304451400303204508450011a00b10101d12404050a01180900002c107400380e2040410750140354020b03140307034500000e01503124501509415644031280c1c41c0c1401c0003c0591080b0b50704010000510003008078480d80d280c2c035095420502442081100126130640710b0303250746001042100c405401c0c2c48000c1400307041e081000d100481c0c00e801600c145500740e121035540002c005003900300ca980d41420f540340c50450702e051990140c12801030960a0400b03290903903420808a01078492101c5056810126140c080c1c05c040e0560700007040310b0000d40070005200104c0002072954624000c3c0003846580d500c0004100e0380406603c08040c2c01c011910000300c00c10060340600780d84068003224690185 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 848653651 1250 848652401 848652437
    0x304080d062619080a2106081b0103050c0f0a05133c050d080408011104090e030a0c0f0203070e01090e010e060705090d06110a030504060c0309030516081315 69
    0x2a01001040b104c010008690010301c682014640d0702001c03246481000c00c2c00c07043c0000e0f5003a68101049507048000e041e04050110380c005007000c1820b0070103200750310705880051200d00610814000d4214001005c0511501c503408890901c0001941410340b070b91180c14083c0d0b840440c80b501c102100784010224001d014030315030100c42003076010401000b581080203000c41151008403c1311030050510010980f00001e004208003c1c1e08494260b80301c501d803401c0001136500c840d1041c1c8aa410030005904841d80c0000828160380d040343c00703096105401d2020a14000340c0f43c0c001d2221100913070000c28051540d8015120f8010f0a00c028803004080480a41d1580b40030746d02480804c1c01001041c10500306551030b450128003450740051080c55440b09443d2661211800c9400030303a444040204002d068803c09080e4122858100446003240d0741c040d21521450500700003408c0710314619010041000c0444048401c03022000c802c0703a507101d81e40e040c016000a410404101d06040748040404 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 848654901 1250 848653651 848653693
    0x7030f0b220b0d02062107090501020c06031e0a0b01110609280b04240515150412110102280b07050405030105070806031902060304080d0626 62
    0x28035036000000c05000d606440003005250040b070b812860041c0c900c0090b81d07a00c0c0c00380081103041081c2d55088140d0130384407010300c0c200a04000c00e020481100b03020030f076800903464034401010395550741d40c0c1d101d00181c03020204061100d4590380ca518810403100c2038881c0c1092070f80100c2038a41030300c4103680054080e2200c804030f03001042c0d584092034070000c88041c0c240c5500d80c500c0c1c1520f0659100c07255150800c0b100300444050324a1741818030494568861184224074064400790208810b0030005411401c0104250540e4403450300340f01c1c00754011090a080702c0080c1404508044188114981500d03419171800134940503020718104000002d07003d042400440502102c1f050a100e2180d58100340040007406003402c02c4002d200c007150340d460034810180600040d4958400c185040b200301b5240000c520821581048449034000c01a00e645054a4010381d20021041d02c962040643e50000c10090340170802002e401c03005c000a900c801054621009020b005440d003403c0e00a010b5560b0072 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 848656151 1250 848654901 848654929
    0x131401090305060c0a110313050a0f060203030a0b03240402120d09150e06040e09010f110904050a3c0504080d090203010b041a09160503131a07030f0b 66
    0xc0c00500015684a94130802071850503541e0a104040810a104035440c41d0042303090180705e4010441c0500803890f0078010340d0700400c009052003000c00c0c00d00074001d40b40c0c00090700d205581619000c47d403140340d4090003403101005c00e01c2000c2d03e11400b440c2040700d0714601980c0690003505d4a60741c0541702c03100032651481c2c1d003803191100721485141c07610405200b01000000380400c1b22042410283d80d0314a0000d10041403a0000312206040c15005e483c21901c0402010700406e00c1d2007002000c81c409001555aa60301c2240c00042d10f94803841c560f4082d0a2400759950722542c0d00c0e00100307103014114032200855540f010400c07840c1c1480c40c004d40071100c040c0d0f00a401381c0c80c00c1c05114010101c2e5080307150b80034405400450040905000f2800313543c1022905a0b081c0c4890508807401d0500c14045c907440060405004c1c5050b6206502802c00c4c4070203007128070703020010102c100c148900c141a007030f814004042c40c4055480c200c40c1c01001444800404c80903117060030070203256442d2249034210a1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 848657401 1250 848656151 848656153
    0xa1e0e1f030201080903120a0605130606021e0102040807060201020a1e02150414070305010b10050f071209030f120807050c0d0e03100e06040c0506070c0905180102131401090305 78
    0x1950560b0015074a0040c0180700c002c0c584010019000164011a4224080ea0303040401003209030401040000340c0c0300310307454420118a070000400885074000f59020780180080343c18840b80c60f520302600d002e0b100355007205859106091000031115415401040c58000d19901c0403020003440c0390780400000c00c00c0f40040180d20021842d1807100700a0845a00140702d014518900c513440440c050800400c1c3c2d00c01d981d140d47d2a035040b0b405060002c21008400040d01e032091503c140c0c1c5400070a030340100360014010030b81e008a4130100e68010040d0801464000d51b0311041c20030305281600c0a150b0f0704454400103440580031864070740c09075040d61820a6000041c1c000d01d40f01d50000c0703c00040041e40a9454070560a00c0b4002c400305200302007400c2d40b501c000d410203251030705106442c01260740c482402001c0c10444072004c106403800c07080c20741d11031000c082a40d440d00c1c1940f1840b40c40c0001c1c01e80322544005184050007581c006084115907030614211180c2c4040f100546003210716100190103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 848658651 1250 848657401 848657461
    0x1c02180f0901081209040e062701021c0f090f08040f050405160f14040e010e0f060a0303050c100513020901150c0b061c0b01060810030f08090a1e0e 65
    0x150b504ca0006025107a401400008500344a0403620345000001e9520b80200c44107441200b103100061040b141400d20010000d41c41e041c0c0426229541242c48020100e50942e40e038403003107144140b50442182950024010a40040c917410608203a80c000d205034461442c02c01e900080714289802824482c001040c8841d0301c0300d40c000010f442c0e01d444514244c0c10000013800010300c040e500000f4001a0000e000b1090641d81001001c0300081000350181100070116030400c0400ea81d141f140303900f0317664145001a240c106840e422850603811845008000c1c0c104030802084020384403204c0a014000c589000190341d844185800e40d83c3d000c18508001154022032001003032061140a4008402070f01120728502d42d915181e42c0409002c50032641480410010480e040e8082412a0091403030f4021125461035907440d50136440d038000d00182250700220b08401280e840418840003841c0e424a50080b450400c41c101203454458010940c48400c000d000c6005043d0304103031402d001032508040c4607 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 848659901 1250 848658651 848658673
    0x12030109020313020406170106080a02030c06070602160f11010e1507020d05010f02031e09030304060e10110436470d15021c02180f090108 61
    0x1010354801000f507280300c506504000010b03140da1060030000c241500c81d5030144c0c001041200e095885580c000c3e8455400f2038800d074007680e4045424400100708944003560307001700c0d2510300040c1c00b8140c140900f005440a095041c014440300c001c0d042c070701c035071700081c69620741400643d0039a842c4e85400d030f04000514a10380d00b0714040b00c0208402400100b1000c1c0d000740740d54803542500c0c40c00543c07054050300402032104010300070380c070360100c0802030b0010321240c0b500441003580ca0100801c00742440d520b50400700d8480c4000e00c003c66540f10019000e00c400c070030f825503c008682c414403462003a4100a01c500140d8900701c03c0c900b80300700704182c1c880900c0d03030303d07201c02070280007098071030b40e5003d1a07101d040650707090b0852101d9081e00ca00c0c00000d200c02482c4295070100d0304101c03100b4028100390a1010008212004030000b0354010140180c44481d1064a108262800300c05035411741d00c0000c0300c4502d5182c2a01c010722018007214003041500ba14010311801c00c600303100c0d0011551202c2c00941c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 848661151 1250 848659901 848659919
    0x120510050114090a170c100f1d090406051519031401110c0106060f030c0f031d010606020606040b01030b1f0509040c050a031410120c080607080901060503120301 71
    0x7107110340c044182581000440c80c00940c5443c01395200840c408031203508400d01131000d000c0400b41c04170465000d104e02c1c5902001914945825200104203c100f4070300c0c1c95911140c400d0030029100203844100d02e4641860160010903003076441820b80160308484104514080c60400490412030420325002d80c0345580d040c0e9030104d14a8000c55a540329030b00d0fa902e482c6081e01800710800c803400045803075403038144003070f102d00402e0b54401c04060620101d10012070b0000f40c030480e030405900c0c00249840d01040102284141600300028550800c0ba0001d407103540020329901500301214100f180100541c010360844400c0052127802c41850b400a026a1001c162a40c031912003608042e4500020400020100c586120b40b440200700702180d1664000c1d03251042e00801e0a40201100040c14012003200701070310359110310410311a001d20502c080007002c2e4030b41401440524110384007400c012501512030034003165181003561900c0400540e500e00014000500b451002c0050700d964217004000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 848662401 1250 848661151 848661167
    0x40b030a061a03030f120105270a0b0306090d0908160b0a030b0301020f04090507210e0322150f0f05030901090533040c0510020f1504031205100501 65
    0xc144000341c142c0039140f900c043c402040c690800450781c41e950207208428001c0544180c000902502e26002015002c81003031400329420ba08080701c07400241c0d07074002550007401c4610f46c3c0303a4142c040d4505000700b08000044494607031246442d110710154503a0801c42e512811550302a602c085010000c0003840044d0004100000301858003144031140e08001c20f017668410340410512010010b02006501114418107411002a1415189a0050034500203803040780044021005a176100c094036028420012035109000400c0610585581e04002d05048440d6110b0500c1e20212030100d031800c00d11607540f442e407040c060340380c090a1050b800340460303440c0c00c001e100c503c2c990340c0c445071840411001c000d220140c2a40704206244003d08852100c594501c00203940d0324503002c001070200050001820205403903058401c3d040d0b0648102d412860041e44041900460003481e140c1d10300f04e0b030f00498091045009448000b21031100310740510803110100e8072013014075081c034001d00c42e540c407034040e07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 848663651 1250 848662401 848662421
    0x10f0c020f1806180c0304032d21150308030a09020a0905040302211e04120507080c0402360a0803090f06030f04150f020c011b08011d0402240702030606040b030a06 72
    0x96990b100ca280c2c0c460b44e5000309c03550714003000b19805540c1c20001003205c03412000c0410140a0a1151303086640c0701074552185400000e21000c00800014034602c100d5004030f00083d0001c02d05642142c1c0c8041c450001c0006a40c181c00600030380d10160340c600c0c581c010b1681601c203000107081c6045540d070903050000100902c4c004200b102000005116560882c6182905008034060840245020345051074408800691800b0b28014064000c0401044104580198a04055041480c500d54544100818078000c099002e010703000081188480000940020007090392245035007100c17281008603d02040300c50700d81c4081c0020020740080d294041c107002d0b20054142c0868500480c0c1402c4c1c050741c00c00a50f1700c100707030754440640e0041c01c0d82000120041d40c10741840080f0b5418440d5151061009487c0c0500321403202d40820f04540300c241541840c0041e01030b00707244c90003010400100703e601004e0264402d10075200819103a00e443c3c0704400382d02c14010001c065181003961004003916801c2c0d5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 848664901 1250 848663651 848663687
    0x303140f0904020a0807020705030f0a062f030f060a0302090105011b080c0c150408030f0c0a0501090c0e09010b0307171009240b010f0c020f1806180c030403 69
    0x1c112851501c40e0700290090b0007642d00c8000b86403030000da000385801c0403a40803030700c203034080001a1400c617408181411402e400c540b01240c01031000c40350601000311040911200481170325103a0003c40950091809420b003042c2141c0d0903220032040007946201400060b52000340d450042100750300600d508006404074422411036441161100c02f040d030400d003038005442d0800049103085162030030701c06200703201c640c60460400d4104a00f041d524002d591403694179060018640c101040708000c0e002d4500da01c00e009102c19001841d0207030a03071207580b14071440b00031a2004250000010701a140040c103016004041c4c00e450002000100000541400c1c51030068000761000d070781c01c0f4094050300d1030040d024415141c2c0d18070900c00c2d0307458880110080041c038003200c100003030b80d110000f62a001c006242480ca440a14000030b0103254030711008940c042140c1c4076410100035010101c0b1b20480040b610900198003801901c01003c2c0225410700f9642070410000300080e0040511144501d1014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 848666151 1250 848664901 848664907
    0xd0c0e0d080309010c0804150c02070e09030a030b040e150c04051305060306131a07140a0306050a050f01120e1c080609060a080c1e0303070c080c03070303140f 70
    0x200810000440104159460a400803c20201242c24042d0100304040e5280c940d55a1402d900c0301d11011010110f80c04402e500c0707004440040348204440e00203060781303e106184034100550306650343e40c842d403103010100c0d0904580d000785113000c1c803414004000d108003400294114410103104d4002c0208010030004044c000400c06440300c42c001c20704401c085e640010b4604110041516014004001c441ca2490b00078081c0d000415000164810408000307204200b038544d9901038684481544405400d08000300b0501106981a04024202e403010389919824684900034403540011000b6040d0214001e00350880e4204000e45c401d105c2030944505940901c02d101003020402480034440c400012900c109002c283d241c00c41e0000d0b00044200c034904103003450803007020307180c801c0300c03089a01c9484051103265030a501c1c51443c405c001c5006003625551066860208004002c50048a004e841130321403051003814005900003d9940540300d10b00f90948810054a00c2d510075070032103961003824 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 848667401 1250 848666151 848666177
    0x50703170a021b01050603070e010503030a05070317090a031202210c040305060f2e060f0909180309151b05010b0613090c02060402061611130606080106080105060d0c 73
    0x4950f0b60020020031001041350b05050007054917055094000c0510841c44200410840d0783c0003003190018505420402e40b030b010316060513551410007103010100c141403202000700d00700340450851096403103511207400e0780c002000d0b83d000300c0c0121036130b0404111104520384003d05e1007208490788490703484c001c6454552260307681c1c2c0c14124140c40a011911082c811302c548003e00401078249021507840c0c002070314501300034078402e01c64030340b1030a01481031111400864520420004005e021040414808030702820035030262034203084004d4000034100c61021030b800144001c426903e421640e1103240c0f10380300c480d00c00c0c000c00b01c01c0c40880f40d566030b996a81d4940e48039100580b80e41c122034a040078000d49400c029030103440704600200110b42140d410003005a4074041543c120b5010b0f04403540c090708141c42d00792030712169002c00341d90240901907a0420402241c0100090303401c030303554180d52a640c2c3d202c04e0314600002e014495224905020300015040c40e680540544d9040e85005040804e030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 848668651 1250 848667401 848667427
    0x1009110d0534030b0c0c0109031110090c031b080d032016080c030706050f04050f0d05030a0c05040918021e0a0306020c031209010e0d050703170a02 65
    0x1444200d030980c000c0d00b1610030000c86030200780040c02c0d84800c842d8031035000d05030320100c91142d4000207001048030b10109040c1440716040d10410412100208250b100900700607000f40c0310765000c1211403084004c01800d05180e8000c000640f54031510036400e00741966903094406032201c040c00e070151483d001c005644c5000700070121108500b038400058084c00310944100c61180401d0509603800c0400100080b04900621000d2454203c82e0840c0c035103044a90b07181c258802d610024000b242407105105ea5596056080c901482c4198100ca49800c140702e0000d4031550011248404111b06000146200c403081c2c020901c8100130f0700d01586066259288582118a01e40e0042140e082082c6072104500f40740c08490070100c0684440c04980e81848005034110800740002061141c001c5110361418004005030f0303404044c0408a071070145001d01c0d04500908003640060821310994040190301805a0101c801080d0995a1240c0c280d03044c0c144071200d014042d0800e03058030740c200b0030b0349682c140c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 848669901 1250 848668651 848668669
    0xc1d0609010c0b0112050d0801030305031f09020d02130e090d110c0a060215090c030d1202070b071e050f0a0c0c0b03010b071a010f03240213032102100911 68
    0x41d002111898038036950604c145480c02007d06202844404c2d001400800d80000a070ba900800068050024151414a41303010350419440182d0240c00441c80410188040c0c0143c400c0c138424000003105681d07600d900d00308200f000d4031603c01039000103a140083c01c1c481d030482650031101c5021200601d80350400b1506521f40d950047c0c0060300b20796664a600450b40d40e1071500b125241e00240341000c1000e000945a003400035009050002da4411051000d006030140c4804a420240200e12464203c001030207a080c00c19055001d0b400456107044014068002e07500000039101a85003080d11800c030a07070307000c07a88481c191462500c507800010400008001580a4840011090345403002c0d03240607684101c000f150754503001200d4005100c001a45480c60081b6a003003c00c82d03d2020f804103840180100c6107492040306800040c034446600d1414428400f200d12900210382c1780500c03240740304541e070140300803800142c1000010718070501007604100307030140c007500b80302c50f4140e01540000c0c0c40340 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 848671151 1250 848669901 848669909
    0xa1d01180b070306212f060a120c02010e0f0a1101121d011a010c020303092b03022415041a030a200102060412142b0c1d0609010c0b01 59
    0x14015005032810802844115542001984c000080800c1c80c05200e0001807044c180c031500400300031408814449c4210303010200170048400030005100180da00a02a0241b0b0341522014442d800020180d1344000a0000800f90800451300040619000440b00f01e00c00706c850b4011140c903901450200151414150700d00c01032030f0f00000e8050343d15130050140f01c0c107811409040c02103140c107003030158502000f01d03026003808a4a1140da0410700d280041d081c0c00039410411139845000c0c0c28420190009603004006182c02c1030051101c6505000010b800400c07030b11800b8079545030180307040604260304a201052003180e1400301c0d2042e0080803900c3c0011a000c155803040b507046001149062008100024245c288007a0031503143c952100c41c81a03504515041c00c200070a6a4458100148020313192100c0701c590092980000300d062120120800c8040080306500d04206a10064061082d003043c0d2421440700c3c40c81c0e8044030341080382980000d1026410302410240e000000391403140c049010b4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 848672401 1250 848671151 848671199
    0x308100609181b0e0f0f0a0b0307110d0203030a15061b02030309040f0b0a0902040605070b07090312020618070f0311031015092d0519050a1d01180b070306 68
    0xd03020000810410164040c40307980651418201c8201d1901c1f04000c01d019140120b1410782e07680c0303070040102ea21a40c40400c4555600840c0c450741c8038980e0100045008004a104c14040d000b00f135104000880d0f5584141c101192216a080404080e66446d912400d1300041c2901e007826107410114042c0c039214452421156070f40c500c001028500034402c0c4010f0518243d00314241402c1c010081c0c504d1183c840081c21070009680060300c1c0501c01c0c4200340c0610303808842800c0990400d035000e036480d502900ca0248040050480324074460000601170100d40c8010003414a0610b15150310b103044e250400350b59014000e04072141e40b8110300d0b0048440100c1c610750680c000d58903000701d010454038400700c04601c1c40e1002c0d41e05281c155041d08034002e859100c410005032234890107841c00d84402132142c5010040d040c0800c00c400082a5030000c0d074110036a9410b480c140c0d040c2195a03003240e00c021840d800a02c020801d0324086040744004c240e000e1002d086c00203999441e50060102400072800800d80 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 848673651 1250 848672401 848672417
    0x60d170f0703120501060e01140c010f1e0e0d0f050405061305030f012d1d030c0c0a0b12090307081303120527040b09040f0308100609181b 61
    0x4043e8002240107203046800010070080d414100014803141102d0703541030401c0060701040d01c038810703440116020700540d64020004d03605a050480054452240700152900055840280c00340440c001c842900d0f0035140035100400d00400c05a543c03a441700400c9041020600010405440b082c00030001d2120f02c140d2000340518003010145864005411543c10364100500503000210007040301c4000c005080d054103103959070440740f1005204a68810907040c1c02ca550242c3c1c24000400100310742c002e15000e03500501068814032020700424417070203070451070401c813200d401c8040c040c80c107801c045d051003582d151024079101c11a13280c0022681300c006ca00000c4040003001488207200700c9404c17260034101d0401ca0001c5041c49691a5100c048a914062004090325681d40350700c1074042c0e1100800342e803160300b002d0a03c904004598102280454a0400428038080e03220710041c007250510340e1034042d41f50070600781040154001d0358250030340da103540d0250788400c07402c00302c070b01080015501c03044 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 848674901 1250 848673651 848673653
    0x4020f070b0f041412030402040c0e06071a10181503020303040312020712030e010c11040e010b0906010c020916090e181e07050d0f0203060f0a0c0201060e060d170f07 73
    0x4c80d6030362074081c01550358401d03401c841101c000d650a403079025404450015102500780c20590700303014103040c02540300d038000540000b04210303c0700700d07504642d0507401098980e03035826000840c0d000c0e90040c9480307004551141d42098030603411404c0c80740008800d20140590360740c0820b00c0c60b00316802c00c80b260003881c00d05c414001c0e410449500241a8540780e84050050b03034502034000341e11021040d04014912416905000740050088040330000c3e204100c108503d50703900c1c0c020504010300740c2c4103c0c3c101012a80c0340d84150130149800d500101a001d142e220240740642515200c2131800c2800001c000000f002c440301100144500326034008622000b800400150904194248902c949803171440c3c400c0040800103118019034009650500c046011410b26520300d01e0425402941485500200091000f1885040e4001c21405000748006c0c000040268203070b0f5520b000c4e695100325650002001072500407002c00c0e0960041d1041e002503072017080ea410340c5500041c0d08030181200011180 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 848676151 1250 848674901 848674913
    0x207031e0c180b0d02010906230a1106010e061f022e0513080a0f180308070b01060804050d0e19090b180108151906121502090a0504020f070b0f04 64
    0xb003100f88040700c40785501c01c00d5034001b80424181d07015030410090b04048001001e0040c0c543c1142e00300703001c3d06041d11101c941200070140c902c20200444107004031400003414008100400d401004010300100d0880d0003101c46150385030360342402108500c1440d112450f5400b024a09071810300e1000c20601d10f0404034000841542c8020b040c180b481c1c50348080c2040400d040f1000d03101c074a6143e01e003159101140c12002c540250304042d8044210904075000000c00c60700d8801080c480c5e1181c8000c01d00e60b030f600c42082d24a0380302240c0c00740064100a0203140d2851082c5c00001050600400c201c00c82d8003088580b148422051b0800c010950342c0d06031900e1645441d008030f041c820152a05840c6135030600c034106894801200451580f20808001f0500c2c1200a00340005814610700081000d969141584850b10750741c54001e441e01e0f10744142000c0046001c3c0201e51200c3ca0103407018040314039000a0000950002100a080c01c0081c03091500060810311858080c400d0948031801c1030800381414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 848677401 1250 848676151 848676161
    0x801030209180d030f0b0307080a26040b09060f1c061505090d021507050706090f0b0a08150d080d0b060a021f02040b0a0c05010f05070207031e0c18 65
    0xc2c030020b0301c0b4680400c07050b85000070820010303c4039180c0410f0408100c02d4402c0a0b240050020750b050042000c0030601460016502d1030300c030b018010090440c083c40d004520212404461015200742c01c12052000c4c840d401c008011102c1c2c007420141c500504035400ba01140c00102440d00101c0c611501ca0383c00300c0c01c500908000d000c24503030300d908002d503803200038055110f5502c4a900498290f5440010355a4100e01c4200751090b40365015501c10940c900252582e086001d5080487c4a031b441c08151980324411590070740340c0c00480d003490040c1c85032003a41e482c007004103503070780c1300011111880395500d694811080c058030505400c2e86441e0f240c1d44490a561101c101c0034060030040c818400d40e2540010001720030180e1000d0120181b007102300f400040d11603900020006400022059000e5a220660a0040c0c0c010002080000d0703082400000b071381d4083e2204801030340301070818030128030780300d03c0300f00740e01c4040380c0745036019109695034001d00c4001d80c03092900e080c0c2d034007101c1040300c090f00130 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 848678651 1250 848677401 848677411
    0xa020a090209010c0b19020f2713051510020a020f0f030303010302130e07060e13110a051809070f0801080f0a080304020105070b19150f0b0703020a08030103030801030209 75
    0x941c14842c200c00028200051031201a2000d8001d00200b088010071019201d09844140e030150341d170b00c01c001c0d000c00856200d080d000444c00003100e4190074500d141510311411480003000d07843d050200d614500c026103c0501100401c04152440d1240c03503561500780c0ca000061500585580400381c0104940c290b04214500c0c001d4840c110529079650300801260b0540703604486171609442c040d915500280002104140103110384000401e003150440603800c6052022500c0c03903800603040050ba0705403100c1c0413a00f00d80c02014450740140e00d020703402030072885060000c5800c2c5000e00d6030000c1c42900c010344405021840c48a01c100d019507003c4051409070a41000800c00b100e086d40c82c4554030b0900102c0942151008004075045a100e04100c0301407580140008809003440c4221014161410364800a05c1e0310384104030f2500d034151100f41040f47d4006d012100c0607450f00b0000121035000b060100c1c11801503d00310400250000c001d180a14003a9540c04c500b5030451041c4a102500504 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 848679901 1250 848678651 848678669
    0x602152d09010f020c1002221d01170c01200a1406010b070b0f06130218030f0706080c03040201020109050f06090c0103110d0b0f0d030305160804021005070804170a020a 74
    0x41017444034100040c6803821000d40303800060f80d036640c0356001c41d02d1104140000c583c0d802c1c020030010780e44c1c00e46048400704418541d1810241d9a07140c105c00c9020003c1140c074041500302e0b080712038040d03000b04030541c9550051500000d000c1e01c031038640ea0500c1039041003140c22900d1000740041c101c800300030090240003807018051426250340c0322024010001401090020010750004e2075a0703c8504007003040c0907881b2010b548844a520030324030b81c940c1c2001c00e00d02034801c1c280000003442c000680c1d84100c8046450b5141c164a54241c0300b42c003580014016070640d901c641115000070703001c1001d02190705000e40600440c0c2482001141402c11201c6000d04260500d006001284d04c00000c50300b036101c41010003d442d0f070b110300c04a800030003400160307548032040c50005010f06030507400c0184907174802202041d0980d104101552684001c0d0b07400784d0440b0012080d0401140a0802000700c4d43c0600c0c94642400d43e6058018002c011824400307125401808000e000c42c201410441c01500310b00e4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 848681151 1250 848679901 848679907
    0x2091201200406080a0c030f020412050d0e0d06020717070b180111030a0b040906020d0204060e040603030215041e1118190c0e0a031a100602152d09010f02 68
    0x60000d010003c0a4034000170307596a1811120380c1d074060751000010645200041d51035564850a502c0e0b144280101542c00d8003a80d05466801c502c01e031b0443d19101402400901301c03107626103410000b50032441e81140c1c004a01c01d0038a007840a0070b000390007118820964510b440c605a05151030380041c00005500b668100998081e05000b05416a07500800714800000c5d503400040000e00606403001000c2c118038400100f0788107078002a0010700941d412915000501e05540b17041c042207500034400580103030455034002ca08003c040b862035421030b028544101020800074100d1380e0900300d0282c1250240c070a001d4240c15414007800754a00c1280d14480107103e071801096408203419040c0c143c00d099a5500301c0b4603042030050031800b14110010f805030071500d8403403400c0b01c400c551000c4041c210b036212400061031f01650110081c142c400f16400391a64481200a031081303124094503803664541d4030b800915000140c19021319000c0c00340760750750106003040d1000030700b1540702d000e041c0b010714010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 848682401 1250 848681151 848681159
    0x1002030a05090d02030a060c030f061e05010315030c080307150b0901030b060a0e0901050108210f030c07060207050c0108011221170a0e120a0e13020912012004 70
    0x200944100c25400d50f603c00c61290184000ba0512a40f100010161450311042e40080c990544c8a01500d40c134001e020040141c940002c0c2007212000500c05250311308400040c4500d502c42d40029004d40e007404601090319480b0383c1c40c0d000304001030304580b41540c80851000248040c60040c42a046510002000850700e4100484c4d001c48050101403c40e521b5400480c2c21034496882580041803000400121410004a400d001c3d20b0300303100300c0a0a00c115101d07030940f8061121600e046000204503d032400421400c030300142c0e0002001c00142120078060346c40400c516000a10045203c0c1002d4942c00b51000005401102d06800404002c6071411080380020340d002901440b491496645688804907100b080720094650f680401d0740325411414070401c03104c260400200801d0120a490200088454908440c013900002c1400200380340c0c2046880d05011007803000703204a030440940744c1a0034002041c001c90064240d010269520703403880f20007910041c0c85408040704101141c0c030301850 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 848683651 1250 848682401 848682407
    0x60703080601020622120c08041d0a02031312023405120d08060117040303140901020406050d0213170709360201030e1f0656070b0603010c1215090510051002030a 71
    0x10381200180402e0000d182000c05e203008000c47200110500403401000c44c4a0441c0800f05054000c055507002204084040b0b5245040c000c001042000500184607555011200b01d58010001d00098140a0352011040007095020b0600d80301c5e0780a5200404c1c030b03014203860924014001002d801441c2d01c1840140103e55100b4101c44603030f107860b41c000d80c440304101c6044a0054203640b00407010b028800f4030316204900821044100c8040701c500308203010130480c1c0c840001c44524a26009a4003100058501c01c2d410400c20681c940189400505a89450941441c000c001d255000d04070018030300c1d96244100c54000c48000d030941c10b901c0b1038485444e41240d51041100380da1940351f40c00c60701c03003024804040004008000d0369400da6100f04503054250b03500c6030307124400c01d5a41d8500d41d00003605605050103903c001c034a0310b40d11008038042d400f41c00760040082e4206007409116800000076100300c9401600d0240c7c2e841650240d0311440e0808010007000844151000e541081c090b04031071070f0b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 848684901 1250 848683651 848683681
    0x30c0e1e040b0a05100c050f010c090b1c110309010b0402040e040f050307050a0f020109050f0a170336190312030b060703080601020622120c08041d0a0203 68
    0x3209550224142d00c0c04800030301000d086810a41c0c1020904045125850340020300c1c203105030240041c0c0745100d0b04c0c05190340c20b0343ca00071005000304240d0401005001c0380070009054241c503680035a20041a00d150160070764040380425685000080144042500c0c00c3c4200c2800c800112000c624003403406040801c80710008102501d1700810102d00c01c00d01905008a5440315400420313200031084a18007184001d0aa07901603000507202c40307000ca010304001101c0e00009000034005a120351402c00c1c1e04440041286100070f0034001403101c3d0501c42c0c69080356080b540f80b141d10703c61800c46545001c9142c4512511010b1180ea4401d441ca0030004400038518150381d0010500c900041e01c4841c141c0152010590b8580c02401c0021040c0c02d040d0b000d035032039000354000d0f03003601e01907254000a01e10114406400a448001c0b922030000060301c0c0007030030b480d041c6080c00d14001052641e180c59041d43c100f503014401080503152546010744070098210791140900700c0842c1182010301529880b00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 848686151 1250 848684901 848684959
    0x90317060607030905060a05040e07031e02030f04060f15060908010509070e220c0e100e1509040c050603090303040618080421210210050403020a20040c030c0e 70
    0x9030011f501030499108004880140480d001a003015040400000307005004000c1442010424886886a0a45217000b224051068640f805040e5155600c404c03005025000710051420303a2001d0040000d90f0700d211a0000b4034071900c41000003490b0103109800c1d244002c00d00103640e008520203000303e001c036505407508001c00c03500707064582049204a14101c00340c0d51b4040e00c0018071400c0026141d80400f8620b10a0288040307401105907245c2030601000d6098882c4140c02e4444005e450840c10040c1c1d81d954000d01941840340e0040c0c2c0c403008105680e02c00c0d103070b090040c0c0001040100b485640c1c007848010700131050a011442c1c50320744550141d40224040c180607407246642480c0c5018013010982e071141d4018400c02c41c6003004042a064180c06811428054084c0868101c02c00b1000d2081a124680640240a002c40255106841440205160709214a108801c110b8a4546104803a581c4001d83c5001559084070b42010700220381c5520254419103500c0e419142001c0d520210641c1b81d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 848687401 1250 848686151 848686159
    0x141009110c07060c0f060609020403151413170d05061e010905060c1609020a0906020313092c03030103020f06090a180b060d02070204060f0e04020d0201050c01090317060607030905 79
    0x204203203140c4405c0c00c01c0c0d404405004141800c02c00300700710b00185d0003402143d106d407160050b501c203d003505005a4103911801592103251038000380b84a151112030303a40c01c46c4074540c0c80214246603010000f81c0e070030462001000580c2c80c8100619410880010401154070b05100109070400e007000804164030b901500d4000c610100b030b450800001003001d0003600c540f401442114a4a400d0703100025001a003a030700c001a621040040e041b030001c01261045050021075140301420520b4490140c450b4031020350a000515440302d581c81c500c004d40ca844ca42c140006541e49525600400100d2580d12000d07520503403003000208003a980f142052003c0700c0101c5800701958443c90302990040003848a003e80244000505044c80308a9500400c3e18920890b0304200c01602e4440c40c2e0080c080b01e01543d42c851050368086001351521340510f02c90144145499890040c4021400c1d007034804030041240480c80410204a078a200030350358651100c020380307a4905000b810b440007085810144186409 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 848688651 1250 848687401 848687417
    0x2603130b090d0203011416031404020f0a030f0c08010606050306130e0c0a06020f010c0507030c200d12080906060303042601140106081b0a030f141009110c0706 70
    0x10b803100b07000c00e800c03160020000c100e8040040581d890b02c050844840303102c2003800d0804c0b072040f4002d1166a00221103420244100c1d55035900b40840305080c60b00b40c59018442c00800000164203c00740110a440783d04264001e0b0320b444821429242160045401d0100a00c100002d54844951026089035140b00101740420120b1150f0700740001c0c00941900100001800701d00f403030f000254009800000c60081004101c2c0810480301c1d4041d444008000549001c040e1020840d98544d00c880032043c04544509000b0403800070344542c58508080701c0641342003500090341c0d81c01903401580203034000064030040c545503002a0700c82c07040b8018850b5141e0082010203d0702611800441c004140700003c108851000b901110751079424461840018441d82c0000c542020040c58000e006000501c0181043c8240c4400e801410044806884c500e542e10300c884190b100401045004078481d80c0c44040450920300d028041d05c424440c0040d400c0c8007000011500500029034000312002c0740b4040708 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 848689901 1250 848688651 848688667
    0x120b0319060525110c0301140f09031204060c180e0622020304060209030d02030405030717030d1a011709030307050702030a051515091014040609062603130b 69
    0x600903241c0e814008403c0902801c5600a03421110b4105024580300850f05a406000101401d94249024200c10030141101140783c141184c40060781001c0d103032050b6810b140031441c202c000385108860542d101a00c843c0a5401560010900ae04c507010000da13035003042d420107121400d0030301d018142a00030303515944990120381011008031102080c24200b0340d582d0600b400e00c00040e42001c0c43e02840780c00740001141c1c050340000b044a0458401401420005180680008407075000301c4081310640001c10405080d1346151040c90b1010001d8000d8048585440c80010306010206100c480010401340900203881000402c1c2c0f42d110581d4a0103c0e660030b8184007103420000b4140d8014020704c4cc10b0300c0e5018010200c0380417449541140411040380f40c2e4201009405103058510011041038840144080320340e1100c03040c07650784040c2010070340a544042160880d401588000420000c243c5064528451290050a5414180011400c1c0484082d000d006071030b042c811021050030010740e00d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 848691151 1250 848689901 848689921
    0x1e0a0f1b1209030204020f030a180512070f02030d020a060b032b140c060105011b020d0308091f0b0f030106031505150907020606040c1b080f19120b03190605 69
    0x201c007851380a4000d40d240e41c880c1014000982043d1810500300303040031508515401c1114034064410f030000000d007418130a42802006075408402c041c1c503d1002c00d503115000da2402c011495a06c42a680100320032121800c00104036101c11403814880d4004c1d411a0080d1040b18a101c2007009500110a019945200c810340d0405a0700c000992840004900188000030201d141e90483d8000e80780d000950f050207242c0c001031004050001e6129019180346c90204e071091142551000303e4100300c0754641340e12072a2140328201c2415490b00d8035241c0d87c500005041c90700034100b403820190000e10406096645040e40c000301d13240310204c03083d42c45c80000c2c0880703241401d0fa00c261a000d4504015410124402901c819003161182d0240d4203010700c101007280b0840c46000340d0064400003040d5443e90ba95544295030180c0700351410708500344441d0100844d04c1500398132070500c540312555500b03614031100c4291424407940c584281c10201d048094622031103000f0100550000340080c85d0b69500c1018 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 848692401 1250 848691151 848691167
    0x20105030907080d050d061d01180b030f030c070f0302010c15020d0c110c0f100f201e01020403030f0c060f0e0606130b060a050901051e0a0f1b12 64
    0x140d003d48940240d0760400f60f046002403404c85c6c0d0740d2030300b40842c075240d0b040b112803000d48059075498803c2003c010455451844103d0070400c2c01110085501000b00c0e000070300e455904d1a10103025040010503016040c020000c0c400204480c020144007640b079600042c006552510740580320134003000000890004a1b0b045401c00d41c0d20090800510028800042009140d41c3d640c2c0101e02c80c075000e038900b40c68050a0210100401480013082e1260503000b144d101c0038849040c001d020006149500500c10b00107285a0140c5543c01441d1030080b41d0403103d0391401c0b000011001c1d074410072060010a900007030103918840d0608007540a910646841401482d811481103103151410307507041c89a420204400e801008102d42004ca402a010340c114203c07110034040c194850810032000200c54002da000d0221614141800340c100f1b001031441d00c110750451401d0310701008002482031701c583d070406040170f51540c40d854144c0c0c541752000304d2524442040000a4880380c0d0b100f0016004500c61140c0d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 848693651 1250 848692401 848692409
    0x5090c0a1a0a021207030306060801051f0f0201021e090901061e0e010c020d0606090e0c031f020f0f04030605100302030a0b27030c0c010305060907110c041d010518030403020105030907 81
    0x590340d179443e032410001c00070b103020302491000540c00000050240b40100011282850418604065a0400001f070701c1441214072003005554007406607405001c0c038141c00200c3d8001c0441a16a9110150104241840160031010034068014130740c0d040005200342e11000440bc0e13007401c0d00302c042c40b080180c5202200034002503119000c1c00c5031004114058200310700b22400720000780f1400103890416a1588443c072091901039100c008010780800050440c010b40d208001c0d401858840c078070040740f4495200a0b10502c041800141c00c10802009104555020508a900750f8070242150300003501c0304107201026041c03502a40c086186e10303210030104010303008040307605000942684441600c9403c005828166070054080504003035000c0c1c0207142c8100002491440243d07940314080d6044070042c1441407141c0302d002c0b80c8408545030380c4603000c84041c210b907100f15204011006103007913900040000d40245070b811a480701509000080e60213481d82401c1040c1c0f25501e000b0a90314045071034ac4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 848694901 1250 848693651 848693683
    0x405010812031f0e070f020111040b0a030506060c030703051806161118280606090e040813060801050f12120c010b0a060903050f060105150a05091305090c0a1a0a02 72
    0x42446044c82d00808480c80d5200c0c07d80003442000e004603801c80030b40c081c62140e6124500304011560401e4802e620003980082c2c001c0036141003103c0d0100d42c910b543c0101008a0101c4d5002403c0c3d40403001c021041c00c0310900c11238440c0d29007401107000300b242406d813100c000d0031450040e40d0080c41d5907802c1d00460038407410308103c20091805c403c0d0380401e4007102418800760141d506003909500b00d03d0042c1c0c801e903040c0340c0340c0c00003181c5001c07420992032000402c01d58914a0500222100a403102c11410042607550f03607511007541000704110b241c0c42d48001c0e440c414200d80b4198040b00801145181d19110035040c07598840c032260010340e01614142d1100c41d070094142d0380201b00c2c1c0d9003001c800001d40e40604201c4a0403890348900369610300b000c0c040c4035800083d0a8001000003a198002c110f003041c00d00c0d28038100171030140400c864a10b04020f880200c3d07140c0040024074030081140094011046401051181c5401c07030701020416003100d0740000903000102d0043c000d008024003240a509a1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 848696151 1250 848694901 848694929
    0xc02092802090a091803111501150807030e0a110a030f120e1008010506090402040b0a02011a152a0a0f0204050a0e100f06230405010812031f 62
    0xc440900a612010300d10f446558980307804140120305205070040d4800c02003400c119142e003070300d09603181c0e0120614280544a02c044210501202c10702450080a030b42d8015650300350000805003514000401c400f040510b402440f410700c081c001900596660015440240f141d2004046407a1403041d4101405040c00000d8100070030040c1c0402d003039090895503d15400740001420082011054800140000c484000600481c98004004c0c4400c06005000610b0990b071440d81c00c00b290040c25012003d40d6503102c03d00182810890134042c3e01c0c100301e802c9802100c0b8854242e00a006000c150003510424030b01c400003040e1416101641403441030200c6220b508585030022810a145000700c0c040c47c00c12004c1060044540550b034035802e0404090404d046540c0d07826002000d0341e60b0a42c200c0303620707444001027105118204110003d80c1c00780324850404c0440500c000c1d6201a03101c0c0d1301c5c99000000001c6802048020780781c00140a0600700c5100721a4040c000c000182d039000142d0000f054 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 848697401 1250 848696151 848696221
    0xa050303090105060f0a0603050604090609050c010210060b0f0f040302120a140615060a02070f06050717090a05060c0a060c0801140a05220608030307020d0912030c0209 74
    0x80658070401140009101650343c020a0001001c042e181003600104041402d0025078040c3e00a1544520080c2001405401035216102076488103070040d2650340090306602ba003540e040c4840c401140d00e13078005201a07440d040d8041c0e6103201d4114a40c43d01c50000c64000a850740369405c890042d0703001800b21614035083c850300f44d16200742c250308130b420b1008005040c03061071001c903410f44155205010554001080701c28800d0079801046944118003c2100205182d1503050944005d04400d0b620240c071a40e26260035a4107202009640741300683c01e01800e00b0607510040020166070b410781c0d2140d02c420b4402d00b010724112074213100600b824203041e000c002541e801134049040399060a10040c2c410ba0b0f0a003444a500228000d40c0e4210580075014080445207200001e0205032100300021300a503035188150454005a88100050b0000152615042d6020380e10340301400c104110107012521030f9802400840c0c0d2450000e0282541900181110400500d9418020264900c450054041d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 848698651 1250 848697401 848697403
    0x3070f0c06050a050f090c01050a0c080d052a0c0c211c090b090d03030e160305160602060f07140c16030302012904090204180606080c0619200a05 64
    0x21640103017030074543d50000ba404000007030652407081040c3c450030b18101c00c2c0c400482c0e011200b02800c1d0b8150004010b40401c00080c2c0c4103d51180c1c40c1a0000380c0744d8000c2c01c02d6024082c0300081043d600b96000d0049001400c0f010640c6032006004948201c140070860f404400602e81010040f540c5008005d08600c0684826200c03c2c82460030b40d40d201112030720f03000c40304c8581c010105500d4008a801c1e03003031030001e070086c0c1c0300720100700142040394200301d06507840200021441d041210a9000140702440c0740d0904a0180c000e0704283c00680030f546400a55150b580310001c10100030403006402c8400360034050000c0302c5100f2862700a54114240025170015240840d100440056181040b0031384800800c2040c07003034404c0b100707141c41094000b000421029010000c1c09a07400fa83d203c2d20f16142411000c9007242c814411900031a90a14040c80c0f1810703e45002d8149008100411a43c99029400c0ca04642004070905102424480c1180c80300300c1c4075070715880c5c2d021620030407400c01e0034400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 848699901 1250 848698651 848698661
    0x90506040b010e28050919030c02090c09031f0f1a0109061b0f0c090216060c03060b2706040b0705010e24040615030803041a04020603070f0c06050a 65
    0x2140f0140c9000c00d80303d62001203507242d641240328054146807400340700d84190700c4e009a41c0044d45c80c400c980740c400f640b40c1038a0301e100300007000324003040f0000316640450070205555503200e1381031800241840204400301b07840e0300f452411b260b042c0b4000c040780c1002c1d51156004801041c583c910030403140d41072500003a214945c5102060114074040740c00a9181d201380446481d1100700043e000b0141c40a40e903521001c004031400719551664107601054610440c03025000301104e0207800410f040d40c13801d0440843c1e01c8603082e01c0c209410620244585207407002120a03542483d01e104080c400c107100070b00c0712644418501035003c10300240c0040c0c007414100180016038080d0008110400c1e4000c480365481054407245512502030703004080d0035000160782d690f031050040343d010920115801c079030400b448964004941d4400003005010500402c0f00d010b80c0821101801c0d04c6003420700740c000800c02e01004185408001c4c001079141000d0703204445413841780e42c0c490014865801d1940c4480003420b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 848701151 1250 848699901 848699909
    0x10e0601120501030201020c0f03030c030a05040f0803070302190503090d0b0a0e06130f03091701140105010318060510030501110a080c030c030a1a0621060f0f06030a090506040b01 79
    0x44003000700103009865071042604881d8160014012000070606000c5624815080389a15001c10302c030041e1940000d0000f00f1480c50159200e0f5604c0342050714450341d194a07034000700c3c91544180030100c00070b0340002e001c540d00080c1c0c1c1c4041c107460105150051940c85480c1c1155000355104054004000b01c10460324042c0400c05810b0090301c90540003d0741e5039004440720243c00c00c085858a000c00c1281440c41010350003442e12041c040d0f21040307020322080004000703140703a81d951041000c40185526080380901000d01e0140415a41842e200c0103080359134401409480d0380700c010401c00405a406a8000c550140080c802c02c0c40e01b4449203c660000310884c004903840c0d0700007454808414048030310807905200c12074115110f40410b04010071424501d0b0b0502e20a011504070b180d510300e00a4045007411030400740d030020035155413404030b02000e00381c240518000d100a4403a90b890808402812409a1f100340c0c80342e90320300106015148030003024005002c0c42c4d00384000c1c0040c84171700906172 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 848702401 1250 848701151 848701157
    0x32a03040c060503191b08010b070b0f0c070c0f240c0201031a030d0302070611040503060412021528050129090a0f03060c1803140c1009140d080405060f070506010e0601 74
    0x1fa80e642c0c5100b004074821281c00901840a04000440700418101c4040c2c00c8207421040b20708050283d0341d07600700ca0380c0c0d0b90410f404050b5042c2042240c0007000070000008031b0660441301200d01b030094050030b000380d02100241071503121110044101101d201440041000404a078901e080a0001030001d42c040102517078000e050510a5a0190304a0105d40413208090024402c7c1da4880c0c880181c00240390190702e0850042604c61046030740d2100a01c0d0091514590198404150007a094070a0080250301c0e000a0708100040011604c0c20019844405411010301000c4c1d032070501c018041d11450707281c5540721303840500c041001e03c45800440d0580303115a404112100381a00309039001449400c051036a901c101d401400010844820407031055000012161180c15680018891811404500002480c140001c000544009040f11142403054810500001c0e454a803100d4910807405480e004560004000b0320701041102220f03005a00038050712031958444441e06403811054a2103800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 848703651 1250 848702401 848702417
    0x90326030c0418020f030403050d140a050906090c0112091104181b121502090909010506010201060b0f220f08010b0109210b0a0e03032a03040c060503191b 68
    0x111400e601c22185c500b0402122079007540d80d540d604446c0c1d035110302100525140c942011904041d844150507008201040c004034043c5800c0100629241005001c13500a9000c0e8403246031598203d07507444003541000101143e00c0c8003506180504511000c00d00c0c0e0498906a4441e200e00344240d084510503102c1c0e6844840210f076001c50040c07160305406001c1e44040c100c40741c5070018140000b1030351566800c030401743c10f20b00b00c0c400044030007000300d6080d606030b5110010050150b80c20b100780302c0074000c0507450600b0000e601400801794040c20840c3c5c600d910380b0694a2201c1f901e0102c22230010000313200c601002030303200c581446c00f9181a01006001c20b108502c0815490320030108641001141c1050607482d091030384850300701001c09802d44e010780d59188074400d084507003840150702c100090b566641242e00e52122081c01c2640b18110110007502c10700c2072000064400703041608499061510b00d4403034031340c40001405401040d4803040c91500e44100c840280c9821124000889100d80707889407 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 848704901 1250 848703651 848703689
    0x1c0305070809031606110a0e030d2303060102010605030303070507050d0813020d021518030601050f0924040c03150f060c0303021305090c2206090326030c04 69
    0x140c640320076100012150000d00101c4c0c1e50881454802e24070034024140421040300031501d80405a20190700c110018464450b402c42da81070402042582d005c035480d0000301c9454580c2100c0044006c10032202100c0c4002003c106e547e80b00750408009000000e050741c0d5603040600300900258401c85003140c607406028000c9030864056510988a8039142110240c2004681e08010820745445800c991105074411005241c120603c0a0300103410706001802c242c524100c20103290450583c011441002d1100884055491b106026a0040c030030352610720120085099542c00c1d100031000540d0800e2900c011142c103da40340e0071410340c201902403403c0e440740d00c80d00c001c402e5503900d000310004200c0c03400c4a400024071030b03802409242000108403050907218800104000d07410b40d48000d5070080800c0c0a803d492100302c801c0c031102111100f14182074544400544642a14800580b1140010398003003596002c00d40c0c208200e00b02d001c030a640ea0720740390503060700a8005000c2c032600c90941d504080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 848706151 1250 848704901 848704907
    0x61906030308070f171503010509031806070c0308120109050f070206150112060e0f0a022704020c01050a150b03010b090f011101050a1a0603070816020109051c030507 73
    0x200980750959506046540da418065811240702c1004004004940362404a2000d859010900801c018811017001c20784c0c1c14200760a481029183ea40e40d03800c10482e280b082c5481018101c3c0ba00e0040ea0300fa03442e0b440c00d05110900c0b8610f60b1010303005c0d10001a10000d200303c5603000b00d05840b0090070030801901c4503030709100c42d49401c44146001d607001c81c005c02d044104500035040c10400c14505001d004100b1080442520610b5200c50510150b07441030200f82403094918950206000a0460901c0840500001c02c0000b01070100c0c000d000d901c1501d89940ca80e60115010108000000c0c4a0760400c040314100404c0c01a500c0030346400340c14030100d42c40c8c2c00c003c00c69040350701c06201c0e0380c02c140d5507a040080d0b607000e070040e9030b0510040703520140700ca46080c01458440c0e00460b000085130350740000d22000785a494481c1501c552820000c10404903003140303106400c09100d00840d0b9140340c242d03100364010480c0e04405403036803240c804100325102400407a54141c800c81d55040c410b58071501010303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 848707401 1250 848706151 848706161
    0x111606030212090c090c1312151b0504051512090a03080106030905071a0408070602100c0302120411042903120301080d0c06140903180f01050d09081b0619 68
    0x590b001c070b44100454121b0010700042d2407001da540c012104000d5548a0620400d68821021218000424000f00210002c1e01c5000307204d070201307050008060305e8107000800510481c00b900388600721040d4410400c15201040d200d00d50b500b12004100790601402c466980c500501046000503040c0c1e0021400611071b0240c171040170380c080300a0102c2c5040038055603044903465424007280b4418480019803000800c600f0000b000e0070703005031141d09280110141510580d41c00b18051600405c0079200c1c0301012440c499200f5040071074034500303008040015014007222003655003801217245e0002c105000b45e022800d86c0000480844003062141e1040484074002481002c4054005000400c0e28600410722402d002d80305001c00911450f001d0807241c6200404e80340501c10b81e1010802c0071210500d101c0001801c001110201080042200000d104c0d1044c140041c52030b64840e07a18600308200341d0159140b0202050182d440c0403540341000d507580340c0031110100120b9446007005200c0d0407920030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 848708651 1250 848707401 848707423
    0x91203120b032103090a0f0f030807140304081c020414040b0a0807030b07050903160512070e0109110c0d08061302040b040e07020f0109030e120313030311160603021209 74
    0x296902910b9518082d43c05600028442001c034010520391400250205905d400c1b40340c442c100360f1071a0315180c18000c05182d40242600e00f4403004510910040600c001620740c040d81c41645550b0310401103c038079601e003034012054101c440c0013284c042506042910100d1100509070b80070425440c00004004041c0307081d1041d410b10380c01049080c4042107035515020b51084442c00c0043ca802c140c00c0c086803a003a101e044003420303c4200c90007030080380703072840c00c002c40309044000410b200c030709240f2900b071450b506108004c491a070314244010074500038010b580d06415610261200150307d0280504012403c55003240b083c0700400c2002120703212442a17a050300c94903110241080d003414594405041d015064409611600500035141c440c24055240c0f020302c640da03401c1b4030f0b0041d0303002e01031101941814003c2942040c0702100010b021840034000f140d41501d0401102a1a0382901e410b040900601360341d03200103c24041452901a0000c100c90300d0001900310040d99101100c944403c0c0c0207003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 848709901 1250 848708651 848708683
    0x2a0615010e0d020906010c080f0d0e0604020112180b0411010e0a06020a03080403030204090f0911120c15040f0e0106020d09030f0209091207030201090b090712080703091203120b03 79
    0x4250058201303d070070719903c0041810218140581601d03420401d400801e0a44066a00040d442d40070840501505030081a18030050506080650010301004150f003c140411a0740700010000042801d00303002005421000d1f0541c1404c0a003000303400201025003113030101c2d02d121024003180c1444c4814600300c5056a002e0042c0002c145d800b200e00c00405001036003090740901c40442e5204881c4603030703650f00006c01e500099031000382c50560310001079030007220320178000c41605024114012480c0840d07040e04540e0201d4064140002800c40c0c06560040e0b10351810f070390030200e81c0c82c095030708040c1641e042e602140d0001d4544981121050814000245000100310f00c03180142041c180040c0c01c0750111040e0784400303403d0100444160804c44054006039140c4003d4400d04c0445000e40e41c0068400303001d441d03006c0c10000c0d040395554205000411025000500700c05240c803400d0b041e0b01820307082114040c401614200203000710f45902e02d201444c0c0c50821251600e00c3e0024003214840030b004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 848711151 1250 848709901 848709919
    0xf120c03031803150911060906040b0c0a0b0f0709050a0b0405040507030608030c0c0a050a0303020d081504060605120a141311060703211406062a0615010e 68
    0x5942100c100e03000c6060002c880e05480c00110008134a03003004000b504016000140c440d01c2410b01070b2803482041c0800e8080d8404008140542c1c1f200c0040700c0507548503401195640003000140e40ca40f403950f80003c1c0042e440740d0309000900683c0100107014921a5503088900e03034444080212000881c460460b132100c080004000a080c0358104c254420f4807402d001964680c0c84100034203503402100e030031400c0d4104002e0700c0c0c2e072481c0521000001e414151441c140c003a0131a03901035501c2405031014003d1216403c00541401c4800c0e10490310b80c84050800e100d62035076500040c245811021342400035014800000c1c248912030b114040080064400d000416204c0324010800c0e109452400e54207085180310414a94480c0300041288500c00d80c1e640108000e61880e81c403a0007400b842c1c85c0201424034020350042091083c80705d8001034201e43c01c0341c0e110300d180a0060182070709009a60b2003000c0544c48900d201e0041034a5104030821045100c0d00060789004441007805a60780aa01500403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 848712401 1250 848711151 848711153
    0x140306010813050601080f01061a040b03060d050708060a0b0d0b0403050d06030b190c05040609090b0a0e0f0f061804060207030203130902070203070b070209040b0402061c05010f120c03 81
    0x500358141c10181400c1c0310000b1035400d8507030604101d002d0f041840150f02c03105a41e80100001d11681000b020301c4c4140ca0206e031140f00080142e0f01ca140720340c0404410203c0803c11558510081100302c6070301200301e604855642c0d4030941c9490040b25403020740340c47d007070b04083d00b810b00000d00b00d101c2d030740000d007410346980e655415101e50300110100307014199103500100010f04011801d5016031199400b8003229507013064a003003030740c3c020603162080200c1400100006600a00c000064804200300401c0e055001400f1070945d4195500032400d01d1459020710000701007075801c017070280581e800d4091ba9651094144202c00130040301e04003407104018001008141d42d9030141500707c1c460320540340352102a0443c1c9200e28881e812001f0700580c001066011850104012002848040c052a08140e01900010315000c030007400a0f098110520000302190b45901c200c40e1100e03a0080c04007205607c0358803c20040409025581c41120300100109510091105802980d5401100008080d041d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 848713651 1250 848712401 848712407
    0x20c09070306050d1212020a11060601020d020319030b0a03030c260d0e0c03011e0e060c0f07030c0602030a02120105120303070c0c050a0603020a300e1203040f030f14030601 76
    0x3640308030004100c01c84418000c01c0d00140010404840230350380340000c005204503400d09002010342018159445000055044c607004000c0c1c5441e415098424807a17180c40420540c00703000f0f120034140d8440c0d0030342c001004054100042c4c1016500480c1103500039045003a1b0040400007510302c00d10518028848164070001a8000804440048081d1401c42c1480000b003825620a818113104038645400540180485486000c90100820006014074103120030414460b02c035070201c4034003d9030002102010300d40940d40031144260303c00003c555901d00308000c40c0003508070511062801400340c0c000502407524a40c4c0208a901610142d8507545511100391440b00c1c06150846100800c030100144954500b1040e000616aa071005651070802d014014040f4a610144c503800d050f5150484143c442541c11962840554a000045c282d209040c1280340462160074485000c00c0082003204100102c00c500e40000d1090700c031070292000c583c1c000e8801506114180030100c0050001a42c1ca40c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 848714901 1250 848713651 848713673
    0x90b0d1e080417060414210a1806020d141309050415020f090405070f1e050d090602040e010501080f190212100510110a0b090319020c09070306050d 65
    0xc4640c45040c03800707543d80c075440b41800142c1d84941c1e0941040003040280320810b1035108111402001400c0500b040d020b808000421001202c0408000404c814622a0040e001c1c5514150702002000034260358150007591040310300001070000304426a0000e042d124a81502c61740108184a000064106403c5c980108401001698008035031481e07102c1105052004160001030101400d540d81050014001940c1e800b03082e010400c80100e11294400350310202007112050701d482103502d82016464100c1d03140c0103050302d641d8881e18090b120010807189900070022034105480c1a801d5a030b0f544c0064230300c4101200e40d41c44040610001034581483c4840c1044010001c89006013000d99040d8041401c03801150180a0101c11030706c2400300340742c01644421202a06d1402d0380310a1601a1560344840ba40b00e002810030b6490400300751410818425901d4401080910444e50054044003c1d85c940e6040811806180008040b5410500c0b900400c0181c0700050b0940c80b141c4000e5864034000d171 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 848716151 1250 848714901 848714903
    0x80412050a0210020102030708010e01030213111909050301060f06050f130e070809010b1e0d05010e031204030306080105040206040302010c030e0a09200901021504050309090a06090b0d1e 82
    0x40a0480c0700070050341e42043c4480c000100d0f42c00182c607480c11200160401d001038100b001e03001c270f0f00b5004100581d81c4007545d840740300c103071a0040f907503030384201c010340d440d0052040c0e0031010030040040e80c0d60541e100010303000b1620120000c0c401e40359513041c58907501d40140036403000102e080214180450ba103500400311075850300f284544560740c54454901c0040143c684078002480c44c0705000d07400b00c2c24020041d203007034100e030500120003104c120158100c140041e480d000b0401d04440b5018080c081d8811440d084d007030010b69640c1c0105041c0702a403183c1c219001c9001ca40b90510100e40d0010520170503100e143d02500403032500703095400540f1100c001d140c0480407c80b240c0542c00c2c04e0380b503080c2108010040841d01091b508040c1002e0306801c500d0106000001b40107100111140c1c0e800513156a214501c1101c21040d501c2e1410902d085102c3c0c014442e40182b40309060144640b41c1d0b502075001c1f00c030140d00070480d032030005080004107143c40f07501410803200b0300401d05140b100c02407112405 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 848717401 1250 848716151 848716153
    0x90f02010f1202030124030605010203090f0a090606030b1905060702062203031e05090f0d031101240503060702060c09040f2f12190e19050708070308041205 69
    0x2c5180380162080e130b8400d8114038800c2c81008010820070a029528075044c9903d0b04044c42a00c1c10032000039030f24020050400d202d0392400c0002400358031032245040140c8a04c89090126a40351600580070305102c98840303003e0240d003207160240c9080d1355109000c0d40c500800c05803901881c0c1d020002d494005140b01d215140355401d50803403a141581c0060020f5209440d107280741c1c1d01506e840c00c0001602158102485020000020f10340c2c2c40e06512400c441d000c6a2098545100d4102115071084800c9503210540c6030800c0090580382004802c001000849800940e8584810a151701d8500569290016900000c007059000740008040c0c00c0d410000b800000301008002480c000341c8000508290040790303002121280212140d02c0714001c2c0c01c0f0500314601d041325001d404403010030003c00761001c6100000c00442d802d0aa5000044680082e5044800024050803044050151680111000e200b407a800081c10710b40450050110390300000440e04107460724030030360701344401d2100849403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 848718651 1250 848717401 848717417
    0x1005190501031d011409160b0403020d06150609031707120e010e03100501090b0a06020a0b0c07020d05060612010b0a0e06150f0318011b030209040f0f02070b0a090f02010f 75
    0x502802445108a101700845074150141801c040084c10400d03a11030030004200e16400501c1448101400c980442c0ea05a650b400c8000f0b4501f070441c002c100740000b40650000c0404000360b0294009644002d07a07008846060309601900d811100b03c1c4034601c401000c0e41d003181180785d4010700880500340d1900b41814001500161000001e0030494122071740300c5850358480040c4103e001c2072049018005003503c80d6500f042c10140040e60f40c1e86401c000800c5980b1003000125010a1081507400559000e412001825260701e0300c00d480d00f400b124450300030101c0c58540c07884075905004800c5481c102a2011652a041c90709208081c0001080303241c00c006280348208802904000500403540700c00c0000340c407400c198502e42c103066041c0c041c2103440d0381018a41170800d01810701c1c101c0140040c0c180183e03964841307400f0901410106071358880c2c003842d1810041c081c80e499001003c0440c45039600064a50310440c0c044220740350f440001d010460100c0d055001540030340414003030a03000707061640c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 848719901 1250 848718651 848718701
    0x1a0a060e070824301216050c1f080a05040c090e03040810090308160210020d18140118050c06030402030f101b110c040b0a0e0c03100519050103 63
    0x144108110070340030201008120700c8070004ca9000e0700d10144a050f1406400313802c55650080710a40100c0035049510000b46840e1300411400b001628905030000d4040c400307124440d00407041014400d84408040782e08080003401a140c1482018444c80d800780744040e41303074200038012000744400b03804960284410840071030040300410413050800801040031419000c85d15005007010801ba08108a84001901040701d1540100d0001c00c178051881d40162103800306951080074042d0005c0060b02c225031000d101781800700400a401c001c541a00c020f0000801d007015601e402442e02c0d601502c01e4022500c09026441e04d00c0003103030020f0000b81210f40c040095401d003814003900b001c0010715250744503d5040584490151000d21a1050800c48200700242058545690050500c203114554806c030951203a80c0d01e1082901901c00500040360781e140141e0b60034280d9000760350518ad101d81401c0c0000d200d103860020030480d900e03102e1086100d1490a4010b4000d0011241240328040350081014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 848721151 1250 848719901 848719909
    0x110d08031801110f030406050703090f05011b02160302060c01090804120606090b090604151a040521101503061e0c110c090907031a0a060e070824 64
    0x1600880c14440520440740009003a1421103d080b040c0302d0501e0010b100031004603480006595000e038104001180d1a070301e10b2001c400401076100c0003001500c900c45440c05000055100150740346900440f801e4a21240100741e035030300442d0382140000d11404034140018105000507054641402d4008500361405607105162a0066081898402d0361003241000340a40703401040300408030144204203907071608012900d00c603401860180503035220600c2103030740f0b010466103000a05c40514081c500b0b40c142a803044155106114107885450303014003003103030000200010300d441403001004104a0500c6d50140300980640c0460f24205094040c0008c0490300901814442c80c103110b0031258450f490781c004400f02c400881c28603041242140300d0b041484c400050750000d240b01150490020b0359803814080c68910540c000a004075849240c400e82040403c0ca110700804000405201d020b44030b00c4100c5044608640c1c280005000001003440554046c886c0001d43c940c4800e0400b41c0403018000c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 848722401 1250 848721151 848721157
    0xf0304030512060d0f0204090213110909060603010b04030b070507020a09090203010510031205071407060306080d020615121c080601030b0d0b071812050c0a0e06010903110d08 77
    0x15000700c0e40c0000d991054240d9007650581c0b0110403601d1402104079601c40321110800968000d001c0d540d503290380000c0d55105040180d243c10401c2e002e01c01d191030415291904e4200c2400d007405040c1da072000c24264a44601601c9c1a02c00c080000790a15203581c840481503503000e800174081c44410001280980c40c3c50741c0c21409845121000300e034541541c070606084442c02488594244a40d542c240b0014000b45018440c0f2403080c41c01c07580b60f00c1030f4145031000c7c0e0041d864841581c4075020300002c4003500740c0c00c131030704503035030841601c601840c03160050740c0314541240c040001406021301c480807840c2915401001e07401c0d0104640c1c220090b04240c041e20364681c0c5280d00410307450000c2003202d6074180580035040740244e4145c00914941e6584c4001014054101801e1010700340c03401000852210044005003118968040080d0301414501c1d00c1716071040c0c015000340c00f0228042388810a80e070700c01e0300481040e03598654207031860310ba481041d810705820b0382c0c2c80500414040003003a003150107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 848723651 1250 848722401 848722403
    0x30406052205030a11010203060f04020f090405010801060824040b04080904020706060806010b070f060b011b0c080d0e1c0606181a04090f03181a0702030609010e030409020c01020f0304 81
    0x1944d446814482c040c0c0449540040c4408982c010420070002c0c0c2c80c0c02055810f0818241c0300544c0f03d00020321340c1c0b04940034812501d40c003d494040006100300054004000312040002660401c120300707184088580c3c4000805440500c41c02c4c082350009000d0074840e90711a014080c46070a00900300c000909a0303003c000c0a440540e2a20814040381c001807207400d0061034002801894400a540c900014801200000e040f442e0340f10150f51180e4000d02c40d4401c402d90348000b2410008103883c019080010ba030144040c02d10a628021041c1030044001040c108401091b021040b413441c04448912510303810202c990545800000071008054142403129242200d40402c28a14810710540f025010944062040b810048206c011803002700d842400307140c00d40340c00b008954040741c1c0120440c4082c0d00501d00550301c564044a0304441c0f1000d0103681d8400c605903061030b161801e9843c240e4941ea80381c0003058204003c200300d58409940140904010703000050b003005110044101190004c0707030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 848724901 1250 848723651 848723653
    0x20a0b0a120f09230a140a050d02030301090c08010e042004020c011e05010e0705030709030c0e07120606120914070303110f0303010f05010c080d060308090a06030b06030406052205 79
    0x10f4030b0100444d00769850080c60701d44102c85411566521080e603910303010007000d806003401b8450f010400c5030a008807944143c002c0111801c0e000d115030300955a5009104041003107240c00c04602d50b8174400c601850486810b40d58041e4035890719141c0d8880300b0b00c0c0f2401204d52018640d2528181d0300e59002509840c0842000024000b000d2a0481001c042146020092030303d0100144043d05902084982000f06441c080da100d41e40d82d04140e031400c5882e0805408600861070004900d400d0100d100d104d5505d9a4a0308030184003130540f48155030080c0610b02c041890390012001c00805035100000d000c0c0525821580e50200e00001030500d09180c00580024901103d01046545d0401c1a040e00074181e0009624662400300111462000c6008440c10400346000320750034040380c24291400c1503c0351004000c0e0558038174003055250702c081c04041c080c031699000000d6080c00ba1003070b001c4001028240a28540d61555164000d2000030b0040e220002c040c00910304c8401441c00441d40180314034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 848726151 1250 848724901 848724911
    0x5160606050111010203091c02070f090501050f0d0f080307140409090317040b060d02061c1a0109080c0d080705100b0906150a032a120b0409020a0b0a120f 68
    0x8001085040f4803071002e0450381c01002403051410b40001c40501300d107540e00c50415000d01c0710b80c2c120305040a9921261080079510800714006101c0d5016504aa900721103119001c80980c0501c102d0003281540078207001d140c1c45c0d645000c0f0b08810b00540d03001c8954601106400c94903800341703c49030841d80003d001c1c2350395090024105900822404401d42a40c940120341d03280039034603610250b5009003480c0c015100040d401d02113403110f030b043e9080d50704003500012403881991204002401414410711005080380801645540501d14010554080501514071140c5840900c521043d8643d07085441d0b00c010800100070a500703200c4210485600750700031610b0b50365039041100c080b1018003087c2c07180c48680d5a8050344218001107038052002800c012a0141c010b48040240c0d00c40d21090445041044117044110799010740103031071034600310904201401a5000380801c403140c410000390051070a20082c0070010a450141c52503603494a081041030542070071100549207008000c403c055291 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 848727401 1250 848726151 848726159
    0x240605180712021b1c030227010c020414060a09060f05061b06011215111206010207050306090d1d0603040f1707060603020f010e03030a0e120304030c080f0c010504031205160606 78
    0x180700302c40c017200214034066080c02000400c05201e000c3e021441c0c0300c0102d043c0ca100005074050604d208021350010b00410071802003600c01201264100e03107551003252a01c0780801c5480f80c84c80f039181500c3341140d40301000ea003031805116443c0c2c0031000c12808120300c401d0400340c1c40000c111860181c5401e01c80100860054179140d90214584600302c030949050507035460001c9144d0056580160081c280d00e0b00a40356040142c0c02c044203a0807142c2c2501521040142c070f260300043d1075400b1030040c1d551018204124405000241c01e003c94240d10000030404180031884042030401c44034000e15081d113004d81d0001852000e503002d500c2c1161019240c00041041d480c285a02292640c0c080c20043d442c080d0410000307850788200c2c0c1010060080c00b21190045403503d06081d60b24a42400881c0d9503a5100d051140122031507101e002c0c0d0510034414042c12080c0c0119400994030740c103844060805041d5540d0540c0f5150541c2030004000061000c4d4001554602c103076a002401004002070071400c3c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 848728651 1250 848727401 848727433
    0xa1802191b08031314011e06032006121003060b04020306010207051509030717011b022d011a040b0a0501080c0a0903240605180712021b 60
    0x1011850041c0201007280030540c0310100c0500400070b0b0302100712a960760314010500f407449403882c030150038002003100c20010002e05602c4040740002110390081e6403900c810142c801d440141c00002c00038018002c50110f00c41c280c10800c0702c0c00d00c0040c0013300f0115080d410708000c0720120780301d020310702034040d0400c240101d9200ba452400c00a40c3c040d0300e10f14102300082c0d42e450a40c840c1c60f000b46020080c8441c1750042c04255013002c0c8000b010b4a50a96a400c4802c0f0207651440b44501c603540f07898071110704032a1106404004030802c1c0c010f0044100c840e08255165103d92031590103841410020280e000300078864140655082150910702001c11004d000445000d044800c1c080d16207100203129a80e0031102c0d10b07902c061401c440355500c0c0c880e071008407000405503100400072048440c801000c2504c641070385c12810045035042160a644400308140c0307800400c0308103001390a4001084201e44580c0b00e50f2500720003401c026140502030350400860000740310b040c40301034000c2c42c214042540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 848729901 1250 848728651 848728687
    0x12070309082209050c120c0d060b030402120a050a06020304050312070c0302070e070e120a05011d0c060301050d02010302280207060806030304060516030905130509060711060112020a1802 82
    0x1020f5100700036038500854043c009118510020024040721400544000081001c88040080d2004281306559a9030150200d0340c006403000c901c20b001e6070b040c8407481000021f0070768015800400520941c20a42c98010081d400074000f03503018042004900716403502c0640d05030213940349581b000080062030030000d080c00840c0e00440c0080c1d070520140101d66070b00c8842f1400080c01200d0450790310700301c011002d240055400c4001c0203942002003c11a03404000f00208058103450143e40c03082841108002c0f02d13100034003e0552081c0c0c948480405035210354041c00c0325a52181814840f00e00f1686142c09907883c040c4800d0059020b41010b02050303501000340c580102040d8015410305042110260a270700a00325034801410441000c031f401e040c1b0801d2114018180070b060400e099854105e40c0d80980310441d03040015200b030341c0100304650700c110b980155550118010f0250f99080420000320850044403e81e0f1180705080042007031201a125404400307003462005030f0f50740d03502c2c007240d02c845 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 848731151 1250 848729901 848729909
    0xa11010f0201050f06010f020a0c120c08010b03121809010b09010e090f07050c15010603020a1e2304090510050a320d060c0e01030b15120703090822 65
    0x64105001c3c060081d100c020f10b985c1086007400c08005c80003410301c0c00c0340380c0050850003501c58000d042c00001c0880000100001e06400b481c41900d41c3d0751100e0f01c0d2030998004900447d015808440300c210805400409800314040c9800b881556020036400110303013060a800950511a00040f800a590380001b00d1825080065400034040c1c581100d40000c0b5000c0101200b09116002410308182c14003407040500d503d20b84000381c00c1c196142c190040007504030501000206001e15020740d41c4400310171000041e401d082d070f600c4a480e940000c1c032101c0c4821608049000314002d010200d01074555020b00740c0701d40d84c0c0fa040c1c00b18ac1498a010000c1048142e400300030003442e40703103244601c0c0c4111103101e0f000c00c44540384180108035010105001602c2d00e80b01801c41403418402c0c40c40386034000141035281d4001d0360240010003102c010084101c070b112200d01c0307186004020081c0a016402401c075444051800c0000704909103488084096103c441a111412000d2060441c2002000d040c5000b40c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 848732401 1250 848731151 848731153
    0x7121a0f1005030105060706090b01270e1e0102040b0a0806032e020304050a080d05040b100602030a0c110a08030406080912030612100c0302090102010e15061905030a11010f02 77
    0x20115002411503c01809214064400002c0000c18131025400640c0d11562108440f4103035a551030451541c0c007e4030310401d011021480c1d81003080405030207040703111000382011b03164080c0002403091f0183c030800700a2186540034440054170340101c0000d000301048a4560301200d1404800300f6043c103003100711548000400c0030700da031000c0c21000c0301700d880c1c42d10991005940e41c44508105103031903e8442c008148100c0013483d03529000054100a008506c42c1c41d1440080d101c2182c4004440458012440103034410303c03c9002d0300b80310b0804e0001e0580101c0b401955541160042110508190002a003540c8000340c1003042d0b0f9486921684d11000c114064000700150440c0b244840c070016084520401110840e006402c1003442146154a04a0b070200088600c2c0a40a8040d402168105015520301071101c0f24071500440c64006040b40e1405402050340c03480d007000010f1000d908032040c0c0b50890200804c40340c804014200c520343c0180480d40940802c00001003212010000348411 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 848733651 1250 848732401 848732419
    0xa050a06110a170406031d15100308030103111206070516031202071110080606070b28050109270321020d091e0b0106110f0304031b08060106050a030507121a0f 70
    0x441500820144140c20100401080320340b27030785c0c00d03540c10595250000380044c030001000100700402507510a48991040e283c4481c07441151003020b80714601200c500c00410010422480018681001e000240348031303003400151f0620718000d0204a0704101c40442e641112010880300c1d524284103d155611403615204030189082c00100d066401944802006020b1490103c0c0700360001c90b20594881300b071080e0190210300d99400d01c10241c1400e1282c1012030b071031310003141d02100d01c2c03001c1001403c90b002d001105180441d43e0480d140c500080c4021408034481d14a29070990720b40c00240070b0440800404141e01c146400c103d050f100b406288210540c8103240c1c5403000442c403c00242c11660141001080c00c648841c4683c10f21419000c2c10f2554003000401000304002400d06014103144c0790603560b038281c0c681000b182d40c2d070320030300403a00850780501c42d043c0c1c100e211703400c0503a03c44018505510400294404c12003a43c0d0408014000c900c402800f00455090a010241c20a4400c45000203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 848734901 1250 848733651 848733701
    0x120510060f0f050d0311011a1507020105030f070311040b071109130605090717030711030a0803010909030c0602040e07030e030405130f09050d1d0a050a06110a17040603 74
    0x580690b81c1c403805000f440418045400e041c0189019901c10781c2c060002d10461284584000f0741104c0029a14490f88920b040e00f01c15400c140f054a1800c0e9040e1542c0d45942c0714950090001840201040e0805031204048459868a00050b00041010b00c18290310b4220034074003689aa8108045940600616000c10004141c1c84e40c01e10300081e044000010141c4540850358200710031a003003116400c001e0b4898030141c403c00402405090f02513000d01440c03441c00d108068607402840c41c0a4205e00d0700f8070041c04040c2590b8007180090b40f02c0d080489407402d441d40c0d544180c0e0400e600c44c2512000d200704000b0070a03050301804020b43d40e81e44c003852802d410300002803c13103007660000c0c03035501c2c1d928098440508a103921213031609401c0001c40302d41000481008020604280d0110900b04119003058003d082c15244901610002014800041c1c242002103500c010044007000c818403c040191004c00c0000d102c0054100e41c5008095550b420f100000e0140ea845040150310205c3d2111040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 848736151 1250 848734901 848734919
    0x6020a031e0c0212250503060606032e03020405191d06072102130521070302060d0222050a051203030a1d010f060518070e19120510060f 60
    0xc490558102c9020040725084c909851408a1251017540c4c2040b50f4114131201209070054001110030440488186951f2001032011600090355080c030400841c1d0084102d42c5490401190344216010307036210350982c0c1e0f0300014241c0360240c0790004042c41e86241030b00c10180a01170700c0d14000491038141ca016030114102681c4903001042e2030208079200c3da07500d0030403485510072100000b8000e010354a40b1808080d080200e81d592061b00e119150400020700c1d1001c8820100b454105104058607039146540c0901c2090b61140540d5540c895003001141100b40f054400e016841304082410396080e82444c2c1802042e00309504110320842000100c0c2c00300080000c12698091270403540868200100e040e0804202d10ba810880555403c109000551510980c442421107604445030300b6103003290b100001c50710801380c5090300011072032002c048140c00d01e850f40b620012502421081c40a44c0c5051081c0148090310040390250030583c20b00c102e86a4a02521000c5c1c90340c040a41e020600c2d1081c80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 848737401 1250 848736151 848736167
    0xa0506090a0e1203072102040e0105090c07060f020913050f090a0209010302040b030a080a110118030c061d030a05031e13150f0c020d0216140f03120406020a031e 71
    0x3c0468a0000001880d41445180b118055008003a07611401c1c0203100c407108007a410130302030741048083c0540002a01e00c3c00c0e0700a03e0180041e440c3c0b49250403000d85070740014008440784880c440d5003c000c000d50b107071540f004c54900c0d48046070000400e41801004200500d5000d402c10798194040c18a0b40e02513511544213a04490b81160005100030180c030100307003401d1150f840030301481d101103070001d0201d40101034600e00d40b00402c001c000396103200d11040d80c241d000e82c5010f030008840c0d8441c2000241039a2054034490394545203602031011040390207241d9032201c000720000030404000d00244110700d03004d421000124107142c540314603203c0c1841c3c030743c1d20f903c81010f400041e8068802c140e0742c40c50390060507034044481d402c0c4030a08000d0070103035581101404080040c8a40001d00e825440d0070744640060392081035502d407070304640c00204a800c50340911301540c140200d084840b000d0300198010300041000ba005440c00c003005040103454a507080031844401c400001c8180e007001e41c0300d20b00d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 848738651 1250 848737401 848737423
    0x3360105010b340204090f0512040b03010e1306020d06090b04020306090f1e070f080f0405190606050a0312110601050a060f0e1005030a0c1e21050a0506090a0e 70
    0x2010340d082007400d000720090f0443c50b4010750801c2c500803051090041822084504601a1040b1034041108486400d006d02c900e106040c50032409000522809680e0390003036030001344204000070340e07241ca034591340120ba2000003035440155a6880c01c018071043e9004180444a003114218254908a000308442000c01001141c02084510000f81108440b1920b00c100b0801d00398070b41400d29045402408102070071114074013280c98200000e0601501d14070300d920403a030000180c5600c07003000c400e4503002c403280101220059103641300821642c84500146d0001d5000d21b10464154404010107041025810008922500040010f02490f102c2c100d00302c04075106803900204072028590101e070010f208114182d840001340d50a011021b501c0800740d4003400e4072010401c07900300c40070780a60782c000160520b941c400c0000c1e10000c5003540100c1d882e02d60031056007800143d054039204290f0480780212041c1200958580a03c9160700b011b004d0180e000014035000c0200160049a0964500400c01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 848739901 1250 848738651 848738707
    0x3150b03180129030709090606030606080f15060a09090b01061112090607020a051e03010c03090f230d0513060908030304020d080f04230d03050406030203360105010b 73
    0x661400c41d84c034100499002480d401008101c003590a10b4101c016003060711041d9002801c141e03004c00c0040000c10f03819840c0c180c2200500402002c892030840c1100c000300560707400301d001d1030b0026040b4800c0c040d090321144122480000b560407d00080e1410800d075030141c050341d00101084000440140c2200c9005804881281d200c02407440010310481c4a0f40155800071340c10089815900c90241d050242aa001c41c02400403d000c4181141103454540703000d800c415080148101281041211005114140f04042041a0300c00200780c60094403d100600240c0e00003052040319008a1024000d000ca601d0000005442c2c10038080d40c2e03000180c0b0181c0704424405042c010070160204850000960150040e1656500d081100b40720207aa803800101d0a4800c03008420791501442c1c00c0b80055064581c5c0741841c2c1000700c01c600135080204000741c020394247d094601d900c4103070134201010400c1000c9956a10b0410446800c1d940183d0040207161302c00c0c09076a015a06210780440306030351200d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 848741007 1106 848739901 848739971
    0x120b0d15200f07020312041706010e07051801030e0706022b05030414071d04060f0608070603020a1209030503100807121203150b031801 60
    0x200160301e0496040209418000011001c0c0003524000390449018a201c410300c0c48250f031050700445000440c00c00b2070030b42030108124175409400d1107522145642000031000d440d900640e080f1000c1070b940e1581c150035591003030b80114640315910003256602039440b00e0194940b1243c070501070030034a110032040b00f000401c4066210040699455900d141e032a41ca41d88044011660403802c580101800040c20080b5403254159203006804680c0c050b0038103150200803240441107500030907081c080d0810144801003101c40444042e8200907070f60b111051822100c2d6002c1e6000007100926052000c010b0560080143d0f100d04840c03036000d0042030704c81c0003495850606200d0300700c0d64448502d45200244050403030340c07000800341c10301280e88000c440260f02e0032150380d0000c51031070b00003108000d00d145030851220300380c1101c1d50080000c10711a01400c14100c84101140b0380c0741e4160 = true := by decide +kernel

theorem cover : BRFrame.Cov 848561151 848741007 := by
  have h0 := BRFrame.cov_init 848561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 848561151 ≤ n) (h2 : n < 848741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
