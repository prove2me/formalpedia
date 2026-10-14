-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2083
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:36:55.367601+00:00
-- url     : https://prove2.me/submissions/efe4593d-fec0-47b2-a550-da338f507edf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 374460431 ≤ n < 374640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 374461681 1250 374460431 374460451
    0x9042c0c100203040b03060f030a1202160803070b0405030f0f09040b01171609030812040201020606090106020a03030f022115090c07061d161a0403050606061b0709090b 74
    0x580c07698401075200e003c0c034080c1c0768040b2030120000301c441c0e07111031100420340350207011b541401e40182480c641221411446c50054425401d02217240050f410401045422107406103041052958130080700c07600c00351081d40c05100910018055090f10700040105900e0710742400e03603688000d8280810b440c01401c0d400d0602203895181424800080c0035903a00600c501941440c0781d00000d829200c00446030070262480c040441c0c500704060780601f00c2c3c1d0159000f60200e60f42e41d81ca0701c0821010385000d0044c8001a006020300e400001c2c0207410992504000c00005802d01d038014240c400c40029041644103408010002c1c03101c2c1e20850b009100e16144155481c0c1c079240b0b040d03402c09809210b00b01004000130754403882d0103000030000211240c02c4800c00b0940b04e8440c80031b038190704180010b000345000e90440050303001c0b0710b060308003c64044a43c03210103460036689201c100107080e04203100f00c8403518000031030441d200034144001400b812201d02c00141138201c9040600c0514001407101ca41 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 374462931 1250 374461681 374461699
    0x7122c0708070806160f020f030a051803060105100c1a131205030402030a030503040614010b04060201060621110d05040b160f020a1101030f0207060203060f0a061409042c0c 76
    0x8080192011485d0464403810184080c90700702c0b43c106d1a2542c50b0030000d41c1c0b4000840d060007840d41c044010b110150350303160011415401c80c0101a210301d02032244552001288000d40002c0340104400c0a04a014041c42050060b0710003007001d41d100100d4030031000b401c40075014000c02110804240ca03801062805506618299002c00d41d80d1504440140c203008020000404001040d00603441d0743e140000d02481079651420704030055023250082002550900758003041ca81d2040c0800c0c1092090417a8000340c80311800104d4008ac1919841540000e4007004462840d050350b0040b075004500c0303191420500e241c46034401201a9000046c0e404219412000d502d0b59030b8006000c0c2d0f519030b003011100b1611918400141c0060040a12410005002040c0502400707540d0340654400c860070741d11210265104410080c03071910300c0c02501c0104000000054031506548060002c400d40074100040011090030300da00d0191840c8a006031140c01d4000b90b03102088240305034940725a0644400032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 374464181 1250 374462931 374462941
    0x319020f0610060518030d0c02100201090b0105090606091009030204150b12090313030f050118150e0102070b011202010e04050c0d0b0d0204020c0a030e0907122c0708070806 76
    0xb481118610506003040404141011806202c0d0050303202c1880c02800c0343c0d0313000d0b03200502806400c4070180030b034410401c480d00e41d1b8200b4018028500303d43da210800c9200360782407104104440c0c101411054015405011111194030f03152001c1c185941d20b61200450545584108003d4440346009223181c0861600108110311200302510a107000014030300310543d0318007146900e18010500c4103000d50310035500000c03d21207640b82d08103400740030300000d20a0101c0e403000e2074282c03284081c0050060003100c1d9420b04540d543d52242020312500000540740c501140c840c030344400c400380c000700111b404904440f021982c01c0b002401c007441c0203440600c083d160280c6000424054a8416490030391581240801ea86c1d81d40e440508265004200310744900756100002da0f101e404035803c0300403400003418601c1d0341c80e025400c1442001955140520003e810641d50090880710a028091129407201c0494100e41082c5103002ea0040c400217240c0640340610b4107281101e19408050144c01c4001402 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 374465431 1250 374464181 374464201
    0xb030405210a03020d0902060418110f04050d05101d0c0d020604090e0712080a08070903080706021b10020a0e04050402090708060a080d030b180609070305090a050319020f06 76
    0x51000341c000d0400507110f0707117000354010140900910003540480005004a51030410a2044510034101102001382001009410040d0f1145051b500c488d02000d0108000e685403020107806664418000ea50b02c5803d00f42c00f807030a491302804484900c5d0a070004402d490304080001619940044840480c44515034003c600244510700815502030303214a894405054204a0702004103013501110012203640e082907500c3d50040d40050340054013050100740424892541d24003034035008001c8a01c0e04410b03590b00e0000303520419460240880782d112542404905000030180e491249801507940c1132584402845d900b014100944a5403801c0203103c09038a0307400145500c02e80301e082490298903180c001500803510350380080c80c0707442003d6100742000ea0641108000800c251a019501000541c05081c90351084990700c2d044080d0380001000300381300350005904528400265000070009032919401c40d40324582c0005500c007003201050a2650420501408546500152016040c036501c82c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 374466681 1250 374465431 374465437
    0x203070c14010204030506130b010e09060a02090a0302130b04050a200a0203130303021b013f060e06090a1e05092424010f031d0102040b03040521 64
    0xc0c00704011030081406a410950445000c0c54000003154124a04034011210484603100115271111010b0000160020f02d805068010742c0da81c0f01074002950b403045050300940144548550180e5114000001750300c9105142c011032450780f0021440070404018030094a030301030301c0084038034500510030030001c5a022880202c076075850782884c1d071084040403ca10310700030007144081c02440423100200305500002c4114455801c100f0625004965800640c0c0081d00c19031444030381702112845810074000010360591405400140114196074240550100c41c8281c0040003004a40401e100982c500282411352026000c134040c00140d0320000c038080a15100001c3c40c001c030341c0300e40100c0c12400c028040384448000400c4150b802d403095941008440c101503da48024000001d01250041524040e2010104041e1140d0600360b40c0090100d00801e04100030a0901034102401c01098200703000610003407070030041c400c3c3c0741e08103810b000b07080000e054400c20500882004110f0758a00302c030b040e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 374467931 1250 374466681 374466683
    0x50a17060612030d15091d190b01030209060d060203180609010605030c130e0d0c020f01020c010906200601080a050d0503010302011d060702090c1309050108100e0312010b040303120203070c 83
    0x100c5c1c40c6042407507921905ca140e80104a140d800c02642c8050704a40c2e8540c207441c004004111210303c1020030000d034507031030282c8000d0440f0f0440c41c0144013504142009030b0300a40e019014400603140b50702c44c5022600155909801d00700c500c518480d11040402c40b04d0b401512500080009a15040010b0340d640c1400d40114000c0c58400186211070301180e2181c09401c0c50b0781c094510b08445032a0051038007010f040100d210311001c2e4442000e82d44001002c200003041030f102d0804043c10304905407910340c40001703030b42001c014081c07003820106c1c01401198000e200341030041c00240f00c1480c2181c1010a221603000401078144010000360380d0003040e005a040341c1c03c000000780d104140104809103e40300000e904504580244482c8040d0720380108800001c09440c0da030656290103009064036000c0c440c420f0907078004080000c0c0300f02d90b507103c5280da803004d40c12246005d121046420a00a09900c203050510001c40e04005141d049010395105040c410000c524520b0001400340c80c0d2a82040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 374469181 1250 374467931 374467957
    0xe031b04061e152001050a0f1406150c010e070f080d021203100312020c150c06010b0c01150303090905070e092a0f070c0905070518010306050a1706061203 68
    0x42e40d80d0f0b9030086000701d004554001d0030007083c20701d4a000c00d001c3c3c1800d50b18810001e02d0450b204d42c1700c0e0031a00c03401c0306d26528180c000d00c050325240e04210783c1083c1c0c01c00f00c41c8070805c10001d40c60181024850018404905006084114034221b0030103010340807940908026080140041c480304e90106000c0180030744010695140c0d200c03810208900a069040180a02c2c01d8a1136691035640001d000c1c101c06100302c4003881d01a005000d254981d025002201d8403a502080c0140841c0b2070300384c05003407900d040e900002251700406105100c1d2540d20350054012a4640380240a45005801220390041c00784c02e003003510324501c0f004140c41401c020701111516508038543c41d1407847c4400e0440309020081c203d1601d508d070419084021341d11145003200d8407580d00200166010550247d40e204a100351252428509403040e1440600c2001424504240d541c03100410141e58210302603000d441120380c1d10302c070859221038407403030302c1000340105106541d6001d51030803000d40081241c44000707001c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 374470431 1250 374469181 374469209
    0xf12021204150207090c110d1407030c1712090111180111070305010203010602011a091e180703030e040b2b0302150a090c06090605090d030e031b04061e 67
    0xc1e400c03030a11135641c00503030116081c400e03800380403640403c100300301404801c2941c085186520b0140e5908002241c4520945014024500424000e0189150149c040d001c82d60079104140da03802c6003a0310502c10504d115102a09108004401340710341c2c11905102c071285894a41081f940a144459003d00c85040002211146c1c1071040107001d09002150310500a5440b9611000060b020f4120001c1c480101c0c3c00e001d041c01c084c0c1c948024541e001c0c20792507000980806400d5940e00f9283e000a0800d00455031040f40354002c004100310010041d4082e1b83d494140c0c140500400003960440c04031144915407102c0b030000c3c0c040110321228000000031503554107000721490103030b080c60544480840f08058850400149000340c4e0050b01e81c040c89450100303426601c4000c15100988240950800204180714008260501d00700c0d12080f503000e801d084011001d40000603103800307980c443d0341c00240c07450313500c986050501e4060603014000881801e03081c2c2121489100ca000c207144600c80c9544115 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 374471681 1250 374470431 374470469
    0x604020a18080601140a0b160206040f06030c03052410090806041202061e010b0d0b09180d03020403021c06110a080708070302030c0d0e0106050d0f12021204 69
    0x81d46010780500010446480c202c1e42d600d012600d40078240b0910100c074410b43d4a4801500e002c080b440c0035565a07915007410101641c6200d80c107103000c00822038000034100404102c6034000d68290005240a039800b14003820a1503004056480180c0f009c0154080c80e41d00580e0910703854514820030005407030b1105040112441142d0316030640d80030031072a000d800c0a2009004c0320b5a1529414003480c0c00311076113601c8082d280a0f00107010350312840e491074160010300461450000400f01d02c5600b0308046900d441132030004990081c00e079810103641030a480c40b00d40118040c41450150341047c2030840c1060310f15004910791040b020b51000d48143c000c9203801c01c01031264008030503c3d00008120b51144018039000e451004107071400d02c0882c1d03082000428442c46402200d10550468201a041241e60700c440005400c9000c240c1245548558020aa0b500d0701c2c0610705500340100c0710a003a410701c0c0c1c18000c6808070301000d01030443d0081003101e0410342ca40c2013280d08441d03505010580c1c028038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 374472931 1250 374471681 374471687
    0xc0e0d050c2412010317040501080c0c211806090f040f0207170a02010501120305161a280203040b0c0c1507090306051501120c180305010903021b03060604020a 70
    0x381041001c0003040031400340f0240010180d114142d0388122004440b2a6030a89503410500880c0705181c00952441c002a01d440503120190284800e590121079060316402e1141c0c50300b906c1c00440c0c0c0301034003000c503000c85039075003012016480000c10b445c0103180c1580c8134081000349005401c004d0085031550305110305a03006034111404260050b0700003003950501801c03600640d000f821035100540c24003001191000030241a004020303495101c40d40f80c004019407503000b0382c01401050f5000c4910091055920040c000d28a214900480603c034074410703141a8154042000d0b00c0400c8034910601c10840003401030000a500300c0101d2240342e4035148900d99007840e0003402452801c221070808144a45250421605015203100704010b029581d00c81040740c070f0009403006213a0002d290880e0342880e44c425a80040d40d0341c0c0c02450490b03084044480048000b5407035904c1100d1583d5070314025000e143d4103000c205d1014100c10b85030411001c3c00d400281c0e41d41c0b400f52405105d254001411a020780c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 374474181 1250 374472931 374472979
    0x80408190c0b040b07261b070c08030c010c02060907091808120a050604090b060f0d0507030f05070618031b0e040620091809070503100c0e0d050c 64
    0x5880400c10300d240c5014900111400400d6441c3c2c00032a02c40303650b58000c032103101c1001b00b046070784901c030409582c3e55182e1420403145c114003000c0555000c00c4004041360300c0ea5600005000075100460313441c020510a0ac2c00c44d942c240c4003408541000c2d0038400160804503c800c01c0310200a030201c1c5030b00384000300c0802e10703400340c100038000e0000007182d05840c219402c42c02e110705904001040290b83d58020b000695010030030042c41121a800021428642142c00041098000d842000000b0280d074465141484541050313035260200f100c3e00d002c01c4010040c402c05482d0503e07040714060304a2005100e04082c1d80801040c0364030301c2d9003600025450b524400014504d8641c2d9403814201814808002c1c14051442c0c0d0b101280c90f41e07000580500c81d8222071064501030300000d00c0600d00c124040358051301900b6205140112500007486690400607600391005081002034251880303500a00902002c5102c1d500403411020600003290012620010004007a40c1081d8401c00381d104500844c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 374475431 1250 374474181 374474183
    0x2120c030709150c020a2c0901060929010e1809010b040218040c090f030b0411040207030f09080d080c1602060d0603020112020301080303010b0706091a16080408190c 73
    0x101203001d000002d1360b01c410741c508050700035516422000d446510100803ea006c1001d403030031666005850304074800341c00c52aa442040c1000025403286c91f41020bc0030b0b20514003900c0090b00c0356129001c406184043d1081c90490242403005a103c1c1a0003c5020010441c00740018440c1600000e00210f200f9040014040001001195110084010b00c0041081c0c2041b940c0030340d11701244c240c01c590003444211700f6a02209030081030720346541d8039800b8017840203104440c0030110402d28401a180d41c005801403c1c030070b840e588010000e1000c010060100e951001e441d690050724652031003504143c1c1150000d1001010603074034110342442e0500b1071441100250030100004100108a9856000100b80c0303100360303120f0700101704d1014490217074042030040e86180c4d0410401004040003a400030040726114500c0800d090040f0344400442034071540f485800c20055008200440c103d001c6051a07240090410104070700b00350b115510745004404042c4403180c102c130141c0c0802402264000f40b03c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 374476681 1250 374475431 374475449
    0x9021c060e010914010c08060319052103160219030309020d0203062404050114060c160906030308010501110d2106030501020405040e030406020318130f09021302120c030709 76
    0x30079461408070300381d442c0c903407480c0c569500c0c0815409101f8402c0c00c03450f0048000500810f03a40d481d40c0943d0308515051030046590f446400d801d141d843c2c0000004c070007046000c0906644070310384401ca04551185040c81141113402c22803111f6611250840380303040140d010301d40010348a8103032010440090131400d002e940351054204110741100c0c0b038005001440344a094540701141000140425a202030240e62100440640c18014a05010300940200aa20f60803185850701d102030401502c0c0d01d54020420842d02c3c0c802c00c2c13040c10307085410350340101707030a00c1c1c1030f27050080040c00c10b9120b5480888500400410501c401400f4030051000c07040008510740c20842d10780e172490401d000f0340c858070849001d81c3c140040c9002c010400300a50b403c888403500074600e0201072841a1143c824655103191388100391040c003042030565840744a068000c4240d000480e101d07280100b02092800440c6400114010040d45c085051000711580d048800301440c242c983d15402403d41d000e4400340c20044d44 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 374477931 1250 374476681 374476691
    0x140603041212232514030a02040e01080c010305060604180b0a080d020a0501050601020607080106030f060b0a082a070305031308070c03031419050703141306030f09021c060e01 77
    0x400190b90902c1c002d8040c60503034480607014812a00c060912104e411004c145a0443c124805030510011355001207204401032070144c841806102c501400c0e0800601039001807141e02c01560144a101d03000181151410f00301860400e268180543c1400300310400d03a1501c80e0307030307589464541007200940700010598020315040d010082d03640d49204000d452a60a14010528550011941c42d000d44125035822f156603083c600150701414064600401c0b16030b88040c00901c940210b4007401d80d49100b655840d4240c20a984100710001e41c0c80242e901524007403044558421000088030b4055601d4140036880e5540c008903403d401600b518041c1204800003141410001b183c0e0544042d00d1103a242c9030302c4018500407041c1140601508041c490541c28140b10102e801140502403c604c2807811030810740048003024140d0700310400d00646200110380c1880b81ea5014000e001802c6e410103c00c1125184540008000c04026000710001b8801c40a03003100b0b00c05140c000d01500b0500ba0000d0003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 374479181 1250 374477931 374477981
    0x40b030c060d020c19020907081f0b0a0f0207080c010c060b120a0c0e09070608040f020a080d021e07060c0f0b130618031e09030c0e01140603041212 65
    0x1e5800f84c07420700c00900411842c101d02104c080a402a0550064219402c40c0d84285041c2d41c1d03c10040c00c01c0e0f0802030284a00c4090301042484940139006203000140c0351030200d54040d15111001d5008000e41d0800711081c40010b400259804000d1003d10f030102c0268141d04240000744000110b442c0c100c06242c039451482500080c6200005120f444805150307555414810940031040d601e030340c0340390020441000100d02c24054140c2283c095204802e02400725800102d100c500350340310001c240c04c0410944200364041c81261400052841c00d02c0000b004c044031103840340d2603030266500b80b00c9440d105806200c8088142c4114036880000e0760000d003051a00d131041680018421155a400c0140780c3c440e800c1d02012001e406036042d11803191b08080106801a0b8001804000c1c0030024200000401b1401004801008103015803c90071154101103540e100d01d02500c98a9000729820824007002401c1c01c240035800048901d03140000c2181c1540400103001c00b090840035100c030702a2455 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 374480431 1250 374479181 374479207
    0x1704080304120506090604030915050c01050406090c1202031e0705030d09031707020d020d080c01020d0506090906010b040b030a1d01050601030609060b0a0302030612010e0a03110304050d02040b030c06 88
    0x142141c1c3c00745040b1036803682e038610b0859541c07408403402000510b41d20020841100001450051014141025410640c030b600c8003508440b4203c03810b80b5a1904c81c2d8a40041c00901c84800c0043e106e03e241110040a07541c000c295105055402e201101c017500e1521110b001e003d00c512005001c2c000c0903038105510481000305400020f01064419100c00020354546610000407141116406041080c80318071036020802c40c610442000c0e07d0705c01c02000345507241c1c0001c0c401020302840e107140c005050700307005090044000c001040302d0480d5010000500403440b840055030116080c40500e1662580d035403800700c0140c981075248041c425500c400c00484c0030b01c190041d500c2280701fa601040440e87d50b40150050f1603013031003a00300311070041005480e0140320b83c00559101c000540400400e58860382c2c1e0718212080104240c141c6d4110800c410100340c3d00a40c113203089001e00004600345401c2100148000206200003403140741d640150700403035202804a0f4100701c1c1c00508668580d51040046 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 374481681 1250 374480431 374480459
    0x50307030c090b0a1410120509070f080303070816050d020f1b120d0f0e0d0207060f26063d0302030103052806022803181704080304 58
    0x2074401410140e40b4030480c02d01980480c1211460b08500301d0390b10150050100032614180540100103401f9a4601c014045c3d018085c02600d0200c003d01c0a24580701c104500d4013000e40180034550410414060750365841001c40750030007641c1c02d40c48051140740c54141e5152041c42541d00d0003d002007040f5514550080c013900c1291814540b040480720072003140c9880310b00c9506c840d401907005101c0c00d42403507903d81c000e05000c03d04000010b0410300301001c044c90445002c0d00b080040e4040300042c0b1a8179801040b0004054403030400120300005000e01c0c50092a51201036011018900e0000d40e055841026400e41c0c0c400c1d541e80f942c040c041d04491000c00d01006480280c2801c034500b13004902c14800d100322412250410050f040610208030040100508005170350908000c0050000110f0102e100408085c2a00c1107208240070f555030008001c1d01c0485044402c1c1803030082200010003841004086496002000c04441080f14013110010b01030758200440520002c2408a08898503000d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 374482931 1250 374481681 374481689
    0x402090a0909060f1a010f032409062c0609130f0506010e06180f040f0b01060503010504060e090c13290307080303090a081e0304110405060126060a050307030c 70
    0x51100c3d000c88811250605c07903a5100d43c1c0003402084081214600c40c0d0300800c043c0501596000c2d180010180c80c0400c15520380007080d4641c0c0e07541c0100085040d602294411603840c00200d0052200b01481427020080244002c0c000c120340d900042d400d48804001801c40d591001d2004032049141c202190760754800d01401442003200404200c00d882e1a501280d904504141c8010169850300c0b821000440b010788101d400610300f805400010381030242550181c082980d56984941c03504003081305070b0f907031640320a015800b16814042e110300f01080c1100d4400c07090305c1440d030300000040380000030700c0c544040c0f24200c002228140c500180140c1c0c1c0e40d00340c042c1102103c0070300c0d0b150780095440c1d11003038a00c549294070440041c00003e01401c098103e01080248080d84980101082c00e010741c4100c0f01141d0307003040b44840800c00e180238403620f50806000e1825001c601680b0254483c0150034040040445425000141c00c1d070340d40442c0100504009030640e180b2903507a240c803440900f03160103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 374484181 1250 374482931 374482961
    0x4110405090309010806040b03030d0902030705030d120c030c0c0b060111061305330417030a050106020d020a02010e0f061306050322030c020103020a180f050a0608010e04020402090a090906 83
    0x1003010f1f80b5080c01850712000c0b0003400765251441c028580b00042840c400201d8150040c1000050b071980c00f40700071449655143c607032030300000c485042601140e0401e455641454584600c491100354480310703151002d0f501c01c85461580e1070388801610840301403003100501d03106403020400b080070003080c5807110b148102d04a412007044048000134603400361090100c889014140300040c06014207400740c20a003d02c202901d407264400075010103500c00c494030311840d601c810040001c0c0340c0c10081c40460b2183c502c082d04170031916900003081008a6074030684a00742c0000c1c40070035a0f50707800880b211300c2c0340c051500d05041d541e0180504990803c031414511154041c0b428080101d044584d103652551554403584490071aa0041d402900800800000c103d1807100c0340000200b1000044050070300104900189480c00e420488240300c1a0019001c21044000400034145940d441a40007a4119400350316001c4150110f00c0290f00c541c0489401070034002c1433818050646d00411034103441807 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 374485431 1250 374484181 374484197
    0x1062109052107050309040c051c0c0905010f02060708090c030f210f070201051b150a0501060509060301090e0109230d0804051c020c0d0803011d010302030a0b0411040509030901 78
    0x310b000c0c6024050000050300c0d40d0803c201d42181d41c030f080e03400918600c80d5814620b040c800d6100c6c28100d80807010f50111a1583e07140d4418135401d8000b241400100300c24682030b0081041300000035160203002d0b2801042c40920303808101c2040c8240300c0d40582110140071590b0f4500400405665212400c1d006140c40ba4051440172400020030116803090103c0c888051900c1c4040d4011100341d4403011100900005040113070048103018010140c50f0491840c19800e00c4c28070b2104401110b40c180c0c405024004208103840803500d80301d05403811501920000110410207061650241100810051071840301c60620400291541d14101580c243ca00448a4110080c0826075120f5411b03500a0415071001592440300c0403800304003a03190b000b503c10743d1344842e0100041000da100c04c19040321003003004001032003041d40c644298192011a10007071403195242d90003203511a41299400f510280120f000101030200e660f600c50303050100913204110510340542c0c040d8594000c1e0701e4090019400d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 374486681 1250 374485431 374485483
    0xc16081c06080d14070f0f06050718050f060d0204121e020f041503060e01090b06031605010c0c0506040b0705010b0a0f0b130e0a1d0304060203030106210905 69
    0x501c10032054a0358000188100d1005502c16240c8400d40715980f07440300c9040001c1000603940c0110028028070401512000380700b1480c0c00001c0d41c000822000400040c00c842c118200c0007280484210794094404038034140e42c2501091862007070107103204a0b01d0000400040c088413195071340d0040c0d4040c075803905007a405d1959180300c01d0b0a20b10081c1d0300007600060503986e45001e6209070f004071002948018000d03501e944400a5901103108200907940d41c5800d50180301342e0108465000500b14080e00c10b0403c4050b00d424030b10058001e03039041140004442003044000d2074064090200100000d4550b40d4900c510350465004900880341e550801c04044070700c0c2031008104058881c01e014800700c0c43e003044440303062a000b440d80400d400c0d48000e00092000c050140c0c0701d0140701801e03404200ca03100807074100c00070008080d000980764410041040080e5010040c5c1c0c0c1960304601c0d00810844554000310007010f07001202e590326a1400f5140f104100340010610540a810503034481101d4003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 374487931 1250 374486681 374486737
    0x19140f0d120908060408040e060d02090a0209181003030302030606041e060908010219030209010201200903070510050702010f171006021606021b0d0c030609030e06030c070b0c1608 79
    0x10170358000300440020700051010300c505164641c1e100c000030b032018924202540000e9080082600d60760001540003420010505080e0328040b40c031717444841c070615642400000d50301030454a00c000f40c1019400700c08102c45540701d0085500600e10700c102246804046031242c20a000a849803601003500c440c1c002915210600903129003480b581c82d148415100074030b040d070180d07121050450442d50ba80103806200f2540106580b09160348000c1c464540e48508103041c54281607030011445903a5003013510b0400b551040c01c1324103c41c0c0c28a40840c800b08500410350300c0001c0900f095503030aa903501004030912949029030221030241c1d0807a1400400710f0705070529400741d4041c04005803c448420301109a2103020300710b4000e0082c000011485040d281c89181031400d400448040342c5840184d0145940b001800c4000300044891a00d1414510750340500c9204100e0010301d044400000105040328110079901102c40003030380c250302e01d0018036081d6969400082c80880c40007060b0019042048 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 374489181 1250 374487931 374487943
    0x1709010507020114130b2703031005222406020a0302010605012318030f030c011406090f0a0b0310020409050906040f03050c0a0501140108010b19140f0d120908 70
    0x4110170120000510301d07210070a50460061000500b2011070341e40798000d5042508240400b207a00002c0c5840c1d007404840c210080240758485881180e401c1c0e017015069028034442883d02484480c009004900341700e0300714a00b00340a0703400e04101188000011050f8001c24807492507440b07036000b040401e840303000646840066020b000c0c0c14172009080302e8001e034440802003c401c07008000306d8283c10350002c00286804c0d0441d03107110140d08007091001a8807000d00401100e8402c0c0c904007900342c84c044010070b8034140002c0501c2c05089481d00407910308100ca60083c80000f0010301958460903400c527254002e0351241c40b500300724518000c0040d5442802084079400f881e030002e881c940e040d4140d1000c8441e41c01c46a803c0c1114003804a4000000d503091254002400d894280240c040d803501901ea82100d10311815a8002c000c005030040c003001c000e08602c4180c0c0c0300154078200000340b00c1e0118400b103070304c18400c98010211401c0401841604101d5081c62607003a52400e83c1d030354a2760400d80d00c0381 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 374490431 1250 374489181 374489191
    0x6090b090703110f0409020a0b09090a05070f14070b0c041a041a0c070b040602070f06021f02030c0f07050f0c010c121d0301022701090b03060609011709010507020114 73
    0x44400d010b14007894541506044d42500034808a40c41e2072540003e0000140760382300c4480c2c00b0000541080a00b40100c4495100f50100030803c11468035400c0940b880d070006d007410302007203990804400f03100364107802d0340d4a00390007002d41e01491070402c0c2c22280d03d034800d000d1600e0300c010324a0040c50401c482c3d400c0f01c095075504e07929047d04525980302c1d8680e503040030046540900514a0100300307404a100a8001025650700401c101c034a00b1000d5102004075420a0045401050140a81403400704501500c40f5003ca0016902c0e55403504007000c7e0b000318047d40c80c0c030090000704003050180004007044011500020740d168034503903034015644203011a13030041c0080e4103050000c1205004814a4220350000d040b06014070104100081c2240d002c0e0a12264807000d030b810174020405500042c0203946400e090400a090410660401c00d000040226105840c0080c1d00c041907486568075018000c5a80c001e60040d05041c907480d400381a046038598015031030f01014240703290716900400d02803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 374491681 1250 374490431 374490443
    0xf020a0e0906030a080c0318010c050d0f031e020d0e0705011d0d080a17010519090209060403080403030c061404020a05040507030b030601330806100309020303040306090b090703 78
    0x800c0034000c411600401c030036070602820484801289100c402000400007483c0556502c85801816110003c100c00b00da0b81005280c489000c00280d0001e00380001d807011342868141c0c404c043c2000c60181030110103503540303401c11600c084204030154000e40000d00203200c0500440b10322540c219604d0106108013030000d20000c4507421160402200c080b81c2c03038400351800040d06c40680780c45400c0d43c01400b200c1c00003003807034595100200030100860b000d884c0c201c071000c0701c860000440080220003400b507155296070010b01118240d5444c4101c0303000795800646191199664100030f002c2484142d0140c07002030400d5200004003001c3c446080c03103590300400c4030302d095043c00c0600009003c000d00000a060fa103074000c100580d82003102c1d03070003003002d49440d00d1602001c0341060801d40c02d1640540c134000c4142030f10100c43e41c10000c0c1950100c001c1d075254101d403004020890151986200c06501400006004014070516801c84915603000d51140c4142e516200503031030307079008a80302c05804 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 374492931 1250 374491681 374491697
    0xe06010c0807080d0204031a0703060803030c0c070f080105160c020d060c050702042a0311040909030903080301030b07030b0d020306070311040b040b04150c050a020d061d060702010f020a 82
    0x26071104080d205041c003498149040801034404841281e22541042d200c06d007031003500015109070100d28544c041c2942c5006e002c0e02d464012619940d00015051030551038003c249041c14060070084d45006200c1d06104007070a5950302030641c02000141c0d01c1c00d2448040e207902c1d00703001c0d00858001400740d50252182c4d5200d269030702e59a00404445c0c1070380341040002c000d00b8000da40d0b207004036800d103001070800071170740c42900481010000403800c07404141400c0013042882c9542c0305080e04c04441403c0000b01b80b40007285411200c1240a4000030300c0c81c2004000401880b07035010308603218000645080000b04501030030403080c4d00c0d0720800258141e01500020b21040d10a80102041d10078681040703042a4540c030aa0789039400035044107502182c0490b0411296419032102c01c001c42c5c0e1400c1c14000340807141c40e101e8841080c4c0da4080c3c02841d00c203101c0420030026a01031456000c00d0400000c1041e0111f444a440d81000c1c2d07401d9006600386140362104982d00e20803107480300070644800007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 374494181 1250 374492931 374492933
    0xc1516030c110a1709060703090e100f14010201060810050402090112262523060109110d0203010806091e07090506031212040c0905071d030f0d12060e06010c 69
    0x2126202080c1380b4000c104c18460021161038030005004828030a450300000d01c1e0600000c84180c00000300120301c20113044d101042040c40d52307900b4505480502002100360307214100182c0c050302d00c641c86240644500243c82041d110144e01182c041e80c030882e94508640d998043d45400e41040c424003901011101c1c4120142e0007014000c01c1030603850a040605200041c41080072045082048cc0001d13440c410031101045402c810044001c801080d8500d015001505050f68412050007aa0b101c1c2c3e54038040e461f4040128001c1d1001900c079060b0079956983c55818141e2941001c0c2c8848510340300300200c0205148075200c44a4200250b100248041031411000a01800c0082c044035014000c0e01d0b8401d84800b5180000e090a4280070415105030516107030010b2281000d80c0000c242034a03000c10300010340d41c04040c01d0550740840d181d00c1c00c220759000c0060709180881580118600c6038200003003d40e5000000c13511400d090303640820280c1c1e6200307806e8615008c07c6070058009109491808 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 374495431 1250 374494181 374494193
    0xc030b011d19140a020c070905070f14120a0e06060d260c100209010f050f0d0506040b0a0f051c0203062d070306090606180303050c1516030c110a 64
    0x200310020100b80108919941c030003504411a03007540c20301c0074141c000a000842100c1088110003c0480c40400c00aa141090006000d100212000000c100700004241050f01910301034640d4003564010166090629001d00303c01000e00704154a01800350000050003450106009401d69800440e40040045c0c4960307510824450b506642e0b000070000e10225801450401500c0d0a002d800d201c0140d6030035096001503e07040f502c0b054401007120411500f458a964041650f41c0212003001c040703400c0d262040014046d0020303060858001003121400901002503080340c40803150309171030782c00f011104500f0b641c0916040c410040e4065110f074001c142840b40d2009551110242280b26001c0c02c428500c0c104400a07055860784c000035103074030003400504e1980c03290000618490912090305950100c000d883c1300d0441c400603081c0b00c000310341c48085500c1408410380d004018419038110740350808131445510206980e450001c1d1030244d141c47c160340107841640c0f072001074400800c40001181e44203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 374496681 1250 374495431 374495461
    0x12030c06100f3302330c0418051003060212011503090206120601020f250b07033608032d1606090b01030b040204050c030105011209050a0b040c030b011d 67
    0x83d20840c411551003500603c05494003204000d40900000e0109251414a20380004003500062402a041208100411101180a40180c01c601003c80c9580d600c3e040290700882a40c009450a400066601c0d0740d07030000c5c20018169245409100c0100b0100e40f012000c03150800b40081d0801c03400c222421403421424846d503031180052040710101a01d00d0a0a41449240804035158100d0110882801d942486e946c3d0003903c124880542004450749005010181086682d00c0020781c48180d101c10a00c00b10a204041960303800d007085141d51401e10350b689a202d002c03245007000f1041210329008000c821140d0035840780700034050130502444040c0400030602c4500300d60040d6216212170002d950304042500075402030003034032241d103000e0042c001981c20041c01186203d004100512060380c000d0f2940c00e05c0504c170100000e510f4000c0c40c0040ca0190b00c0c010240400716204100300c10400845003003401d403032081c0a000c1403641d80c0d4141c120145507207810103440900b8600020844e04400340b0b0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 374497931 1250 374496681 374496779
    0x90203040311240604060b0c160509060109170c03030c0f160f050105030a15030602070326070f17090109031d0901051c060e01020c0d0e09010512030c06100f 69
    0x1000401b186d444030010031030340c404030310b164560700099081c544040d26940110300a120039aa608024542100000d24101b0f25020301742e118001c424060342d5204040015030f00c0400d014044941d1050800c00c86a640c07103801102c2d011603c108040ca14100041c0c070541000c440010541c610390a00b405c0054500790030040c0608029580c48400e80c0003c010110f02100550243c0700059440382d640c1002818001840c4400b0311a5060310b0044450381d20b00380d002e6510042d140b42000d441c00c0c0c140700440e2031035445076045840b03044c8881405800c0d070065200d200c03030780d2181e124241c140e411152032482c0002c646c1c030300a87c001ca114004200c2800d084d20700200210f45410241c42e1080b9980d03610044801032046400b00340c0d070120340c002002c07004000f400c2d650078150801440c0c20300c5d0100010400c0300140540c0303010306601240003030a21010800d542e10b6002c0c2105540340d900e080e0340c0820b076440c49031003040a6504c00c0d90700024861003518042e60050b002407803404241e2101c54409025200e9000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 374499181 1250 374497931 374497939
    0x812271908090312120f07050702090103140102091201061712040e0a02090405040507232116120b0a0b03100b032806140f0a0b010e09010902030403112406 68
    0x780580741341c3d0320b54010001c1d20002900031601d8280441a100401e50003040441401f0081004030090b0741c0307280515044035400015211014519005580a40100390941d038100302440d1820000c800190410f81c2034840d12032800700800400075a8070746e2100503120441510104000c28854114a21803082c1d001d40034807070141c94001c070780c0b02003404c41d00e08450079121600039500920070b8000307503041c2d51064210100c0102c41c1c01e4400c4000342c41400c00c5800c181541081442c4400e8454040c0103443d024400700000d044d0703555542c1c142c482c52441103401110004426400500c60103014410700c8078605002d40141803240e00118200d00410408108941c944114080c00d91001c103880e07a9400740d82c4a503010b51200500e145080c00c10b070358a040780a1038541882081100c11003e844c2d5040d40300060100101d44d007000300e030059441500c18030025802008510002c80d0600d0180c0095005074803d56588141d0a620b16143e51116454021040c7d01600b44000010307035004c5440150704550014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 374500431 1250 374499181 374499193
    0x20703080f0705071a190b0105120402121221040f0f020102151f08030901020c090a0b04090b0402180f190b030f010605010f050a09050d08122719080903 67
    0x14079000c405c0050f01010142c09007003001000191903101100c0f107a0341d004030009101a104150001e880c0d170240348040310342d21b00b08000040a40d92030001d540c50314013102e4152240c1c0350006120b03584c5544101510481031402c004020031441c4c0c9100454801c1c6d8212a259076010880c0e0380b4202c20400a10050341140701e804c01078076103011025243c501034001d40e00b0f00c0c5c10784008621150b903040460742c4040c0c03094005002203801a40c0114042c0b68111044420b04003595918a01e28020441a040140c010b403030500e4034001c200c1c41000107030280c0d008a490103541402c01c80301001914045400d140703103c05610204004100c0004003840d501310136003001c03034400c02070000300340f8100038003410076050303034607007004024030b50b0440d1104038080143d1070710915000c413030800904420743d02d00c40c450140c141c212183d418069038806441c4940d040455081071401c0c200c8803507643c2500c8881080701c00350841c5110340100b200141d038500405c0b0f540b082e0543c0308070940b140c0d00b0541282d600690140600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 374501681 1250 374500431 374500433
    0x120c0d11031c0c0f031112041b030b010f270e0c030a0b0a380f061c050105010f0e0423040c03060b0d02030c0906030c0a030c1503020703080f070507 65
    0x40d440c0c0110703500c4840c1c40024483c10500b00244540b0036014400280b520700030480c01070a4218003103407480b076140f00e4200c0142d01e883c50303d0500b00b4141c0c03485416040031140080200712040071210304841c0b0a450344901d040c0c852a0a805051070002040861001c0b00c84081082115402c80b56449580c1000c1d0b602030008213001c20700305800100221f031546088010403850020030701c00c0503807403104a825081c108400004504101104c8085c1400c80e0005108504e0960782c2c264141340e0042d0050580d13a1140b0075406039680c0c544800702c03075042d0385013800c0000c140703540b05003210792062209940e40300311107a400080c40010201a4a6180c1c1009980004840141032000f2513000300c0c4900c0d0880c00c0145181080d00448085000c41031242c1d03581c10408025039400648100c0f0b9000403688050140c0700d4000080c03030310a41482e41508074a0180b0000140070100c4e8030715048502c60b0103004500c40e0810400c40c103d10400e8802408100c00c03001150fa818684003182e43e105081d070034450302d00505 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 374502931 1250 374501681 374501707
    0xb09090c0405030a0c08060f060108040f060908040e0a060e150d0c05091315050c04030b07170a020a020c0405040b040b0703020f0712020c0102070b0f2206020f120c0d1103 75
    0x4150820380340e031407085d0030400012204008966002c540150030007880d086c140c00080010001a1002d80202341c001d03800c006206c055440310051380d9001768500d545554500d1003443d0700710112000404140752000000340500f402204510681e8581c006269a5010404010813a0392005c0c0645074a402c1d01d03400b05943c2c407000f508a000700c9a8440640280e5214544003108104500004483c5400c01003448203c0560500b07950581e98424004002c507601d5a0b0100d403242c984403000c0c0188010710b01032003070f0840246d005240c1d80081c1d5095a0038041000e0a11043d10800d0740e004185100203400140842c4800800c140c0064251601500d0702180381d241001c41d40100205135a500744108070f400c0c030709404128400a9100030f0020f000140e1819140110b280241900241c18200000c0c4078600c8109060300f0184509900f03011480503a145d543c029900c00d0094040c050520a861541c580121944103451a11845400511140b0b1341c40300225226807400170100058403081c0306084580750 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 374504181 1250 374502931 374502943
    0xa0b0406090c081902131b0509120c090a020901050d09030e0418030e10030605031e011d030f0711090a0b0901090b09011a0c070906050a0506040b09090c040503 70
    0x301840c030100d00c8000ea820034440e0301405038030030101680444254403000321041c620410703554044415064130108400420050300b001c3d0300791908020610a101c162a030004081d00022000b910f0208006004c02d008540d1a04880c00c1d4940c0440c1900c00a0002e040c290010401d00006241081c00d014500d0191419150810340450205a02c80c1191802d4206031180300c2406405607243c580244550b1005895a40d110200078087c0341c0f0f85200030105030190f0003481c01810040c04484201101344c0d06c0d201c240e103207044900700d903509051aa1480700c11021042404c039030900c0c051854509480646a4180c1c40131030200d80c1d40700091401c0143c1d680340884a1320440304510003141c9912040200840b03810160041c0c207900e0303d041e40010f07054496040385415102c07445042d210102860ba0000c00601503042c440002d8410f072140881c0c080940c1c3c001038120b50381503030311404403620b0750108400e900072030040c0d62014005111001007460074403c0150801c06103990246025100d102103410301c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 374505431 1250 374504181 374504183
    0xb04020a02070e070203041707092304020108041407090510060305060105040e09150406021809100b07050a170c0f030403021e0d02040c030b032a0d05100513031b0b07110a0b04 77
    0x240101500b085202d216014bd5242c01c068011048441410136100740903580d000380011b810095035900150070007089900122074131070a101140c00703042d03480e101000901012107035020b40c40740f0f050001a6050007070148030b0140405848203030415007800c002134402e1318010500c0030503100d584100010300e00500d000301e0203035000b000c0150359128802ca906500d004540c0e0058002c07109502040281148403150200307070344001c01c0060f85c034a40c40c10818681a04e03180080d01c805948989040081150b00091000004960940716117190080c01c087d00da0140e8803020303401000c01c9503910a418071130000300341c0101c40108040e01c170301c40640204086034154040d0311f021aa803004002200d20301000400584c44c44803800403d82005110b0502d02d03d0900c48440f40030305040103c84017000b105104a98407019841e00c10480d40c940059640768108110070140c0101e510920b0310020b081148114035801608940e240e8034035290000300b280c10941d10320188031940540c01c00040001c8815001c075000d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 374506681 1250 374505431 374505433
    0x30209070e0415031b060503010501200303070e180610030221090d1205090a110d060e010f050f13020f1311091507050a030806041113090b04020a02070e0702030417 72
    0x50760039417034210981d01c0b20601a90b80040703c40c2040000d10741c088100c0303042d204c081ca40000250400c0a000b041090f401c40108058040801044190303640000d000d020784204840400c043c1c0c072001c1010101c1c1c1c40a486ca1900000d820a41124090181d00205451080d0b00400c101807007100c403280407501010384800c5415009403942000e100e40c080b0182010040300300c810042e0303007020005c60380c4e6101c130600000c0c280c500250103030f10165202e407114502c1a070810b009006107240da0710560300074240313030100303860b85440c000100d03c030360b490315448a200f558094a45143d00090340c00b0051142003401900b680000e22076820340886685d4082c40904000403d01181c9072800c0ca8100105005c500400c4515000700703100b403002050000031312034080368040c02d0500164680c0800706018040191180d11400000540c242e10fa0b803130740508104441c2c41c4007040103440c0048081105034071800294000503442071806000500080540540000c0940101d07858a0303514507985d00070480780300104180d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 374507931 1250 374506681 374506721
    0x1804060c020f0d0507060f060512031c02040311091012050106050918030a030b0a05041e11090a03021e03070e010608010602060c0f0c0a150207110f010801030209070e04 74
    0x2469010440440003040502c09040c141155110040c11405220001361155803150a014503248583c0d00401c05010094008001c040c1c4642120307550f903008810403511800502c102c40e1480f510740c403e9030141c0b81d0003003103030240800325020040c0b0800040c00246d140100c540340060351600300c54104c11141d100304004038485240c1410030203c210300034a080303c1003000b41810303120004003008950105903941030004281a410010908600850308035640151515a080300c1e44040742d100d0700710700c0c0c2c502c0c0300034001c04a202107007846a0040c1c400d001d400c41c036102070138401440d10010010700c034150b80d01c400039102c1104002138641600d550020460701c4250303005200791030703000030110301401c00d41c0014403080c1040c9501c1805031007008200018000e010505010303100040c003490b5406030300062801c0950010040d500000c0d40056021a8401c7c201175a0002030306240c0113903034500c40d0503156002680e1940c0c003441912a8010108020401606150300301940d451151004c540c1c81c820a0f804 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 374509181 1250 374507931 374507951
    0xc02042d0f020309032502030a0606150e0f0d051006030807050601090e4206030d0903020901090b130204151103090d080f040b0d020901020c0d030c0f02180406 70
    0x400c079001040503101d028010001c10005400c00000c903050107042c000c1704118a28440384001c8006034070400203506000b84101d00091000307540040c81550b51488c0002303000c040301c401c2991482400c00d5202e421540d040800042d504d00b240d21094041d000c0c0041e10142c0317105006200490b50103070800c44d01401c4c0815514140101000100c0c007501c41e0b40020050712540c0909103944a403070000714143c2d21114483c6c500d44081d4440e00e01a030500b6251440c05403d181814002500700444d407407406031080130b0410310004e200e043d4401c2140d4000d004030000d0f13400e000801000d0007404007040d0301700091a21907018030318075200600c0145002c1c03400114041460000070150f4485166001e0030394420312880c60141d850564040c0601d41c407030341407a45d4174102d02c0000014080c691001c4649003001c9405c107111044d0b40c0060418003426400c1d0350020070f940042102440b009100a00011650015400001c2c00300d1424010b8074001041c44c1004e06072034000c10b2010904a50807201d543d16203a140e8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 374510431 1250 374509181 374509271
    0x111030414060702121602010e0415090b030c060d18081602030c0925030b03070e160302040807060f0207050603011d060307050f0103111603020312011d070c0204 71
    0xa5008802440076010342e4818840c08417039400f5024140f2030075020307082443d045a0082e04a12154500a0028050200000c480d030202104500c44c0000c001e0602041200310301c3c000c200d55208440c01441103051105d80c0508100800f074012404410070300b0b41a207200410200c9000e413181c20302c1c495140402c0c00b03041c81454102110400540c0c01100c0840c2440300302220003018602a1203070501654011031003060460107010b034201c2658060041c00004150b001c1c001f10f00c0382c403032041074040038095a4500b508508074411803040341420b4200301402e2140c148144069144940310780304551580f42c440000076000d51081c0d0050000a41d041012080d4844500c00303039074890300840141001a140002007400300c070358089464101940d400c0950303121b1902d5801e59859108101800c00542020302c2d020b03580c4d5102c0f0182c00c4d0341c194108000500090080c1000c8000604d00d410940103480da250180d40c00400c415040764070545528008094140003070031075400c181119110990030100074445 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 374511681 1250 374510431 374510443
    0x1503230f0a0c03020108040507031407090b10050a2d030c030b03071a090105040b03010602010605360c0c01050c09041103060307060c0227070f020109020a0501110111030414 76
    0xe02180d00056078540119800d4003100d011280c0a013818100da90f102c2c0f0301035041411070b4000500c1000e00c66030b0000d0050002031204207075504010100000481c2c2c3c1d00708912042c43c0324a07080001d130100f05002d031283c032034008100f00c0701d01e6042c456802464140040c40302c0b4031504014000954842ca02560540d240c020304444007001e03009841c00e241003a06290070400400c140c800054000904040c01da445002154014038030081441d03200d503152007009000e0101807140612031010130126444107034011300c03c4640000b80d0924402020000082d5100d0240d0050109264800c01e100c1d4a07001c00007801132078804c164520045030340d002144100421a2203d0307030000b0000e9010700401185d920005041000e0380d00d942007855244460340b0002d288031400101c00000041407039802c44031002a0200a40281c00a072500707190b240c0141801c078200d6820540103940a01d440d481000154050303481d41411100c40380001c510349074807100c00e1486174010360303040320703070101d10590101804402d0100c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 374512931 1250 374511681 374511703
    0x30611090f010c02100f050d02070c08010c180905130503120f0a0c210209030307060b090109020903150c0408010e070314070f03170904060e04050c090712150323 71
    0x24001d2402d40101d1170448022480009103c07107909940302c100e00403000c1e18005e5401d18000c0d5170344d003e286424101c104483c443c81100d9800c001c9181c50503805109000c5503a640360f81d01174034041c0b4010b40c08001d00740c090600048140b11070225000310f40d050000304021600401404824142148a000c4210000b805030700c040b80b500004c04103403688508800e0591808c0304d8480c0001c62b01c50740320030082c0300780b50659500d807000007006820005035821982c0f03040022100301880f40ea1b9080443c06a00c1407041881d455084041190050300700c001c0f03045c2e048003100c03600ea4203107502d03505914216805000d503607885c0e1b031042004104114920001c01405404440070b803800b45d00d0000c083c0c882c0300341070200a1060080140003115146d403001a94840d032001007051120755550415000d007084260b9084c1c4140c005e0100710300160070425600c0e03015121540e903c10001d00c501ba200c5008000440030714840ea040101c00101044510078101c003040d0004138091003149103040594034206d05000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 374514181 1250 374512931 374512937
    0x6090209010801141c05100504142401030209040f08030c0414030102210a0e0312041202010902150c0f0106080319090501090323010c090f0f12060e07030611090f01 72
    0x40d010381e040e11110707445c03114145140002c00020116160041c04d04801c0d103100080d07186807100308018844070302c0e458021601c04009a0741c2c95908961503801682041445a0210039060010001814103c1d621075006015140d80c4d085200c02d80e441408a0340180c540f20b01080000c1002e1080d451401411184480214001c500c0c0074802101d0408061070004001100d80c80980010651601504039214105c1a42c080d25960480031901c2c0104110075901510b0842004101c00d003102e00501c135400d021070b0020803241e054142c0b0b04020101b03030b0003005100301c1805000b8860710022402d01501014001400265448102c11400c249600741c40d69600010004903480400c05640c001d0441d006490b048155245d0004217404035080078840c100c2200c2640d8a80700b002000940c0c04078130fa0054904100d041d441d03150360f542c54816138007d20300500643c012000d003003000040c45079121500441c207140540b242035540c0c3d1500c1c02201d01240e001e60404c0d0340011802c501e4540f110850100000900f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 374515431 1250 374514181 374514209
    0x209130c030b06130501111615080105041e1517010506181504181e03090605090102060a0b04140705070b060d080a0f0e0307030302010614040207050a06020f090406090209010801 78
    0x1013556400888035104407814000001c04001c0c0341242440710707004441c0602d18840342150343c3e8828103411044000c1c580001a941c2c80007040c0d502d802c0c0580118070240080d0041080e1010300b6180040100000f41d50b500d010401e40042c110b038802e9a02220304800000004003490281c0510600610300c901c0030210440b03550821240300c1e9400001c9100c00015900050322141c4030541c3d0030200c18140024204824040c0b84100448800f00c00c08070191090b41e405e0b043d40d90302e1100b600c0c41c0c00385d14201070242c2c1058000070f8015015038041c6d40d403008020030204610260100c3c500d00d4000c190f80d9080003030000225542481400d800c80c0360040c50948043d58104043d44440e401400b90101342d00030480e800d031602c0c80da00d00c14494860a42c00013402d9409055484c0f402a00800f0507100740c03004a0f4100d40755000b54034040c0309030f501d02078201004c0d05039041aa612000291b11a0301500e40d600414070081d00151224404c3d00060b09a00c04016a2201c203d1300140011030160f000c0304844105c6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 374516681 1250 374515431 374515447
    0x61401020714040209060706020d1410030b0603120a0c050c06040e0103140717010c020f15012606010f06080a0b2d030a0308010609080c03120d0209130c030b06 70
    0x4201d01103480300a0b805074040600c2000401910584560640c0310390003080f9001881205d034001c00030a9454402004000c00900d011404503104507045003140403d001e040000ca01c00389541a4000001002d0701c03505103010055400c550055071500000850341180501008000c101a5000341c3c8110341182c10145801e03200c1c140d41034140401041e18440c203180305640e200400241028000388000740c0400c0040c0301c145802000c03802440710051092401401e51540d001c02c00c0030700d64079106000c000c26802c1021801c0303007680d040441454090071400705241b042040c071459001c2c241c06003e02900f6403401100174a01540500f0414200b4907102c80c0c4800c0e5651244012910600c045c034005000300c00382440c0d10b81c6801c03604115014081c6142080030198046c8540d41a9900758945010264492190594580c155140039401d0b41c0040720a9004081c92006050140c8031750340003601c2c01c500200031501002010307240c00640c41e01c42d00385031400b90309800785011481c02542d80500701802 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 374517931 1250 374516681 374516683
    0x131a0405030412020105070b07020c04110c0705060a120903080711010c081605040e01030f06060602150606070f0816060b0123030403020a08071209060806030307021504081e0106140102 81
    0xd148200002090f49007464000c590003803042e115400c1d00041101003514000714080c2d2680b040c3c00b50580716500c0c2c00555007940814109407014410028014a040c60424041c0b00c1103500c0b001d5010280100c16082c4000b01c401401003001c0203201384d480030075a003030203940601640da2a50144400c1c3e41001407414040741d001c01940e510100341132000c007504c1c030280825a518840c0d904014401c20420001106001ca01103400515074410f075400c01c40d8603500e03c02261601600c0030b014190070078103008151540307000009001054011b09056000400e81e6950b03a080394000100781c50782c1c0f02d84007160b6080c41424800c0040c0424207003040700d0140405038509007481001d0300c2c400400070300030000c5400c7c9442081065a1140e10141c0720340e49220318204081c400180c0303009440020184100804c1080c401e0b001c640c01520007034000c50410003564204603806640da1120480b00b42c05220006000108100e54040e03240322142240041010050880c00c3d00d20319000141d0900950394204180d9038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 374519181 1250 374517931 374517937
    0x4063210120221011a03070b030402010507080f0412051b030d020a030305040819020a06050901140c072a0911040e040b1015090501021608030d0207110603131a040503 73
    0x1504580052407280442d483d5890340f500140c01c451550320748840740454059944440c8035004c0120103c07400c00d541c0b9004c850131440704640080c0010014800307403000820040c0641420110b81a540742840e41701d40c901e1010b0390100760280e5032070b8081c0d14980c201c00f8a6007028500510240d0282c0100856034101a65401150354002c04150361800010705000098098648039015503681082502040070000e55074018a0420b8032000e20b88000b10710112014400e408403400300242c291000da0304c400d42c081e0150003d9005444111207615504400e49000310715400704158645004001820906200119000089081071620b410403082c1300780d01406c03140c1e9510aa1069204000c0c2c1d440301270300c0c82030381d40c41d50043e42645a81070781d440c0c1254000c0341480a488013a82150b00701110b07107264940003882440341c2c540540003001014002d02064008250030f40c040c000d041d00041032400419801e03407080b101d0310010b481c145003d80400110031000c40e100c0c02c014a201c01e03641855101c05440384 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 374520431 1250 374519181 374519183
    0x204140405100b0a09030c06170906270309040903050327030d0b0a0b070804140f0a0b092706040c051305010f0e060318070501030c0905090406321012 66
    0x28004139102025a2090b03550390044c6a103c1d65401409581d08070181c44900c0800c6400700080e40f0b013002034004840040d26610030741600c7d031030010f0310b00380042d40002c516586a4110581c00104540500e80d26240200e00c4580c0c425510310342d076880e04005d290385241e0042c0c08800c04a28107811046506000000e59500540e40680084c2c0341d005040010110700c540d511611000030045511000e00c100c041c060000c07220890a00007110b82c69a041054003002d04840c070b0350081d40030905100c648201005440c0c1c1001c050404103c2d80b0120524040752020b0501110300e410a90080144906140c040e203204070280341441c50400260901a02640e000d0340076850400010414000180f80301b00c0603132040c680003426440da070717041804080301041844076214009200e4590005403551103445141100505c59456507141c2e82001c0400001a10180040d203480b030300c6601100709400c451103024a255440c80035603034006414440d07040c008000800160348000e14400800040518180c1c60880c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 374521681 1250 374520431 374520449
    0x30b07181505070b0a1401030b040209070e03061812040326070816020411030406020c0c01050c0307060b210601090609050417070f060203130c05040c0e062506020414040510 76
    0x3503035824800d800401c0106c4400144043c1e1780300010900c048030302c405006038001c1cad03004c503815500d80405403403d84030301d64100c1c1c15500c00f200091260b44a80300c1410032506510940b20a5003800000e00030a8100b030304180ca643d011400301103068007410480307503607040d03d940b8094208801038640940500411802c014203542034020b0f0b0085550310760006109280503c92280c69007001d061400c025005001b014015100d01c565904641d070165003a281114a40d000840c0f8022990f82caa034044e045580c101e0b60440b0252100c1104218440002440398421200070b145562500c04500150781c4954415801d0310b01c2c0c5003e000110340303400b40020300e16078006440d0b0350310310807494000c0841442c4e00380540081c0c804014005006901e00451450300d004140e00c10000c1c1c1c0700c03c1088100c0c1c811080d2803005c2445000c00c22601d05060f00030f007452802c3c003600460300d01c10700c4822495180040300c0483d0034960001e8284400402120f28210109007581d003000f15140005206449101c2402441e5070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 374522931 1250 374521681 374521703
    0x90115180b0301020307031d1c110109080d05041b12030f1809020a030c1103071403041a040501120e0c01122901081602070302010f0306030b0718150507 67
    0x200c8400c5400c40c084600010700215900d01d0220b40050003852640b481407000364041c0078001c06d4880c0000c0040440303001a40010368104045400c1e00c2400e90304039640c0c010354955170450045101e00018040442c801e41011495107001c1c83c02988040400c0c03400600c22040701d5080c0042c800d04810b522840b60b0500b8104041c803c80481915032080810a007540385184c000017042c40041d9402030819a180f90302c0034400102d407800b040d0348815031500e86c9805984240300c0e0401150904120070340460f2950241c0346001e4640142400c142d4450700380045503c80040c04114551b48065044140e080301c5400700080031080d2480d0703031110911340005040000b015001440325140740d00c400100c080007503503003811180c1c103881941600b200350f4096011840060010741d0b882001d81480540b00c2450b030141030300c1415030340103407460206010854101640d03002d003c40051a010b040602030030054641081d00d0701542c581c80c0c41e040d544d40100e20b462541000c00921180c100c0140d800d815405210428 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 374524181 1250 374522931 374522969
    0x80709030f06020a14070f02130204030f060b010e09090601140d1208100510030501091107170a050f0304060e070f0807061b0b0115080609040803010605070615150206090115 76
    0x8000010740c071042005c22001503260200321812255850503882987e4074032a50001c072421204034080e610014020301075581c2c4203400954243c0c4000324222050400d83c1c82c1d11180c02c040740f0b0300340007140e5440080d480100140700c3c071700c1c400e18080903028084442c1d508409403965084c465a41d1403c20310140322818010550113088058404040c0c040509400d0a10381001d4000300542002e1003000c0c2d52a10308500c60411284000403640c501c0d03089071280d60014401c0b440c0080b180d0001d03c010080090510869040e0035011000314000c500940d00440d81884007004142002096800025031206c8464100410100452101d00721459401e04e1540105124510010040c0f2003100410041601c400171074961807840071901080110380d03400f5495940c1c0400c1c40555034090b54081c001040c00e100421049205100501d00a44103a2022031401000030101400c0c40e10340c1c000300ba0a004102450141030b6041111a40c008402d000902041d01c8100b15940d000c1c51070f000e00e030317115900802444 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 374525431 1250 374524181 374524187
    0x10f2f090f0f0406031b0e010806010303020a03110c0904140d0e010f0c02010c06020c01051605160807030c05012901050304021807051c020a120b010807080901090218040201080709030f06020a 84
    0x13400954100b001030b0104002035020218484550058020f4030000b60004580402d00007041810782e80d1540040407011340d2624290390302c6180c00030388100c07403041d030b90407180c1ca4441e80001e600407485500402c6100c0300440400d401c0c0000c401c008810002c0112161416a03448840105c0c49181030034030034040390407400101d40300104090081d01c528000110754102c160158891072040c4481c5182050360440e94004454503c1681e0b00c48004100306c501d1800852565001080490f01c282803140300b0060316030341d103403d4500c0121150880600161078440d0340c4100441045482002d01e01141b841c07626500046045504d10f01a590014994002410b0f060040e4211031510032100c0c0503180305a4010b13102400380d84075030500b40008280d4030201c152001a4042e0300219607058580c4002656400c0341141c46400042410005640b21110b05015807a0304514100000f010000c035003007460140005442c41c40d011744941c0802c540982c5c100081408a010142d82c1e030f03400f00c0d0141c1d0380e002d008400c1b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 374526681 1250 374525431 374525441
    0xb090a0b01021002070818010c0c06031104081603050d0504180527060601021606080601080c04050a060302041d070c0305030403020c180412110c12010f2f090f0f04 72
    0x200c03d01c40c40002c0701d400b888907990203061102100540500071440c2103004542c00c41e145000203020803000b4500740f02c000d00070703080080c0186610741810b003029a00c2c00b01d14500840e045030a0881110300e001441400700c1400b81641207552803d12a280918046906c0b005400089080a11680d9800401c1c42d0b0104105050a003184001040c1f0a00c0d40605195460b102e00785c0b12180940304007110f03a00100011010041100e0058580c41156034501d001916044c400604409020b0401c20004c1034030340d01c3e0088a000350620b550f0060f205d505060401340b01e801351880d01001d514a4004105401d540281e5206103036900d8540746803651210303c1c040c1d1030200000c0003a580112140031075000380302c03005202880380e03014003000307504092100c4003034903041d180d0030141066402c81488480c0d40e050102242080400100000603a41c80280c034840032a00070fa0141884408184500d0f049075100c41400fa5210410054052422010f44009040a001e56500c00d003d01e80340e0105400540d520f0b882 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 374527931 1250 374526681 374526703
    0x4051215010e07090501021c0320030c04050909070302030601031506051305090105100e071404090c021c0302090603060d060213080c0a09063804080a030801090b090a0b0102 76
    0x50241d584980ca00702d80c0200407107100e0f0006404140c0002d080d8030004e0b10b400f03400d82c8600b16105001d2201400c4015000e17060344000409c004c1013044030402c11000c01140310310b1490749810b4549062004021100380050715400c800da100d04420301c00b680c3c01060407811654004000d5003083c2204216102915080d400240d02c80305202c08030702c3c010200e0f00000d1244d2040002000103680f00f0340c801c021a05103014080080000c40005082d050088805810a000c00450282030560351680310b804d4902c081444401604070080c4041c2c0c055001403000b410341b21a040950078070070540c3c0400e6035030100520340c1d441803401038440e40521030103904a4103d0541800c00f921080e45031004940c0e1007110401041c0070b500305130000500d002c5075100e00700c2134072586500d040002d501c84400011034000c0348d200c491070020055905045070340c3c810040000703200705e0010700781080e800c0c2000340a2440503840643d02c10300303190440e2040d82d1075040301c0b03601408182c0d00040311050040100c0c07400e110340c18 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 374529181 1250 374527931 374527963
    0x1302130b04030305030610031a0f131a03160b030c0a03020f0a02300702092d06010305151f030e07031b0506040e0a091e030c0323040512 60
    0x3000301c14543c1c0003005510600b407e0f50f001e507042400c01c0b0110100c500c004c0d521100080158003440842c5004528040c04600003090310012040c4200d10b04200d401003050003102c40f010303001940d03003414203000503e02c0d412010702d81c009103442c0c921342800c0c80c0310050400b14102800a103c0041c98020713815200340d40480840c0f0383c0c441e491500c010b951a1203010045000310160394030300a100a0901c0401c049880c856455402c1885541c24414110005450001c4422100102c921010070414401c2e00b0700ba4540b15024003401c0ca000050122078000c0c119101c0e0a504050707901864076000c080014500311110644e8080b20035040c11001450704a0820465001d0b80c00c0c000140044010421071506200301445010ba65690810030144658070616001c1300b240781c001900b28201e1b0388075005a82c041da102007150007520b80301d03040ca48840203044001c01d517404040018150700045051001003544500c1d104100d20300d10b590094007591040500c01c02e00206800140c50040c8407180250104c00d03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 374530431 1250 374529181 374529187
    0x1021c0522061e1506120209040c090311042c0709020f04091d1207060902040504060e1501030206040b18040207030c05160b0910020307140105011703091302130b 71
    0x841c01c42c0c00b03040d298280002c0302d000442450b02c40280c0b0300c1948940050b41c0c68114003a40b4040090740c0311080910341044140d800c4c0440925a01d035402440c1d08414651340342e4800758150f1070100d0320394604041c805c0c000d41c5041005030500c0b1440035a0080c60014105400e18525180002031a00c441600400221800420005c050510680140003aa20000030600c03d0000f180030614007560902c00c04040e5511490072542e49298503001014094000c2c280840d510950344c000c2402e44000740c40450b04030390b0741d40c03181d49039480520118181d0202d1007010810341d495600058082d0103507000d40c08100c40700003200f07403d0820341584190318500281003551681074604001d0030401c2030180644042c0141c05411004800e212a4001a81d10901c03038142000e6070007040c040f0b40c4441003041815444100411008200410660100740c070f03503800046219030602c00c0841811449400080d00da900a01c04400c1c0c0b503030707601c1048008208042c401031300c03800300e2580f103c42c01085600080c80d6203400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 374531681 1250 374530431 374530433
    0xa170c101d07090c0906031a010c0807050a05030405090901090201140306040605030f06060108010b1903090809090a0515030f060a0f061a0c06180c12120f040e070201021c0522 77
    0x6600104e48280c070540b18070b40135645c0c0f40004d030241c42441792046074512080d00d1017612980281d0f0f0250340c96004070340d80c43c02c0c0362070b60382d4540c600030813404151100e42c0003080c10005c9107800c000302c9903c19030190081c85081c03040d900181503a0800b83c0d907031250030004400a9070742c0c0c41d03c1d40418000c040c000c040f0b074661600381c00110380302c010555040380099003c0700080340302843c17242140da074043c003241107044c81d014100086000300940c140c11602000100300c1400c542e80c80c986c0359805070f4121400081c040c10000029001c005240c12240d0181e00410001c055041c800309402d54044032841c40410700c7d610000c88400244103d03000364058601da82c031300500d842892006405980d140f0401c8a20a13101c104a100b18150813030705960b910341c0055914041410004950005020710004076074501802440c00b8659400401201041034000710302001141c00640c00150440550700086103050140708500d00b100b84c902c02140d1a441c0c0310b101158040d001c021072090350320000c20321012a0049 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 374532931 1250 374531681 374531699
    0x60c0609031b0b061005030735180c030726030c0109050f060601031b0f021f0207021504031a0903041206021209060f1513020c0a170c101d07 62
    0x244d42e00f40c05495502c10211503103000d1000c0701c4c060040e544070f000e2500000c2400201202201c0d0060040300c0580ca03a404104100e400800d0049100c122900c10800700840d11620b0135040381d01107403080d80209000c0069180440c0702c8003203800c0081441b002e000401c80901c1c550300c12007003210119840c0000079000d000c008503440078401502001e4595035281e5400440c02e0300d45618a00001f9030740b40c4050840f19001d0919a00e0101143c01900c80c540c48112002c00d4840c074048101e540c1d560005100002c502c0c3c418104c02c0071180e844c00c0c290804d1f040d43c440d020b1003950020034150108101c000302d0b0100c3d60070826100240240c40050004654030b140c2035019411013015a050144154003060303041001080252080078a0304595465035610051020304002d000304c455013080b90805418011007003030009020803007044005001c01c21591901c20303560a0541c002941106003880542d11400c00442c4085c2c1d0744180980215001d0a0b106803100140e4048650047d1071166810001c2c21200c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 374534181 1250 374532931 374532953
    0x102040501180b0d050915010e06030706080907060e031c09031e02010c03120e03070b01060206060102030304031e030b06030a0905061e0112030c0c030501020310050109060c0609031b 80
    0x200a82c0e5100400460780c000c40e0320806680030380388240c4070034003031042d03611410307800142e00581100440fa112080e1100e905842c132400e80000d4000c0d9074a104001d56401c0803c41800244054500703045246401c00219464520364000c410822603814003100700741c2c0d02008464440b148005081d4800c0100c1100946245014802245c9644514847d008503d024440845141d9010b03102d400b1007010a55046034807002d52001c2c510140da03115440c0740074441c2007018150740352140088003c41d50501c580a4500710b00207142d64110b51040040000180d070184501082c01819119002d001c11050300c16005041c2801081c0c2e00000f021041210381d0a0740d4001583c5a40600c2c1078030391230740326540c5030007075010b018840c10315410649004100d14600e600105402900074586000342c00003c0c0d42e49011801c00d540309580d542c1d008400d02c22110041c3e00340310014102400c0040105140220140000326201000703441c05035a213503c0400c0c907006d80f41400d622440001041040d00d1541390402c200c0d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 374535431 1250 374534181 374534189
    0x209090703140c041802130504060204090903020102071e1203090602090402030c0a090602030a1b0c0b030405030d0605182215020a09050d0c050d03021207030e0f01020619020702041b02010204 84
    0x1604014542e8000c5c0960b140380852103401429035081314400305801000781c84040c1c011242e0325070030400020741c4c00c0c0620030340c07080c54400c2c0c2c00560348040a08210184007541c0e8844400504e11395540c800150076440445402d01840c10003080050306d41c100f40c002400394a4074190054000410450100c905100404c03009103161146051a42c582f00100e0752806041404800b16110400f648021100c40528400c0b0b81d2250081c450480e80350036503030300950001c2c0c40c03c0b19158000308403c0c10300c42003801a28054201070f1a100c5420319806007010300307008041c0101318107200340c1105a80c07107848421040307203060f0440700348802242401c10350360003075201c520014000342104002081900e404084025051b41080b0803100047c00c0c00c00f0054504010340d4200c00703502c141c2400d540f03401d204001800500d4000e8503280c007a4040300d03060142c41c2904125450441d00070f0300030011400c074011101c10302c0b40540280161240d100381f001c2401085084060540a900e520381e5440680c1e0540082c41a5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 374536681 1250 374535431 374535439
    0x50114010f031b05190206010b03010515070606170d0206090a060b04091a10140d030305061311090f0409050601090b240408071508040308060105070605070e01110a0c030209090703140c 81
    0xb403140039034126147c90080c001c4002c0c2d44020401080b8030300c1c0c0160f840081301800034125152403001d1340d40c6e2080b12807903401011180c5171010401c10b40030003480364120010003400074144600e0034030f041540700e1000c0b410050143d950352203180b00b980c07119807041d03501c41e60000e4824140008902c51100c5048119200f40b40c814815201042d13071010020b1007580010060602e00500400303079001c3c0c01070710004080342c2d0800c080a118900920150044034100f42020061079074411002e02030060004000420a00642c241000c4800140c40028018110f0700004400103000b032008000400d082c1d04881840507004942c000003011280000040048805090886200c2c0d5921280e03000318a8581ca03050001c6000d030030004002c00e020f030700615445541490410701d0028503590f814112801595010700050744d0540b002084e580185c4805200c00c5080020142c00500d40da5081c8c2c100d0705804001e01490078000810181c200c204200780256034014080c0200d490844000795607142214205445 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 374537931 1250 374536681 374536717
    0x1903080c10050a11031b090621010f0605070b07200606090601080601090915051c050c010908070b0705010b040903020604110a0e0c0a020a0209090c01080a050114010f031b05 76
    0x1001c4294450302c80f10104521a56066544101c0d50306e24200b050712000d2400a4100204000c90750380d100101001000c0d40a0301c200d003101c140c0104500c000503000250354000d4280c1c20310505400c1020381d10316a50240c4c1e03060301c590318544c00303d400055550348552003444800c0e0700c0e14100b40101e109485800d060700c003a2000d0b903e00c00112140c0c1c0342030b1a2180801d050b180700f800100041e8022440350681c6082030900165a1004144000a111440c0300006100401842000303028050f24070f07a08401d29142803d0740c100300b20783e9201d5804d84901c00c00301100240d92010400b00390840c85c01403800070010050806103043c0a920350004035000c95002261500d07000e810f10740f94142800303030303140e41c0007400d990b9443e440e803803655a05c181c0d0b200041d0b200300c0b450a00141c0d070b4a64118030810101014007030300c2c0c181800142840401800d049915424000140942c054100c40101d85602c2442c260f80704000c5c180f07042e001426800403948240c0e103204104075905811000421554000d5104556 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 374539181 1250 374537931 374537941
    0x5030601180e0a030c0b0411060f1210060905060711040f090510090302030a3209120a080702040203040c0e0f01050108060f100f030f02030f090705030712021903080c1005 75
    0x140300d1095003c01008030b6180d50111000c1034860000503030040c490905200f50801100020b005a0010403a5800d000b40008208054000c1052080e4210711f0b410020140c2c0b43c10f10301c015140480b14003031180181e0007c2008818003080200751100400058820824142c0540055000c1d01c0205801c0e1041d10401c426031024410f2441840c5c401501940070398105509043c2c101d1310300c5003806400c03c802c912820102a9034100c84210f40310261402d00096645854a060218103001980700c81c900390008800200401c2c841408ca440301c81d4110b81c01030b526540d0b4a009018007407250002c1050801c0b07070003001084448021110b05030340098980740d003035545082c204101ca5410034070264001c84040b08142a8a006160500f0b1003112820007042e01d211515030f000480c0c00849070040f49120041c00d1002c0c031034040c02440c0c050642a80a010043c0c1000d818000c01c40d2084002405a01d213034964031000d160b404050700280d5402000c9035035400002002036070b601025800e001110740303846e02140d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 374540431 1250 374539181 374539183
    0x1107050706031b0c020f0d1b03061d0318012706080a0608030a0c06021c14010503030708041e0b0f27010f0e04020d181203140c090a05030601180e 64
    0x11940f90842d6101120040c181d0309006400b00c5003141d903900684403407400000900382405643c0c0c82e0301340001c41e8500c0c51540c140351094485604141002d0b400380e0000500c0300c0008011255642c00e041c85268803a20000d0040f540204200071001d412810500000000613140c40840100d404945d10006240c40344021402203c50b14854408298070411605001034014800302c045035020303000041c1403820a103d0140c1050000c1001360345c0e41e03520b117400302e002180c002c61070f4003501083d0000c505000039569003240510440c011103000c9190405c41007012a140101c0c140601060904c0a4503070011031031342c0040342c004000c800c02c21400c40b141052030010050340e88000d4103050b5940981041c070640107503845e0091140440d0015000c000714810300004d4010b0005028410282200858031070a010400a204240d00e0301010300340310501ca8840300f00c5503069000310449a0a540d61642c4000051031307500250721013a0180030384400041e1100281c60380114600c8441c005201420f5448151 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 374541681 1250 374540431 374540471
    0x30601081f050c12100306020c0a03110325110307030804091b0909020703052814090a03020105030612011b020c090402060a0e03070905161706010e04020a0201110705070603 76
    0x150600881480444400c8240c89681034010f030307a040b401c000780c039266110350007a6480094844d00591181c1610b0701017650040c00101e0000c00b102c081c5080c880ed101d00b056080d004182004090032040c1e450070b00b8003009440b0b841c1030a000030110382c805070380e030b14080310305d5001072080380c500c507140c04005040c0e8264241e11220354040c03683c80c00403041c249549030000b504203042c19000c1100500861a042441e000d46411013000800349210f4141c074414000c280100010780000d0f001802e01008a65458080c0040152a42400c115449941e4000400c46c200e101c01186403180d030a18000c42500c1421454132401151103a0940d2051034001c0c0611406590544000b500900c1c100016004540f041640700100103004086d2011540d960240b40c00f918400e0b6605240c81c0305107100002c8240e00401141c81d4180d003004488403a00d080c0700083c1c118031f2107041d02d5000e42c1d00000c000101d14800e40c0108040e001200300030352116181d00349075503500300c94040e06c00800d241c8000b03040010018040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 374542931 1250 374541681 374541691
    0x8040b1b01050709242a0215040812070507060e040f090b0402100f090e10030803011401230d0e01022b060f0506070314040909080304060c080c0a1b02030601081f05 72
    0x50f00c90110b04158070700b01e075904090404103642c480c1404400040e582c01d000c02d00b01d4120807914580722402c0804590400010bc51200b251100400c00761380059001304200f000c841346c0c2c2c1060700180f840907000c14043c00c0340c8074000c0d104502d040d070540104074808030011700071070007650400340025407008182d5101c61110075400119007154400c02034503603030400840e44a5044454000f401d80c0e00e988001c51a0402e82000c1500360a40c1140382ca00c1d640700b0110812200c2c1c0400400510039000c2c0304c042e01c1e02c01c58246401403900c5200e00d8504604c25012603a4502e03520b400c01034007850201c03450f0328210b031403403407900010b043ca4000600034201d5008403054580044c130442c43c00380e8070740d815910490400f4041d050108144070001e403811251150700c00345402000c0081c2e491a0500e0040126003481d50b02c5c85c140540c4406000110400c0b206031480003070f1904001e02c0e48401101c005420f0f8252035030080d8584529000441c0c0f810001c6504921400b0419071402d0702c100109520b004d456040b24 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 374544181 1250 374542931 374542937
    0x5030d05011712031003060e0307020405011d090a020a051905190608060603040b06010503040c030c06050316030606051c2012010f0b0d02031909060e07090908040b1b0105070924 78
    0x2178207101144699000c40103200221040b24946409a80450181e510903480580000c241c4030000402503017003a456584801e94502500714003100350700090f02c229860180300e014500800000b081035040c4600f2a014280007800040840c80850018510040c2ca004203000142080d0104916041500640f0b010790f1b809058416542c0d0703000c0c01110b03e5000144185c4507200302508c00008103140040032800b1f400941c0c7c5840d50f0b8a4410b00e40383c24030780014030100808d45000410881154041c0c00d42d0305107407160041d50400c1104c404071401521400009424903080326808008003d80880146400700102000c44250780e40c4514031000e56003d44503207044420100403641c0865440d50080d588200c0c800710826a928403024001c04a60244000310b4080e640ea62410820200400009008048065041c004111280d5400040d40075511461613807013004519010142401140d01ca111011380e0000c110503c3c00c03800003050b686440c840e980d040310440c18040c401401904004e030707916a41b51 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 374545431 1250 374544181 374544211
    0x60e040b03070b0f1c061401050a020d0e0f040203132612040f0f0507030c14061e0c0a03080103021840080424170405030d0501171203 59
    0x210101c0f00ca510000302c0c00801c030020403084031008103480300301c0038048488400095039801c00d4408468a00d8600c90a0b040c07007828458003201d25800500604081014030f41081800880c1c004240e1408501f035255900900120402035544411a40046014080c00c43c0c156420800c441d0449600c02107851994420420000d1080e0b03104100045908144031f1481c1144030111030b1035081d44490500400c60301a0401141002842402d10019001c0c00c00c0409240342c6450513000614588203000320075803200c3c88610320351418031400381034400b541e14813001d84841c4cc030240350040c100c2c60300f400304034410700c58442c004182032550700300b8038861228822403a10b1109c0392500395120a14441110b01d0040291040110a0342256020001c0358407070005d05803161700740540c004140044003110500d0841c0030000b200c00544c0a1180c0844107506005080d5985903400d11a08502c20151142c0c200d50a007400011180340241d00322002c040300205684014080500207075183c030050f0341221482100b1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 374546681 1250 374545431 374545439
    0x121b06070e011d01050f0c1b0109060918020c06010609090e01090f0b06040f0f0e0f0c030a1203060f03030c1a07080c0d0603020907080105090f07050d0e0a1407060e040b0307 76
    0x901c4078120b511014105641050a81a1920034990218948081e41e03001621423020444c1c4072034208110a80c01d080206205042500007000586544145040e9848001c4d6080c500c200981c104c03003a0052540654081d0742e114500a007025001e4814080d443c0d00e40340300307403400c0c60041c0709048005500011036060742c0003649400044550240056a201c2c1d034440322102800f9183c070501c040e8003500320001c00c1e14807404000340e04100c1800040002500300880f45000c039a07000c503c1102c8140d0080e06c0b0303404060729020071001800ca5030000501d04c0420300c0040140358001400281c5148920607002c1040b00a9420581866040d80d00c1004200c0710000f04105001d46c10140c80c00274805030b00041ca036030b40c903000105003042c25205080485e031141d0042c00350303080814220b5403051b5039040300321842c100320710000e069202d80c610810006030368406102c940301e42400101e032070540083e0340c4038100d440524080c3d280c16151284002144540b448600d00741054054011140b4000700504911450 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 374547931 1250 374546681 374546717
    0x7141c0e0d02010302280318110105030c07060e0307020a09141810091a010803040608060402071a07030f0506040b0d0206070203070e01090515010c0506070e03121b06070e01 76
    0x300c0710403410305400780328140b800c1e15204e0301103000c00e260550344100c0c1080c6110107001c03140e0f065075400c03401d203000d40c00c1004141d0038260300a580d002031034456500d17581d0200404150040711303002440303030b8203000c52480244000400307005001d00131031307a2034801940c402090b4111445030b03664000d808144000a10385008942d4071729040c940754426200d203594040f50701c0c0102c5078210800c0340e8980e8569022004540401005800f4000702e1005504e46810702c4401b406640005102c40c0c425500050723400c017008203200c2015000346541c440e6a0603400d14002c09000f51010044607070038140f400c0c0000e0707032500e002c1c09250108031026204410a1160f6002e00c07034180e10410090340c051042500009483c2000d5820a00030000e40e540002c9074245140490906810440c0312410007400c0c0865001003003000c281c00307403c0038039801c06019500400300400c0c01d00d51107940d101191034000c02e0f40c0981c49400c6446611521503982900c00340d56a07100255440303c00822281d0014001c0c90321b403454048 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 374549181 1250 374547931 374547949
    0x30315010926030d060e0a0b060a02030304201c0506060108060a061101060e1006030c0503040c270c0908010506031c08091f0b040f05040818010e030307141c0e 70
    0x30b0703290580e4504201c0e0340d0004151005035000700404801001009464002803140e210070b010200c8050f4131740340d40c1d1b1000035924040544082d0441610408002403410f10b040101111400942280395182b03c65480c1c090304d1082000988150068038005280e940c4a0f0318060b00c0342500418040e0500e00b4210100e98607410100709010070b40d6220800325038902c41d241e07918440d003d25801c07c5100d504002c001016120011184000d0010600c240400100050070440a8840f024010201d0b14003c40408126001100c2c03050a204e1410001a11403070b400b28070041070b5416040280150b403503a0302815a40c21100c071507846a60030b203c90703115406d880ba02509400081850484690700c680d1070007030300800e4142000310105641c891341c50b07141d8207041c007481e51220340905003000381b0300d0f01c7c1c4c0305d40030503100f040b580b041c034121100f00c044410386c016000541c2640b00501281e0302c408092400b01c2c80e0001a00c0800301c148a81120341c03000c1002c42000380b220b00301a58404c07040e62202c1043c000400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 374550431 1250 374549181 374549249
    0x130302061f030f081909050d030e04090c0b03090d09030b060d02031e0304150c05070618030f150e0f0a02041508010c03061505040302030c060d020909090303150109 72
    0x401440000010485030801040c005004140481d41c0d020750701d8000c599802171060f80c4040c0411884100200d540d800c00c040b0205801d800c00402400140002a001b880041d800402e072064801000c0b800c0030410000e144500c9001048485d12401d07180143c8440404d444010480c541c10310001e030395801c00c1c92038500d02d00d1024044546501030344e04a01801da0303400c056070041360300c045001c20581001d502e00340e04002103400d0a08141d11140c403010b403101064000d101c14000752900c1d064140d181460a02d00650300030b036402454103600e1404080850340101c040c00c843d07040c444038891120001c039811500c0b2114000904001e0025424071010f800e2140c1041c6d0f41e12000a000076100200f030060301d22022150350000350048c2051064488244080c4603e01007000621090005850005c3c04029110f030403120142c94007c101400e070b003c0d00c0303030a80080e0441d04840501030030980000c00707540502c888514543d41d901e4548011100701429100354541e491501220000c2003040707100d000414 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 374551681 1250 374550431 374550481
    0x14060f04060308040303080415090201360b0d050c09180c1213020411090a03030305060301060f060801060212030c030a0b0d051c020f030a0e130902090a05040b13030206 74
    0x41542d0b500e40d0042d0b6000f0b9807090300802c640c5c03803c101c108004e19200c5a0007892510040108103a550002805009050b11500c440ba00e011640e2100780d882180345001c2c4600d030703480c102041ea140c100308813050300004545000d0328148404640c2803d040c40a5420502000d040a0305064811061042003030014010610b104010041d8205425103005154441c200104520181400c0b6105100841e510394503540d1a01c0400d01c00d1407441d940d051144000c0b2074040c40c000c500d0380c840c40006070052010ba031080b0050220a00e0005a590300b103003800b4101c0c0c03246e0302603444a14484000c10100e1200300c0b0500d00360b0361300b040050102002603103c0c10040354040c09026500c0a1070b62500c0c0f40012a2590384203855600104100144d03040104a2003084008040c40c02c0104120340a081000706403400d03403103090102e10311003000e58958064082a90002d04000460400e099036100034401a681035a0041d18180041d9408403610390407040d66a060f80103241659840300c0300000c0e140303400861542 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 374552931 1250 374551681 374551691
    0x1081f0806100302030c0108090309062101030c03150509211c050a0c05160209071103070803011401170109050705090d0c090e0706090303230307020f0106060314060f04 74
    0x616603040201520800903524490740c80ca0a500403d881c080c0c3c014506070410866208018107034101000b0303270b4500398040d11070a440f4500007003501c81c44543c1c4110403074100c00080000007030104071102c0340d0440303006503c0304000051400d140016180304644034007503071f8841c101481526940b00ca500c24004000b803030281c20100f580140030b2030f50780310340303c461240d54031a418072403d10054800c07071103160201d00b40300e450a9007050b880d00d000c0056410103889240580001000c5502070440304420b80310381d0342525500d400703074600386805410038012184180c0030004501441c0d40101d4010004c007840c400c04030300c203a18044002c80500303002080441040002d201d03100791502d0300d071040d40c0c10347c0c03241c1841c42020341407030210b104840800b000845c3e00d6010b09000c0244503000380b05e00c03083ea03400d803070202c01d01d14106001c214440b4a0f40107111440800204100b40d665010504000000801c0003c0c4429551480111b090300e00031001181050b0020011460a1501d00c0d4621b0740c0c10000307840412 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 374554181 1250 374552931 374552939
    0x8030a06050603131b0e04110a0b070636120203160b01030b0609010b070b0a0b0904050f1501080304060e030f01020c060a05060a030b011412070b040503070803030601081f 75
    0x145402c1500c0c410780c40100c4d04001810406120650041d00c03500e40e5402d01958076200703010381b21140c05000600720800f244045885501c500c1600001b0b01440a04a03585125500c2c03c0c00c01040a070100c9140143c010910718070b525040344082c10890900201d8440354403d03034451402d200c0140c0e15510643c40200715101080010840014055001e500340751159072450800c51020180244907911a5104800501024042200b07451010780c01800e02103080d035401201400800c03007009020f0784060340400300410000c0c0001c020f40d01295040590305415031031200310050400030b0182c00c010b0742051006020481c403c004410b59084018200c030b1b40700d0702d008911400c9034404801c4088a0304850108903140d000343c0240c0d5080340d4250341d406007035455905c80095100040c003581820510441035005155609041d84090115090640f82c4460392080c0910456006215403030107800340950000740d000d404800d80e4031501068607940e942e0381c2c9241f80403072240040180c0403013500711510040707 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 374555431 1250 374554181 374554189
    0xf061a010c03260a202b06030606090203071d010e010c020f060c07080f0f2a0901060e181608040f120306090b03061021020d0b070e030f060408030a0605 67
    0x68003c2012100c0014601c01d0310040800000d0340344000301c4010400c101b421054900c03d0700001e1100c1e014482c0354510802051144003500241d0f2014082c0c0e800c152000c00c003803800d6402140110495209c3d06000382c80140c580030104940325040d0f012541c01040c0310980d50081030000000c0384001c1080505c110200c0c0010842e07003121017100b6090f440b80e10203110a050420280071711035034650080c480d15030103900240d1340d40d0b82407003440d512448080003099044141400032121440081140d1038940e11208010201d54031510301e24455550b0b08410740c401800d8006160050710f800380341c031461118105040c0d03148030001c0c1c0300f00c428110125400d0041198441c83c00031900e19a0340205815142060f0201a100d070200a10312039005038042c0001c2000c1c035840d40301102c0b40904034510000140c580180d40d51516070703010390020100708030002086144099548144956101d00d03640001136418155641c00300c40300080590322030004079000c600303200040e40e448034001d5004074895807210085 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 374556681 1250 374555431 374555507
    0x2061606020f04080f15160306090207050d1425020f03160609090501150e0f03030406080406050f04030537020a03022815090503070f061a010c03 64
    0xa4900a201007018000001c1c2817080491211100d801460541c1c204141c10514010142c03a040b640d684800e5001c030000e00035005a0020107002204545510650401688541481d0345000c0000e10721814400e0b2030a550050741e644580a4104020300e200c6810034078003e000c1c5038002d9074854a1038580c445141c0d02000080c030000118910290360a180000191203504070350001700915040000602c0681b0303020210028640051815100403060f60021413608000c0c590121f4142c040000e0200e030741a00b00c82030501075413190204020941e120002c00300745105c1510300600240c0104001e2000d0b8554101e151050b140c0300c4982810048a074445c1e86018441000d500c02582115540c0300505405212303204444403c0c1c500a040e06103111000000c94420341401000000e483d000b05d0745081d180e038801500e036a8410201ca5580301d482c140340c0748110348410308451483c01c10288107882e001801b18100702c1101038540e0014801c0d959006d985802d1944000c0c041503c1c02048046180403528803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 374557931 1250 374556681 374556697
    0x70209150a080a0b0c030f1f0b04060306170d0c030f030213060c0308100806010b0a0207030501060b0c160803090621040b070207080f0309060a21020d0b0108040308040206160602 78
    0x786001002498071310144900184598400d20090080101c05c0e43c5070501c80741d05c85003c144902c00f410040020004d1408940c0126008a501081c08103086405034000340582d65408488802d03608400c151030768481d0b101c0704140004080c03c0380c4100080c090668040030302c2c4a03003009410244512095852071529901a000241400c1c0040303041c16049680507810009202044502c0d6040c0401c241d0341c0c1c1d1040c407585601040009101c85400e05c2440550b000e10f621900920030036540300d420030b9070380d0071900c1c440b039807805802c0200000c002901e0000c0c0c2103802c001d014508000b0b11104100541d044045400d03000c035200301c2c81140c0d181034580e100788554400c040a55890421003030007031a10200b500040200c2e409050209110350000090320316490088034056911418504100c90702d88900200034070b1161840b903000402c450380d4000d052401000b5008200a892403001140d12002c10b8a010780413403440d50208000d030404000611200742d520f1180304600c500e0b0390303400c0d040f03900442e5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 374559181 1250 374557931 374557933
    0x10e0d12200a0f0204240e13080d1a0306100504050408040312120605040b030a170c1b01080705161202030903030a05120108061e06270a060906060203070209150a08 72
    0x510003085142c2441980c0d4031146840d01e10740c01146c003200c1044090300c28002c01075481c4101c3c00241c05140400b0070355080e2035004074082e84410039528103002602007151802401010a101d40c101e90030000b890b68400e400c0e0302e5002500510b0310060000903d800762059804080400c00800442d8118050030355403212555442414041f00c00801c1c200c0c1c68079000107205506200700c88002e0396001a80095a50f0490b1000c0c0c041c4030005500c00c1544159014079055004101d4100c00c00030350703849007608126080c1c841050076551003908036054400d500e00c1c0c14181c111500d08a012800ca5a900076266990380100d034075000c1d0704400030303184d07400082c0d2100c006600020711000034004d044515004001c400001e04040c200400c0a242c5406100400d11001100703070001030311030380c5c0c4110044450754640070f1843c0110801800b52101c2c0d400702e84500e042401d22a0000e018072a51265200f02e5500d58003850a00072558204290b1030b401900070150300c020403100e5090741d910b40800000a02c1114 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 374560431 1250 374559181 374559203
    0x32040303051b0f070915080d1e050703080c0a200703061404081b030405060f0307170f06060708040b16120e010903060507020a05010f0b010e0d12200a 66
    0x40702010380c07914000184941c10440703d003260f0200c0041e100096407020403011940303440080340f0031500c94850b80000c54911032200515a1030381c0108c10003c4644207000c4501c00c1c83c10b0f03003005554034070902c40002d000516a00003d14950203035000303064090868900403030b95620107801d80c54000c541d040c040d03080b0380101c5001c208000451103080c5c0c07880e4591615442c10302e4030703031113400c13a03401845101000d030180074141100881d0180704850240000a2a0303507140c04208805000c6500101d581c0720102c0c1e107800100b2074041c032612183d42300340c3c41142d0141d80c0e95200c4050041d21380001800700c0f01c01d1818000440e4032503c0b80301800ea002521280380d4420511381c24009a8603a0340e000c0001031201012220525983c400001d0040d07a4201001003850b440d410b80403071500c902e00c84085c000f946810080040c01d0b48c690046085103100340d03a2640caa00c2c0aa041102100540c04028100a091920b0001140c0111100705101c8603a105916040a55165a41c20000352000031203001443c9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 374561681 1250 374560431 374560447
    0x9050c161401092108041203020c0715030501261b03011d03190f0509040b0111011d1b0319020301090203160906090204060e13020d02070b0105130209013204030305 72
    0x10134500380b401403850944140e0510341c0701c80000e182090a500105a00001c800b00c40b100c04000c440c00030130035100480c0c03101181c01402001001e00780170b10007080007291000a001c10250b514094041205405048036032031008200b25242c20402d10183c155403650b54802a644101d8410065820801d020b160b841c612070070f0002941d8840d01580d01440704a801d2244004d90060503076019a90a6400261801c0d49038010380700c40c501580c0d10046503080c6010304000780b15110700d01d400c2111080488045111189102141c400b02084564165000f0032450310440c01481b40491000d002600020301141c649e00843e040c490b074800f81138480b00112508000820862041c0300c001c0800400450038142011070052400740070142807803080642d4401341440c04169811226503a092550455131030320702c1d20300600a14001d01c00c0a104916914090001c03191034001c40c0d416440594030140701c4008600c68040c1d207100380022184a03550301c070704500c0002c0c0940c000c0c000356011351125074a502c00c0d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 374562931 1250 374561681 374561723
    0x91208040e0703140f060301021903090c0f050d0f060b0303030f071706060301030b0405010e1b0301050906100b07060b04021602120703050d050c0a08040906060909050c16140109 78
    0x5090b02c01010301d010924080e04004140854000900c511212006e03114400041e01a00500d00c00120745e43c000c0c0c000018090b0141c1c005109140b25220240e0140d5507038442103c3c1c04224400d20b50010002c111103000601440c100b584600d20404000940f9521080424550b030030803100c00080c0844581071058260704500c000c0541009490100981d2a1110204041d030006110060030030300c1601c045800c106081d00701440c001e0f07c600845044c2d109000020750070b25143d18040b80654a800042611030a0205807a849100106441c05a140c60445045196400107009889960742d075640580076030b07194002494501e4502e07171248003041d802d004001c42c400c044401c04c886540420300c02c000003000801c2c40609407070281002030711201c051030300c030341040c070382c2c180c000c1c0701440c001000b1a2800995215034140c800e40d03030350485c4964682400c80d080350810358030103140d0b0030140401030035000d0181424858500c05c81010703101000c078071050313030940b000c800c811a081c008029017845201c1d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 374564181 1250 374562931 374562959
    0x31309060e0108030406090e090c030109050d120515060f190e10052b06031703090d091d1b070c0302010e0609090a1d0d0206100b04030b0a0c09120804 66
    0x31840d00a985094a0618054800a011f110703000514010748d0000d401e402e014040c4080c03540014000784102081440d0498440c0d142010000102c0c21081c1c0041608101c1e01c502403080704595200b400708a2030504101241d0021484100c03645030822501903407003009810720702d80382d00c0d50301c400920a56030710820422504042c100810458207200030b2a11000340d0b19030604e000210918440c03110b400f4103115020301602e40024207001c5481441c03000d401485001181300b10081d0301950107005201404450008d0103104003a411551444800c21a20509400a4100c068820f02c00c000921120b421485500010002c3d2171400c40100200b00b0755800c10041c0403101d900b01c40c900d141c0f640310000948403400c090800000f150355480d401c808140481c80310823099120780b044170954862100020f40d2100102c0326600000c00300600054141030500582e0140d90b40601c408595541d2060048010454600ca11007080342d032110018418441c44040c40081380035044441c0e440c1d0a254000c0e95201d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 374565431 1250 374564181 374564189
    0x7091a04020a080402151e0d0e0a0b010303180509042004020306060d05060d0b0c13050619030c090b040b0705060f13080a02030c010f0b0913050c0103020c031309060e01 74
    0x94010002034248543c80443c59501c030742d0442d0b050407440b000c9000d0f007205005200e00078074400c4010740b4480801c200b480c09042d02c1650003005104220a03400002d803030b0814180010014001e2000503c0024021241c040e901e99132103909c04a401d07a04c2d800181e15103010f66050311046440202400508103815000c0313926482070310158074604000022520304d1080803401c814480e40e03000032a00c19030703454400c0901540c00c20103803440d03810820030ba90105da110400d440400858607400040d2410705105031110a41511001c5101d07180300d60059000c0e10f0380c000b58604105080c0302c0410b50524507030141002e80720410328962101140d242892500001900212a0300c8882d410418011041c00501c118180d01618540d2034030300c80007047e4594010700c0026007a80d400c1001145584045501c03880980c0811141b94240e903c40300340c0140003c0c00d0220180058100314082e000e254081e400401f4004004001c076450300c07410441183d4104c140c2c0d04080d1304141c41d4581005141c009926045c058 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 374566681 1250 374565431 374565439
    0x4061b0f02190e0a0b031b030c0315060901121e061404030201021e040803161a0f160305090c01110a020a030c06090602121603050d05040506091b0307032307091a 71
    0x201e42240003a643c0d0346c505049080c81f1a0004203a01e00361000d0100501880d00502107840e080003001d002030508008441c1c040c00388031131000008140323440c400c0d5010300c242c0103400907001e20808080104141c482440644040341c84414801c404244000713910f11490007170380016182c02c0c40c528140c585025040741800c0821040c0024024101c0c044101c0b18120016110300e0000d10152031b10340c244010359003840943c00c2c0d00004001e14245040000d603c114002c82d140d1041c5414184d060b02140c4098603044032039400000141c50755400764141c4400300c04004129408200c0c80d60006402d440507410440749060075401c01c11400350000c102002625407400601415030362494608298010090700c041343c02910011007044c14050f17800c5520180844d801444503261a0400340c0c1d640d081500c95040c0d03880f13140380f0b0303400f940e0b003242c0700d0300485100030003820340c02c0d246894440d8442d00603210004015040c42544007034141c2000201e00500b80c1500115612110030312800020080c40340050007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 374567931 1250 374566681 374566691
    0x4060506031603060b130501020d050f030610031b03090501140702030d11090a09050405072c090c0904031d010206070807050313020306010b070b060604061b0f02190e0a 74
    0x2465652506a0303900540700c09003500d4061000404070041c00320740c0d01089411800044000600c1c00ca590b0b8482520700a808540080c008580d04031458410030340044030200f002c2c40801c81c0c6207440190050351469518012545131720304030080c04071142c0b0400c1007003c40c0da1002e0503800c000007130040041100d074580ea045044e14111038042d4481c4560100e1014160741c40803402041c0c1ca2801c02e0b0b0b21010b00192804c81510344924220300105019282501c00348200500081c94030840c00f80c1800f03a40b51499010030f5409010722500d0196000b1342070f80d00701e0040107844a4952200940d9501c140d0003a0b0752580300b2041d8490a0b0b062454050b600d504540002d000c00a0880d0050036140d045120342c90410341e07e50b14147e0181d40c888518030025410300502d070000a442c5903a0001d0660070707001c1c40d80008681c40b403404003c0c1d00d10840c0b2540c0c010035510100807800c0048603103d0440039000f08500c0c4151a00e81d40059003030a8260300c25030121000010078410482c41200b51030388114003240402c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 374569181 1250 374567931 374567939
    0x16050f0a110108071e0f110c150901030902041503031b0b01061407050d0f020c19120c170607030c0302090d1202010e10020306030f0712060b060412031d0406 69
    0x72021205504640c10301c0600700100e01c056103c0d00c1c45d66100d5001001601d984e1180240003003114031809240400610f90080084c54050041840f00b007010004040d070010168400005944d81c00041d011030500d42d5540395400540c0b640d004001e2004c051100384910b4034110300d0003a044550031100c01c001400c2c02c14503440003504043e8100c3c1540e910342401000904407a440c211140326108005020380216141c50904039000310640d40b02d0340003902030b03802c480346503030a100c2c048072421006c1070301074203a02d401c100d407244803401814200d010b41d60b0040f540b903e500d0a40c8850511280380c07001e5502034010403844030740c0741c824424006201c2c078095140942d40000111301d000c810602900c40d9580c007a0050310103000750f028041300c0c4003034000d540204ca040d00c03800009401c1102c0b0307540240521000f0384103103a40031071003509444100702e10030120ba0300382e01ca180051640c8501c030794102204002c0031821224907503c040941e40f080d600c03030040c00c09040f24581c004699440306400340382000170502c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 374570431 1250 374569181 374569193
    0xc08010f0302040f0b18010e0903072a081b031501081e2a0f030105071b0f08070f11061c05060d020a06090603050c040f0b0702130216050f0a 62
    0x220850340c0441e070124203400c801c0d0f07081d80202210780c03401d80e20002000c1400a06d65030481101e040319065281680d903544c4101c115030b22071244120050a00b02c080e103c500c92140020340d00c06914540d091500c00d0985c90302509458241c4400d00402c1036400d502925680340703010402000030a003942c241003000c1d490045071039900c0540003103841c110742045807801e020342003c0016010a401c010704299091014280841229005918450140c500c100004200c0e0405001c2c01c0d000710761035901d10100016141000c111425200d004603407040a010501011a8a4401418101d406003050b810510128035021007018035a1800714000c98050080c44c5c0e10101103007114081c07081003400824140d9610b00090111420700c00300a500c10044c0340e0204080ea44103009a054a401d500d00b081240c4910001c001c55020304d1051203041c41c00f2400a010000d81000a0214070f80301a08640314407480840c02d400342c2c2c12100b100f1441181035200b00040c09000c214401030b00b51110040c100070301c0d070354880c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 374571681 1250 374570431 374570459
    0x30c060406030932120a05040e090f0102030109050105010f0f05191206030f12050717070615081f02120c030c0c070303020a03120b0d0b07050912010c030c0801 70
    0xc1d9091603a40c1000750103200150840b0700040c861001c40d1111500c2030035070803800000014a01c180c500c80e2081d0752001c500c0032411141c060406071078841c20940b805102905480005001e0016805a5020784030b09020900195018101c0c400001c00c645d03040000040ac40b025015500003080380191001190390340000c12074840e28480207080c4e00c41c03c1c51700c0040d1180c550944101012074a091070003c1806102110701003998801c0f01a036541101c0b1700002c036140d01a848000e8050340b2400c0e29951416040001001c485202d00004100c030b10088140c0c03800d03030445030b11942840c0c210340200b078403400d45800316583e01c01c1c3c004401c500704411a04d5400e07520000910b200707498400040403a5031200e116065902c0340380300000b00e0380c0c056180e00d40207407102400d4404401107003550382480542d060344c1c09680410000940ba252200c8030540b0345110444010b4040d0041c44070030008d02314a130300c801184288061912001251004200100800715000c44c0741810030480ca40005100c034500301403039 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 374572931 1250 374571681 374571689
    0x60a0b0f01081932010e06090412050a0318030207080f07030809090403050f0a090521060703110d060f0e0906010f1e15080406050c0c030901051e0f0c060105030c0604 73
    0x14601020702c2020014409048004544e01c5400b20070382440400002e00b181681c28100880040d40c8954003407000400c400c1e240285000520382220200900c110b014100780100d528001c110004503401030703001c0b141040e4041c0c0058003d070b28107000c0140e0405c22909042007901c018959645142c480f81c0c1c09000780401d0307900c2140c88c1c00100d01410300c90300c10b45141c015041c0c1030907070f55000441c002e80440541d01c940b500480c08452070303c07074a5094078200207810350700c640070380410b40da20541100101710040d03100401c140240440317031940450b4800c0801800060303646030030550428900b502404001403410b011584010f00500200d44209007410407103804400510800f1014031741d50381c41d50b005402161241488400e4890303040d9000c04918040d41c00340304200507945692503113140500c02d0030003072449503100300075080d03655228000030301d480c000900c00039844540320700303182c402a88074850742c0d00a2080070440224400042c05010300410044006040c00c0c402500032130202c3c0a00c1c42 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 374574181 1250 374572931 374572981
    0xc01020609101104051909060503011103070c02041d0a21020a12021203101503091101050d0f0513050f01050105090112240f0e0a0b1501020f060a0b0f0108 68
    0x1031110021910205070b4000d045d00900e810780740c40100c4070300c0030000c2071071042139507041c100140020781c0c0c241880f82c9000310711640c0d02c1c24515a44d1032029103000c40000f00032a00940d0708c000880c3c25011030088428014003000141000c0b034103a090031500d20312071500001d100703000e60105e42d0303034160001400e070039040e40031204182c4110820801c4c4e003441c401e04136103845400000204031036009500e8201d002d849104603081189060410110100c0f041403100814030106651017014541c0510047c200103015403002040103000414150280c03801034410b54a4140c4050f40c050400c03000f130190740d003048221070080180303614140018542100600c0b030300c0c189d0000e468040040c080c00302c1e9064100903001c2d0b101c05001d900c03c9194001824200c0e0381300070b0f4610380840003140c0400843c10502507500142e684c440d50710745101880110090b00c0800d41544910031001214040912445103e044c0c0e110f00083e000320743d00f00780540e4a4101c0d101034100021142000006680740981d10351000c41c41c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 374575431 1250 374574181 374574191
    0x30108160e0105100203070b04050a0b0703091104050603010e010f090b01120b040201050d09061a12010b0306041b0509010b0c10020403080d1d0f0618070b1e040b0f07050c0102060910 80
    0x40d03050b419482907d00152803502100d0403c4203012001560b01c9845100e40d010001a45d5418011000c5804401009201c034580341d0409035a45040e80140340c1003000240000354010420381024210360f40948001c2005407501c036a0018031110248050040c510383d0038000509800e5580d1011000c0c000784000e042c030201180c0644c1d0300c0c0072a44541c01e41a400342081007504504080020066108100349224081d48854142c010320180296109900081c0080c179807502c0359526101e88000f4148400301c00c0122441c00289503848490035070003403011000b443d81e01e0082140080c14000c400300f003044103d00400c0200009803054007114410418401c2c0040c0540407804a80202d80d442490000e280c403400c004121081004140a401484244400da520302e1b60014440c2c0c8421052062088040092000c0078503c444483c0c1004480240304403240340640f64540c0950903003100401c1c00340d07004045801070030480108514541d102090004240d42c0c94181745a0f80e4400d4900010509141c540d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 374576681 1250 374575431 374575459
    0x102030a0507030504120b04060f060f03113d02060105010e1c060606030b040b030d0801060c08041e05040506042c2b0f0519031a0a0b030108160e0105 66
    0x1041a20040c044500f071700100c0306c1c094182001d00c09010350382a20b0103440d1a50001c001c00d00f03071007141d08031030700400c1c80c00b0001d1550702c40c40d070a450180340064110300c0c150715046c3c05003c0e000d140c40d4003841d20007616075101c10748141c0c0903128580b41760320025036000c0e00051245a8010046103100070089a081f1052841c103200900c1d49500b07a0402018542492000b0504a406030421764040c1e000761010840303102907400301551351170160310902c0815040c0c00140003070b0b4425410503140900414101e441c09035074007400c00380a807006000032081c9039a05800e1085140c00c0c02000e80200303044405100345940e00340211461580690702614101c00c103031264403001c40600804540c881c141d801921104060354030004144811300c0c0550000fa00040c410010074086c0007514603d400e158a0100c5007204003030141c00800c65a00520404002190301441e180e94005035000030b09904243d044c0c5a501d44138401c1e01c0d045240107680449450f0301001c4c024444d417120854110740703080301d1146102d122 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 374577931 1250 374576681 374576687
    0xe1818070b16150504030906110303010308030720190606081b040e0c092401020303090309011b02130c0e01020a17031b070c05100f02060a0c14072f0102030a050703 72
    0x7a000b43c1c103681000100018036030401c078204121945904c81c0745015400107a62a1288400d020082c085034043c0003103041e0b00e20407110b614500c5034004101c016922800e1800b8940311524040000740c000c0744031042d0800c407031400380c1c10003089082c00408100c1c1e480035403c04070010758101c1c01e0142c0e03518103440f03191000c02c1002114a22011b1300c070718020304103c0d0500c1c00c2c0103c0c106d503a101d10504000701031004d51000003106d11a8002902850130a040c0c540112140c0d111a4002d54220b2801c03030200001d0780d41c5045403d00d00c0710303801000502c100b82c818007401d02001800c00324155001202d0032800300d1551403900e4150211100c41c40d641c1e6842c0051880345010040d8243e560201c081010000c100480310700c1d5007915012600c0c1602c00108540c100c40c03409040c030b148001a0001404200c865450b50450040c0c3d0246081490280a0320301101c0159042a01c0039126030030200e000c40d101ca082d1049540e2950300644d0103c0c0b041034001d00103075591050f010140100440026900140340c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 374579181 1250 374577931 374577953
    0x90201081902041a090a0f060c0b0604090c0602030703020c0301110706020c0102040f0305030c011103040804150309061e060f0501090e1b041205060a0504020a150e1818070b16 77
    0x141080ca44c81151001822181080d0480c81c0300c14091100d2010129007054411900d43c00c8503c80d50320022042e00d50f696040c032420313010703000582054640c001c46000400804c10300740588420f0b8021619000a810020310f44691305101601a0345080c01c2d5038080b00031681182c5043c2d4001c140540d860760315040b018024840c81e4071040800c0700615010082000100003422000c1c00207000b03100140001b4580300c0b881c0310550b00109802420042003051105407003c03181341803e14100020260720070703191441681c040170541340e8040241d480001340d04100d403180700040e09036004210600c508250002e0012a400e0150344400c1100d140050b500b80c00304945c281490500020341c944441e0b40c1d0382c075802c058400751002c499a000704000034415003400d1091612840d001082190001d1408680c004403e100c2d0309503a0400100020007130130790b01c4181d503840403140214400340052a00d191088442c0d0703204000e04015811040b002c2120540c01005c0c0c5141c808500690750f403003081880e00112900c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 374580431 1250 374579181 374579189
    0x1060905010315150b04300b060102060916090c231e030915100b0403030309030305010e090a0201230f180306070503010302013b01030507020706021009140a0606150309020108190204 80
    0x14034021f054410005811401400b0f01c4003a005c41e4041d444002c00365442c1e000c031482c141c0f004074003940108020301c2541c004d0542c40c5d840f41410b0507130000c04d04d51068041d0f203030b81080149085c00035111900084815070a40d80c5000000490305500302034031078a44500700c0d0801802c1c0c051702c20010890400745044064000c1040b80b141940d541d5403460080c0c0a008182420b8000c24a00000042e441c1e15130402688145001d4000d404581240c2e801541c545401d860000d400004c803041d14190f0080340d0004003007050004c100c0603141c16403040c0000303c0110718512280690040c0040c04940c0e03801c030050702c0c152642400c00840c201503009030b440710581c5103540340b08900c050640c0f180c408000c0a144201d407940c2a81c1c28411942d42100a9035200c2c503074403c00005034040380c6030240c48040b561004a1051181c4d0306003c5040303034414070b2458440c0c40d50080d2600e80c0d03540810070880c9080d440010388480ca6040c28030104500e5000a00308403002410207800084403040251821b400d507040340d01074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 374581681 1250 374580431 374580509
    0x24020f0708150c041508060301150b1905040b210709231305040807030806030c240403060c02100605041a090402010201090816151b1101060905010315150b04 69
    0x1106448024450042a544140a9481c0c89488441c21002c600d0b0b06064407034001103345024050301102014800c3c5400040410209102c003144c411302401c01016071144445450b4850b15000134540923004026001d001802a650802c002000c019000b480250b40c1c50245044490702c000082200d20988008501d101441c1c0382c100300400c0411409444d07001d000f6602e209690343c40c80141641c9180c140c081d240e1056000b401c2905c00d117010780d0710014030726820b0006c43c18141e80740e071000140d0340d9a00c100c50150300002142983c590aa00c15940100400c46080c40300380b03698101c5040d00a80001400c0c011382c50500000c0c1564001d40012200c29804045144e68000019101048001c800c004466400070114000951406405050550185809030601c1200d1003041561400c883c030000004a5480c0ca034005940d060900c06c0d24020b5001d4824070018200c4179000c0700032288005025003030b0000c6c9100522100000f901601c080d40c0c2480448001449000140c0c0444078000c955a100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 374582931 1250 374581681 374581709
    0x70c1403190305190506130b0a03020603090a12020c100f1b1b06020105060603070c23030d05061905010302030c04030203030f210906070f030624020f0708150c04 71
    0x9042d501d94003842c07060560051041c0751094075800d44050310010b41d20140c3c800000c90b035486085c105503101c00b4000300010300c4100c00d29500e5020a20a400487e002001c54000034122401c2c490324010540300720405102500a08030900c002850501d104496001080016240c8103c4940a46a040d04120050703401c01e0380c1000600d041c50200d00920200a189a6a03541c0042e05900501070710780609001001d42d401c543c1c500b90126500300c03000c03509861003007090b90044c544001c0724082e640c5803e8550f010f10799610b00c000740c41040d0360340a0111400760a01c181c510006074406404502a00e00910b00965280c8a581c1c0c0380380b207070107240c0000e03505010018130031804c5043d0200403c21810740d42412117042c80070b1141c200080d001143c111650b50058400290103600c26004200700101e242400103d00340c40380c046124041d480c2c8016a03245150b411207181c900c0e01001080702200e2940028083c0c5401d06454603241c0703180009000010000c4c00100b2074015200040d5000340400c0400004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 374584181 1250 374582931 374582977
    0x50901080a1214031807090b0a09020a020a020603070305040b0105100206041b0b04090b09060607020d03051e04030b06012c0103020c0c180129030105060c07081b0117070c1403 77
    0x80105040c00c6021749a104600b00040d04622034025441e00c08002070016003018542181c443c060341c040d010766411800f0b000031100050361707684051401909190760005480c030341482c0049201074103030409841120310f00d140070f05659000400e5030740720741d120100142c03070b038007201c0741c28800e046c3c03138110301a920000b02d03000c542015140d02150707104000319141140c94403100c06001c2680708030382002c0c1d0400d6244050303002190281d0003c10440800417080e80c29440b403100420b440d03803c41c0d002102c8a45000050011540e406501d0400c050400e5511a03036030313211010b170b0481040d40000307107a0500da004038030036030b20710818000d141c1d1900c0c000d80208801c41201c900070280903000d018003002444588114880400e000800010039540940c0300303031a59003170170304011141d0062080500240725070840480d01c84002d101c090241402c140751966008640c030000341244032600350101d54030074400708000040b6400f04900705000d4201c04180b07044030199540e03a003036204400320f6200f620034400c8025 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 374585431 1250 374584181 374584201
    0x5060f19021e0a3f05060f090c1204060603141528020403050601050316180f0e0a050601060e01030b0f010c0302030f030c04061103070201020703021203071406090601050901080a121403 81
    0x4202401c0c1042c803d2001c4641c2d1300c58100d0368207845003900451400800c2a00c0d0030034091158201c110100030358100307441c00419449080c0121003c40f00203031680c004104210707030b030b0318070340b051081c40d00160600c4003c0c1d000208410500900700e440150108003480f0798003442e14030241500750043d80c250365075526404c005540c0c60080c443c441c000d10511220300c0806100d1584a0305403182c501c035000e07000c00c3c0c400380700000d8086c0390302d00038969958141c8240100301c1002a080102e12074000b5101f150b26180005d8a440a045541c5040c10709000b6030781059034a85508906460782428880c0da54001814124614002c0d0300440d40303d948004107204104a510b406001100c0380c42d6140c21040d100780b03009030786038061070400a016910400c814030052600322000c40000000b00e0440e03007030189989441c20342c07603480c101d11a0700342c22410501c5202001400b0050140c001690f2003907280d403410400c2a034858121303c01502c80026610115041c900c14003841460055440c1c0c07140e101d0920301044 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 374586681 1250 374585431 374585507
    0x31a0f010e1e04020f0705060702070b03010303031a0d030e01030506040207050304050402070f0f05010b0f1e0919020a0302090f0a06050d0e03270301060905010f03110301060305060f19021e0a 84
    0x3903690740700d2381000074030062001403900300340c51032204540c0c19030b4a1580c0a502810440031070b410031280c0d2002004042d22180c071240c845070f0095540391042001800003400f10b5101078980303405580100100000328200004440850f0000d860040c2d0341c00241c00c000d0064089010000c00c4192029484000d101c415000080326490864540760207000d913004010146010004641144094444001042c54150386980d400003410588e208895080002c20781240e004602c4440481e50214011404d4200844c4014946406a030400032f0a414030348040c0c400d02440a80b920b055031510b18618000d4000d0054507623400d96541c10b10341800b404c16551251141590340c990080d880d202c0c0005200c541802458100d82090541080d42c1c0d04549500b45001156000107401d0347d02c0f200c00000040c01004414400e83c2500e80a0400b81030003001c00d60203850070004913100720300510000303107980c140b802c00d01113080c1c0650301035584141854040c0d80c5504000e00c425400e02010441042c031103400c10071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 374587931 1250 374586681 374586683
    0x15030405071202130e0c040203090d02060604110301120305040506040e0a051302240c06010b07030906030b01020312090c0901060201020a0306080712171603031a0f010e1e04020f07 79
    0x281c8101540350b2001001e40c1040c8500030f544408810304c50300c0348450b00d80c04441041c00c10b900f42c40c50803404402217020790380150761980c19540001e845107810b99040c030041d03070803540884090040c6c00411303071030560601041c02807002800d03401d10040e0405000c0c1007164018003000d0011500c40d030f81c910b064030038050100c0310200c2e500c1c00c20001440981000600000090b4001d22101c80b1030703030444d2001c0961001d0103086825440810007826507060421405000b080b45a50140d40c4040d41d260080030480d0a900c194241414425859140c1c0c1e004000d80e81181c1c011004a11165240782c013840c9410040d05070b55070010841030000c20303580d9041d0002d0480d0000d5031000d10187d0b82c1ca00c0034a42e100b1503481030914001100045600080007031610348020031045c51720904185c55005480d0302c40000e11022000309030703030380c0c0e00700700b08415248001030f924030440d8428620240e1000290003820800720b071034481d2105081c0b8445202240140d5807030b18902030000c54403640708a28842140e440444 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 374589181 1250 374587931 374587933
    0x50c01060b0a0801410405040f02010e01050c150402150d0504110a0302060904020304030c0b0709030303060b0306030c0d0606080114100801051b0705010605090f070f020d0917030915030405 83
    0x200100305c3e141c03007101d03180c61500d40315401150500050008a4080b08130480604e510104002101c803e98490150030b01403801610f41500c0b02c401c80c400504001c58100d070300350502c0740901c02c03010314840c045007a80c0d41c10324503005070007075071364902c00103522040b60441c0003c1d48402040c0c010203180550310803441184101031a500d8007230170310704020039100075110096001000700000452800c05402554100c1d00c80d040c81c000e038502a603140500700c0303070440c0d005000801c0704104000b0300d40c0c180105801449011040c40c698100b40000c6a154080d40003043d002d007100006090410640d54410070042c41140001c02a0304d070580300e100030f9007409441448052000c01d00100300010306205050051100c94807081d81c0340ea204d80d21100300c1d00100401d5a9555031540c0000b6a600ca15202604c0b80e550327000400001d24008501a20542c4044000070440d4000c41c1213910054018200e001039402041c2c4100154840036149891071040e0b12441e500305205030b04161081c00c4103809103005503c41c0c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 374590431 1250 374589181 374589197
    0x1009030806150f1608041508041106180d052107060b040b01050a0804050a06020301031101030e0d05031911130e07030c050d051e070e040c1106010b0a050c01060b0a 72
    0x40000d1810b07008280f601e203111002007124440d001101c41150042d18800c485040c10180c0e1401070072140c2c1d011060310f201090417103003008100072070954114031452048840600345883c210580c024540c48072081c41c0120320818440080c040100200c0c00741a016200001c210030b141070071060f50742c10000e011a491410062020f4580c40c05001c0d045e04c07440103945017420114000c0d006c03500b2070009030095802d8001c07500301002080789800210b02035800340180c1920441c040000500f00d078816840c2d100303540c02a009da980d034542d0001c112500004042595280810501c9401c4000d2000110810703490b00f0001e00c44c00c81d108007034401c000311440d81c4200d80d0a40d03180310b03080d800d03280315251321000500c2c1080b0f84e070841d405a600c0390350002141201e20500d0980c5102d4030358400d03820b0314858046603c002030391002d8078090050410440441c5040d1090b030101c10740a076510b0006000b0015950008515840d4451061080d180311900041c0207000030380e5112080d4105600a00388500000c1c115 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 374591681 1250 374590431 374590459
    0xc0212030906060d02011101150f0b0306031002030703060801050907030b011d070c0c05030d0e0307144005010806010f1203031109040e03090a17100b031009030806 72
    0x8802500d206000301005040303180d0301d1504015810b0f106100883c1800148078903400700510901c214034082001c04079000c0f403241004011404950b80c0d5005a50300b140c10002c105183e02c02084182002c141040056125140c0c0e039003d40c058001a004085150301c3c00d410031003929400030310101220f0040c1c03c02c2032036036241d200c1c5051015584203003040701e08000300482c1560784602c00c4118100d0051482412040d00c1d0704c0040c0c20b10070007400b4940011f0302a440e2006901d0140035100003440301c1d10103c0d80d005155400306030170000e5400602d440b01b0341c0b00031030f20349800da900c01c0e08a9414074001c1096001c201402d6040180000c0c00b4641c0e9a1081300c0000c5100902410014103980a1508601203182143d038203c0c003420070f084000090315407d100340c3d00b164441c0d00444a01d0a03040000c3c40c1c13940d0306d10090004083c2036511068000b607050b0700c0e013440340d000070074213002d50024000e0124141c2c11000c04a407400c88c8003510520783c903151030000c1d01030550100c0d100380031701400c4905003031004c40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 374592931 1250 374591681 374591713
    0x1d101a0603240d06140a14070903030e21030307020607090308030a1a12011a04060e0112050a0f0f03170403080c090d080f091c080406140903010501090c02 68
    0x800ca8a00c00b4010300407a095007408490b0060900200005141510000d070315992031054a6000300c00f212a0650030313040c07112140e145c3c0544011910005c50100c0580780c001d070002c020014034480a0140032289005aa41e80c595200900c410210402c44584860b81c040313409607a50700803107200005000303040102d60564400d504200c102c85c0c004c803060341151103280701c460041c0000c01c001042c2000404910803152104540701c0400c03012200001a2030228031071500e02e501864990390f215034601792042c081c0300924200340741516161456844450014940b183c80e120080c44090181050415184200506c0c00c2300d04035014403a654070518900544c06540c20381400341c80c01800314056000040120721803001070980c41800070004201e4100c551125017407070b404595901310603100003440b941c0d14100100903902d600d440fa2114508481141c440c80664040c50144504012042044000b007115413030599034070190090027088503503500c8880074001c1c125001050051b000701001252034040e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 374594181 1250 374592931 374592937
    0x601051815040c1e0801051306150c0c32061809060d14010e1203131b090213030b061c111c0803010609050d0201050d1d101a06 56
    0x7a510746144803007465030030400a403c0e601056010021030303d00d2440909a00110f040f043c1e80c003500c81d84410350401c428806030050b0301c02424402802c0032001c00000c09a2944941c00c6002c500d804000d000241c58507000c2c40300039501a03c80740c0032a03000c0c50440070304401466460042da45105407503245502c14402180203004110410106440d0107856900b0301c061441c1e0f01c1302c0020812019411955030760b00707030161100c124950903903541000c0c103100b16080012400320080c1d48505811450800c45140d80c2000c80000205511030112002025045c0c3c034025501030292404195220f10f102064030722040f10340d1000369000d40c00d0401051305401e100401443d4050452401107051005813181d8481d403c60064058001800004c2281c00e45809005100410b106440255580d494800020214034060b08064801c02d074102c0c0c1d60300145e030002c04455003880082030108000480c904210702600381403448010600660b00740910311440d5038489518041c0410842840201440c18480380e80 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 374595431 1250 374594181 374594191
    0x3010923042003070923060a0e011a0913020903060615040509040804050409030906080f1303081003080408150112050309241303020913051e010e0303040506010518 72
    0x3800c0541541e80911503030380002c0300d40040e045400055443c100c420072140300e1142c1c03103c1440441110b03126418035022003600401d0071113182c40303180c0c20302410180038101071042c64000c001c088000075002e0b0390f01c4290307007500c40000c040c64031114444004a01a50000700f02d2840780c0034076400038070341e0f151840002d03810820410126083c00d0500c400d0010040380940295500b00044c80001070b0740d5a10f00070040580e00c40e0341c03071030348503441e04070054802c1d0405455810b080003010100700c00c00c05600f142d40c203142d80514041c00381d61034108242010034003607000544445400078010441c1000011010000e44041c146d98220380c4c0d80341125203c81503000303030041080d0410800d000041c50951012040059844109108480e100d0850402a807200302c0c151701741d4614100800c00e51610600843e40075030140c1c0074207000350703282e0798064640780c183c07030f2030700d1582d003540d03446c1c2e414620952007184043e42440440f50ba07400c1a080c11036903401d0901c1002d106c0c082c000f2980c0c10007e00500100d000f1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 374596681 1250 374595431 374595443
    0x2b05130219062703050106030c030210080105180601180303021c05041203050a091d0703060605070f0b071709060a0b03150601030c110a030c0203010c021b090606040b0301092304 78
    0x821088401e180032507400f01201403c03040c18400807000c100203108034001540300b02d00040c800340c0b440c07040c0811542c010304804203100d07d01004028503201c5a001141d400c580346240051540c2e80380041e1501c000503481c085200507882d201100301a00000c005105d00c94030b1050178910840910308650700d225500a06400400381c0e814407001a0050000c0c00d030039001ca0030100709254803000c0e03001a082e01404050b60b0a0115020700220641600c1088003400b9685400f074a00041501c46000b5078040050040968007400e000402440c41001c42018440f13500002000c0e03400c2042582d5074906007074440c20f100d6440c2120303525081c82c2c00107070045503186070075071407231940d171403100550082c003280160700f090001040200015080c10300030102501e103e0340311100190500d006050840e10301009103000d65211380d4180810065942c8035a0300a00200c40c046920b07076610010401902496000020031030b004000441d07107810541000b40031000d424500e940001422036001c401c1d442c19a40a086 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 374597931 1250 374596681 374596697
    0xa09110717091905010806100c02090c0903010e01020d0506030a0c09180204060312180b091c02040e070e0c0f0417010605100905010e060408032b0513021906 69
    0xe00d0303010740c00c4507400d444a807441c00d1607030034404200d4020b0340e40406020001803101c24040c0e903820681e290381044040c4c41800c9031010f0100c4c064003100314440064841c4140d48001810700c1d0700c400840d040c2c560090300034854a50302c0180540030790880d1200c51590750070000020600e090002c0e01000054103c00e1807504280b402e185400101400d0b22a102c2c0c0c00d200b0303000d01c0c000d40c8a900400006500c94240310080100c6040010080c0c116582507621030b02da400000c01580107900d05940038483e00715201e0341d001311020251900032051003c001e420a050507c03070140b5500114072036080300c510042d120360039034800b506882207100f21104070349910410b00080c02840c104038050002010a04000149207440f40005103003842c542040600140520700c00388000d50780f001d85c0113648481a10281d00b0700e400d110101d6141d00030744003407400c004440541181d082c1d80041004500c10210141044141082d0001c2510101180381c203901905200484000001012030f81d88101e9110b540c58680d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 374599181 1250 374597931 374597933
    0x90b0d02180703140408190201050103080d020f070b0109020a09091401032d0804050406140d0f021c0501091406060a03031b0b09100b060c150c040305010212060a091107 74
    0x28002800751840b41056074403900d4a807030391000c089460040d40540706550302c3d4140c0e4100f0316078075a0542103801c01c590414004100040d1103800f130703401f0752107441801741c0c6494108441d640c6a0180c2400070388400400400010740b9007080e07004000070301642c2e49082c2c03c5500c03403d88006540c0c0e5100000c0c2e650101d039004001140c500803600d41c007600c207102042c4912821028104074500b2000301503c00c00c40000b01000140b820b40b00d00c0d00145a2000440002400640021000082d01602401d01d00c41401d00d00d08541d50b600c103400c00030f64810998900314a450424900904020004076070520b01c1c0c0313560310642c80001800324071820b001000c1424880c2113507001c451548585142140b08100e014400000604072a44a80718043d814002c0c40c6404428143c20151414540802d000314420440080004404140074107545956843d0000d140c40750501c0d041070f40700301d0740064010b501c04104460622501c500e100d001d40400c42b0b1210059031242d140ca8101c0301040c82c415184041001040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 374600431 1250 374599181 374599219
    0xe0a050a020417010614010f140d09020a030609050114090613050c0a030b0f1b04060507030207120303050f06030c0a1809020a032109050f010c2a090b0d02 68
    0x55124024420260400e6a03079084802c610700343c1d40d4010f65594507400140082070340050061821502440c0898400320940b10184c50b401301c03414000c80c00c0000003400314050020f07801c0115415806494401010360b07a04141c0000d080c4040122129400c1288a40d500000314a41501400140e0041c100b55104c030b00802e8080c0445034011107050042c01e2111546a0f6201c0540700214050b2000b00c00920f042040d4542c0800000c0c00e26805c0403211000003000121042034500b03480c03490428542c1c90b00d060400341d103800f00d9a0b00c4005919692500c000805515401c00c2d4040d481955401c0400d0300e4032000c060f01c4550000c81580c10807000c0c8410880c0566203442d9081c0d5041e10f0a001404003019008514191015041528600320760301c0100c0e0340b82c03c0c490002400080618050b02d6150906000440d045c0d114051075040090810111050201a021101c690340400340742c180048044104c01d010035030948a101c6100707161800802c480e0511002e035855040d402440d0909070b400f600500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 374601681 1250 374600431 374600441
    0x911060309100f0b030c030a030203120c0c07150806030c031207110d1202060f04020d080c030c0106090b010f0207080d1b0f0303092f04022d120603070e0a 68
    0x4145a202da00c20700c2460030b90a00c80c3c03d0000a443e80b000c1a085108030501d4505211011064081e5118001c40c00211b9804030031745034121400311900d03096450711005000c0310700130307401b0304900c6000e2002d0018204031200e559945250164549443c1941c03602d00705919095081d51807a0141c00040c44000c001503c1001054440c0c410490700341c845000f41c0114406100007030b01115004000324400c8035403074042005a40c40500340f416001e052170a64042010380910580080a00d603020925002089061040d900d100311141c2c002c001807a070325000100503080304c1007164041b0714448196840140301080210980b8000001004c1813103d501084485405010901200c000b0030406500021404040710b0340480c000da402046001560800b01b05581c006010b0082d840d00c0c8045280926143d90030301c00c1080e0f4210b400685a4085001012203082c0b0501d8805d030b01802e01d01310b803500c1d2682c40090720b0620300c04031407003840d643e50905042c0d0f41c2c4207500907030820b03503174040000380701301030641117 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 374602931 1250 374601681 374601691
    0x6050c070305030c06090c15161406042d03020304120303111606180b0601140c0f03030405010e0115030f0f06061202030f120d02090409020603090601090f09110603 72
    0x446420581e01d45401d401c54009003d403821a4112005000040408105550780400c0c2101c00840019295109841c07610440e011413211081101441c1c00f0b1220324140c84030016601d4058640d0791429203051406041100c5442240540521040045001d4445e07091740041d415002149058140302c102124aa07801d10110209500e40c09070502103061174004e4040c041a04050303038608000d40c9800002c4d03c0036510550030001c2e034402e440f40442c5015081d190401420700701006da00c2c05420410146100d0842440704078405c00c01d42c0800402c0000c01103100d140110000c200380c0e03880b01e92090980d0074040804900840e102c800f4004114503d010f2350103140300c3c0d182c4070460a00e9540d10020350752a80e01000040440420b80b9065080034041e81003c80010400f40c1480300051480354458014249091040c0d5404a00320b0b0350380d151684602c00007500101205e03200d28161182559910b001d018a1128078100080d00d811141035010707038603655500c0350202d04011550024043d4507000180 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 374604181 1250 374602931 374602933
    0x1003050606040312080a0506030d050d021c05091b090702060103080a1206090207060c0f050301090209040f0501030813060c020604030807060f09050d021b1825080a110703080106050c 80
    0xf000400c6601d9050f0000c019071102e007214a02141001d0845500410490194010090700151329601c1070403150000710601005884000100540c2c814100102c50151010702d01014480d2400307001034036562404032180661810310b01c9800344a400300d81641c02d200580d200400600c0010f55281c0503010300307210707032508090351110700c82d8603020303a03c403584030728002603000669400f8060b0902400c104603140d420815888685504006c21a02c81403162803180707903011813008125a284c0c2c019956400b40d40308203005558503400c1c41d415643c01040b2810030603071005000201c240c000c83ca40140c06400800c00d03420b0030310356190780240d075020503070403a4826601e81c0b940c1e101c040d40b880343c442c00e036000e40d0060030940304102d0060b2500a803113410030600e0400140003455607840c4c1d1222080d04175625150704003500d80c0001c20003d0705000381c040041e000f0405c00800c110740d02424940c4030b41e0107a0790038894100c00d94181740c00d603c100308020b0006210708005000f900c0c0508000c1a840c0e000e00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 374605431 1250 374604181 374604187
    0xf0c0309010f0915150b0a26041a0c03071706131b18060f0c0809041509061403060c0d0b030a111521061f080a060503030a02033103050309040e0c1003050606 69
    0x1508c1034a6a200480d0b045840b911034080c1702c03d09885196429a10800722003405103141040c1c48082c0c050080707059180d440449082c002080e980b1941d02c44114a050290144544804440054400a02100c5040005584201545029400e0501e4600300c480f01c0c0c80e0300c03501440d140f50499046652240c152a0540100001200f6890701c3c864540c5104080a551003400d042c42400029030f40d181d880340e044800546580d00d540d035400306220b504981c0c215100c07644c0380c01e403090040180106175640707503243c090700342c10030705001044400d441c0804007185c908070145081c50040d8120700404c082d1030606170420111500700e803c12022140c1020004000d035006c15807100c0c20b10352903401e4032150300000c0d000e2014050b110665000d454090001107002d9420710000e1745c4020764902500582504000c440e414107202a45080280d9005201400071035001940300e0410329680d91114101e01d01031827524403804603400000c80c1c3d42c51319000003020120500d0002c1401c402801c400b83c900340c0e01010070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 374606681 1250 374605431 374605487
    0x1201021c09021c06020c01110a0e12100204080a14060403080402060c010b13020a120b0924150c0c01080402010e040b03030f0d090c08060f0c0309010f0915150b0a 71
    0x843c0d81d691549214640c0075a6a0f035a00c44043c2c20f4902043c01e0300d81a400c24031513030070399a81104045940000a07a146d8000e00b414651036450003101d070503281c80a40c4005401310b0380560101d68003080c030340112030000703940020048165480d10308807006000100c0103008500103140000007800302001c0000049035a03110c45e00020341e142040c1442500031540083c0c1252080e8010108109082004008004129005021401072680140445203e410323a004c80303501c01e462619610f90014000d04400c2310007038001d84001c9160701040000e2814401c0d075511803541d41c8030f031026520843d4182d55440c81e40a115041c00080c2107000d034a00c0c0d00d808280010284004420041c11f0051554013000c074864026040c00b00451106400c1130806400c990100310003603040c540c145801050b40001950340e681c0d40d079151801040c0d490200110f0703508201544062014081030509002400075040180a10024951112184603c51226009800d200d11540351380903610805199041100c3c420501e07140c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 374607931 1250 374606681 374606719
    0x804030c0c0e01090f0501080303070311190c0204051501120b01050409050a0501031a0c03070804020a0e180607030b01090b09031e010c020601150e09090c1e1201021c0902 75
    0x80e0002d204002000004110b43c8006003d440503403050303403400304182d504084040751a80300042546c0c0605441f0401441c041ca070034400c544160040304011443d55043c0ea42c000c0681c0c0c8059000d921540c14080810549a000414100d61000c161249901407c0c0414880040d02d0760925007414020b09010004640320380d4003c541c46041282d900160660542c40d00808040d0704000400c01005e013481080034284102084a030040c0180c10528984d568600c00141e950756550400500901700320244002d8010030f1800c7d40324465040265500c90790b990304201c04035408a09628002041c8840400000d00703a200102440000542618030303c000401c200070680c03030480b00d0b40c06c640e9901c2e821a04119414040a07015180c902d03000c0c1181c445880c0d00614041c0b03101080d61041500c400460500c440400c10705041103800380c96030f08405408805400c10307004084026024248140420390201c0040c0b089500140140d200e580520364214011001000303061802c0345c000c40d8041c01c820a05c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 374609181 1250 374607931 374607953
    0x30613030908030d020c12090901090b040b0d03080601030b031b120106050d0c0e1506040b030907091514030313150c02030312071238040c030c090b04060207060804030c 74
    0x10070204c05603452074070000303451401a03260b0100080040901003604240d03107203044e00d4115502540e0114203400c40000007401060500f00c0d03542d0012018a81c04105504a14128411079003620108100c1d224079040c5612412001c06034081c04a80c3c00d040710061408044014441c00040000201d140e11007002c01d290014800c07050352080c002c244100116010085003941c02403501c00345444809150300411014021405540c0a83c0408130010310005400c100030401410240c0d000d0002034820320f00103455001034040c9c40c02c0c1c16400c810250712070400004480d0220b00c045804c241e12464803030481c0008041c80c0941040208108100d0b002d45d070108050818040462441007c80c108218040c01b038444204080030f00600700482020506840b40000c80e450b5804181c0801c40c10f05c1d801300701d500080003403640f54040d25010917812a1540350b0300840f0101c22985440c990aa1140300c1400140034a106040069021480c01e0000500c60400c02d81c000740b0030700f4000301e1780056a44280c0240 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 374610431 1250 374609181 374609197
    0x605190c0501060b13150206010302150c1608010f0203011a0a1403091e01090f030e040207020406180501060503160e12100e0606040204050d060c0504080d030b130b03061303090803 79
    0x2000855400d4a84e03950705d4a000040c8480d944500c4400c981070300103910741d074051002911800d9a0364045103094500b1007103405265845058540f0184001701151000314a4000c50156600e0692401604505403084905130307110b194401c43c1ca06a04080850a540412001c1d0104004001d080103800c01460186000e2007806020340f60728004000440906203e0f0082d14220740c1c100f41041010580c0841c10741c04140e05032408101041c008004039010b4419108000c0d0041c0c903103000098100d0480d00300356420700080405101c075903680c0c4822035890105581104d4602d405814a1a445000301d4a003030900c2c00240c050030704044000061801c14007034069001d002511180e41b07030003030702040c0078499110400301c07421400d0501304070200c1c1499000c0c1d500104160b603100540841d45004a007550018038000d411541c604450040060140c18000182030041401040c001d01d030003001d0042000c400c501900400455492030076117402c52050034010340c103120280384046100201480246010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 374611681 1250 374610431 374610449
    0x16030203120601030507052a070306020405040e0307031205040203071a0a0206070539330c070803044205090d0c0c05031b040e070605190c050106 64
    0x40d072034090940c4022100100384504252600003000f840a4200064070202072640025801d100402d80202c441c5200101664100780f007001800810044990014825140c0588051105840c03404405550380a042c0f4000c1c0808d00d03e00c4d000000c0d00c820341c06541d00038002002c9840940c0c0d140c1009422807030702c01c1c0c1101c4013180014400707074054042100319000145858500c3c6080380640c0c030000d20425140d500e19101452a0b00300c52195004240d403495501c0c4102030307481c1c43e08540105414125001000140d82140301000d40c0c080300150011f170b00c1f4024841c4000e240618070b03a680011075000400c121040202c1031081c251040d1901e4105c41000c101d8441d100c0701c00c6000003280000c1c4185070358005103909103030410040a1004c0340d01290b0282e18146119503405500d0070b200107460070303007040340c052049060104441104611608504000b0342d03040102019040415444807014082d402c0803485c00c0054807031112140c000400001740da441d02022180c581e070355503801e40e500d9500c41454 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 374612931 1250 374611681 374611687
    0x17150105030619060b0d0f2009040902040902281a19020a2003010e0303100918080a120c0203130311010306050414010305010518060705090d0605070903030e0f0108190216030203 78
    0x110390440c0302d1080d0600c0809007044001c0310f92100512940300310b50038a2b001e292641040001c40d04c1d16040305842503070007000508040a41211000303040c91403400a2101640c4402c00501242c101e00780c0d014088050f1181490070300507080701803219098034890801c44c410300c3d02c240d01050403000c83c2c0403149003200301c41c008442240105429140e43d41291056a00104103012003d845900100111004183c1c04a0b40786648482c04522204245010306400d00c005054010641d0120041410014010041205903084a0101c1c0d90b801030310f80c0a800c403020000203002140c3e4014044000b81c0741490701281c01512031000c203040e1071080300920314100c010b4005104020082c004d26a1010001000412081c429600f46596a101511030014440300150150094a8441102a40c99040314013400f40e820240c000406021951100fa000070b50b003803003040001e01e0400c10000c04030005940c0c56899859003401d000a8400780a280d1f0262039003001720b03480401e414212601c0d028080d40295403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 374614181 1250 374612931 374612951
    0xe040302010f0e03042402010b0909060718050631060e1311030c03130c080c0f030105152818110403030507120905040617150105030619060b0d 63
    0x20075105541d20740f015503001884207015500d03c254184001810700350719080004041d65059005144084a00da0445201c1040041191000410034052003440d40d40303c00c06010340340d403807043d90301c68066982e01c42410080812505000f504881020903a010040b141c05c1c40b491201401e0040c95000703202140503245401c14a160035600c500d00f22414010901000b0348005100301948001001c0c20f14540e004004a1541c03007040180c109420fa12181e5903a03503a858052190382e41100c540894458540e05e000102c603800d0600034035020b4581c2c80d5405402149140801641d070442c4113810301c080850101c40410240404504070041c4aa1a03900041d081c0c211081c0702502c038401f102c5000c0d40d40400c020400641d010049070340a80e002001d810200d00155011610074113203030301c201d920070300f440c4010078442c0c0c50300c4412110071402412102c0c0f1420b202085108480240b141c1581038000400240b0b0300c0307604c102039651003a898000024410344696400c80150401021440d200e551155451 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 374615431 1250 374614181 374614211
    0x21b0d031d03090a060f020106050d08030a050a0e071a090d0b06010f02030a08070302030c090405040606080c01030935030a1d0615120a0510150501090305030d020703090e04030201 79
    0x258401c0c8850055860044900081000d07004180706904c00c02c900110307803a420038401e50264020340720081600210a546d41000002c80d0810789174024a2860400492018122442503810074040c0c1006405403500d450301d2040034040742100480600010440d5110643e10282d055075030903c68841c00403603080807400181855003030108103040d9401040b4050a442c2c211b40360507031010b0f00f454056034030f44d5000b200e43d106000e214401500903040c04c060004000d165001b40c0182c5180c00e0451b54040b0454004405449407a0b40c040d00c8040d1224418080e000b051000004038100081400401500d0b203500c1c400e00c1d40125074410229680d42408119161582d00d80c00406968500501003410a0851300e00343c0c1c403000045500c10b0441040010303a0010a210030b060035600310083d1544401152000c201030040079540759018074601d400410f143d801820304105903604500114108003108101d40003d40c03045400b501844008203000402c00002c60405101e18403990001c00c0e002010956a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 374616681 1250 374615431 374615471
    0xc040e0601061b03020703150603060915200301180e07080c0901060f02060703090203011104141c0803010605030402030a0209011d01091b0c083009060601080406021b0d03 75
    0x4502c3d200039109080800d9000402909607508003948190740f07a0030070304180c0140029800104500d0410b800700003070010104060038002424082444a035040545603960b00800c00344000d907108090005000300060042c0e46c41028441c480700181c01459684807501d40340656004880d164403e102038002c40c10141d100070300504890420b140c40940004000c0d442c0d0b0301c0144003404240d90b0746014015036800b50814100e502c4001e86c03140e503481d15013514040d0f19109081d402e001d104890310000e1800d0201ca142043e150b007003c0c0781ca0840e424070300125800e81c805002a40e0610500c1403540241c1c0d40c1c1c003119402400340421140381c042e800800d00c100306605a10000081d407170448d92200b0f540760f0301041c1541030040d05c0c203440d100c2610f10700a00503008500206200400500c02500b01440c40e5070107444142400c0c50703182e580d41d0351110250392004111102c9000070381082c0801d00045140e006044d84240074001e108050310080c0781546803a00000c46480060b44030301a48829580103501e03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 374617931 1250 374616681 374616707
    0x60c0c020d03111006090e06090304080604081309020f07060b0405091f020c011803141c0504060b03060c0a18080c01050309250303030f140103140c040e060106 70
    0x52000400560001039800360a244003505010365a440c0340380e010420b00c01c105000c44414020010181c031041504d006044184001d0014402d8402040700c0c0c020010943c0c1c101e54400000341201e54443c0d59280640d040304440c4901c000440c50046040e59040c005000e4501b0a11409074540340340e410150140d64410360300e280514030f40000e1040246e00030414005071800048129211a01084100d0091241d0ba050307000d1075182803820700307500906010f128621030082e0f8a04a60038030100c1e089c11248901345103101c00440c454609103c40d240c54006550045c0a000e00040030103007040441e050440484524501b6803000480e1559a50080c01d074607440301036103904028090070018a03540d120001448035050107008400248526070402c000341d840c12880000e0000e200c101201c0700040ca415001c00c402280c14100e0f0280c0d00d12140c840c84452543d440007080c20b41e483c5884190500140c680c24140501a440d1700031310030b0b2194000e420405106100500c2290301d0700d4002494100121f003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 374619181 1250 374617931 374617937
    0x2070c05010e03120307020c030616080c032206020c030a020106030212030408030301120203030405190312030216020f13062d0503060c0a09030b040305120f090d08040c03140703060c 80
    0x201511958500203954114803904c0320b0352540e2030329015030692030490180e10095052141208200040f01810004a0000c0b40ea0b01c400e181e640fa03161510101e80801c840c0301e034041810f484039048494401280c41c200d5400b5410040c5080009500541076a02402011000d03079101d41d410000c504140000d640420720138400345080c14103000243e45c0f00c0c130043c8100184071201e05004800e541c1c051045400901005090020b00614424003804a50040c4802c2d20034829441d2030b004264028002c480f4444008184a801f2544560070031082d001880c60b401d4102c074444002c0c188145892140340042d1000e248400380c424250034100c0c0781c0c0c9180308050001c0b02044c0c07004200c6902c00045039030300680290012902c035a07450900319800c12181d440030f8042001e00040c0424550000020b05060218549c1c0e0f10303880d030301c00c1365018040406480c50421075100303001c0f0007201481000d055400610030362a42800e6541d035210415482c0c4440404446508540c00810801000d03108403e00c4c0c1000341 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 374620431 1250 374619181 374619197
    0x6060803030f010611121305040e0d0212040509070c140d031509061217130303030209032416090b030a2915031503060403080121080d0e070b0d02070c0501 68
    0x1902880d101c240201b105d11041302c0204010030003a8080160201900000e0020003650000326010340c1d64229142c0a0f00143c019524410402d0400400b150140d0b04080d003000c4071500d4a2704c049982462001c026030303900201c011504d83c40b0100740514a000d02080e079000c1408501035111072001d00080e405410094074082040101500d81060035042d541c009800804010308105544680d1180724568a034000c007041d80401010f401d5402781070007501c250111680760064190034402e025142d410805621001e0700001d01d2041000348002e003040b0700740380500c0036a540320203011441d00141d81d0500f00e07079107403410b0466000c1d000c8185441d200400681c00211a010030202d41400c1c031074055141c1482c00040002c402c20521004c032101c080010701110303003901d00390078010013000081c050489890306c50311a111903034006400f1a00b180340c0040c0943d1415a0224101d4020721203100300025a0090340d000041c2c0c070711342e20050403140d10400d00142c0d840401d458a400c800206070007940c180100d503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 374621681 1250 374620431 374620457
    0xb010f030912050913020705010609050105041515090806090715090e070c02040902030a0311010c050a0e040506120604032303090319020c040218090106030b030303041e06060803030f0106 82
    0x110030b02100c00582d09046584104d500041010217600c05820a20680006441c40410078158041402c9807a444e604000590301d65003000f09840f51104026103485004a003031041c020264100c400c010706170300b000d0084665404449040a4046640350001d4010000c1000508048504410341d01024a000d003403903814260510300488001e0819010810416403403411511281d00c000c0c0800e40040480c0d1003280c0340d1400034402c00c3e07190100c0c20154200015420424051016140c0e03030129030700e8280c0c420a92009000c02400d0040946901c00d40d00e00c0c04030503808090207124090b50180c1d031080d002040d82068a0080500c400040078801c904000300400444084207940ca072020103422240030582d02c1508a2800d42042c8030554003a200181c2041d4210501410302c107441e07030556404140d6aa511001d80880c2c00d841c8901c4d826400400008002a103a10788180c2d01440c003900e000a02c201035100d14040720880d4111550035400002844040c1501e0900d060050071240f91440c00c00c280 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 374622931 1250 374621681 374621693
    0x140c04031a04020105040b0c0c0f0f0a0303050903010b0607080a0e03120405040c030f06090b090115053a05040203010b030c1e0d0210020109031d031506010c0f03030b010f0309 77
    0x100d00e407404062a025008a42168850382c22140200015403090313441e148014030b9039496045402ca590310902c080340d503000e205e0034000684c45400d00d00400440b0502e04d581c500341c171903a1283c0401c6501d5507941c40c0680c078075900c6d403001d0b080d92801402d03a26100c82880c0c0e40900300c854601407180c4660301c01544083c034024900120303010341e0b500b40c43c04900c072a58070303800790041d00c01d2801e80c0200d64140078000c210841c0f42c0c0c0c00080414000c46d08241d003a40d03220403004c11000040305000c0022402c0102c1580a640ca20301551050b0247c18a04224140e00106096243c0050740100c0f40075125018001903140074000c0c81d20400b805c902030401415a01c00040c52000300c0c40e048a440f0140106a030507031390720344201c03400594001d030020401402c0c41c1d01c000d000b080345480c110042203009080e242c16035004a42d8481159000d00200140074000250b00c00c1400000c00240c10010103074410400a0183e20070024407610070b48020506039041d100141064455000303c1080514015158001c550 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 374624181 1250 374622931 374622953
    0x40c14030d021f15270e0616020a0515190e07090b0d1b090b06090d02010e18040606030506180705091302120a021f05031605070c031103060112020303120a02090a09140c0403 76
    0x1511058015040e020230409034181518514046c12501403001c5603c00c60303050700130030fa1007a244e0701c0903214001042050701c800c881d0b402d41c403044603a0000034184091001a4400d00030003030024001aa808070b503940c2d0b40c1c100240304941100c80044141d040160004900502e5218002201c16a0604507004003240303c00c500c7d110007070304000840d104542c29440c1c90040510b05100925001b40c5444c203403c060014207031a01c03084a05204080010741e541c203050540b032800341086005808070038a024108020341b607002d40102d030804200100c003070041c0d0b02c800a1000301680350000d04024000760042100c051000c40b041d609029030f00c800880040d51101c21203a020071002c0031000b120542d140202d460303000d01000105010708a180200c00d010803034901c0c0c196030350110304480749680c0b11903085d90060b130650f80c000d405034402d110384204140d048180d030350b0144114500506041651000529010060b40154040c031707540e102d0302c001e10820340803203a44954240422854140745030344442c2664 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 374625431 1250 374624181 374624191
    0x7050f150703120f0e0c0906100c120207182a1202031009020a08010f1401080f0a0e030d0c090504140103150e06040c14030d021f15270e06 61
    0xf1071001c800b520742d42070562001a0f1865080c40c10070040c1c90b01e1858070361b01c00b2141e03d000e04c203540c4800001c9031841d0a030040580403082e80d48003082c41c259076907641d00301c0140312a03010542c0100301c0b010400ca001c60b030000b05007100500000c0b032098040104401e07100d00287d400d0111400b10040d51603840d030480d0800d020112441c50043c1d49a980c40c95103d20003056402010a4600016040350702c2540800114141d8012280c41e6a5641d5500d082d8403040301c03147c2202d400309400b000010100c0348098103c2da0302c00381200011900c028405c2203182075a100040c00115181c1c0c070100804040e521220345d00161200740e404020054444a200c104008148030003016142e01150f02052942d20340c0041c5810800c10301151424101803410401422043c00740c0d41c842030035008840c0719444c00003510f010040399a0050452100940c044101401c5081003c0b0030f0251200100c140c80407220101d1720003490009500c50400d1060310030422404001c0c41c281d0f452070305114015021a074041a02500a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 374626681 1250 374625431 374625437
    0x3091e10180512030c1e060a0501031e0311060415060b0c150702150f01031703060a060e0d05120c010b1206061c0f050c09060a0e1f03080a0207050f150703 68
    0x51003440c0700f003c4c61486007550340f1059000740103807190b64295400c06400d1a00c2507009a800381e540383e200c1030301110000d100142041a6450307050741680d0070041581c0805000b440c01c0e0119a0503203030030340c3c6040c034150ba0844e22000a1a182e2001081c00d103d000e001e80030720307054a85814100c6e0210b0f0381d071f1282c001c100c080511103040820851802044648505c107204000120540381040f0a10a0b6003800d00c8150340800070b44007000010018401200e100d000e00404211581c2d080c910304075040301c440400c00340c101030b04661290120341d08101c1c0c11100d508040d581580d40b010704440900355804442e176030380602070540c03a61100742004554245c1c8444c0c1a1800445042d1075102c1440c14104480050701003e01d02c60280d003480000700d41c510350008140c0e8280e18035180c20b41030000c541564411246110026408540040d59000c254403040c4000e1020b2140240c503900d561f845c6512000e00c41000d40d100d80c41c10030080c2098003080685200031a8240305822008205980f9481101002020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 374627931 1250 374626681 374626699
    0x306050603011a042402013e0c011806061413110d0e1c0908030405010c110414090f0a0c060507030306030c081b0603060a061103091e101805 62
    0x4180303101c0305580080c600f0408807140c8110317807004807640b860000303c00d02c019400e001455150380c1041d4004001001c4099000c840341407444019032403040301c49050285544c0401c0184a051800d000d0b03141c45140f00207442981c8105da00d040c1c4125016a4004000083c0402c0e94049668500d040d02403131252882d80414070b140d0701070100039244a040100043d0515003011200c469900007903070790351062051a00c0c00800140702e41600d00b02c0d5140f0a10710b481d07004000034082540309003034a91003180b0030070755541d03280d4066000405442451102000d02c0d900303a4204101984104007000d058000c0f0701c0542082006521040d2649a05000f0217051110004464040520a521900055402514001501d91503404040c0c072110a000f01c50604209120f10002900d040c0b411a03002e1500102048082c6140c204141c0d0b03400400c4c51a42e00030302080c0407028041c2c8510720b407006c04548809144007019995030402900342c03403040c110410045042c040c0035440340386450600a40b00b00700c40c0866 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 374629181 1250 374627931 374627969
    0x5031506060a050c1c08070807140a050a02012003190c09210f0516050f06070b0c0f0a0e040f0e0c0910091103070306060c0f06020f1207120b01030605060301 69
    0x1c41c04000090a01c810380f45603410003207a0346d12150240c003990b841e80d11440140c4034800229101031605111501e10001040901c0e842030048004000c0552180000325000300441c0c42003041203000340c404000001c001041010003007890300400701003c0a10410011180003c030002d00c1c8052034019141004501388221440e00300d404181c115039640420110103515251410030f03281c1c8020117078a030121902d488082032900d0410540c85101c00c02800081c10320450383c0390000c00c05005441c03030628481c1001502e081645110040c0b6030810103131100031f036102c0042d003400100c42002e41010345051601c00f80144045012400319400b4004940d81d0440d40c4640c40c1d03074010010703a540080c06945c980b03203095548100b48009144a001d0643341000940d42d07505d0181c900b5071031554000d0100303c44c507854000040c00b55028080c03002407804064241070a03c1d10031440604140c44100104192680480f0030310302c1e60245000040c801e10f000d103c018a0315010916500060240321a907140c0080004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 374630431 1250 374629181 374629183
    0x11100c0f02040e0613060605060708120a09020607060911040b060706050601050c01020a03060503071d0a05070c0804080a0606080304320a0b03041a150103020a090f0f05031506060a050c 81
    0x3801c4861402d0700d001d814417101c42285007401752022100e45080601c00101c929241041e00e8203580c01140d00303458209506034800c0c200200800c1006203d41c1c2e81c8284015845140140501600c201d0b00041c4007056810291020a5520301c064032990500905050b06d480308030a0310f51070743c0d0000011a06494060043e00ca0740103e4111180030340c800318404690310351640140381150000c0d400d459513243c4500108407080c00d0b04054460400001020494004450780f05950006952500300c4c90081540e40d40c00c10340d0f2250340003620b980c0c050148441030000d680b041000411041d4020f6186c01d01d0006070001d041006140580340800400300e1117070b02c0d030001d4a034405115005120500c52521017581c4500c680050320309a5904030500161108072403080100c2c1c1c0140044045c00103842101c00c0110082d5102d522200704104400d2000150b640e081c1c1c4420005c0c2c001000d800c12103e04000a25150020000744030005c01005414420961101401c454584c5100d140c41341d90f80054040e49 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 374631681 1250 374630431 374630441
    0xa11090f01031409100b04020705151806010e01050319051f020f0301030602070b09010c08150409140d17190504051f02030f01090e0c01270f0311100c0f0204 69
    0x40f01c1c5400030040d68000104c1e140d00c1100c01310800700000000402031008078010048014100c0e8802d0a0388513030640040106980880501294070b403110146200c01c0c03d10000f079000c1c154404108005010a02d400d108210a20354050160b200f01005a281c50f80c0d26500b07400c082100c1c12080c10481e4490481380c040b5200e00700f80c240c4107135895070b6038030303244000f940500001e40d100c603810800f080e03034090180942e148411055172011400d4481c0320b012078405c000140050ba009940351901000581003e20401300405a40d002d0044c1c00381c264406030009422448200041d4480310800c0500c01ca88095042e0030744031000c2c006215543e0349401440e21518044c5000600d550300d801d1310f10100c0d5a0000d510a000b42e10200900d81d03aa85024010303a03d2410a01707040d83c02c086071201403944113060040854950422800c2c0040c03105040c040080a00c3c0c00030f040f654070028050040c400442040c0c0d0b10084241c90f5490000c945400007800040300b02c40081c030010341d0700710000c11b42d5116000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 374632931 1250 374631681 374631701
    0x100e101401180314240f250201060501020705100519020f030c0a020a090c020303040b0403091703040806011401020703030c1104021c0507020105060303160507031202030d050a11090f0103 82
    0x300380600f5128200501071003c000541d80c480d20902c801c0f51407510041071000b0340301c01c65021058050701e592541031103403040100400650035600d042c0d4658040a0307050305120040540000900f64108000242003454030740040d4000c40c000460142c007d580030040780d120800000b1000000380206004a082004520081b1030702c0c4400300d000c07079102501040300c2100038821514011195aa110318106031041e01856030702582060000074003250105041c241d00900c02d00e06940c0c400c3d03c0340c2c40702c0601d4000c40c007840740d150b00c081003d00400030100704880c00743c4000c80c0c00300320440c04d10300002c0d901c03120390000804001301000d0300070400002101c10040894010400c0d0740f6405a0300b00b82000300c83c078006c440e04840c100000302ea0700b10300622905020b07120140145107002c0c400c62240c40003804a0f50111030502c2507940010118001c034138480c0407031400340d0203140d03280c0c00842e00c0b0b025280e0261250292500d849107402c00540c20300216909440107860700c501500031070300180c004020044c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 374634181 1250 374632931 374632967
    0x63c0f12130b07170106140d090f020907020c040f092109150e030c040e03041715010b091e010c060c02030c0a12121509090503040b070308100e101401 66
    0x14001100c4d0041400c481c010fa200c6101c00d01030780e0380c031011110348150085802185000300b1041c0403861075904142502030090282800010b13060340400c0c0c00c03c0d0304944050040e000710550f144649024002c000340c03192081418001504a91180c1a000200030a40012244045c4000e100345002d842c000d0001d08441c08041121101c400d000f0704611422490a8860b000d19111381c0000d00d440d11070410704010036401941421305120000c4030807661030070810003a204000902e10402414041c050182c0301685040e80c540d00e483d030074000800850502d0040c1644040f04082540e64010380d2009000e82003440070030700c994910f10690945c840c8080e0441c150003103031008414044080c1110108402550310741051b48501d085000440d0300c111903480c1e1428034480100304c802600d030044403030b00740038030160307881e01e6034481020b01140d1080c10100c010031011740402100900c0c051000000b0004101058014035240200600110080c05120104000c5061b10109a445001c0c40c000c01c0920301c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 374635431 1250 374634181 374634203
    0x50123070614090d21020f040b040303090b1c1a030a0506040b0907050d15060506070c03020a050609090402010c06060f0f031103010903090e0402063c0f1213 69
    0x206000d0040c18402c1110700d590800d2201007070f10050005000506108540e030741c803810040080f4690b41c014901c4002d444a50b800b880302c509070840104c000e100620460b400303079540d1451840c002d000c201d850380c040340114106006030704008920304031004206c11034000001c5c4a0342902d003264034803401c449940d0381600c11101c40d1010000300003052400795000301d2909000380d4540c90780383d45c0c548842c011580c20a00710b1007000e0004108459641c4003100090000c1241520346000c00d90b613030000b900030784011201620030001d40c00c01094181c00b034072040e516a4503101d9100f001c02c6074420058030007810881034009180c24006180c2c00000034085220030039180b00d666100041420010303020954460403900c48440c59403a05102d240c0c5101d40c1038540c01613261410a003880c0d0a4401441a40c000c2010030901100350041400e003061703001070100040d41d1003454501203c40b40c8001c280b01c00258003c014007901e000c1c03200c040d681170543c84441c4400701c0d69029800c500b40d141c01a0010400b400107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 374636681 1250 374635431 374635433
    0x20a03020903010b0402191b050d02030304030e0907140309012a03150303020705100201060803030705041403120d1109060c25050a090b011b080c151005012307 70
    0x40d001040c00e00340841c001c0c012400d480003044200d115035030003c0c40e1401d44180c0c01c600540150050080c4840119128220100c03039102d075810084480e09240040e0800000c0204040d00b02070403006200d81a00c00703040c24645250060804030031526030f190b00820100c00a070003810309400c22440100c0c45c410503201d0103148000010120740340300c0c444022038205400c00b07015982c4c0f41134a0085a4141c0d004140e090318100134842000c0d044681c5030115500e4201c08590310724100000c1d4082c5426aa5550baa14a0042c185c00b41b142942005d0b4480e400018940d2519020b0805448102100e090000340503a01c3c6d03a03000c4da103031161440c91500440042040310280b800441c4072143c0d0520842040140f0340300b07052004180b0140c0c0a4142e014080c3d0b88140500002a0300c540c15850060400c030301404a0300c04194040090340f48121150000001d51010341002841a034069203608200da401504051210200705079207070058504015008c10804400351440303c207002c0003509044416a10585 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 374637931 1250 374636681 374636687
    0x102070b0109052e05132a17010f0303032f0904020c1009020405070f172d071b030c0809180f0108060c030f07030b010519090504061d0a0f0f020a 64
    0x603512910384210306e200395046100304140100e00b0300c0c0b107904d100003040d450758803044d507011a0042c91034401c1020144440e01401e640e199014082d00800c0810100f052551900509803162205008080f82c0d4910480908200c8041c0140d2403d138440222034a405130240490001d002e2581d16205a02c9000100705014180358040c01c80a8001e40301408565a511004e642002000b06114006604102e541128240c0c8056103038204d071554080b80e054101c00030410b101103400345482076890031960240030307081d60402e0300380b034a29410703060800003884503840150424085500183c80d4000c00640051203603a84a04501001c681707a1038503c42c4d003400b5061201241d0b00340107022240c800c450229080103046401d503072040010781d51044d880e543d01d0b00120080c216210925040c0300c800c6c01240e20192058007141072503240c1d90350f11407480b0300e0041040155201548003021100841030010101c82c01c550380250b0110540030701141a00700a01c00000404140c1d0a40004d0303440401c0e000e4038164 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 374639181 1250 374637931 374638021
    0x906010f050d1a030d090e0705070c0e0a020912011a0402030a110c071a07020a2c0702030909180604120203160c06030506040608060a0905120301060f08090102070b010905 75
    0x40150100d46500302d0754402500c81b4840c0b801056681c4041c0d0380002c050f98070130b4009180440c8a48112500e407655601e00b5800e0010560708003506d503401003044165410200402442c4c0c03000f000080c03107000754580141c21500442001c0c64021a0000001402a0116040480b410790050b03c056a01c00d070300342c4519101d0b181c50180b1101181540c0340c0d00c400c2d140240c142e49205130000c3c5442981454288440c0c0684100c40664041c41c4c103c202c2188184003030608640310b100303a6006103070340b200e0080400c10515001405980303411104c2032513241d0500c000881f25407142c0d10101c0f1450000310354130f040e440c5001e40c1d60142141110103200300100400100c0000c11210981c0b81449240c84600070001511070038014480340742d0110700094101949504050306131406481a80d207030803003402c0da40183d036000740c01c50703800b0821019214041c1035014032420b601c14240340003181800e1040d40e4400d5074006c18401c4a42164680d404507070040c040d1003410440946c0024400b0441c11130100e1840c2c060 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 374640287 1106 374639181 374639231
    0x15030b03070303030b15030103050a03050c151303031805101104030b0a0b15120703110c010203040302011a0d051207061b0504150e0906010f050d 64
    0x144041c44104042c6010b0f64011031000b00c004240014036101000f0000122810001000460008070744140420781c54a8250344e40c0c0700c06001c036031502d4203891900c51000741d4101845004080c0090803504240300e501d0a000142c4ea500d18070020300340d0712402406903003092103410402e48290b0300035080a0a003500700390805441c0e40700d0304650340b02202c0d4400b0666407210b480310785140101d84a601e13440400c0c06146080e130010314040c56a8800360160f014151201400082c0c400501d0a440b40c03414020002c644920b41070034000c2c041c1001160012a481740c00744a401d460900356a43c0b460181c1200040c0311900401044114561062506403440755070344419070403100309d02d60041150016955055126810048402d903100c90802d44070060007001c071080401502d500c0d40c06a032200e001d0900301c60417020710390207940750f210f1109101c1d030152400240544001c031400d03480d1300305 = true := by decide +kernel

theorem cover : BRFrame.Cov 374460431 374640287 := by
  have h0 := BRFrame.cov_init 374460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 374460431 ≤ n) (h2 : n < 374640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
