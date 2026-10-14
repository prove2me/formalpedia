-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1806
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:44:50.603174+00:00
-- url     : https://prove2.me/submissions/979a9dec-c794-4854-8075-c9ca03d95170

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 324640287 ≤ n < 324820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 324641537 1250 324640287 324640291
    0xc21021e010b0a050612010b030702031c0c090b030144150a020f030c07061104080d0e03010e12031003020d1a1303020615010203041e1707050112020c03070c0905 71
    0x46814494603640d074130601003288501620060741200c2000144415110b0360010b5801841c9481140e18100d60900c22004c000b01d00604d50f4005c54603103802c0c2020035840a03003400523006a18806d451940360200700a410121090340b1030f003034072076040c03803155010418a098071a488040080340d402c1e000c100d41d181e2906206091345045040d0500464401c10b101c0c4203842c116091603500e507142d9115a1150f0b039090b0052502250842c1d00d491130414980c414a0181005080e0000105070031152614041c1580f812401c07801e0080c2c0c5040004001391600145003002e00e201071a4081d1740c0d032580c5140c240c0d07072844c0d500007030340200740300e4905820080c1c85000541503045d04003080205403113110890b400c00e00c40f010003400503484000031465040d90f0200211941605004507841c041e61001049080301403c410040f03024680d43d010840000241101441d060554021f401d00038100000600320740002d415240909502082440403c1005c0085601294100c104002c00340e03512100d82c000b416007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 324642787 1250 324641537 324641539
    0xe1c0c1406040f0b010e070e01050313060e0106052d090405070f0b0a030605031c0503060d020a1517090601060509210d0f050702010203091215040506040c05010c21021e010b 76
    0x201c4c00002100c50750011081c0c01410030781e80748400c1a902d1001107640d50030151041c4620982c00310700c2000640c280c403926041d04408400429002d03e40340405c4013113510baa049110001c0281c908d504007480c110040e40500c134041f20260015141c50400620380040360300f10b880084400440850600d4146028100c412450342e001d0200c162600306060301c1c0e030348513284181c1e180161030304090200d0290006d1944a000038010784842c3e0305a0300011215541c0d98490080324550981e41d106840d403150214404940c9008196901d0401101e807981e1440140700701c2c802c12001103200c950580c1c0f100704d03100f507a0f1405c2c2240114580f18504e00c0d6181c01d1061052408282d650001080d0b0074011b030140d1700d40c560160091410450010113118030303124414000e4402e402200c0038003d0f02d8241004540c0694001e00c01001246000c2c07070103815280040e001241407140d0f440310a00050000f15103038002071440c80040c0343c08148001c080e81392006200c0900c11803240c55000d80d030300c800c0560050381540c3d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 324644037 1250 324642787 324642803
    0x303070506040b010506090603190e10022106130506040914150106140421021f080108060112140c09150301061d07050a1215090e1c0c1406040f 63
    0x642e440c10018581f0071841001d800010a00026420821000c29007a0310000c0d580d000c20710240b04600c0c5810802c0c0500759006050f03010901c00e080403400400e011107000c0c1994055006e04040c80000c05240c0011440101c01c1c0d203404c002040d41d107483d00f0090b00c140c0d10400c449030301c01103d020651134a1040e21800841001d03c400025000c0c440c207441d00c150000c3d01c612910301414034202c0d22540766103072406010340c0b0a100801c00141c07035400003e03140b40080d42583c402d602140360001e1103500107034130074000f5600c03d04c0180280035044124650719035000c5100020002c0c1e415256041208400703185038485582d0b400c010ba0091154131090899404400130021591038050000385c070f007800304403200281d0021002440c074038021401807000000b42d08081075030310748008040781650740e82002c5100c42c20000201b00720384800e03400354090300c002c6180504a8001ca40d00b080c0e0b1031044010550b07080000503050103080c04082078000030060046d409640103407030123041400554049a404a07541c031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 324645287 1250 324644037 324644039
    0x20706050f0a1103010911070b01080304081e072c01090518011802010804020a0321090e06090604020d140411190b0d090804080619050901020406050d1a0303070506040b01 75
    0xb40280c0301c0c002415604422080c2980d09050720240106403c0c0d04204a90104104450100d26100101ca0007860588021a070366070502580e030341040110340c446627034046513550320038035040c0100d072803001e0300c0105000f10305254081845a682c18000b405441465010000110b10315520350000c2e88506440c400480c02c0d8440900c03103600b246c524851104003803070344c04440c4006600c5410b421360043e000409100d60180c4944881c45105416100c10000203800440c0700c002940104440700117010164259030b1a20380540482c4038060000c104900c101c2e400220859a4440e1703920458052000400c80650303880d0524050403000c3d40468440d100d4541540c003241c00f0451002100140d030407000c0307801e040040000e080b5019061141c001c68845406200100304d442081110911400d10702a0100c00c7c441c0b516091005c50b10007810707031100c1d41d004000c00d0010130380280468000c0da0b00f803400050300d0030a081c40d0203041400c6400c416418000001c0581c1403200000c0c840740114080d00c0542266 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 324646537 1250 324645287 324645301
    0xa23150403020f04091b0603090b060109080d0f050d0c0305151906050d06120b0f10080705060705031207080a0c031404080706091506140604030201020703080f0d020706050f 76
    0x14021480300a5200b40014140342013800d150b0480d40810784110181040000c1810310031300c950403150806000a960707041c0400c14000d40c4098503400c00380c00e00701034025500b07003038400f9261040f100041050014080c443ea400702c0c840d800311200b03102e080701d003000003030545507004014100c10388000d220300c1311070220850b040ca850340300e080d01a4803078094009520b281500a9036241c204440001181d903544100003201c1018050b400c80c46032207401e84402628140c202450a02e6002e00114030480c5001002d2142400c0003c4078003d80c1c504480e01382d03d0f000237150a03480c501c2110506400245007509111246400201d094050828800180b2842c88190400c8003140c4418401c101554414004540490303290320003041504d024010110384d110b1a0749800404074010b1020200c0c2c1c5a0300da400f08030720080078040300300c1c41c202162058641071564000035030b01d44180c04080d0442d400050303820103504021007110103000010400395111912424500010042202e00c0c07032100231020002004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 324647787 1250 324646537 324646579
    0x150c09050a1a090d06020c01110a030c080601021207061b02030a02070618090b1807020f010e01090f29090d080a02130312021207061d0d020304140a23 66
    0x101c2c500072106a0a01c4500d40411a848510706001e80d0410750800070304250990038024000e40b011701004a039541d02403103070003e00300e4403004480e004014004045c0040b6a0307010421100d0342483e00071250704d940081c2481c0c0020902100e441161481d01c044210f5003a8000c4050109100140c0940d03181c16036901d0207071010016002e8240301184804000d014410455015448110b0301808d0701c540d0713050341810100032040c181da55201687c0080307041b901183c800d004c4d007510100b4010013030100004036a100c10261040840c014804401d102c0041d1f00680610702568000071121009209070611040ba01d443d55a00c55404000558036800900c0507a5079000f00c401a4800d079400d20f0140346107440d01d0001f04010005642107000d04401001620500005015030070302030800011216001b90703902c80d0142450f10808a103400c4551401191500807007601c0494440c000d021441d41000c0c00000c011200c980c1260f000307514840303e030007000302080d10040c418100540b240f1719022025484510 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 324649037 1250 324647787 324647819
    0xf040203012d0305032b020a02010b0922060b12071403120301060815010201020d021803060703060303021507021908030403030c031808070609080c0307030207060804080405010c150c09050a 83
    0x885039000b001240d03e41c0c68007440c28480324440700d038040202220425281b05aa0103d2083c0c1c00603912003200c56858582444402d8202c04524900d022858500741c03140c0301c8040d000c4014000c01c0d5914002c5000b0b0305d5031019800c0c1072001c5c00940c0c407140c2c1c4038021039503503000351501140603110310344a0703240c9a0b0f01c0808890680b180c07a26804401d54424092580c86149610740300c0c1195020302c074039030203004580041c00505000030240c180c0c10744418107061030050004c0c0801c3c1050704020040010030740100d0001d901040240c9001440c0d82d03100801ea180420010783c0c060300c58004010745d002d100d005800786010794840d83d4240511600d110048090b140c1c070718407900c504c0408412880c0010000801048214401d110100d0341c0340070303612902500d8110f81c45556254000045407000c042e41403040c94064078290400c0c40d098106500c600c1903600990184a06100c42c0369490000d010070340300701c4412581c1d417400c18001c0d000c0d1044020300132401c130700c2224040c240c01540800d50781040f0000c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 324650287 1250 324649037 324649043
    0x40816031a060a0b130801060b0406021b0d02060c1203070e0117010305100905010e030a020a05060c03070504030b06010c0212031e2106060408010606030501060f08090d08060f040203012d03 83
    0x7002d03150800351401c0d443d60203245540c40794511040001002c0e5020300503035008042420249d500c070b526002001e41001201c09129900c148071000d48461551201780404039103805444282d26554141900743c649020156044d40c3c0e50b40100400c004990700840d40c0e80594420390721200f000f4015490000f80403003c2c000200690001601faa000d000c1035881201007c3c040c00004c628650814034241c10b6901c05842c140058214011000c14003804100f86600001d8225400f407039072403c1d600040950289010040045004402103080b90303101c1c04a92280607002440007070840e10740364400344d80c4c3c1d002c003100035041151200c03400002000003041d103405103146130030000300081c6440c1c420310b00c01000b002d00c3d034014018480824031810900c81d44024003c9030324000f03a1541411400ba0601a54030041801c12180f80704001110f900410420503001c518208019192140e00c002262800c15811590f0481c0c40440001080e40008075002070125190804140038401043c5165048050340005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 324651537 1250 324650287 324650299
    0x260711010c09050603090a0b0c030603061e0c0703053105010e030c04090303060e070503010305100603030e151620040e031207020304050d05011a0102030c0d050d02040816031a06 78
    0x401050502c80e00440d070226a080607a0721804540e6940c8d421640d0944007252034442c007000b0008036080c10080a50880103003000d003407122a1641c0e180c0060580140b5421798150080b0320541010302900a0300c1030481c0c201143c0c91014070381044202c40c04082007880341d041566040009840d4040c1000d0448804042c010340440f038416018400a814440d200314201030390b4408c0000c1034101c03e0900b5000b5070866a840e503480d45181440e5142184415250340701c44d03d09403040000035000100b90820074029540c09030000450280c2c40450b002d0700c0740d0080746102d420488002c02003104003084054140b1040310b00c00c0b055030024002204d0a80d00032400544c010421820600d80d000d140c0e42e807009403031048030b00d4036858100ac1500700c0d040308402c071410fa446010420510008040c0082204001c0c801507042c0361030950300d2070355010014101000d200e4000f80950b003c85481c1c04840207003813003c007210614040d0030310760b509031101c6200980c0e0a0f01c2c4010600c290010211003a4000c610017850 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 324652787 1250 324651537 324651539
    0x20d0c080601120209061b10060f1401030510090e0c011206030c05060c0a060f020d141006050a02030d020403030e100503010f060503090f0d031e02071a07260711010c09 74
    0x70304001e41c4482421035200c0c1083c0720403040840140c40550307c3c524442e002d80200e80c1d03461200001d80d91150801282c6413042c2c9800d010b10310f60b551840c0382c501403d01e004986500c3d0010900424082074110942c06418140d18030524000081c005031b41c0032003a680c40d92020210444041118582d0100030400703802e030041040246011030181184142e510706580c03a00202e5580c050032a003440302102d040ca6000320315600c1301000c40c4034002d503114058468080d2460144040c0c42505e019000b41002c1c03080100305540e03224801c0003522002c8500641c215920b0742c0b82e0802804015507010781c148180202031a00701000c0c45581624129030074908105d484034201603003074a064200605c1d14802d0b100f1007040341c00740101007000205401094074001101c4c02880010014000a00026400340380108403084c0082e180c483d207051502c1d4840031001443d112090201c98922a011030122101030305c0904c000b250b441c000c4114080d2010351540e0400d41c05d896413090a849140031800e0101b008404 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 324654037 1250 324652787 324652817
    0x40c0602150919051203040605150618040f060f1d010501020d0203040509191505010905010509010206060f03031603030f061215050402060f0a08010315090c14031c03020d0c080601 79
    0x200f0f881040e2050707040c0c40d0110034140c502c8942c0c2e001250140d605503196030900004640c0001d464440d400c00307891040c40e00852401a401070801d07100014000c4c1e540b4904c0305482d154541c01400a0b1100725403c4c0000c584e5901e80400308403041680c4071068550340c00001c1d003076000198041050070b05030060740c2010300d443c1c01c02040c554014645071080c441d0000c40c909107021842079040c2c0d041322040d100b5001c2d0411000500003800f541007541070180400c6200354580e0001512544241d00721558403145941c00d009c41d0550250b07440d007a40c455080d00c000c034100354043c1c11900c40410202010800c455459200c56650000004c020f0484001e00b041040c080059400040c0c0c0076001078226460045a19605019a40a101d03d6000926520010b10030003800d1030003000300488510043c009140103444200e20000540b15038410210100c0803159243c4003401008003004106030f900407101c0f0444005000395102100c0010aa442e01b1031224219001e90740e094020401a5140106000203003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 324655287 1250 324654037 324654073
    0x10e070e0c0d0f0509030a090f05010e2e050c0c0102030703050307110a171e0708040611120a17100e060d060b04020f0a08180a021e0405040c06021509 66
    0x5070000100b1612501486045034031070080c030b8010349502005584d40d0401460040c591445500000c900c240840c41c2000702d60b0f845482c4a0580400b1920b166104c882049014405000c0c0f41c548005149003854041d0b10a800401811042100c0d80991380740226040c01244c40707100c0c400000700450b20600120f0196807062002c8482066070108980298003551070b5001140c011090941031300100288070a030740c04042c2c54032680c446280d40124180f0019507548450340c09117018507000c02461140304001c004041008807001e40c00e241100b0382d01c1c0115400103140d090210031440032200c2c0c0c03070701085406010402c640c0483d02045000354042e00c0703c0c0304000700118014011340d861a2a05415600c0c0c0c2d070b461004105940103084101d903602c41e00c40c0003825402d0010000e040903101140203c003600b030040f8400101d651f04035410507007070481d0704c1500360380d085021180781c00c140341600300010440c0040310641030b03904039002c40350203480070303101c01c0704512040740d101006810070f08401402c11549 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 324656537 1250 324655287 324655297
    0x2030a030902030a0c0b0c0c03011a040203040f0b0108030306090105010e010f1121090901060f0c0f0f0b040c031104060302010c02120a080a0f0f0309050d110708030c030705010e070e0c 81
    0x34140c1c0c90304a0507881e032040c200042d0f0000e1b202c0e2032000038082c11038503007009071044411066000f0321aa003e045440c01c001030344080c20300d01071a000030000781044068030310110078035449101d0341055611186202d0350381e0011030303500d8007601c3d42000104a540c0128103680c0d003110142c2d502001c0e2204000126401400d420300c0050701d12500311689a00c4005013146604103101c50246a1aa0b6404040098888060348128240001c800d5080c0b200307a84a001d10040c0d54101900c24240012407800840d0184e011b98058402c4101c0c0e000c0c4020081183d16010441e4054140401182c004030104012034030f580c44000d0200d074540000ba001410001180c1d049400d4490641700305126a40b541e1400341d001292110018103a2100040600d8104071410000d008500c1d040140800c00c1d51195030b1000340058a400384400c00302500ca8043c42005000044c0c00c041003521348031b031a41d1b5010b6a0307a400c03441003168203508152802c01f40c4c0500148010444020424000d15a114401007040aa02c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 324657787 1250 324656537 324656539
    0x406090b090a0c020708240f010503070e07020304050a06030c09091a090a0e060f01060207080111040909110406080d141603050d020d05010b0c1b090105040213050307030b040c1502030a030902 84
    0x40d190001410100034000d40c082c004c1000c50360361f00c4c113004600714201800000e00782d14100c0000c40042c03045490004142c2d050b2600860b0129090301c542e00d05910b0342c010390744590342c8031415401c081003441c0d058200c00e551509035154174000a0300d5a84150a84180c0c4a484860412080d68902185441100b45070404901140012038155100da0a42403890495072240a031040000401150b07a040000c00010314146008100d090510b03003810240348182d120704901c06440b20050010700c00314407407044491f4001401001120303a12400700351a04102e01c4c809001c07903034440c80400211082000c4914550b500b042622031031043d036809484e2a0071801810303211030740c00d2013500c0000c0703010310859010b004c0003281161210708104a01d8502040c400701c8031fa8541d030000040c0d281d0723110405c1c00ca056030011034001d0b80703400d40c0f50b014206c150b1056000a038580714070b141c00828801019050350045024000c5410090307102d070010000d00341e0803410200142d0003009a116060311903449044c41c644 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 324659037 1250 324657787 324657793
    0xf020f0c030d05130f0821070c0e060105090405040b1b09030c190b0403031d0301090210050c01020d0f0f1401080a02040f0906140a0c1d04090c08100b0406090b090a0c02 74
    0xe140d80301d80d80c4a40380ca0304440c1c6d003640404010800000b80c0070b04140610900804c0e02c0c60540035075910840b1880034031420980b2003485c8007180b0380d680234000b0b9410142018004021501d8542807400c0d88140507924040c00c10002d44456024014200807a41c540c040500285a035600c9001400320403500146004500301c2e800030081440d19008008000a50181d580c000300304042c02c61817480d21003110f04092090303241c11341031001601c80349180e801400d05c82c20300d162038200904810b40039114410300040b4441ca01a642d4189205581c400e9659160a44042000c1011900c00500204c001c0c050650315600211100d00149455008000d01c0b000b4218041244021540c400c426252048070000e01001001704106001c0c40d50303c201c0c19040014030302194a0900118002d0000b044090343ca401151107011030003e1003050403954000780030100464203048142440200180154081c035886917040810004d210f907580d005009031944002e15405480d142c41d008400148403140012082d80 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 324660287 1250 324659037 324659039
    0xc030b030c06310602100c0c0b132102071502060103080d0209130e03180a2709051213060e01080a0f06030c17070902030103050a02011b120f020f0c030d0513 69
    0x541010700b0f07100401950b0000c01e4540d44440c10303c0c090b04c45e00111a400c010304544401e000c103140d40d0842c0e0300070309038032401c101c4134420741002082c1c3c5031812045050103040000815616500040c10800c071210400341d003004003103840040340c41e0311080c4005450040e0034040e900310074845500800903030b0401051f0755143c0074448041015505029a80314041d00041030103411040407001c40b00752100c088030000d1507141843d200da625200c00c2510305188841c039000010800c82560300032200d6580100403140c6100000c443e13560740f0340c043c2d141d040b880c4284110000313501c0d028a001d941c2c8000142c4502d2601e60340c0324203540090040d146c0c102d40340e0741c0f1602d00002040d51090080d026101c1c078030782c1028007440d103141d9516104580d400040f81600c1000104089035001c51104200c176424a0314950801c12a4001607031680c01c803001030204484074000c6401c6907000f101906150303c064081c1c0c2c42d14851081d516444242105d00241c16400503010543c05a2141e401040090340c0455082640c1d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 324661537 1250 324660287 324660367
    0x717100302040f14090f1015050301050a09170c06150105190906020c030a0b01050f15030112060c02010507090506220308041d0420010309150c030b030c06 68
    0x65034a0303406070043c2039551000c214542c0c45500c4420b511445040040c84001c40e141950781d07440644600344400259624080c281d4041c80722241401084010000e00c82c500702050284000c1040240071500021200b100003e0440c01c0402e84615041000181c0308a545012500e03a507008041c0e0f09504008003000400217000450f0210750211019a40b82c01c8072508003000a480d1160480c0424480e5200a003801c0c00514245000303419101c081c0ca500e2101e0000d080030880c51040048810302506000c80045044000d1411440816024590920105e06140c005900320390080d01c1890010720f07010740c1400303541801d100510420103090400f213424108100003100d80c003a0703600215201c0c03400141c20884a5440500d80764040e080a4005c0803a060139500d0580304021800b0820344910740c0c588100c0310746e010f54094000d05401c08620b0080f030400d81c002c0300050990031100000700e480c0043c3d041507030500040c03e55401713501801071071403e030041d0440e8641c0c0403000380c0c0100d004d042030448000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 324662787 1250 324661537 324661541
    0x240d02040e060f010e0c1e1b07090b010e06070b0604050c0904090f2003030301060c050a08040b0d0f1811030703020312030a0c0e0a050105162117071710030204 70
    0xc2083d80c460b10042c01c0d410300c181a0300b01c140142c2000c3e5808002c3c000b86a03040e50703200d01050440c001030100e83d03a490034100014030320765030741858070380d68000c008001846854070303000110411409d17078070000320290f0181048441d01402c44003810201e441c80003c1c1d2241070540c89250840c0d218400c090806c2050300001d801c2d00e441890440c0c0950208103a2010003507820074581100540510a0681130a140c010982d207000c140311314410071845802410501c0070038024130340661741040860341d8442d22030f0b03100e2030b43e90b20071031030441041e2901c080c12090800900ca410408510100ca83e001003400392982d40d081c2014106050303150164100000040e03404101c05d442060b00004410b80300d1419030301040848a4620b5140244125800c4443d600c1e80c8076801c613403c1d2102400c1094440079005030015401f14243ca0003809842d05589404810661501e002c007241d8650741d540e0012658aa040303508a8000d617081c6010541c100001e076404e081005009500c41c05160b882640c3d250b80c2d80004007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 324664037 1250 324662787 324662791
    0x1b010c020103110f0a08060301021923040f1701060b1b0c0d06050f0f09030f25081e040f03060b011205100e0f060d06020c01020702060403050f0105240d02040e06 71
    0xd6041e04c00554810896004a0503030b5002c1c008030021400d06400320700c1031a494445c84080410050320000941c41071804500d04840a102c03101c1e10380d01d943c0c8681d44485000c0070b901440f44040d020154054145a05000d0a8150341c1030000703403810007003829440440c00c45049241d8105014600ca002c099403908400d0f070140300d000740004522401c103200d48484200e805404c3e40d01c520250350402c1b203c0340d0000229042007030f10390034480d078444c03001a05424060211690601d88041c410303204050000c40380103800e40001c100162018542e03205000280c5100f0340c846c4600031881d419081010a045d40d0006202c0d05060400480540215284100f1910704580d44441d80004000a010503d6010781d00303540303c5c0504240240608010000940c43c40f503401300201416000210f0030000726081d010385030000d5014081988031360b00da14002d5203c034981e44401820790720344400a4200d4400e211303c11208500e050307034414a848800305208108000f924180d0700552500c0d0103011214040043c54 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 324665287 1250 324664037 324664057
    0x8010e071523040603060815070c141605041a1c0602040803070309090b0103050c18040e0d03140c07120f09051807091406040504090c0e0106051801021b010c02010311 73
    0x583d0346051482c043e08440040e04508900d0780012040814400c0600c0c4d80d9130405d9850800c40c0241c52a89420044000b01d034000c01130300c0c06040c103203d802e8130003481e15909840088400380b142c41c80c64408282c41c900d10945666000d04851345680307802c09404860300040d0300407440545019244ca054501d03507405480c0c1103000070b00c000300801c12122180b01e0f040c1e08200920301030101d420b2840600c0490f01070000c48030078040010300c16002b103603035503402204c919a00905032600401004805801032102130b0740313178035400396110008641c1000b4008480340303554000c800070310b4152200f00403200d5101342c4803d5011302c0b105400100700c41e0f40d00d410291341140a0040c1000901e0005001410030f0040d0348615402010034408422035034901e025a41541c201303590004400015062a40518000394403000002c00f81e84004a8403650190081850b0b004224404d68186c280b5801260368003014264200f642d0180c00064035690f108840700c8524600501d00811350002c80005100c645e0b001c5c2c07440c0e17 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 324666537 1250 324665287 324665357
    0xc0b0a09062f0a080f06180702010e250303180503060c0d0b0306010f050d0609020613030c120c0b0307032a0906050304051203070c061a0a08010e0715 66
    0x2244500e00303079000e0809084a103482c0301e07080030803d14014140942c050700201d0004210340004695407135500304101040030900500039039040c4988043d0080c03160b0f140790581c5014649148106084101c05414000c4603000f580520720301d141c41c22a0440142c0d5401040001e40090014030340e80d0401119000b910031810040e910003003108040c04455120744103030300940042c00101b010080040122044400917521f071103110103a0b00e0028024103501c0b1000f90700c4400450a001ca0424441c54941a07034882c1d08210f041c192038425035181c02403c000c000b051521207260600072204900055500004d10b0b040c0452007807802c8004158134044c50000c581c030b54101305980f9201a52006200b0002d00c5182000b80c5141032503100d19840e04100e007080d80360888000b01240c559403040d50440c040c50b401c000c00f00a180030100c0714030007880d842940307144204801c0742d000c1007644c1c040c030643d03025000f100020146280b40c050110000c03034000044006100500520300c46444145a04442480080140b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 324667787 1250 324666537 324666581
    0x130504050d032d0f111201090b06190c031b0b04050105070908070909020d14010902030d0806100c110d05151f0e0a060f0b090907020d0c0b0a0906 64
    0xe0480d101c01685900071046200240c40e604030721060600c8011600f41c0c085000112105410003824410040100462000601042c0004003070100f9041e0b44502100380107000c0310408000c1140160000f08110300c41200c203070b000c22801106503842081c840e0501d010481d50728000700d1100c04c0a18016202c140c1203008000810900780319099010303607907080c5818114203040c07410307607500340c14005c50003401e9850b10f0103810356036204131017104030350b001610801428801d03120314087c105502089020340305071072100301c0040c0580384040c41540050314101d84010f0010b0200c030b800100b441d0039100052003034550b114070f840700155140d1450003940101165030180c20062034900e030041140441d040c40c40b040034070042e5100741503002c07102d260040c070089480c1c0c101144000d25803070740050419020f60400282191400004d0119035800316062202d40c0d8400c44140c2e1a50710385c0420400050020446100140184200030380000c04104002000c1a0580d5044100c5a21100d206509412111 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 324669037 1250 324667787 324667813
    0x308070312060612091103060108070609120f0f021203030a0603050708071508070504050a1401080601170c0f09090f0910020a0e040c051201031b0b0f0a0302070213050405 75
    0x140d00240904a001c01c208952600500800400340241074805444d02ca000d00c0d0240012070150b801600030080651b02c20b5695003241c15500d003268030940e40850482c07900060f0b2090034115032004190045013130140c1605036500c07112100100c0c241284d1162107003541b80d0401800300080d521070108854001348880c2503082071840d00c0000d0307000c1c586941c001d0205200e0000d120141840c17002241c24030b25550707102d980301900c0e1030007a50030054000040103070010700e100420000b002da4601c2070b203e02c0311a440355001100d0f1054105241e4a802824901140b41506004018002c914220704107a0510600400240312242c00382c610486252680c1c00b07002c0603a40502240c09044208802140307030003020f4102424900148601a01c01d0f0b56445881000340c0c060400c48000111900c0300651560710780c5899603003e480b10304042d801a1400101060f0009154201c07411102d4aa80d40d0f0304240c1c200404174081d5116503c1240c104401040100030480c0314007810b800b40348144060300172038068003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 324670287 1250 324669037 324669047
    0x6050a0204080f06010b1605070b07051b04020c0c09090c040912020105010b031005010c1a0f09010b03030403080f030703090f0b06030d0e09070c0525050f09091009021903080703 78
    0x80f80d4003a0342000c001003240071850300403280c51404120201c810042c140c04d24505000c80341e80306464205002400c4800c02601146a0307410318854290126025404070a1008a025840340240307180d124140310f10051500a01c040d030b106032204100c6260140950208050300c061050480700381035500200d8910940a000f41c9000d0000d042c0d00b1419807401002c1030300742c042140320b01c034107121000d02100203002d0210011951043c11942c400c007641000446050f010034121004070300d952900341e404500745404030495040700d4204d1000340c1414425140400c059101a2418050540e96086040026440101c2c080e1881c0a290791081500e05101814100441c050000e010002000e400c00e0050b03852069040d00992249000c920030302c600e10b820b9107006001c0c51004440b520040282181030600300540040d16010b6a44e100141240014400314601c16110a0620307007245105904440855100c071410300d00007002d001e05403076042c00c0210300c9221901f054501140c0005c0d585c1c1416084 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 324671537 1250 324670287 324670303
    0x60501080313032d0f110306090a08090f030f030319050132040e0d170103051207050c13090605060f0a18060f0f061101020408031b0a06050a020408 65
    0x4400036610304207001d21100c00e441158000284215108501c001c80004c400030780024181100a1402c050b518500702241c0303540881608031988000566085081d0801080380707030050030b400c001000c000c403155503454140e80004119075040308625124a4031981e04000500c1c41d54545c6001d16600d09203100942c40703105000396009a42c9084c100108200200420a003810360fa0202c0c0741054121245203955030017070340c04031060340141061032801010f9004503446030300e01c150342c886070b842d1220100c2e5803170707400302c24800648550814941d000403211564018050144103600355805800c0d03003400514803054002500000e0785e43c0304203074400c0010520469422802c21500000700058103c00107000c0d4025002d541c014030107049401d5912296500688050201f01d001d084000d03407550011481c41503503200302c800050f01c1c0300e11040820303418801c54090300e0402c000b070340c503101901020300300050f01211110314501c00d07101508041b80c1d40c3c1c801d031402545229805a580e40c5000412882c203554 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 324672787 1250 324671537 324671549
    0x810020304050d0c060f060807090c030b0d120c0507080d481703060424030809151306140a0507150207140a1208160c080c0703030c060501 61
    0x204100344804a4800101401c081d035a501e018242145145011005014a00740e41c2d11324500300307000421004804216142503500054040144111090044040c4c1c2c40322500150003400c1c0c5001c1c030003c1241c1c41d4021001c1e000310709002031b81021a40c1d815241c060290f100305229008080c843e000c035903210803034903002203511902c1c404244050b0030740c417450f44580314203200400303010003150f541c0d29a1100104007070303401800301480c4c070246c0d489184040e4002c03506903200c2c40c9031010b0210314040004411a14908030803400c0551400e503600d0709500c0d400f0104a0380c0c0b065801c40d0003031f186540c000040808480907100f1051061500c440600314904c03103202041c02d814107001405806a0050a440f0043d8204041c2c2c0000d90420380d02c80000d10800300f02078840f60740100705100301d0500282c3c0c9008588220f0030a03200c8139241ca0f0407900c40c03109854070100c0d43d0318001180f003690303c00e055a00c0325038002d8012038503000314910000e01d032524503030003100820700c24600b510501405119603801060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 324674037 1250 324672787 324672791
    0x21e0c0601032006180111010c0504030c0609030c180906021b070b031b070c0906030305030708010e0402090103030806010905030601060c020909031617090904060504051c0f030f23010810 82
    0xf40c000c001036410b0141c174500c50f41da40c258070b66184d010303841040c20081303001a100082044540b10607008110b85c0c001d000a444101103441c00080540c4a40144411640c00c220b03030020a41c10103c5a00b6680101e88100c0e0b032803500c80e82600085912480144140062105100c1c0f016000c114910b080c0b020a5000c941030400c03d104110703049514000c0321800403940b10401ea66400301c1c0c5403540310b000281e04420305e0316281020100c10150010015409051310380c03140311150303a841d0007402c22010200c400a4015100710010400280566841a000307a030504114a00c0d50b200d1001c207161101c02d80c031400002d501221100254100410100d810001c0c42006e1442c000b04a002e91640e040c0621004101d0b541604040161407000f50607100d028070001c00c08513407820310b4240400542829542500c1c0b0780030740030740141c07402c02511510445d02c00715100c0d07004c90340300180e0a5000300705601071184001e49401040454003070390144c8a00c1c0304171015100200d07504021003149815107400e0f51441e814 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 324675287 1250 324674037 324674093
    0x30e031f0b0d0c1512090201120c0509090703020417150f0408070b10050f040c0f0e0a091b0e0d0b0610090e040312050907030f06021e0c060103 63
    0x98800020310200903405034010409a4608000c10305140c40c200c0050802c98940101142400003481504000b40042e903500000b2070700164044215804204002e000c00d0211034032004014560304900302e506014100703941031900c001d011603070217801200d0340000264002424442c02c03000781c1d8411000b0012070010100200300d041115505c100c040c3c640c10080000c0ca00103420414040200c0b03621030390007410b112950a01d10f8080814000703034004c0741d104a80806025034141028070440c3d45020140c1da506003803581c80501581e0054464149580084070030101045d816100d0240c42c000340740d002076095040c032094a0042007502c0c24100c4e6485003600490074008508160011500628100c981b0b200300c1c00850000d584004056000c064411000d9040000340f640000a201440c90680020300c4642d603688950354803420180401005100900c0ca14004100f02c0e6014262800c003081c85c0000c101c0e801c0c2220003280e0440984182e40b039100000500800030302ca4421402403802d000810319034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 324676537 1250 324675287 324675313
    0xf0302070c17030c15040b011a03060d02040b181909020607030315030605130c140a0303110a0512071704030803041524030611030c04120305091c030e03 67
    0x45114801c42c000c4a4490041007107181c1c040c8100d40361a0300030821100082c2c003000c4102c00784403044500b078400404a00c000900b1310f80c0c000c100c085c3c921803034045034135607230703500d810080200c21005003640c003d584c4001d00f48060700d40c212142d40d00160300400c0034982c81c2032030303050300c50720b03a151000c040090038a51040010b80f80c0400b62490300d0b616017030100b1441543e8204031001080360b130000c0c100f83e003400e09007c0c105240089900159002d007621524281e104d0440d0140d8101108080c7e41000340c200702000481e03ca00c600009500030a401d450118405450381858000d0f500300b8800c1001c1d000407207038108210f00303198118144085221b54101807454540f01d840b404010b0020b400322460201c0f00707004402643c03060b8502c0101f1810003042c000e40158284108009010485003e0316140d081c64800074403900703903032240c00c0e0703040300b5403600b41003079804420f8001d4280c0490522406201e2a042c50741d48804054011034508814072155142e8100148205c0000c8081e070300a4000c85100e1f921 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 324677787 1250 324676537 324676553
    0xb06070209010e04060f111c09020a0b160503040b030105130b0312090d02030d0e030d08010510031d03030901151401090b1b0105090d1e050316050405060a030501060f030207 76
    0x119a00205992110b60b00c504000010309020002120702c06c0c81c2c607c03144500c26400c4081c0c40440480da08880d14402e0115085084076900c0e14007a42c48007441ea400c00401c0c08080013800100c140d1a0410b04c140029901c152540d00150004500c00401100500c10350400110303c41100a03200014860708030424007007511507007030502c02200714070001144401c0361248001e81440b80e031302508803207101c21488401042e41c42d20704052882801200d40c00552203100320100c40c140c0700d008240060b4001c155100b60028502c0500356084510300300d01c2c0c4920502d081c00654894104040081104249028080c101a6176504000c4621240d0f0810f00c0c1c061f41c0c885c242200b038a5460200ae40d499020340030459075007100348400701d43da41c240010080000d1003c1401600255141c4403010300c0707100c0e144020400001c032140440018070a2000030a822801a80121203a100b41001d80c07602c0c1e1194041440d941c03140e8178440204c3d4a80e00100310385544003030076510507842071600f1418605079903510f40d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 324679037 1250 324677787 324677789
    0xf02060c0313060b060d0b0112110f0c160b0d0f020c0a02040f060b070f1a0403021009020d0b0103030201021b0303161101150f1703030f01271a040b0607020901 70
    0x300424401601c2c10041e90742d01095070010300402058a034000800710101500181101900017801c4d40c04e0200f4100403401928a05020500e40d1810400c5641c421412604a000075071001e01c960316810704461041004030380502181c411041c0c2e1001c01c01e2861017030b554216105468548100901282c41c44003094402095034119804103e90260301440e0020700750540200500901c00200481000030b801261040c0c2486605140317040d5204045401c140c402c00c81e0040d0158200c07420380c2e64070f0300d55548907200a03440244280465207981d2190030001b0400d800440150b9070010307428a480d07944010088242958000079841c42ca444605105001d041400780c0b0184584009107035a6401700f904141c10100074400e0fa4000b9550b10030384000c803000c09202c1c40c40040d0254010800c00100442181d120304200e05031200c0c5a403038003403a00b8a0b401314001800100c410085c07002900780c4540500484026503030400c00c80034282e4010081201c3c03040440a00c1140200b21020041c0c0707d83c7c0c1218 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 324680287 1250 324679037 324679051
    0xd0b0609060a0f0b0a030605060702010f0507050312070507110301090201020c060d0b03060901021309290d02041401060e0102190311031b01021201050f0a0e1f0807060f02060c03 78
    0x103140d15407501140034040d05810071412081c002c007000c80c101c1014005095040850703a0f050045039515400d01c4614821490040d0001d03194014121074207006100606c1c90342d100d001103e01d41032201c50141c20540c02580d8003800104001030220912004009040c800b00040700200841801c80c2d0020350358000503904e8601032000810100c8190710554007180611801802350307050b40ca4031801842c005c0d403110340900300080b50380c0008542c071150343c4203802d0701501c02c3c0c60125006510444c2c0303100d082c1e00c607114680c5c00703002119074000503266400350183c400c441d90400c113032550401c0005001510111130450441d407160380c0c0006c500c28200040024207800d030801c43c240e0751101508a045100b80503210341010300d1407504d080f00020550051250041c000b81c51a00c1da40c8481c00c002d03410a030307911200e91201d800034041c481038000d5800706d6000710086001e9030f105001d469014000f003410398442036880e00841000c00044d81c0100c007840c0f00107210320140541d4500100c00901c2400003074214 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 324681537 1250 324680287 324680299
    0xc0f0301290105070c0b03180d0903020d0c03150506040e0f030d0b01140703020a0c0e060f12010b0d080408060105010302121501090306020c06180c010906050d18080c0c0d0b06 77
    0x9240e00c1e40580c007144c0c02c0c00c0d008007091306840c0d25404002460740c819103080202002c2e0104c1c001002c7c0d80461003c101d80c04598415003050702d19002c120411501c60010740d000501d9040000026102c80081541c1900d24103001c80d041c0740400070401160111000380d00150004000780510001c08000c40d0085207030648001010b40244004998030600000f8031511a140040c005045c9500090b1f46c9910311b00c5030b80304044413a201e05041d044c40d401980d0090f003100c0300c0c0015140510300445541c0c0040c20100c000030b811028400002c003444458541600c020710002000d1180c201c05110740b03809450203007810f601c1d128442c10182d00e01d00c4018841072032805d01201084507a031040440344005e40d0018802e640f41c02402402030380b01e90050300c034411103050b001d04034100044040390b07442068005071a6103100500d403901c1034031160f100c5030308070065542e1014113145020181400c51f0515025002c1aa1100317846484d951801041100135482058001a000001500c100a280c1d100c0c6080e180 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 324682787 1250 324681537 324681611
    0x50108090c09130c060e10032003011403010b040903080112030e060a0302030906060a260309060d0204030c271d0a03080601320703020f070303020c0f0301 68
    0x45038104003071011202e50280703404040c00210005810004120340c000c150021046669010079030b4a40110102250045103200c00003401c0b60207030740000940102d100304041266101c003103040da1a0b0090300b00003030300f00741c2c40c1c0a010242802d00c6038102202c0280d40400807440c0d10f480180c44000148101d201c042014055035041501c2100e05a42c0f81d100601400e4841d0980480500a50400c41b80003c0740e104000001d00076141c03035107101084401124480b040381d190031843c4580d03a544510180003034401040795050301d840303410080140b00020200183c0b01c1d07003140b80000c4240c046500c014030318203560880e403410701c403000121020791912902c00034404003100c0c2d1403405c60080c409510403602401445100741038201d401c0e0b42c440c0310b0036a200303d911888548440701c1d4009030018074810010006d01c801041c1181e40c000c3c003281c1d019004840b03460307990710a00307860680c25410072401038000b02ca0204031410316400382c0075400d0040b4002c1c008060044841403011040303408030349030f005480750 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 324684037 1250 324682787 324682801
    0x6050f030606071b090b090f06010c1e0519050106050109151b060207050c01030513030c060e0a08190834050405060c03031914041101030f0216030306051504050108 72
    0x204448008070b9124040800b00d07552805c00c8014840712000781c2c0204601030000e505124031055030340c416403058642d05514072a588902040d07090307680c03840440005070191580031540030000700350110b5080c3d01703d010b0138241d4504503007524001e074031142c1030006511060043c081041d003010700090080c03034036450f0386107010800180c1310754601d0080c1405200203465418854013082d41d0141c0d5a00f0b803400c0c403941d207034000300301c85a001c0100094002a081c4810302d0005040360042c6007502941800c42d075400219031202d150ba60301c03600c81c1d842e90380394490412100c140c11a0441785d00401c1e0894000c1a80ca03142d280394105aa41e40d203151111007065000c03c54980508141d034007a2001030892500c640d200480e150362a407017907400040548500300c1d401030702032143c0100c0e0340b0b542c1c0c44540030216444076568040040c070b544807024185902c4003d1210884c2451000d4542c800000c2c40d000c1d082122810007508440d00c13604514000d0141c05410b00340503040c0f204071400c455080ca0030303450070f41e2054 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 324685287 1250 324684037 324684053
    0x13020a050d0911030114011206021803010c0c174b0a14180907030e01020711011107140f0105043c030b15030f0d120606050f03060607 59
    0x4410400d40600c0d08030202e00b84021a0000305021906400810268581060300c00050409224015656003400388030380014030329401400003480c003629081408004c0900003400e49004840d01800190120f8110301440015110502c1030745208014a18100c4520304540e81d982841800c1801480601d620b4034200c2080032880e01601a0a0700101c1c000c84802260b10086e40705054000024401ca9202e07041340080c0d00440300401c1032500c101e00302010f6482400544800149210149640d44540c0007650f00c0030300061000603c101000a0206c1d407510025100c006551020400c0c1da00c000d03001c3c0101002c18a00600b0020100d61104c495043d450040b078035486243c114ac2c0c002e49090b01800b0301c100d03140d10b603001001e2200c0143e00e2140d007805070650400c643c0b0300c0060001c900b08804103045600240f40218a5840030342502c944481c2c1c100e12a182c204c20810401c001840d801c03100c006c9610611420003e010640740072490241080684042c031700015195900c01c01c2c2c00218001080300c42 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 324686537 1250 324685287 324685297
    0x30e0f030a0b180f0102090307030f0f08070c150f08150f0303040e0a0b150406030b0111190209070c020d02090a1409070302030d050c1f0b060d05060307050901030213020a05 76
    0x3000e80022071500350700040241883c0811060948114076070041100818020340d9002c0380e0107030060480c01e24540710140c1021240d0310035a40d00007600c00380320200da101401811082e000d01c180303441d02c52800503140000c041d49018102000100d004403440540c0c41406190401e000c010601c030405070940000f2128072900340e1055242c0300010700007900807124900c1c50301c038026000c402c00401d2018014841401e1008404100c0d81c44200f01c103008560180d804030482e043c0c117250468a0400a04c1c0091030002c103101c0c040540d88510b00031804600d40b500c9a00d5125400e4903000040302000d80c0407840350010448000d1142460710300050648031a503104805031540e4100c004180d041040c652520340310b0034007040c0d0090040001c40c1242c0740c02041220010003c42006002c1001000c1d0490011402d0000c0050a00e440b482d0114450381c5850190241203529000002c85003400c40401d4503103501980b182d8000da08220040000d60303190388401d1182c941c1c171100541c1e0750000001c215024450 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 324687787 1250 324686537 324686543
    0x12060d14030a0201060f1d010608190c17070908030d0f09020307152c04020a09080303092404050d110114010b04060807140a0c060207051002030f0a0504030e0f030a 72
    0x1c0030404010203a0305400a00c00c40394400c0703040e00c915488403d1500710b10100303040c0300308015504d0010030002d0300ca94811680b14010011241d1281d110940c40410b40307807550b0462002515007060403031000107050030b00350444980c2c02c12142d090728120b41170380c907805003848201e405036550010183e0340ca1550403404a01d0360040036244c56a07114400030b0341c00240070f00300d03400088184c2d001300400c4000c1d180846804020324254151101001d0802c406948500000020444076410000e203551040014500620710040a031107002c1542c0c0b807074002c9448043c410840030f401d250501001c42c40c0400c0d400c1c2258581c1c80c0c45a02c03000c000ca0745d980076150b4a8805054405100000100c44070060f011384151542603541007559108c05a0131a403840d13042c130f04030b20312100c04c00840b41040d0060850707505080c802c040150a2200e5900c034242400700d1254800780c110380000810010403011b02c0855404220709030b0401080c00c250310010040f52042e24828068080795140020700d0b5401c1110700302181d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 324689037 1250 324687787 324687793
    0x80706112805070e04020604030f020105190e1203070b010303030203041a0702060106080a020306090601050903120c060601110718050a021603030c020705040b0f09070504120c0f05010512060d14 85
    0x1501000030101452040810b07545030151403070100f0781407101d09142d030151360000d0415082c40c1c25a16800e04803000c500049050001c03c0116480701c500d425140c9a00d07480a840300f032101070b5a0018051f022100c4403140c1490780040109200182c5030500181c103494240c03070016101d654074034003056860400c00072242c1ca101200108110544e000901c64180c2d1001e64680d421504d805a01409a00080e10a103034814600c01c00070707646500c0340e4040c0801c52001412565000d08000f0551801c0c0d016804c440c41a0f0045020000c5558002403404100d80200c4002c00035586410000c1c1000d91001003a9601c4545403400302c0c1d420015a01900c0c44d80340144004100c3c105245000b9009040f078524120140c058484001014900761007480c000310343c00343c406c0e0030104808040000d00c2070028140024810280008100d07440b2080e10081068031171020b40522508040110100c00320580c0008d0403c43c04014001c0e5040f0780c0002c90360001d00585511071208a00d1400c10019048601507208601c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 324690287 1250 324689037 324689083
    0xe0109021e0c0303090d0e0d0b0402061605010e0f120a0e0f040c0512060406050303040905061903050708121c09020d1b0e06090618100e040c140a08070611 68
    0x803000314082c403a64001c40c1c3e0f040c101b1800580700c015401c4101940314500440310300108410610a0b984140700070320441c540260f4030304444007414600390079a5241c0d940c14484a820804104030526909000020301d004c925040200003584211140f840822502e0360640c0702ca900c40d0340e560a50303000000e2080c4044803446c400140a60048105029691000c80c00310b9110304240c86180c065480143c00b0790328107420403507a04003504014203429000f200050103820945a421103960265110b00003504107103140402140c81e2005011202c59009020042d480007007415241c0f01c0c4548546e4907000c5103068050001891410700408050300049041041424601120401105071000940c2c0030319980c80f44400d004c1140070807540070f908036050000c06007521803880308080d400740044c5801440951544d003a122006000d0340c1c11203006240b2241030151a5051041c07000000040d100f01074041d18180c6107030342e03d60591003601c0c107112441181d150300c80d40c00c1c0704d035880030340c08100302074441 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 324691537 1250 324690287 324690307
    0x203010303051c0c1b03050c030d020915091e011715010f08091002160c0b0306010f020d0206070809120c07090b090c071506031401050103020909070e0109021e 70
    0x194000082d0b81101c034043e450360043d40109201c0d0300c0c40741c001d03581e460b4480b00c0c1020000c0c0540e02d03556000e505100341880720b005880170810040c030780003812400141c0c6030410b2005216a1540c4808910250801440303080c00c1501c1c2d00c150000104d8030703405008c1d00ca490480058840c00c418044103e02c580d0039408010181360450141003030001c2c203a0f607400003c0100303841290b03159010f5030b40c904140c12450416080c854160080e1802d0039410415142120081d83d5060f0118415030069040700d03400720801c0021760300100c1d4200409200d0020b0b0420030341ea500300035280c1000034444801e01c504880884d400040800000100d410440030007580ca00c40110321990f01e40483c070030090954180700390b140c12070a20100c1ea83c00340c003060b444c5905094240e42ca14031480c1c00c000294400030303528580040803a1924101c003001d451404000900f5504500510414142c01010300203c0e5218100800c0141540c810b280d044070000d00c4016222202c0500808038441450b0750310154207030205240d9030f5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 324692787 1250 324691537 324691547
    0x1a162303070906020606011119030302090303030f040606140d06111b0303010e01090c1d240d0b0301020a0c0b0a0b0a0303050a0909230618010b1809040c05150702040203010303 77
    0x243d070141c2e0215079032a9030f404011503055500d580d1154198001c0341d03040c0c82064103001080702842c42420003505200034080828038680003103c0c03080c2d0a42c00e000a12061021600c03030308016104d544040040d40ca10b54000c40d4507910355820042213246d40c2d803800f0514020384800d55074100c001d40c1c0680f51151420740ba0f25601c4d002801500c4004242000000703804507180b01d9421802d102e42c843c100c401c0d6400c21560300a80c84804210b4100a02d06140041d480d886006030141810121049407140031044403001101ea11a642e64040c3c5e02c100000c0490942001c0c031550f1003a40a000302c661580c2301001c50000d48802d14003150007258552022081607040009000403082550b60b40c0e00b02c0d981c452070401031302c01c440d1010541020100c002034400c4035040390f49500101c00fa101d048000d2201a4032a00350009070b02a903141100801e2440d0003500030514074032011001c840111613400c145e102c5d444120400c1c4605481980d8008184203019480000e0ba82c9a5800400c00c546030740c4d4904001d04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 324694037 1250 324692787 324692789
    0xf130f030807020d0c24110303060a05060a090b0a0f030f1a120f1c02150103211b140c09190b0d05030d060306050618010e0c0403020402070f1a1623030709 68
    0x404156060f0003c10100347c004156882424010101d008084c85c00d01882000d5011031009030400c04d19400c080b44500801d801440d502109a03a080c0c403030f0448000050846040da600f03c0303680d50801540c104843c403200204410890212203680389140c1c1c04107500c2c070b00340100c0f00300309142c05154012a0984403030400b08401c44026001c2d196084034070039114503031034001d00004040d1088507040820340c5015a03110a025806407c0c905041800141522605000b10004455100301c9001c240c0e0714100c2800509082e0205440002580c02c0c0600b20703074020000c4600002805a5800003401c0300c0d0f480c0640d034034250740c0200650f0303075514101d1a0440908603600040d1461420200401d08030b00341404110f802d0301a40810710002d03402c5c00d002031103100018058584486081c440480960b903648020040140b040700e440c3c3d62400e191601588075100300c4030b107903c1070f0300240812442001c0c00301c40000080c21481c107602d44410441201c0d155900086040d42c03000404400c000c3c1c0281c000880c04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 324695287 1250 324694037 324694109
    0x11a07050f010c0e031203040807290610090e040f0503090a0e060918030909071806021609230601050d180213021306031109060f130f030807020d0c 65
    0x313180704140030034199100d500004210070140100000741c0410b05040140110b03500c9103640c800300d0084031840705481c0032112082d400c01502002484aa882d04c488101c0c071070105808c1c008941ca10304413956001e110b00070030103003420700384160100c1005014030407205801d030000d220000e21900c2e40c3c40914004003c8034a14040d1b6803220109013644080174a898000d05203d00643c03030000c0b290240088071401500440a105404a1244118074400c0080d405805258000c0500c8641c10b0984800038a4a5100d08141c07843c048500010b4500c0c666001440c0e0401c01d4044966111040102d98500c07860a02590140c0b07410f6038403606c48000b0307510b14175890085411144914030a4015004c0344100c041c80c10f611a2034a904014580c020381041d0240a042c0111a04000e60380c000304943d40d219151448210740300103455405c0d491141810400f600200302c50b803124030304684e070300f61043c41600c0c4041c0c49804440301c01c00c108011a4411000ba15601c43c8004603801c00d1040000d000180c8840c0c1c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 324696537 1250 324695287 324695297
    0x3060c0c05010c02211b07080313050a05010207050d050c0301090f05010b09190c1b2a0b2a010c0906030b0904050303070809030f0301081506040c08011a07050f010c 72
    0x14003d03188000b400502040034086141c40528001d5051141607124040c0c41c40680140306480401c42d400744813800c010540c0c0c90203580c1d90320412003801800721113900310342c1c803442c1814800e100c513980c0015120155031095030304520060150800c0ca2512000d41042e542c1903003040f007030004021416200e2014548101300070b0083e07503600c400300041c040c400c0702c24072004980030703c0040c02e502c0d0580082800751840d04018100c0c4210081c0c0000586070f1381030681d95591000c109004a1607240e5982c4508030903d03280c01c00c1581000c44010301c074820a55031300c843d1000107810281c032103003500c2401c03031088190b40204001d1030008006007100b50f50381326200200345403095610242c1040d0305441c0c46603034401c0c041d61641d56000703010341d40d010000d0001e000c0707840103000c5000070a0740140294080d21600c401003050024900e0f02e12381d040d4008000354002c5003018215030102d600309803858155520501500341c0b0b41c1c0582c07440b20302801903078005003141c0720704c0e4403502c1000419846004105000c1d954 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 324697787 1250 324696537 324696551
    0x1303050105250e100e180f151503040602090a0b190201150501020c0d03020312040b011802120a091b0b090307050a0e04080a0e0a0303030e010c0f0e0105030a020403060c0c0501 77
    0x1c10b40d95064072500b51904000a600d005101c94482c06850801d10701c01000d0303508040e140d44075030040c00c00480d003507101c01f113251081c004c80c404d19140101a090b0100d4107074413811840302c8504a280006040109020b4011900a400b603450143ca000680035007a081a190b2081c920b1030380c8003500350b443d00c1015510300b81c0c0d10204082c0640c03521003034401c180c00905907021003900313209881c0c2108006404500050040314410040c006845000e035000e03403411030155050403170b044009490140728090b40c501c10081d00c1e151450017a141984035440c1a40041d400c0d0b4507040c00130400c0c1880c614030701e0500200101007400c8050304c014000c3c041013601100c0d42d06403a03d040c0f2000440794080c84451107030b0800082c00150030040100070801c1c1d0340c500300211071102c10100d10f0100e5550821000b29442e0215214425801d11a08180d0791281c0703002e131124440c100001d0400300c12485d006041140001c002921034080d601141c00030740e4001404c0205034403204005045403040401106c03c0c0d400c082d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 324699037 1250 324697787 324697861
    0x307021e0d0f23030403090e01050409030e061308030a270503150a0204050301020711010201050a060506090f01140c0d090605030108030301051c060c050417030f030c1303050105 78
    0xa80c01e00c01007400e4a50503480d107507141040d0768103031030562646451125400071011018001c8083d42c010382c829180eaa002c1030605d40d00310501081600003a00840c9025203e00129078004000c881c0d4031402c1d90141e60b20f450900d120010402c150300309a5182c0310000d03074001e000b07510021030a55104070071003c203032105122107810628186845000d0303140d400f00c109010031919100496812035840d00c40145019943c1010034203981200000740d80410100c0d500040550b028001c1c40da10020342003040140a0410000032880e01034841268011810781001035856405242500d10090b403455010307480f00000c0d9840c903698035909240000140c040304001901c01c0c010300689040c1c440c00c002070340c2503038240b1051040d0480f440c1d26410440d071a1461b02c41c04076240b442910011551035070f40f6a07482e420041c2c1b01950301c1504803001040d43c07080051083c800b0050341030726004a00314401d40e650340c1044801607030346c40180d0006003ca500c0c0c00180a900018001c02c0314030340f10304840404019000e60 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 324700287 1250 324699037 324699043
    0xb06040b03030c12090a0305060415060603021e130905090d0f020f060a0515120106051504030c0e0408070c06050a08060909060f0c1b0325050307081e0307021e 70
    0x300f20380d40c0990000006210740c0c002d0101919580c44d02500400d10180e89403141441c045054406a95031760165040006545103070041c800544100e00b001d6240c040c50750100c00c4c09440081c4141041d18010071449441d01ea03450303204000f0100d89800740024280000c030b0039114400c0c000d2441c081000c0048034202c10340007050075015500c04401034061580d8076030540c405407000404803404c0c0d8010b44442029a41c400419140045d50a0000104241803909102407003402d120542d034100c005010400001e440030b016001501c8508001e4040e54449140650340d038090108000c0041c100010b010540551000141040b40034550320020540c803400b06102880301c00340c61440480c0c1205000482a80941c440c094200792101049840d01c4c1e084003040c4115103000c401141c180d000022403582c03081d00b92801045a07a03241c01200c1c000119666100d80d64442c00e00e0042c2081004698080d4101c0c0001c01000004072002c10140d4901c1c002d04000c0d125600f000302601d80d006000910708030442c0c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 324701537 1250 324700287 324700297
    0x70e010609090c050702040c0f090e13060f020708040e041209030818010c02120106031703091c090806040f0303050a1a01050906040521060702120304080919030b06040b0303 76
    0x5500c540281c60308041141c40544402d05120007889020410b410058407039100f80d6221102c103035105190740c641c00000420030340c0c5641c40380c02c1f0603042800784401d03441792010444c540c0c1d40c06080064112801c0420102034050702001074240d100203d00000c202e88140700052045d80718214030302e407118848406941110550102500c002d0040c04159419001745c180e000030090141802c2041021507030004920f03049800030714401da51a184101308012901a000401042d00040f0758110303d1f00620403607031040322a40c4120000058200c40c003c1d24050304076079001c0c0214106403002d502d8a42400400d0030710700034003140041d141400003800d41d0501e11070201b4548a071451988518103400044034540c00181c3d803664071400410002803d43c1e602c0400606225030040c85210841c204040f25040000c01401030055402403401980c209482e441161707032040e4800002c40e01c4141800120b1031000d084100308103503201e03920000c0300b440019103000d440740310100d41c1405649200c070141a160b006d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 324702787 1250 324701537 324701549
    0x3050d0206070e011d0909011505040e0a29160e0f010c03030c0e0d0c0e060915010c081218010f0b06040e18060c07110904020102060f0403030e01060303050903070e01 73
    0x2d401c500f02c0d2a40c440e214500d452624a554011160310003000145562000d42c1d05001c00d80d5136a0809441c10320302c4c141c420042c91304440070021218219410380d15458126030003800005070082c600756604240c0c800701500005a0030711146441c1c26220143c0481e0690704040200c0d108480c0b0900c40e1800b040215080401039544403d801115078054024115030084081480038200e0803003207c0e1034000e04641018000c0c4c1c00308030640d14041da80c5108080140550703009210351020820002c00c00c5c2024000d5100a2904030030790111030603d030a207802558084c140002690080c081c40002d82d45034000c84580c1d520082140c5244001b0080c201c558071880300e0340006090100304000c401025800b540f001d0030074440c2c1074088850b14240d06101088031941d034890303800b00c1d540080c4800000144100c44096460100ca41455000030b5039803940140506090503039400000d003050301c2500309001982c030100083c4801a101d01c0c000d00707550060084a8000d100d0040c0010700000d4a41126048443c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 324704037 1250 324702787 324702797
    0xd0e060313060e07150221090a0e1e0103060e060c132c010f0603050c070b04020907030b21010e0312010b0c0a02030709050103050f01090803071d1903050d020607 71
    0x81581c2e4410250201080b2640c65001d5500009556000001d1150794421603070f01628120024400344c0009400b548800d41114006004400c20b6441d00403600080d140820088800750341c1e040c0c400c0702e58513010045c030400b10801000000c100000c40e000240c0345007000c0155025030390313103034a00c42c0c0394061900340ac0200d981780c0b4800c004240040107031425850521030f041d2005035224240c000e48550aa121680010807450100b03c401c0d0303d88100b50f00801c41c1820345107019625160031440e0400a00003074807a155040200d07122a01980c0800001000500fa0300b0045010941d04103154032550100120342d424081c0c2c42041d40303008800c980103c1e05484070008140d013003c00222264020407445000c030320442c5040d03405640c0404c1100c00401d400400448c956045117462810b00003c1206280709a052201d03400c0054041030690703074001f01520b001080400410044140c031543d20280540003a00c400030089025180c00030303041076078012400c031030b1084440c1004a070748030790458080300010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 324705287 1250 324704037 324704071
    0x6180b0a1b09120c030605010e01060908030a050a030513120e040e010b03121c1404021c0c180605060f1908070203040e0406060b1317030711040c02010204080607020d0e0603 76
    0x420910085526004d000b5201400307440740c2d42c130000c40c0d00a8011141080070702004000ba580d200403042c01510100d4099030905910100280290103100b80e0365040c161030780b000030f01004d0941100195140c2000c2d42c02800720940301c010b8182031401c1d06c0c0340c0c010350034142d508007808814000c000c00c01d40060000e109024241e484820f442d049019903880b0310500700303001c600088140c060850f002c80454085010b0781014810407000c000382c11440c2500c4003114050402140300480010704882401a00440203242c050704000100704c0c40d00040d90080c0d0103d03803504540706200142507902d00e95411035685001d5858240c1c0c07814812191200164810070080c0080035840220b11b2304503110f480c0c081500b5841c0c2c820341e9800d0b000181403400141c225001046201c00c02054a01c4103d0458051890025107850703880c034008000c4100340c000d130b445808000b0810310035070454008280e0401660180d0900103002501d9200420031a8001201e01c4101130b00c61804030216405106030403070b20881d03e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 324706537 1250 324705287 324705299
    0xb030c010309111509030a03020106060e0108010e07031e09060f0b060f1801020109060501120218070906050702030703020607030c050c01050f0a031d030301170105010905090a020d06180b0a1b09 85
    0x203580c1d0800da0f044e00500a029040c45030710204030801c80244660000310b011400c0c0300d4010101864618214100561400100071841400d0515900720401c0d24011a546074181401c0c41e0060444040080180c41e001850051000660208186e03860000d018040c1000344000c00c007160007100c0d9010802401005865616420100c20300c11402d81130002143c251007948900c0111502640104800c41824010074114507041c100d1000d044043c04003601e550401460090000e000390146005000c0c0000b150410f44d038042080c4c1e0000c550003800555106003601c1c004040b208400004c0351180f05100300007070298091800e44003400a01045075081c80b014040440c05000c40d0258156081d011149090f803081d810320096002e44168000998501d84c28100c40c1d08503071050703019240c507d10b001d0074440111008901003064680481c0e0101442055041000003414400c6411464040d4400060108005003548a01c5070700f24110800c00e800081640c400f250031580305140c00607030040c606002c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 324707787 1250 324706537 324706549
    0xf151201080a1212060f091e05091b0102010e0d0f0f030b0f01030911090708150a030c0501230301090902010806010e0918150f01090608030703050414010e10030b030c01030911 77
    0x1185604c61002c2050b543d1072101e060301a40356000440307003d44514200003000e00c902c1c00d800142450b10300c100801d00d02003030101d0b01c45070922030103141c00c1c0744003c482c0016031003500500b059200503025142d000a540c00c018240440c50443d00e40441c000c810210400c80c00b070f10500100b8030f006007114500f0350410740110000c02c441602203c4001555a2040040d12580040d0b4494005910307800090704101307141000d6901c0d040c041c0361103046403890900010320000b503104102c40c000e083c000340358220030540c8a000e40b0151190850a003000c400007a88205a4104684280c001c3e00c9181c01612a10011900115402c1c0c10300d8005c001840410309107104010b4012013918110191200b501d540131200c3c8540b0402d0300c6c0298021400001441a003200d80308610080080c03800941c906001658040c2590003584512100b5850588001d111640243c02050300d80b000105039000c0a128144082d0042a1401105000e032003490b01d404060350181c42201107841c0c020000c080364019040c00c05c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 324709037 1250 324707787 324707807
    0x906071a011e0b030f1b070b06090c070c050402090105091002070f0e0c03060d0305300c0702010c060504050c0919050a27020303130b071505040807020405060f151201080a12 76
    0x114846030140500c1000101e0002e84500c7d8400c80d145243e50910070100b05081e000502031801c40300c0704004140c005004852101c00f1503000f59405a2140e0001e0b0060340c50b40078180d40c0a07000f0006071007111405a011031000144c4450983e0121080c3e01e411500c190f604088458082002c2b08001081061030280b05218400c0d2003464010316000036604070380030581181031480034904554041c0e50420004180a42c0c0c80710b00c142000d400c000403078000030402003850201800c955510404074040c0007040c0581d0080303050240041036141481c0c08060880704080052440c1c0714900000f086030704803e4018610b0139000d00d000d4030000301c5002481c120320380184034100c0e81844100000340d0b0b844120038030b46000b0001264480d440320440d040ca0340b103500f0340c558041c0500785080200000548684181c540f0507805640000d080d658007000f00700e80410b10032100c0d034804a0140194054504d0340b0003841703c0b4004000b4504107998440b9002e0741e49002002c02808410a480302c52486071117254640 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 324710287 1250 324709037 324709051
    0xf0b030907031401061703070b22050a1217070801090f061a0a120612060f020c0a0c06021b0607140717070911090f04020906071a011e0b030f 62
    0x70102642d9903203200f11a0040004128941d44424007000164841210440040c0900d00554035005107035440600b94480101140703040040002c03542d80c4069070740032076031000c0c0d0301604680c015502414860b85507114141c29100090b10a12a0030404240404080c040c3d12162990b002c0f40e424454480003070201095004101651a800019980c21205000d02008800318000c0d075600c60480d0700606001440594103181030414100f044041180b0b83c03a4a6000d410000025803c40c0b8150340502a01c070f14a018191032058052400a0010140300b0f48120740040d02242c400701700110b40e4040d100c04841c1d41c245c0c007100c14003003640410a02403890340c018030103805640445031144803c0c6c5c030840c04520b42100d40e500c0035a00b070000c1d081d0361298140c08540281d007641056002c00c00501410780743c1044030301a503008100c00c140b40e1140000c0c0c810040d07100c9080079605866150b40240341c8405d01c10b81c240918810503203000d089240f0704400940d41801001c0349507940740d0a6110b00300101070701381 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 324711537 1250 324710287 324710293
    0x5010305090c0306040b040b07090f030f0f050d11070504060503120c070e0910051503252115020c0a110102120315190609050f130213030611040f0b0309 67
    0x740300b00c0da4052107102e100328414a0a10194189820a032958500041c07030101401f83c004414010320018800450440742e002e0300000c0e501c1074a107018181c04003013810041030313172007003003c064501c0f50001180c50781d17400d58400b140c504507030303e0080100384e8407680714664064019540c1c14038241e0025005203440506c56046803015583c507200d0315000754007102c103510180c2140e29248002c1946005890300040012560031100c1417400c0020b441d0390402000254880d0442181003c030b82c5418289001410000c0b01d80c0c4140d1155040110100805a8110f0b1030550501086e46440c999100b80c40181000e100140040c16545d0b42e8410400e13072582000b070561141e006158460301090004522825400c0100402d40c07030700342c041c4400802801100b0410440c810028026594043d03080e404558007107501c035030350000c80d02c0070030198894040a119414000509140c40038a81000307181203e02c5283c040050120200d100b502c1401180588010300014400030051600484043d5811403111015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 324712787 1250 324711537 324711553
    0xd0f02040f03080a0201060915050105130b1b0105010b16021c0f0809030d11280f030e030d17040303020306041d011a1504060507080403050d020318190501030509 71
    0x180c15581c0045500480c0d00c40c500141114082e0750a000c1e81004015031403041c4070444145008030780c05a03203405400e04001c00440c0004c0301088008000c0c005000300b8519558032100d90041011108569500d002250309210001071605010710031218012940700c03214120b030516500b041210300c41d0307810f01c1070706044104028021501030008100d190f0720500b001940c80300480185810016650200414014443d178080d540e4034000c607810400b0203609849c0100c0305070804001c5507002007188041d0400170802014010903401440c069040441201110340710200301c1070442c0e9803400c103070100c000800003001180001e0b020303802031500080020404550016480c41c0c580154404410302d4403035071b4444002032040d44207160107480a040c1aa4110101000c000070340405115a00c503103410400001840d1050000d0101560f010b10340c800d0507101e01b50380e144002982e81d00495512080984015401000c620b8054410008016600659048580b5100054000f000014803035207060140c924 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 324714037 1250 324712787 324712799
    0x60a0902060f0a2003160318081005070912030207090203060d1e02010e030c09010302090411120d080604090b072a061a0405040f0b101a1c020f0d0f0204 67
    0x2000d80202e40d03c079500c00d00c0c1648203040003120010b4031814880140c02c104003450125800032031007103025801d400c1403500300307009088006d004101c60b4031202c0c5500841100411032552900200e002d8050f9644100c40240c5403000340d0f403400564200100940e03c040c0c000c100380090f9401555104030b0040041a9102c81519005040c01085407107081088180c4103440440d070f0800c8010b1401c81081d801009111580c02c00718010140601001c1d100350f16000000b02001001080701811460223409564400c1800310141d40d1010200c441c0b0f404180341c03000041143c102881110b035016005034000d40d4035121f000301520b446d007140c1407081c2d02950594200715260035070502c901e4580d100d0080001c0d1044210091000c5c10032020240344190708107030030b00011500400780c0c0a55140c01040303100040c2c5885803140505c001b05d6000742004400e4403040c154070030607030002d0004a00031000701c064141034950800101d20480100c2c2e034641320107204618014686074003420f5001017001c401071800e51980307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 324715287 1250 324714037 324714067
    0x209120c090123130c0210020f160507030206190e03060f04030806032d0606090c03012102030601230904030f0e130609290d030509010302090d05070f0b0408060a090206 74
    0x7004119641c0c881c6208404164100000c41000e031421b4001c60614012994103c2c680c4181962b5921052070080d91502348001880124002c41c0c1c02424140d8410002e00301400c030b50410852100401d041644074903c0341000f08119201701c01003510150203a58569050742c4440d000303010580c04d03102c1d4501a00401486200010b5aa11405036040c542c001d01c0c0102e034a0010004c110318054144081844010180c070401d1720b064034002140c0000388007030011441d0340007004040280d4148541800050b5000c0d2200f41c440003000e102c2102008000410706000c03c2610554008000650985000c1c18583c420b65482e1407401006101800341c2e842c08407070105541c855004030108650b24021031440ca0f80d0545112040100000e4030707607130300c48034400240b0710424408002e0140400000c0805050b03121350f04407502074400034800550440c041c2805603691810380600b02c0c0301e04004e1004118228414191011102c1c00c000422445c1e5448980501a05440070100d07000078041c0f110501c000750349 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 324716537 1250 324715287 324715309
    0x40915081011313206070206030601020a08040315051302102f0606040c020d05030f04030903050307111c0209011e03140d0909110912100f0209120c090123 68
    0x4018441c2400e10310215022100da03404049184d2405100d2500d90f1281000ea90082e5012911180c84c1c1e070740d140c0140e082501c0c4076401400008001804010441000508030840c0c0d04400704114990340c585480200180c0004085c1d0701420400c00c00c600b071031140c80e22030141e40c1d0148990302c0a81040d60394441c2d0076035140c2e6010003504000c1c2000894107013807042c09440002440106400f9071030210240141c0300140a43e00000a600006000c1c903010b4140301c002954403004403941d44286040c52540c4001c0c2400c0e0601c6030522000c145000c5181e070314078603400ea030000c02042003a4a0041d080550321110154003510075040e82000000c280000818400d10020034081d00b0080d1814400921649080d080804500c0c68031440c000c0708070000c0180c5442c2c1038240c83c500d1741c5080701c0b002103140460f80c0f03641c00e0380c10b410032143c480141c2c00d54002d0080071406a44145000140b03c42654580f40f94040b4070350032180580041002800b6400003560104100710104100f40d82800440c1c54140c0d2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 324717787 1250 324716537 324716549
    0x50402040f2a0f0c080a020109080403050c090a0203010b090405090f010c0f0906090f05010804050f0610140d0f0f15090b0405100b130b0604091508101131 68
    0x2294000b07200203003408520a04040c0a1030014032041c000e40b0040c0554203885006130422501083da08a05130003540080543ea4100f0359041d00c071552842d01c60350703034518092824000c1400002141600202d03000740c0b41a00c41d0118054105207000381400010440205440340342c0c4281041c80d8444102845544966040c41c3c0d81c02c0d1040403070305c00140520f074080d0b1159041210044040003d2402031100c081036078824a0110090344550810910b00603400120311094000e0106214103400300e10155000c40b18404c12004a50b400d001c20004120324190780600001c003440e1100b8001480050028040e03841410000321130840308024000f1101c5000c02161030a85903414803048c40381c00c0040d240000d000b03880a00907990b07084081b89441e0815550bc00d00c50f80c480c0000e03441561520281d401401d115902042100c10301e02e0200403414071803041e066107028038030a54000c0a142c0c02490041072090300ea491800344042e103410030303150700010400646410519202c60600c0c07544884001852 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 324719037 1250 324717787 324717821
    0xc0909060105011e020a1e230c040905031210080d170603030c0a0308060109031b150207061b060608150405070815040605090f0601091a04050c0d050402040f 69
    0xb040500150515420807010000006610f038a10b000075800a0030310781d40399000c20076040c80891104002e07000200c042000300a40301102a8407002021603401c400710408000032031708007801c20414002194140e00700070b040c580003084504980301041052540080300c2186480009035075400d0203052890120461001038030400e9220b40c24071039a030590760044001c40c043d44c81d10240140700c0c0e56607500039100909221148001074100c3e03001c2e040503001160005801c02040941c1c185403901d02030180140399503000d42c0031084092510000303000d4162169912240030034448900245190800410100c0d041520b54401140f080700a01c51456118513541d41034103a4105494100c0c10502503400445c8150b101090340b0151036082a080d6030000d401c0030000031140c449407044e03400c0050806104105200703400000511124660058071182110920794190b00015420402610810307921040820300c10700040c041256158443e6030458401080010361000c084005810f45000d8024004411 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 324720287 1250 324719037 324719039
    0x14030408150103020a050a08060703050408190305040203120307050d0f09020d11011202090609010507051504030203190905010801150e030610180c051c2315040501030210050a020c09090601 83
    0x108040c0c4401700500781c110b0f58211420300b030031030455460000a00d12010161203001003418040500102e846000f0204200c0c1c1d40884900b034007034003504040d41c04a01038421030003000d42e503001c01800d480c040d4880b6940d140ca010f01025a4202900f80015042c8126940d0030683c00140c0d50102c000d80d915100e0100550794401c4030340094106425288203010fa10300401c0102c110f03984000c00c5841c4420242400351b25040c0394145030340382040c0c50444000c10f240d900c09001c1450b8000010300480f8995164002da07800181c03904071401a81840740b18085140c88005104504000081c01c0c00e0315a58502101d903a201c0a001a00c0c083c426201034000c04100e503424840d03110400304000c008158440103000c49164500c0052440c4100460442e14995203a83c040c3e0b4003065070842010000e004d0611242c0c5c5807444403126008800f669189010315103142040c8945c00c00380550b9048a0300148408205000c21605071840d9221000c400308601600b1080d920964070610030900504401d4001c16042d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 324721537 1250 324720287 324720289
    0x20d0c1b0608220309050411040503010c080105030d020304080703030c02180a0203060312030606040b0f0c010212270a0210120e030a020d080c07020402070222090c061106041403040815010302 84
    0x501c0f030031030560b032402e41051941c40429040305103102110000d0720001562200316504424500841c0c015540c19420601c8840c11564844036081c142e500441c00d03941c0b450b10480050b03030f60f031107588159842c9402c02c60003000401d009281d40103141b40090701180b6040380701d9041220329a811610b02140d10783c08002e1104900301008190301c0c0900c4902682c2c82c4d4203108000414a0040340f28000d0030920004081040540002c2030b20050000840259260850200605207840e8100d408607218014a0107942401d0100c4460303640c80790006014000d94000d903024003000d2a070101c10402840020381c4030407418541f61080084c1004008043d5850b040b943c40001c0c1000b1449000d4010000400c06004491000d207044880c403aa0481f00181d0307031400c40c40821b403035002c440d20381103050a0389103041d038101d22107800c40c0d28010f00c00c0b0710290760592101400d45a00b01001c0340031406074080f100060006010941c44110500c5400072241815a10381402c0c0c0b800070807507442c0c103420000d42c00400071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 324722787 1250 324721537 324721561
    0x1915140f0a021b0a1406180a08010504210509120c030d020f010e070b0a0e040b09071701080303091504021f0c0c1a0a0302160209100e0a0c020d0c1b0608 67
    0x1110f601115022130b403c1c5003000d014072084c1c202d038030144103200c0040c0d0383c0f104025030310b80240c41c0000540303010751643d42d6080080c0240340481d0207641041200c10815000346031480d6440c51082e03a503c9041c20600501c0900104a01d105c0303040c23201d0721034012840c805039000c02c0740990420044d4010417114122022190030355860750401015684035003002c1c84122211416942086004c0c580341c454100c02900080c00b41040c4c0004c581c104144609000d2880c0c0e003c0410f105181e22100400710507680c4240c000d5407440215032906058201d444243c2c805a00014003541107400107004003201d502060b1404c034251441c00302900410230044800c81004090446036008101140981024101600e0442c001d84282d500d4401050fa0004004c403101605209000710302d07401500c2c909142c50000074088880c1003070b01555249408460015044000c0e9006559050702c00d81d01914441d528120250381b9507002c4601103541c1c4090301901100248800007500080c15155140340040c2480d213035140d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 324724037 1250 324722787 324722833
    0xa1d3114070303320414010e0102060906060103150b03090a0b0106080c070230010c03151a0313080c0d1d03061f0305100204051915140f0a02 62
    0x6030365004403104201080d00060901843ca0081840d0402c000c8440300105040200710100741c8074200226001c142e480e5040c140185131242a240c001c90380c11010016680c0e2081102c48000c0b41c8d00c02d01c00070380e488d4800c1d00210481c100388200440700d2912030b40d42c04190b0b0002c03101c0040c0c5030f100000c69006e0000c44032040340101554108192941040c0c440d111082c07042c40390280c019031140d2020480d9504080c0103c50301c0c084001c8411180d40300c00300c51406000c800140400090034002c68201c0000f03159040b00c1290341d2103000c1c2003013101d000c1c50780c1241d0300020204c1d080c00c80903819610109501340d004101d003845481c060300c0e581040b841d014010420030f0f106003601000c2110250a2a01c0c001041504140c605001032941142080120075026590708010254010018219825840354014001303171042140c800c001d502c007289036440e90035001d203c1c0715142a0204404c600840c01200c908140e40a141c407000d14000510003041c0c3e203580015200b000503800307400500349080d01914844 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 324725287 1250 324724037 324724073
    0xb0f0403152003090c0d0804031a010e010b04120f050f030715050c040303120923031e0310090b06070602040e07021509030d05060d050a080c010b0a1d31 67
    0x2c0e0560900d00000c543d210034500750303e40603000102d500001d0190140a0320015980011041204182d1946080c4940c02c00e22541d410051041c001007201d00c00c60040e54180c4444001251035a60981c803080d00440c06500d050320365008074025403000200610040945600400d00d5007008400c161010701203e10003080300c03401401c14441030000a911204010140c114081c02203a21000c500b0205100b1034080c2108841c04e10035410000030030f07408400703003000031004010212010206048880588800c0782c0d8103140c03998030790701403100c00c401768084142000081c2440c0e04000081d41e9140807640325070040038206050340100702100f50304000d0184c80201c200d02000c82c034201208615564010000c3d000300c0551a000000c0d8551503000780705c0f1855030440111100c210803410060180c0d032125140f40001d5003040700000131414801151411200c3c07a00b805003186104074052120341801034400c0311003103204211400702c11000b00039003000ea80c007966000d030003030700034648128006001e0f0511 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 324726537 1250 324725287 324725351
    0x60e16090605130e1c110f0d0203070f170f0d0b1915020f150106090602030406050301181b05030a0605010305060d0201110f01050412090611070b0f040315 68
    0x24400b54560210b52485001060000719107810300c10704190400d10300d040c1c0390000c0c14100b00c0101182d5030282000f0160550103056900c8a2003803204941c50780c80071141c1b40b001d0f034010000e00380015040e400c9800ca240c001e800e11118119140f800b40f10701d0307000e4109514448404500f582c1102e0703e41c4a00c032341120003150205a100da4489172410f036036855200b180055034680b884152554024069a2030212404003030302c1080765600010710124a080c0269030000f103150714003043c01800002107a094901c280c44071411a0f180c10400004100100c080c0c52496403075000201068040c005607041d091815182e040e200c1c41d00038055011100d030355014904150610301401084c1d2554441c8058040d020b00e4240300c06519054542c0c43d00340b520003144225860a0104003d002c440d0010f142c108080c0d80d0b481c100320ba80c03060f00b122009001845812070b60000c050030007041c0c90bc0e2000381244820070440c1824a5583e880b601c1f41d40340c0d0310003141609504d440e0202c94002850811a00c120a506c40c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 324727787 1250 324726537 324726539
    0xb040303120e060411040609060f0801050106090e0402090621060f13021305070c2a0611032205060d020d0606030c140a03060f061d09092107060e160906 67
    0x940d0f550701000703040a003802c15030750301d8004292916000720014040307200302840001c0e5264074403a0720744628440c0020551a1500219086114000d07030002c640d00c0f4401a0038940791502048081c640141c880c1d50720403208096244034081e2000200c0d200702e0024050038051801096120007000c0003480603002c16504011940140e688030324070948030300440800a1166244c80e000d80b44a01d041c203010349040510340300710029000d212091075039803604043c8001c80b50354516042d02c0301c001040810001f0740062080010044000032031032808141400c0350074203640d54201052455010074103c02c1d0542c0c001030040700506280c0102c5004002e9840c0c200b064064051340101407140841d044880e091000843e4400940300b40c000c074019040e15405d02c1049640c5120183c000e003001c0011008040444501c1c440e0381c81c08003545489040c04030007030301582010007429010b40b0f140f1401041503030010701504022500a209444070050b0740b60041c4044102c0c01c400300d03203041c0300e64026a0400d0520348 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 324729037 1250 324727787 324727811
    0x20111070f061d033003190b031c030213051926070e07032a0f0201020d1802030f070605190509130b0117011a13080105010b04030312 59
    0x260049820614143e18080b807054058100c100f4038202041e030501c15540040c4c0400d1803180c40741945480b000f40035584034030840302142a4001260809048001a00d2112014080780c10100c400740008043c0c07000007000203c4082040e00c003114103000a680400c0014600d00f0480604024150480e180c01244c00009030319540710585010b400400740042e9050a00317100ca200c0b0a500300103001c1c040d1380301591144800c8865060031210b010000b410030b000440040302e40201d903008001009011600d0b4500b5240545100c0c4d11a8000070441d07508100d034580040071131007211030400700082c11007800c452500400d0710745000410040019081110208a02600001203500050300044980102001a4020340f014020065603640000c403010440c444050039a019072500d0000340c0754400402c0c8100e08100d007502e403d0080703500c00010440242a0800060054120b401c02d10204152260310342c0c12090a4070030a0344064241c1b580450b06004142e084582c00c00e404004200400c66605240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 324730287 1250 324729037 324729059
    0x3061b020c06070f020d050703050a030e09040c050913021206040203010b15070b070c050307150606090303020303010315062403050c0702011d060c030a050c0111340605010b0702011107 81
    0x80c1000305481505113626045490341101c8000c62900041500c400359502c1c00c1c56500c41d0302d2124203c00240c210541d80c13000d07140c001c400c140280e807c07585240d40d60341080c00b0301051000c00fa2500c1021495030180300c0040e0380d80c00103030b00800c8022010b400c0c181001d10600d829905290f4606106405281d94034080c003035075030b040d175030025002170039001c0039166502c003529024511807021b4200c1c0000a07413502400081c25010449000e80b100402c1520340d83c3d034003243c1000142c08000c005810410040003c56040020580801034074600011503d41d69440140444a0b0b001141403442d15a6400c01c030681d00743c841c091340213144046852030034045a0008000301041d015850151401c00740100441c3c603041c0642d03100c5c42c3c40b041240d070b886844010180c044c0e000029460110340c00c000c030344c00700a59402c0c180c40e1018020b55403482c0101c40e01400d901e050b44c25010084d180b80048c6240000700b180c03809501e000b88550718803c1c3c3e80d2003440c00018019000d82031a2001a8400f40c802c000a04401e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 324731537 1250 324730287 324730297
    0x301050f22060c050304121e182111060f09011b0b182a092a03060910030302031801050910050405030d0e0607110111010603061b020c06 60
    0x7410548440408030409500041d0301010003501c603500d400944000c1c00d41000c02140614001c0e112220300074903010382190803401111940e014040da4490840b0014085c01d800b030000c00b2440d00300780e0001d0321011104802c0c01201c801042800520700d0b941c09105005194480d1603100b912518508030110b90203822a101c4c10100e80d0400c4248090300808401a503403041c05564403003c0a10306007800303180b651307580c4c1d03c025543c2310501a8400c811117035100d030036110b20341515290310b42559080d60410031410900040060344640216510b02031021207400038080c100704841d80c5a902d906050081c8441814010728040708450040011701c08260004260303282101c90414580d010076501c00101c80c00e00481410581102808030005030807508000540142c0b1000e40880d49024800030301140c491528502d515000042000720170040344034500c3c43c1084007010304010581c161840c030840e00b1208241e00589055546007000d42c00104a80002414100140f00400d032424118000400381d20070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 324732787 1250 324731537 324731551
    0xf0a0513030f030f050405010b030705040b090f06011e0306061412011a090a0312081614091f1d0a05090a0f09080f0703021915091b030c090b0301050f 66
    0x3500700030040ca4441c0c0c202034441c481c0784c0e00030320081c20f182c0307440ba010300890204071b4424028100c0119440c1441e100d28082000020a20718864a80c0060112120406040941000300c04200a0400c0c1c0000b40420028221690002174044c60950010141c0d00d041c0001c941101c03003040703500c406005110846064900c201d020261000803680350300a1445421061600140294000010b016070540822100451070303c1d40a103e5480d40041882100b010460f84040f0f0b5003109407040001200e0080c01c411503000e001c0b804c02c0759091002d440c101c10179001c0c1c0c100168101d0080103444064001100b000034003604c0842e8454180800a030041d00024422208159107048a00b184000d9400c40c503041504004165a1804101080443c1d6070084406601504c40c0f02d1440b000304603644682c4a44c203400030005076550f500340f200c400140180e0f400a5840b050803581c0c00303090000511220008520501c8403081c0c103490300d4982ca003500c03c0403d10a00c664902400c014243c0c0c0c46503031203540010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 324734037 1250 324732787 324732797
    0xc060801120317190f150e06090f0402040b0603090109050709230406111903150b1603030605190603060f0e010302010c030201060f0e041103370203060f0f0a051303 72
    0x4d42c8504603154402e4012055268a0400412011000c11030340110511001c00008012142d00d561040080000c19900c0780d07002181a0002800040b0031190981c02c144010310110312103d00c4000600103802c02d0750340304245d954816002040000400c80c034801084105c00c01e02050302d40710f200c07562580d9002000104445800c00180420032190700102d003103441d212842d52641d602440c3d5a00c440b940d4004a40864a015030031002000d190306801c044881d81e00d0310900d080265090603c2608070010101e0038180c5a000c082615500c08102a501c1d07401a080d107a500b030b15041c0c00809650844c1d02010340207030a01d00a0180c002c14210380b0381900e07020b0901903180c480c3d0b860b08a004203101c0e40010a00c4158820200328410760060b5280500c0c041d92685840c4102070040548810780403030007480480040c84040e94030f0784840042040c92204541070201552950042800c0100480d4800015240700b01004049001028106c0c2c01103a801e004004614085442e0098100b080302e025041c06 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 324735287 1250 324734037 324734041
    0x11040b030a0b0a110c070603020a180312210501230a0518040f06050f01060e0102010c0206010501082809020a0f06020c040218040c0c0203060606090105030a09020d050a0c060801120317 81
    0x24000201701d40001d1488000c0b9005c55558400050083d00501d0580d00051884500d0542420300005044113403500080105003000e103a50f0140c0c0c507440781240000e0000304060102850300c0941c82803900034000401c0c4001041d0f075264041743c00c001d43d9000144039610f540001d02040d2160741d48044c042200300c900102a84813411b240445021044006124500749000c00044120f0404442d04a50143d168000100409401603003660290000354006a00500040240d076209401e071542100040048c100c2205c41c0b481484110700300c0c10000c01c02140c039208840c6c2107040003180c0318001c05011400305592800c10100035198103650413410f1140307402140f40180304003408614802108010000c10055a800c40060103030507a10034164030178000c400020b02c2604014040701e0b18483c05070b40f090711b195141c0c4500d50041107082c2c010703a040480c01680307900043e02003080e1214680282e0040e61064070304000149002416004900c680e1140c08092001a4100d400701c88540f5000020391519 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 324736537 1250 324735287 324735311
    0x60c03090f04110c2508060a110c070807051201060501020d03111204111f0507300801030b010501050a0e042a0504030c151e0201020d060311040b030a0b0a 68
    0x3034561054003089080300000c113640010320000701d10807103400800701094655102c8244280803511351140660a400c03510000e409a03800b50302030390341c440e42260b07803c0c107181c01019224a80b8078035800807000c950012901380b200b40340c012804000000d882d0020700201c0e0a0400003511180006c2840c4281912004c07804c0000f10f031074050f01e851102030300c1500340d00d19103828490300c4141c020303003424007900340009442d07800650100030b0000310b2502e856042c80e021441e0f0750f580042d400444032400101a40c038900c0d0411405045043c900541541ca0806550450910244514060340014140a001c20542145c20f400024995042d241111300049945066824502c1c00c3d0841c18044c04440100c85000c16454208000c0c005880c01803410300d00305519003c09003001d145850920000ca41e10341c0b01804d50589596854880c07180c01d2001604100c4603002410558074070f1b03001160308504224200c1940d040500c540e505403403085000700110f5241d0b03116410744e04405444070000b00d890300c0d4000e84c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 324737787 1250 324736537 324736541
    0xf060e0603070c02031c0f0306050f190b16050d0822080c01060e07020115031a0c0c0706050d05070c1a06030705060f0901090e040507091d011d010506060c03090f04 72
    0x5402e030040d007995002c04c8202c28010300302c2d4a081d5050b01045040d070511189132311a04c101c2040e601c028110258405c900c00c01c101768640a509140c030040d50140000c42d42220060140040c00b01b41c6e1502d15411a161801c00d080c24000b1214030f00b003003041d5003007000320101d0356818520300c3c4a0380c50240080c1c0c060304001d0807621450041e00c802d0f40c00e041c0c00003402c800c0302c3c01c954400d00b1154001c0000e40d0340030168040d0080e2911002d403d02c0801c0d15501c0d905181006400d80001400148030300d8862a51701e424180006540319002042c1c01003641d8038680000e01801e40d011061740f41c070400c1524107566028030705030380030480000f800ca100c001503c0b0b92010806c0101030140244174a0301e0b01c40c0c1c0a030a80450713010744603460019240300400980c000008881394000c40e03204029200365400d14083c000200f189004203101c1c035400e01d02007003460b0001c1c802ca0004504030740c0302d9092504150031007400d40e0805403910707000b0341c6e04110352892980040f0a41c0c1c1c5072407040361480b154231050380000380 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 324739037 1250 324737787 324737807
    0x1608060f10090608012c0901090f1103010f020f160311070e090f010642020109060e0f100e071d071115070c031106070909060f060e060307 61
    0x141209a900d040c94409402c01002c004950032603540440c1c5a0700c421680fa6803400003070700000c600c289103101000321600c6a801c0340d40001c070b65000188010306901c400d02220203503001030350030040c0040c00d031140e401c00b0300503806400005003003075140001096103045944034191010035900c903850204c90400d0b2161010206100e03610f03041b0784d11561900d4104160480540340b80c050b43c40b40127451441c400042c00303004103d9a614540241907061064440300b0b4a100c03d000c6650719681402903c46140701400020f00303c0302950000a4050f028501001222406610b5280990002c00b2143c0c1e95040014041c580901203a0003150101f115100e4900d403008640014083c00080c00003802c00c0002000030620644255549000b01142c20040d5529010000200340c4205550720020300310501234a5140110340c03082c80d01902d0740d035400c142a81400f80c01d07151030000540080c010001c400450090030042d1801559986425203048006041d12403210f481d18003a0b2030202c0018000b03030050910349 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 324740287 1250 324739037 324739039
    0x30f030903051c0207090c0503130c031e05060702010b09010504020c0118080903100203011d1312030b0f06030f01030308190204030b16050c0703031d06070605010f0602061608060f 79
    0x200c110914500040c200954260070f8801803080920004141006026400350601c05071105440d42d190302c0039a260f442e8910206071141e420004002000800c21015038013055012504084104020f19245051410240c0048116030500a007404290740c1e0050860440e101264010703500c2424061030b81c05400007041d1140c10210502c650420f0250540c018107540d4011410b0301c10f080745440c010022808203015841303110094039125006040d034450850341043c1c1c01e4140c0440400e890344c4500c004075800d456100000c3c1c403408810750380c2c10200c0e402c268152040350682d003103180642011401150510000e0208a10b0b880402d20302d10b070700c3c4010b5520a00030704080d59201d480c1e081c4040b0500d4180c6607039140e00f02c002d02017901c032072085086d0b0302d1815645000c1c00290f40345440455401d0054084d0385030429244460700c502d5520800240300c9103204410103d021361611001c00443c400713562000007550000300c204100c07402480c02003002c82e041170400b980f4a40700d544c085900411041d80003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 324741537 1250 324740287 324740293
    0x1506040f14040b0708150f0622090c020703110f010e10110d05042d05040f060306060e161110091115091008220803071101050709030f03090305 63
    0x20080c80649200341e4420341c00b481d01501103407a004c100b1030b50003100300d4004039841400c0d502c04a41e860700545011500f036005103441d04001004860303401640703801450005559058408110a0744c440c0a403004540080c00940841440c2d0b440e541151001d0b02480d41c810503880d0807264170350b030090410031007801c0042d14601c03a050081c140a03004a0f20303160395051901c03500da4007003146072090701120152030b00410014098100d610608200700c40c4580c0741c4141010104002c600d681700c6220701610340da8100004241c00c0d2650030803400b02c501d580c05c00810403404908001c05880c11101d07405040c84249005072015003a1241c15041000010224041034107000b05070b4240207210900480b210303400c80d0070751641280c2410180103442017500e0a500314540020f45804680501262948190300c40800500c006d5250452002c3d0b040c0e0040c203c400380300c0403040c004202c0e40414400015406180204014104944080c00950703003880028002c641c41d803403ca041602c0b90001c180255400021 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 324742787 1250 324741537 324741551
    0x80915040e18071a030702010e0102130905010801060501090e0907030812010302040b120d03020c031c05040516050901050f030a0b100512011509051e070302071a091506040f 76
    0x698020740341c0903603491101c45074105200c004901c001c2406803c8074400a072014419800f2145902540c00040000095550302c030011644540d00707000920360503860043c1d4078441c070304080a000071140d041e00301c2c04081c5e160100038041641c00290304826602c50f01240341082d503400c0132240c0f80c070500e41c0000b00500c00204400214181e00010349050b2403003182c040c40344844542c1404200102a8070b0b59206902c50480288400d01a50041036490551004d8030300e80540e104500a51821a40042c00d100350f8503002c1206021051003500072503a24041101e0311390340741000140c80d154041c007401348603141004041420755020461960701c00da10203911202440e003a50b0701940c10229104c1c80d400391340900e54403958248107210704c40e82400c00c4000c3e00c0e5000d0610f01010000c00004102c0315030072850111a40b00c01d070480821500c03602c83c591b000350341c800c55454545090300c51043c1e9034410480b600c00b400201ca80100d00a21025014a0a158255208000540900481c0c02d520846a00d0001c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 324744037 1250 324742787 324742799
    0xf011404091a0411090f010e0d05060108070f0e13020108191a01090b0705060a05070212030408040f170a0b04110a03030c1e020d121e030e012708091504 67
    0x311a079000d842c01c030390400c02009400e20340400d030f10030b074050103a1110b07402c42403030540e41c000d18a4104900c0301600741c018031070703156071100d05c0c1c02c0f0b01b0f8100380e00720760010808000407a45020300c03001030f20180c0d1307007000e2504004450f0400c49051420083c180808180020401c00d07903048011901008910300703000f184144004400701501164581e80050601200030030058040008c9560b03513544a8000d0605a544458500c010980a401e410442c01900f1280d48070301d280c0000f5500481c0122880380d6603031f1400030f1000107511564800c0c85c001e80300d02d0359901aa0380104980561135045000c19815a446240180c0280b40e518044d83d4054800b170000f1080c16408508010071070712070054419080c02c01b40000b840004448802075000310461a0312002404016030045000178034201505405048d003001628044d0002055001035030341e011000c035510090240c1c04200903002850405182d240e4007003610f40954047c05884c0c1d0b00001205851600e400300541e60b007646c5995100d4456031100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 324745287 1250 324744037 324744071
    0x5061c17190e0a050a06140309030c011e060e1006030c0e1201022104050c060c0115120b160203030c0a050c03073807080c090a0f0504060902090f01140409 68
    0x12a81034080c60a03590f000c142030400c241041d0039260383e0b89070f405401c10410346856442c0d00c01072203005140000e00c59010b05c0c01c0240114000c02e221440700031264262422501c040399401d90040c000700c0a04014000c00c15160354030030087c1c584030b20380840d101481080540b005030650003059007182d4844029030341140190b02418150504694a502201210100d0148244140e8018095801c80f501c15111440c242c00100316003480140003060803003800203c80046c0555034010305070094003005150400c44c45000c03041d4015020300c014500040e14160003566404020224056900d0000d03403501c005000b50140c1d1300409030042100c0c5c1c7c65010386003c2503426140030320722030386910710110543c0e4101c0c5881907240080303e0315070020032603465090884008201030104407548508105503001ca4962540700409800340070020100d03580340c04103003c1150007550001c1078480c4180925010341d602c03c0e060320700035030003483e0255501d5600c00d076078007880c841c03648070450b2030340741000030382000380d5032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 324746537 1250 324745287 324745307
    0x1005030108010b06090604291201030b0c16030311070c0914010f0b0a030f060b0703080403020c0109080a020607140d031b03020a05093604020405061c1719 68
    0x19030024404081000c0c1413140c60300408001c00c0c4e0285041c0810301c080d07d0080c694850946400900c0704041c080080d42003100d51180c51a0b0380100010f80050080c8030303d601c10590420101c682c0d0500e40301d00c440d40c40c0d40c0111408002810140c079801405001000b4406465450340c00c07501d90030160b03699003034500081c13245183d48404c0d01c800600014452030200c4081049030403103080305d8a0700c44e10841c210024510307d04030790001d5075204030100d0700c698036a002e0052184240c8541d08181032504004e0300d07215170b883d010780c100a0880418010140042001c2d2995a410784840d6101c04a52401d03840d0b9210f045442c510301e20807010200c1720b45516410a80d03944115412031402010441e408400764032a40c4440c0c800320300200621402824890400c002d00c180c40805000e0461722028070901c4d10700140da080e807071000c0c400d060000b546014401c054221204031407094918544a0003d1421102c82d0740180121281100c489010325601044a040c6580d92100c00050404450041c0051042c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 324747787 1250 324746537 324746549
    0x2709110405180f1506130803120a020c030901030e0307060c08010f08010501031e050a080c07050109090204050a0308030705040312050703120c051b0102070f060629090f01020c10050301 81
    0x141041c02d409190711480340c0c6010300340c0c80680600540d0303080000e208400f1039480290304440d040101110112440c501d58002e009074a01640d60b03045000c1e403001804501a2241003400c2c41040418070140300002106d0980d8820300f00490400709071078005007107000e4503030087c207024200b0020781c0a0980c0020000c0c140c0b0408060001c0ea203440f6003000342260740c00d000003009e0400051070719015140001c0c440e01403902c5441100d003414419601c00e61140c00c6040c0c401d190f40d01041081c402980c12100460141c00c4144046041a03c1d04000526440c0144805010803034004081111b50b8407880407603015640082c510420410548001000da502400f4240e0000320f000702600049012401148514000d0760b403102c2c01c01c00d51030828200503082074083c0342d1541d802c20580d000242d0f19004c0840322409040300250503440c080c08155188401801011074101092000c200002890305840847d00c0545080103030700076400050785000e540410113130340080d60a844609456120009605851f2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 324749037 1250 324747787 324747799
    0x80f070215070c030b180d050a0207050f0307050d03050c03070836060a0c0c0b040924230904060507110a020303030a050c090a03060b01090b07032709110405 69
    0x70303050100300014025100001c001d15582c01c420008204504816500030004410303100010042d04405850003c0c0202c003d408030b480451810031040e018401040203140554100d07141c1180c040000c0d45034107160142c28800d1106041c281e050510a80940300350304440300c12203545001c01e04021010360011520941020161112641e2003c410409030100c0d0840c10403000601c0c85032010020366030800180c0001b04000c1221500c00301d0600b22418008110080e215036490b070821040c18140c2d200782c1040d013081c254240084540180d161845001c848010840f2200450050302594021001c100c0701e5522002030010301003403204540c0050b004038010b031240d040c03034038807084a0354485500704000b82d4141c200740b00040c000c1800d90041d580c00b11a1075090f13881c01d004040020f07042866038200b5510784d540c503034442c0403550300001a10068074991401505100382d683d0b006004440d855000b40c44010203032400740907154080314501c0580454032091103c2081e03040c4400d0507811500c18548261 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 324750287 1250 324749037 324749059
    0x90f0d02010e06240111010e010c18061112030402010509040911011812020607020d06180317010b040603020c0f011d120301140d0c080709050702011a1c05010603080f0702 75
    0x845542d4074100d910200c207243c003000113420300159900d80030001c020115540b10a4216541b0030b080c4074565102c0318076101c542404000901e403402c1e00010742c00c168180711000070303424404003001640d00ca0112000024070340e21381d2680700407105d50040c0c1c1d4415420509008001d01044080c84c20110024400ea0300c1c1d015a5081d0040028000f40e6807003001100c0300e050f03200d00301505080e801031041c98000362921100c80c1041d034901e822200040ca05019049844040ca000c0680c0600e50304074089084401c600b941d414a040c4101c00e10607840b454050643c0055075829401090007401c4c0c1c204100c81c020808030200c04045802030060a071010712030f0007501d142c00c00b00141a0107480c10b85c0c4042c0d620b0403010031b0720300a000c04064075078402d4451040030500083c1d04001048440c1c041c00c0d9900700840c9a0510a070040d09441015a5004100740030700312249264440d450a041e44403d015410001003485040040c010800c3d900060a010000140043e01d81642401050068401c1d22844264 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 324751537 1250 324750287 324750301
    0xe040c050316050f150412030309080c0c100f021e0a1502030709080a0b04170d0c030f0b0405042612041208011a030105090601051b0106030203070b0406090b03090f0d02010e06 77
    0x600143c1d0301283c000d01042c4014054003560109100c505440303402c000030030a100e500d88607182c3c0c2100840130ce10b039220002c0c4a6880c01c01c2e108107046980b081c18444ca1500308080060f4640781d105900d225003400c10801440705010400800800e40d40201884070311440041610300a94001c4030304c4004188071050018450600007209079540307800c495540c6403a10340f0b07900e40e50492103103154280000740c03d004a101c45c00c0144209401c592840c0c031b000817a000074544071000e5407074080c0030031706c11440c11003000b001c200d40390385c501c4049080c410300d005d104a151812200c0340c01003016400040484004000c104031000d6840003000d5029215088180c0e42c03450400700e5500c0306103c02510500500040010341000300841e9000541418443c0c03d080030120580c0c170301482028032240c607030744414082065013030511203200076003444d1410f1031400c1d04152014102c64018410034241000001c00102c0301e0f042840b00d50410300c00c2109842a544071540000e0207000c1750016008180110800b103208 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 324752787 1250 324751537 324751549
    0x7050909031c0f0222050108060409080d0507110a050a0203061b040b0d020d050a0506040c03061409060f03120c0f06070c0803040f06020f07050601140108010e040c050316050f 77
    0x1252540b100d0795070b114003902c0401d07800342c070034802c40200740c580901400201060a4090a8038008080c8507144480e01c0d01d00010994400a04554041d529000a038400705206404441d0244020503010401e9210300004030344403c41c0107a51410342c014686544100f040104141c0500e078002c0f812101d85803100d88040303050b20706440856450f044100010848241428060a01001400001810046501159810340d01e040310a000e50b00c0d51a420084a03141a02c140382c0e80d0020340c5004c00071039061415415090051501700751190038802d001582c0d0782da490f2000b40325440c020301034581802c41c011f01c451181d0441481b40e401800340040d0520200d80028515100c1c02d010343d2070011160260b1107090f9540e00250003503034094051610140031881030700090400c1c649002d041c80e901e50880c00d20300d09010044c1c01c040c41120072a003401055030382c019500c50650b01b60800510032920740e45080035201420364803450f094080c01044d01c03920340c0031400a4040354400e4420096289c0e0200400c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 324754037 1250 324752787 324752797
    0xf08010c17010f030b0c0c1b0102150c03190608030d0b1f0504090c02101e06081603021002100e071a0306010c0605070306031b09060509010f0b090105070f050705090903 74
    0x6503400d148410004075240301017050300301c1d1040c05100c5c030703100a85c02c00702c0c100700089003071003603408e540d24031444a0750b810401000c0341c3d0a144d2040c038460802c000242400d100150034014401031042040039600e170315601c04002000e910085075551108061b11201404403155018496640a081a000e00000c4d52641d402001c17540c0d40d40340707403a040c502c407840101000149582103105112018440c003c4505c81c0d2281e41120400418044003408680c0081d00c1c4203400c19000383d00070340c03200440c284540300d001c001c0c0c0390704507205040341444500072480c104420300308002c03131070510304148283c007000f04511080d5280d06d10700c240102c0ca10020030003a44030944184d40002c00c80c0d008500850074a0788a00d42052680c42c000c1000c550704d40300d0114079000944d00240c11000c5850411040089104643c0201810741d41a281503140000c64109846a44100041e0010000e15400e01d41c0c8a40111000194461103440d452085414441d544007001d014450140c00d100000c0b504c4c0410000581d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 324755287 1250 324754037 324754049
    0xe1b1504030c120305160309080f010b0f04180203030301060c0605060f0906090907170124080d0c0201020a2907020303091e1e06070e01030605150a090f08010c1701 72
    0x1055151900042031486150510144c0400c0820b101c900c1d28103040204941d80030b4000d942d1706800505000e4621b042041d05003542d0702c1da80c03500c43c407502c4545403078a105200484c1210001a010b0100561092100b0036000080d0f00d800000f0011802641100c0c3c0400260302405c82085140e554034140111442c1007003282e41e02003070040000341c041c500b18a401c0e0380404020252281595950701c981d80b0b032003071004000b134207946889520655141c05114000c0640000422081051820380e4054548244c002001d0401034200e6030503040d640200108613071075600604118460100b02008010300484a04c0440d846111f00003044910b440002542c0c043c00801014250405980348410f100c001200d003564820302421100d40c034984100400300c410644018090049860280c80041000480d801c20314140351070b000044c0061340f13407010403240c0c000420741040ea844401d0078080e6011030055020011103d002000486c60002c107400ca000e9528054841880d00e150030030840074400c1c0240500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 324756537 1250 324755287 324755303
    0x3070305160c05090901020901030f06031a041a0a0c021006060509120a051c11150f060f1207180603050604260d0c080903210702010e1b150403 63
    0x4440d410608460240140c807508440080075070f40c50100700c41410480d580b000e1650301103511150342d601801004000718809604100c51411652840461205440c2d80014902441c2c0000c042028202d50000700f070303d01c885c0c00302051070501d6102c00600a40b10301c48005019003035410103180d02e07500400c4291500e584445040c0501c22090090180201000003440d20464001d800404e41c00d00c0318039011084110100e40e0384403c603001520f500d505e804182d250750f00c016851550110010340503130300088a4501001c041d154500020401240060103c0e80b00c3d40055004104075070002e401c100b1500ea404410401030210b00703850301190041d21014040d500310500050002d01c5c0c42010790f05981e441400c000d03080919095074401600a0452600c0d11a45ca030390301598035800039403055008255400462815600400d41c2503d119580d0198042c17086410200700004c0c004c0d040700440d003a0000c126124001c041e407201d00c01e0080b504c0725034014808020303968059080e0000b00c4040c0c03504071445c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 324757787 1250 324756537 324756547
    0x20109091b0e0a211b0e04060203060d0b0708040b0a15050d0602070c17060a091509050c030a0c0e01080703120804021f051c0513151b09090e03070305 66
    0x340d69010000070020750200080d040440d511441c4c44d81a41481080d4007040c01200b40c0d40307010208041d00058900100c035024604024062a240d000c0368095881000540c50740c990740c0c040394540c0d41d0103000400d83c0c0e01802c1041142940107504903c02c0c1c2c0142d80c800d0b07080d269140b490048a030b00c0640c600c4000c0509400344014141070741558a40351041000515100c10b684410f1500c202d640c0142c0202a0134109201408004110f4941c0110200c0010000d02c0b0540d980c1940036088501c1c1c444110b07460b0200d90007030280074021850040c5001e0283e81000441e450f0060071440c16000e0360000009100011817103400020b08841660340c44403000d8020500900c0a50b80d89000500c2282e00076200c0411010080400c4041480c855858889540f2000c00d0840803405050102c0086001442c08040140b0004143c211106041c3c03c207003494003942900d08010003802c2015036107441c1d00e4800550601060780080c04070700f00e51180104104901d00d100403980c0300d2160201c007a000500c10301c5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 324759037 1250 324757787 324757841
    0x7060e060a1107090c050a022107021903060e0d090e011d09030d0c050c06070c080f090609031501030b0a0203090c011d040608240c04030308070507060e0a02010909 72
    0x450042d8000000c1110701140d9200001001e440d16405c0c20000543c01043d46800d2603010090b58610240a100d14803408910442661450113812030207403045031109400b1002c5143c0d1312030800995085001480941d0724081000c0da030300308801491000a040650004400144000450594403c060900810a0043c2e8034400949000e819500341e03000402060001d09000e105401d003590341600c17190303101c07030542e010a03051120081c981d07424481c8100c00c03e00081c102c10101c442000200717118544512000002c2802030050386102905807040f8150403c002000000785070490b0320030684c8000030f0369845000b41c1640400d0315400d115521400304520203600070302c00150001200400700e20380014140008007501c400d5440580c05030455904032000b0314100c40e010040381841205058070b8240704810388041d02c030b18070019041142d80d034046003000d403007001200d0040760000e2007403066400600c1216240c003d1907a08901040c0c40d80c20018482610340a08540d0b1682d82c0424114000c6000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 324760287 1250 324759037 324759047
    0xf0b032b05031f1e08160905190f020702030c01020a0c0501030908070807030e100302070503030c13030b070306050f0f0d12050c2e02040b03180a0c0902030907060e060a 74
    0x50096603420b502001409460003041c40100f00400200840740031550503c4032030541242a0f802581c031941240031b0b405030014200400c1e20442d9214a00000c0c150354a00304c80b842c0902c1448555440d5040400c150501d20150700680160b500840c140c0c0c000c1a201401640c0e65045510028041c01409208011a601980c01025118002c03448980f40c1000c0c2d654025990f0710042003100844c041621940080c00e01440c1c0d0305183c4914201140303024a1525160741e2400020101040650300180325156400c0c42c1c203004008503802003140215043c2440060050403080c0034150148840b48070404403440c00c00d40700070038408007600315001214580c40e040e9001310003881180a104080001d010707a0a030810110b02e800e0782c1101c1d0088050300b01c40c0035950920328002043d1106006120034404000c00c48101d80d0411544103000c00c807a800151400d04040300113602400f6040e24540c00220315905400071031041c00c210f8107590a00b038860324140c2e280f030170a0343c4058100c6801d1041c9582d0714014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 324761537 1250 324760287 324760291
    0xf0d0b0601030609050702100b0121110702040915050a050f07110f03031003030905060a14070f0f0812060306010b16020a0e0103050a1208090c10120f0b032b0503 71
    0x40c5400700f01141c884151000b500c1d0243d915200513807110301040c05041d0180308400600b0000d00c1c1c062030342071801d82101d110351021818191441e644a600d9001041c10301d044030810340d4003602c01d101d644000d00303080c008030f46221120a00d5900b0540020000007061261601c900000140b0318500d4882d190100d9801c0c0480c1e041108078400c0301b01403440010100080c501ca5401038104a100d5330443c40d0040145469600060058009102440d81d0315004000c000c0d01c20b0302034440d80e03114181410800e0b0541904507000d030092002e010400240300c0010020b00e0b454101c0b690300c0509440d4041415501c1302c0074810070315031883c14003440c0c210544855010208a0008002c0000117441c5c407a0300c444a0404e80c0110307040c0d03100f00b0030f400030480081112030321050740b810612090329040c1031068803006503600c2e26214480e07032004500312600075100103488a4407271404001a900d00b6820000408010b02214481c3c80b03148040b007910030500d810600d0504041501a00d00006110305032110303080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 324762787 1250 324761537 324761539
    0x504170702130f0b1305090616021608060f06310e15180a0b07120905150103060b06041202060c0a0b090a1a09190c08010e0312060f0d0b06 61
    0x40c100010400d2002401030b035600303100b402d400142012410080100030144030501208142c00c00f1b0811030740c144c010581d240e024420408a820702001004d00700d040040803030400f11555040304000c00d8032100092607501c00c1840d00c03842c400a485250402414881d201980c290304281206d8402150701d04407030105c01c20f0407007100428440c810340c15107400c28010401d1704484a8a1004020788081d43e00010b16420721840c0150143c801d060320350503906a4020101d00520228901d00c0404281942c4046402d80d004400d46a0301c180c007003c1c0341041c150a1005842e2103050542c031011f02e14000044500300d4040b0043c0d2201440c0350360a00802d508010a11041e03401f5031b5007014041004154860b1180c3c4103240904548281460702089060301c11209061031070021007001506c2c0b0001030030300c511741000954103800040c03900c0e281c081441541c11005555081101a014419001010300070515007100c0c181c080d0360380c072014042c000d10180125580a161080f80d007020541d290310301900150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 324764037 1250 324762787 324762799
    0x8060d0203100e160306091b0e01060c02010c0c030b0702060603030c030a03090203030706060b1b0703031704060b10020c090915040212160f080f070302221b020601030c090504170702 80
    0x1102ea019204031000b036600654403076454103000d40030442c40258481c64852403200c80c52300e05090030800c80190405014400505c0481c05c46a41035a0181002407a40b0fa48000254419074592801d0001d0000681c5e00d10058400c503404111245002700644201600c240000c501340544098210082c4c8515481a60140070402144002c64841d003e0800504a4004031560303c05c0301c80b601f04600c5005010a42194001150900009030700040d03090014035070122101d001c0d103550400100503c0c14205443e071040e4610001c400940d00407e00c0c1000301c000701d038003040d070ba5108500719850750780c034200070500c0d000d9040008005180c0a900404030703000c088121546500c1010160b84411203d41040d401211308503010050508100008000c1100e070102070000540345030f000c6042c01d420961380b92207e07520010ba80300304800e1540708800115442c020b40b80d900c081d114019444a20a00040c0c654981e440001319503d8803138002e0a00941d40500105903c0d60071036800c1d400c030340108204980c005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 324765287 1250 324764037 324764053
    0xf1e080403020913050c15190906080c0a0804111206040309090c0c0f03050705031902010f0b191a0f04090903020f0d08040f1a0a0e0712020607020f0109080307060203060108060d0203100e 82
    0x1040c0c4070520711448c422a11010300c584c0c1807003000b52122000524201d4444002c00503000050790012245070403503400b04900e01144007d20008403520200721400e02c080c407561040000703060340414098211091100c08015200d6218000c030b6440c00000006052801540c40d0100007a1080b00100f0078036001e0000e90f800d000c403400e0380f02100c0c0034502940d40107070b441d80307401d080503040d9105800c2c6800d0106c0e8200c080c01003c0d900702c0e10209661240307650070300340c450781514054500d000b01c1c1e40d010b003030307158056039192250604402000526000d4005101d100011403a4900005202103070701c0d041c0c0c5454019035620b0b40c602440a1211000312441d1803548100001240d250f1f180c94001c0180403804210b101180a009140001561151612003102e041c1d4101607100c0c0300482d44150b030192404c11304909010016241040709501c0100c6900c0005054000e020700e0b030380610302030072099a808000c0d40f80d1504000c3c10568200f4041c1d8150064100c42500600701c1e0b001000200340301050703440705 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 324766537 1250 324765287 324765307
    0x1d0607060c21232205010e0705090114040c02010e0304061214040b0f040204180302060a0c05090609060706020f0703050705010608120f0703031113030b10030f0f1e080403020913050c15 81
    0x1201c4e007402100c00780c0d10340d804141c9501090000c080030b8801500c40c0d003159071405001d0b0070f1100c90b19000ca40030302e07038515503d28118801c2d00000800c000e0182101d40d5241d440d080101880041d103480441e04d4940481c20101d10000c18449000d603800a44581d4035072500100080f1884002d40f00301e82c404c0c0d646440b441d0b10348000400300c0b442406500a4242ea181c981000425a0811841c2000b0000d040000407400e5981806403002031005465468071560946000c40c0203100f4002d50f403102900c0440c00300c2c01c05510000400c1c41c02e1080c4008d1003410344c0c614450341d40b04030b101100c3da62100d003070001445440341d58000e4211940a80303008500007200c80c5591034140e00450180e02003580906040c02030204c50300401c0d40006400c07010b8080e0f5841c40c0c43c0c98800b0074030340e90024001c8407802c190606100179102ca191440e24946011102894586000e40480d44076110403030250700750304005001810340c000704d5504140c00c8005041c100e03d040003006941c00100710841c0c0c0c140c1781808a5602 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 324767787 1250 324766537 324766591
    0x3020604060807030b03100515030c1536190506030a05251d030f0303010509100e01120201080703020702152a06010e06030d1d0607060c2123 62
    0x1928400440005071409c0a59040d2689580c869a403802a440b05201004c60340790840c0e650404928000b03036540701c002c003134911601413180ca00e5a00c00c040c1d84819948042154030214001003100700e414000814880b99060207101d070900c0f450f03a101030144001916520780d0f070441c50b44446207080c0060600411500c040d190710039080840002098800b1001302c441c107030404120440c108030002c200c0300c40e056403180d42e00d00c814001c0034040d4201c040842c8203120145000c201405007621044201c3da1610b14100102c880e41034164000340c00c400104094500031300c00c03100c40e9600981020440b000c0c45400004a070300c4510311b0350b50b401038101c408414519035041c0e18403680001c0c1c09801a540f40c800340c41300118001e00349502c00d80062040c2d040d60b98011015544a05510305200703480c1c2c40301800a5251f001c0c141c0c02400c3c05040410f41010a5800b2040315202843c0614100c81c03444034005040c04c41d11000c001c100d00c83c041c4155a650864140710b00381c2c1c81a00b584800a009200b1903032040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 324769037 1250 324767787 324767803
    0xa0207150f0b010e03070e0a0218150a0207090b010c060c0908010f020301140102060603030d0f110c03070309060201060f291b010501080d1b050a0b16030e0703020604060807030b03 79
    0x14100d981c540c102d036800d69200c6154006490100c0050031910f040c145110380c0943e011702072140d400d50006842c101302d810900c20500c48900280304030b1500645036001206540103607a91070060103000d90100f180442c0e807144032600d08041c0c0d110320071079084d81d8a40c070003024101030b03120500c80c1503c40022507800c24004c947c0b0303943c0c800f0400b5072294500701c1c400b03d07204a01c003001d50564001030208059070b24000280c035064011444003140fa0480920000000c14424624144001001078840d5001d20000020056980329541b00c2c2803081d6109022800c071032080c068500344004000041140b40c80601c01c1072003c0c1e6440c58080300e03111460703c40103d1540b01b400d070011224608940400c0445081c843c45006201c80c001400c0d03c00081130000340303281100d5031074860460241e00c02c4414032404001c1e03017201c50b0303110b001c0c135600d424031f0310402842004440048002900b4036403804124040810f400c030072668094986070901d824501d0030369404070000d00e42001c01d80e5408042031299000c0001031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 324770287 1250 324769037 324769061
    0x2001020301080c12070e06011b080703080f15010f0507030e040501062012030f0703140a020d060f08070b0a0c080a120c0c02030c040e03070f050705120d080a020715 72
    0x1540543c40010b100c07030001c0400d42c408454000040c204041e8000003a003c2d4081000d107801103603803800d4041104210090b220180140b07c01007886402c1540002d60280916855408065240d50300400d031005040e4035003405000840320b80503141c45a000d1400303400c544e4170a0034050011018600414200c400980c0701900003a500c00044555161441c01c0c0c0c8040c15554028180c0200c000300b0001e4a844054040030b41e040106001440e01e074420380c080300d05001e042128107850b0500d18a01c00194100b4610301440906c0e140f00000e400c12140c100750200c94a82001d00b01640c81c03ca0629030035008404110305000b000398291002400900c02440c13034950540740d1882c40c1002d1004082100c6040e440300c41440004111000569400241459060000c45022070f424240107845400c5005401009005d002021016010008081640d0042c0c44d016149209560f440c40b0b14180e480e440314036160042680d42d40401e40039004d80c2c00414156000381e444000c00c0f01440b445400b100e40d841000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 324771537 1250 324770287 324770293
    0x9040809041401122612040b070c2301090c0f180b0d0f061d030702120d0c03030506030c0a03050c0127270501032103020406090303200102030108 64
    0x803003507490036105a49281030406050159981000c0310388021251101c0003a14049010940005900c6814600501840959201600c808800003000a0700400742d03000c50300d41d8a1344c00000c8120384160460030525803c035070401160341d140c11102920300d011500c0e80485549444404010591115204004000709051300e0b8041b8500022110b258840000d8124250304019082021b0f45e81d40705039142403070f000711101d020aa9986810001026004440c2d1070780c0c10342000c954480340021000e032034498003d03240440e1464041139a42d894500303400c0b201012403503542d41040881d00c0303030380203e90110300a401c40780c001c0b540350001040059640e104a50582c0308000c1032010f941e014410618194005422804980742203c806c0000d03c52402044080c0c406c1c041300c075511010400707a024034003200030020807686d44c69040020303584544d4900300d928028040d4210002a20031320031203044807259510003406904540c1c00b164841c114621003501402d60701c02d07040d100c10080c0300440c0241040310003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 324772787 1250 324771537 324771547
    0x6040503030403110604023105010b0403060b0f090c1605031c0e0604020a1a0403080f0406091205070501031a0a1e0801020f03160c0813030b090a03020a060218090408 73
    0x2c001c100c51040e404c0541550003070307424400161100c00c0d440c107140e8405c0000e0f8207010a031142e035404070b1110416080c03101d4100310001807003c62500060059130701618051103414212024484100000c0400c00d800c50030f00301c00100e041c0a020080c21915004540d00690640140c1340e6500e150061046401e02e2000400c14410b04000b0748a080c50014401019000515260b00050b004c009140b1544a4048055039070502c801c2411086a002e9036101c4001030705c17a04010522a490740050103850b020070403206010a4581324641d0340e214066102d40100030180c00c03d0700450150298043c030240c1001110401442130355106807a0014041050111506450030fa07100c0f1070300e0fa440d03032201c010741e4410840721003a0b03141c2c102100d0380612402254078240da144113003104c01d4400c0e42005485040049841d4010b091054140c80c1168080c90303070401146c036012010303516003c014400401582c445441d0b000020440d802400d00720020104038900c4030500004a155200c0c201d608032400c0b480066 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 324774037 1250 324772787 324772793
    0x6020d0f06050f0d0305030709030f050601034b0f1103010513030206041217010602070f090c02151906060305060301050a0c09030b0c040b12040c051f03050414060405030304 76
    0x100799002088100c6200c0c00340c3c071001c000b0a000f8000c4a1019082140020000d09401d02402c50b4100443d0b00180040d00024507080541c1c07500003e010031a08180c0522882e0002c1d00700d191001a4000c111903c8000c5101d0a200b03030040c00070751442c03518160244046003021170900e403c0914220b00030002450352142c0c6c0c100305030844030300408402c2c10200f1000c0440100740c0c00182a42e10942c02500e0400c9403410360070640c6c0c10304c0c81c060000c0b100315034030b000440d1841c1d0108101c0222142c400c0c2d000509620b845101c801e9030704148036000140c0c0801040f40800c0301c0c19a10340e400c017840746444180200d1354031520f02903404940003540072070340b1b5100303003c001e04003446100d03448145c04108202030300043c2030040c5500d000d07100160020b207840010a0f500070117101124006c0c080303000302a560300f00c10040340802c21012501601c0c0c041200d44005000d0810051244a42650080c00c0a558070f41c81400c1e001010094000e503003000c6404002140b11404201c950300840c01100155260301d0300d0b05d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 324775287 1250 324774037 324774041
    0x6120506010f0c140708061303080c03010b07030e1f05090109170619020f0d06061107030804050607060f091115071a060303391518030706020d0f 64
    0x64441810868800380e6441025400032140c3c00e8140d003c150306540b0a00341440034a401d21680241b00e060090405020b0b40100803144078100500c0780e01c4000d10f550b50740445000340d000074031603030003460010041c02c0000fa1007146800d4120300000c120115a60501445143c1c4001c01d0200c82c0119400160741c1480b0f41c0c01a4800c0300900000075480c5003402e1507111a0345945000e010f0009010400b000107044800c0c54040e281c404680d941166207400f890420388016229600c9081d01150201c011801900310110300003058030f4100008501c0c2c1031510050010580c040d04058403441d503a18030340d900c2000240911025140100381080104141e0003c02c650741c880d1100c903061000d81004031034001100640094154402102c0c8200c40b03039191320100341035200c4e0003490301800f4100300d010f40c820400800c902c0b591070300903d2a100c482c40c05170031306507490881451000d035611995002031050351805144ca50142101d03000c1da8240b05d100e64540701aa040070b00c041d81c12540320306007903503c1c520724 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 324776537 1250 324775287 324775291
    0x11060f0121050c01030915140403090905061e01051e0318030403030801050f040e010e0616050a0e0d0512030702240c0711041e021210050a0e070216061205 68
    0x9032902075842986562056a201892007403a07040c5500c5842080a0000111001c000c540c1c8400d028816091010510003c0382002c540890120f02c080b800426520702e9032083c24801c840103030140c0c0c002c600c40c02e01010b24180c0208040d0400c8001c11403445140c0180f070400c0c2d05030303c000f500c2584130704103948854200d0101c1c40744821654410b010800c04031b6803207d4614116501507404130000440c4001013805810040c1200965608000240003d04000203100384210040c0320040c03100f10240c101150350744107c0c4048000900d0f651580740b07403403a1100743c103114507104408490b01c0d030400f2041140c0a82003152040c1c056002510200400079801c110000180086001400140b80000f012041401084009002d02451000d0010b1503180e40d070120410161551550000c510008500c0c07000c1d5001c159140c0c4403104c030601150300071000032020700a80d00d00404200c2d0003810454414042800140030071304600c1241c0340066403404103c0900c002d01610355520800c803d0185000d400c0c0d82c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 324777787 1250 324776537 324776579
    0x308061503091b13110c1e030702040209060d0504050d02060108060f0a05060d0c140a090615120216080408010e06060913110301110705120f03041211060f01 69
    0x1041045028200030552000304400410f442680e01aa038020034500b644001002541d1840c081a040104040d04080d109945541007120502402d03442c6814401c08141c4c0940752680c030038800b20b0014030342074025140300703c80900003074100540b4070380c00c0041d03520944003a14190054011031034445e605215a901501020004110905000700706045d4144010b16400d1899910800b0400d1555a40210141a6001114000010348921001c5400800b6000440c421400340400003a01c03079450181804540341c40c15209031070740b0519403d440c0c103088001c0c080042a4200315079018604144d0210240d21300074500642c440d030030f00300018219400d15800b0200c6038000d1040100c29540c5140c2c10303a20036070200040301d808146207002c03144011801c21250707065003084151108552064060400036007d0b03411601007030304241d8625400d00c50001086003031002080081c011802c81c680c004030386012460311803907010704d08241c58140201a501c032006a1468001046000c0d44650f0541100d18 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 324779037 1250 324777787 324777829
    0x906020606030a0308041112010515030f03070314070611120906090a231207020a0b030106020c06090f0904050c010e0f090115030b0d080403061b08180705030109030806 74
    0xe0280000b40c0e5058005070040c00c01000d00c2c0040c0400c82447d002268100024024600d660010328205010742021103c070880c8014030703100d000d02c91900181100401000b1005146805090303141186c0004080200565040c000c024071400141745104140b010304220700740a0311205201d69050040f80043e0402e2034980c000c1040c09040740020512903860303075204002d402c400b508065600d8124108440f4004240160307442e04d0319100e0b0340d40007418a544203e5010044913180e9070340101c903010130b00542006a1003d0130b0f000840c14004020401c104c8001d040d444d41610000c005144900102d0742102c240d041064a10002c0d60030822740c200b5558100c9a0182c4901c0c072001140c00000140304c1c48142d40740f40c011403030000d8040d500442100d540a8880c42d42000f01e800c21106603400f61008494051601c80305860030181c101c25800002c2941c1c0c0d60960944034101c2031040144d400d5038104040c020341900085907902440b940301d005200b920b400d207603460020204880c81001c03000980c1c00303030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 324780287 1250 324779037 324779041
    0x7030605060a06081e04031b0f0c06020106030819020721020f03070501050d020d0603060e0d0f0f080402060705070b030a0e100b0306180a020d0c150c02030c040f02070b0a0204030309060206 83
    0x42d4010b00c1039046050741e00c2891703415036900e0030116000307803e1140c810344071900000a8000d02c1154662205e0b458003a01426410980d030305d07002c80c01c80b500e41c0700281030080103124640035554401059400340904d8030454005d191500f0100c4140c0e00100c044031644a29400c1090031410100454450020124041c103405072801c400a411441484034050040b5400100c08042040a41c800c5002e11341140040221308080458a59a41d40002c50040030440c081300500d6401e206280d9103050500d82d41d103100d00c546480d401d0090541089004948500600402260b16860040558810101d40c0d0f0f003c62031200b00bd5005080c0000d200030000424201242a00c96881c000f94164220030f51030307c06259000c503014041e0401c0c0c9580002075003c0034000c011018014004503034030031340f400d070084070424501d07407202650703140d568003030080d0160409001a81c042c40c141c1c1c0030311006103581c00054500060743d40c42c410107106c1100c207400820350114041c03040c9940251076001505540c0028002c034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 324781537 1250 324780287 324780301
    0x1050a0903020d0c320f0705010e3105060a0b090a210f0f03080a201305040203010915050d15020d0f020d0f0e0a1709011107030605060a0608 62
    0x350304888072a0184400580c01c1010002c08219400500207101107401d21414140c0c1c0004007540c01040c5d111461003444000c401e103280119980c01102e4058544105442c5d604060040300300070802078491000d0401c0d42968403c680d241030206805404000080c140740c550b00704903180703000e03410003030503c4000d009007245038441c1ea600c0f0080c0c0c4e8281c0350a0740220900c54100d1100d01101000804040440c07820b0b0081084400100701c00510079125461103648a00303802c0708540d03250743d248428403d0104c103000400c0c0647d004044014000325074230700d80c40d00c900124040e41e20aa1280c1d52030380e5941c18a14024641c012840054002245d411010f44d141d52102e8101d030302e43c1c01c0f6650707845500080740400a40580e00c50a003801644c442036480b4007078020320384000e0041c08407050720141440c100480c0d40d1008200640d08a511405400c1503240d0200301060750b400007503040e810311101c4074414102c40e004000c0c1d40c0066101d0540420245019000c0c44508421a80302009000600d8280609 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 324782787 1250 324781537 324781543
    0x506090607020f0714120a020a0306020901031409061603150e01090606050a050403080a0210090f06050f06060703030905010e03072105070f0609031403010f08010b030d17100305120c01050a090302 86
    0x42204031400810703141001c440e1b60078140a880c000758880c0705100300004106894001e041d40800c262410884840781d1302988050080840301560650080c40000752a400d8800c1d03005e00d400b400786400500c4000c000d500355170200c450f03008a1200341e030303841c0100170609003400750b540907006900d8a9400c2003a00c8001920710f010310302000301150380215007080501d00c01c00c055101c4c0d400b402002c1c805e018039402c1c1841c1e216060b030415500755042c000002d501d9031094000a003d00009450302c0d00c1d004c03864400b14010034410108032401c0d5202c1545084c2d250b0700b00041d0071103e010313658100d0030503403035621414412410072803802400001d000c0c84020500031580c1000301b0b03401c0040407540c06060311b811900c0046c29011207a48003004000890089500640b8000f03661001d0020411000c04004041d40c8900d80c00d0981c00280580415802c0120b5002015400003403010205004984903520719007400c075540300c0c0c890000004240420b0440707003405a542c00c010196010004010a600c009403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 324784037 1250 324782787 324782819
    0x6130c0b071401050a090302010b010201050411040f0608030a02030a180b2b05041b050307050936030a09170a1205090a180c05180103090305070506090607020f07 71
    0x2019402052000600958200d1800401542c1e0002c0090749000d0b1081c4005201d4150207800541c0380041c2c2c540b265005105160140ba00702c04146d911040d0358013044081c08a1041c6a0b5100341c654a00180706c40e0104040c00601c4420380145844d2411420000d00400101e5440142c0f1071040c241041000c0b100c0c0c049800d49180b0314042d592482d503084214541c6929130b0391078181c4c10315040400007070103800f481c0f00c001190090420101d01c2d56400400d80c0d80c11242c050680d016a8030400f1400008801003c0e040100008035038a1414403090702440c01200c180150480383d410010301d80c800725500000c0c00c00501340701e09041c540007190050003581c032400c100000340712000104007030340318500540940344c10f0080101545210ba0701e86503c0840111041d600582d100d06250580200034051400d580074051403040c0311407260020001100a05580f000c2070b0103121042141c0c6020807800e000c0d0701c1c80f5103c032100a10f014140070030001c1c5001100041c2030119007040c14207014040c0d00351540c02d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 324785287 1250 324784037 324784049
    0xe060f041202010302071b08070801200a02070f060804050d0c080703030b0f21010b030a05100b01090b0c01090b01380d0c1e03020703091509030b01080f06130c 70
    0x20500700c0c2c1c80103a009101341140a440401c4100e00001c03149034001c0c148050b9525042500c2c40c8550383c490b501c1c20303540ca01a8211b0095040c07201440303c80c01d00006046038410340c3c4100d07601c040ea91460340c400c2d12044d82180001819000400050000c1000500074007801858541482c240c242c40310011030007001802030805031110b85038051a950540005130f600702c0100440030703550801401ca0f001c00800001c0c29015400e0403100c01d024079004c90035000c01c641002c080e21502004030038074401001500d4401d414400c928401040f0009035002401211028030b0000661f0491030800110a42c1c0c140d10052151413014100d0b50070b50750001c041d0700603022440d9202c0050500f0841c01c2d01d03a00404420440091400b5850042154040c000c0b40440410007004000d0f02d512420032010303440b0364000038010541c22101008501051000a080c8811610304680029247da0303d40d6180700b1700303034080b00459104054510f1440424080c941d04458000207a0a4020843d80d43c0106d503c0144644 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 324786537 1250 324785287 324785309
    0x3040f1202120d02100609051605030712020406090302090a0605060f0a170a0603030f020f0303072717072306090319050109032c0f03030c0312070e060f04 68
    0x3410440d11010486a2a02042c0382551981c004100b4029034030180180290005414600c2c0041c49110318402d03e4003070305100100800c0021031403c140c64a510103008081040702d5004405417502c1184094030181046036180203105155004001c0300b501c01801d0440900d143c654104000d50f40c401c203c4115809502506890b1103518009455101140d10304080e4602d0110421034510183c0c1e200d00e003070b00e210340c40740c00d2460010b20782203036101c178005201d1038070f54810000304000d140982800942010405c004c06440031900c07030b0301400801e295000040c0190056484100f4000c01d200e00005468409030403c1c20350515184062105000407115020300e400154040281c3c40c14495014110f80c1c1d0700d0046400c010031300e01640241002030701a0300141ca910001e981d0400380c01090041c022442903e500361328200d004020304e0038249540c1070b52502c42040701d19400f01050024000c101c0002e203400e41180781560000e0b080c140202c500a03c1841c0c20405039041d00864402d031002c0e01e01386600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 324787787 1250 324786537 324786569
    0x110f0c090123040e1f0b211b0418050109060b040b0321130b0301230906011d0a060917030903060a0513020405160e0102010c020d0507050a1202030a020f03040f 70
    0x31250521040c0c0250300a81c0d03039102c0c82e8841c510015001001d0f010000d898007c18030303110700154400700d4459011240c0d15000243e10341901014254025940800100f0000e0b0100021480070811500c00404951994441001c4000e1105610541e04450400c2d1014001d0b196a100080e89038a00b0300c1110004848100c0c0c0c0100044410080c0c0e460200001400321405131074281d20030f01c58009200d141c0d02e006010440002950005c8000c000b140800f41c404107250b155207005641030100740c504042001c5c104156a0069030b242c52000c40100030f1034580d03510031030510342c140944001d003d0055680c2e620400004000740c400103440c46c1d00a0f0803a00001d407036260101d8441d440d5000a102a500c14140f209000ba0609111a1702616070510344540e4002d089500041e82610b00d455506c0b070150b00800b10354407005001e58010319100d03210b40c081c1d5a04592640d5a501174100024840703006030b20100314100d810b0f03010002d92507100c500310011410315280c0b455400035481c0314012642d03076070b04800c0c1c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 324789037 1250 324787787 324787811
    0x40915060f1d1905100f0b07030504170a05011a150c0a080c0c0411090405060904051b0d0204090302060708010b040e01090c020f010e0102180a081903110f0c09012304 73
    0x3c44254030300c8800200b03009508240940919820f8030b40113100141e8072031400054600c8615040301e800300d6050301c0301c0303051500d0005900c0c501071001d0b81c00301e040d026400503100040c80a03c12820f080c90780800c04140c001c9c00030203200e00c1c0070a80c1e20000078a41c0400440419a00028884036250b5014142c0c0790b80d03011420006013040039a03600e5503005401c041d8001402210707500a03243c00401960100031940d6000d00700315403400181c80c06000c0e604182800b901d8000720704007100311070401909400d60a103050f0b020904565203201d06500681188050004090388a5005801400d650142038141820300d650059002c03410f00c1160500c6985050510f0514007e000e610032140030791008202c500490700e4628082d521950b803001d0350007941504c4848501d0080c41300d800b91640e030310080c0000b4484103007128882d280c0d44c00c1a03040c40748088490400000c01c0103915081540b51001e40b81445d615014040100010f13003100200c05840c88030409009010f0416080018040701c0204011213985 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 324790287 1250 324789037 324789061
    0xa031103090a030c1d0621070305030415030b0306190c05040b0d05010905130b01060804020a030204150f05180112031e030c02011a01021b12120403020a06090b0d0b040605040915060f1d 81
    0x1034801451400301041c00a01500f1010010311983c3782c54034144000c170714000800d82c950780100d405e00760117200542d11107003241303c0f03a00c42a08072000d81001440e003070b1607042c1d00b0310b1600201080000d40d525000107202d024401e00440d0340000042002413903a0360303150b45140170480d05002c0c000800101c1c0700004d0546d40d684940718004c64001d8810000c0070b49440e01882556800c0c096030501c240d00400024590804040c800a20040c800448420f6400c121505107000030841040c0c040201c0e403950704c003c1c1610782082403100e801d00d80700090540c844840103030070350b448602038040601c00c0ca00800f0459801241002000c4403283d461480c00428000050040848400d01000740c811500350100701c400380c07401001524001c581c00c5c20007035030301c501c11111110350740215250000d040c016864021300e160460301802500400203d03001d0740b80c2001c9800c64030f03c4801941c1500158448248010251240c80302910b5480d40c040c0c96030342412050040394841c2080c80080140b26000079068140b51 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 324791537 1250 324790287 324790289
    0x604090e100c0507061d0a1401020c1501150302030f040201051b1b011205100e0a021207030603060b090c0a12021b1e0105090a031103090a030c1d062107 67
    0x4440811680e0700303070300b40100365070410f01040f508246401c0703586040890b15500d00c0c10707002d0400000d000c0810265645141001520350702e40c0a59000d00071000b422a050011078070003c0321140f08034180d850b141a00140001e00f80c801d005040c4100244408100300355081944140c081c01c0155452220540400e0120034010350038030180a82c20f1404031510a680c0122501ca4090340c0f90900103920b225000b0894000b5500c0500342c1002c00b03400c11940001e0314603903501220f40400181801d03144030034005041000ca035101c0c00070b40d0700c4000f84200007607440f800c0d509440566034902546403800c4940581e1164408840c00d0101c10780740b031034206036160101c0c0c0902c0103a8032443d5252448181c01c0b683c0700c0142c40e02110036082010040d1444005102c0c0c030b485503032118020900968662820f841c0c59003030381061106400304101c000403070b0b01c1d5091110000c610801000f8241380c540444000d65031002802ca441c05c149210038001183d4a9041e50300d5104007407151100400c01a000f594940155 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 324792787 1250 324791537 324791563
    0x204030c1734050f090402010e12061f080109021008060a17070302041103040b0f190509100f2c0304120302060603060618070f021207060e070f050604090e 68
    0x540764030062594010034581d06000800340c1c1d40c0305443d1900d0070403c0a51102e608036410100c0a80010099803080019144001c030140100784441070a07030903035040c040111707120030340d5003100484000c84080b40c490303040c0204502d0008001b1000f29900140c0202e02c0d040c58902000610800301d81c60b55039403118a40281721040c246c041100d0b0740d00445440c0d080c1c5d40b005a21591502c682c0d400b94411000481c2d00c143d600040c14241c0b0354030000003c1c890a4040c14941c80d1001030740303030b842d038005a42c442c050290300c02324010040048007014071815144104820309003d8282125444c1103510b180d0110440d001d48101c00a0007401c9481552650160340d20007540080d0a901b901c0c01e243d004600140a518145c050301d0b20b0f6680c100620034207100c00304d880c0300c05440d04000600c0d4248100c1c040410b03a90f803841038030b18141c460311082c102600585015514545c1d54201b40d0496202000090000c0c20104410001e0f64541800150705001c0c9104510100c0c1c0c95010700000003a0038003402c00440c00c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 324794037 1250 324792787 324792823
    0xf031d01171803070b0411010c0c09020c0c060a0201051006030204150806130504030504030b10050d02040f060312050a03050f2a0705030d470d020907050a02060a0204030c17 76
    0xd070070101031240b800e54090b11041d0400c07c0300c10143d4402c400c0303018010740103a003400310580f03094007540c000c4d809002c2d10f24460081982108480d910280201220f5256500101e1103089c0010a100748501300d03407140c010715104100c200550f00c40c4c080e1014005803541000ca001da511440440d900380e07421405000703030500e000d04000816800030302520a8074003501c0044229501c18848082c0380040d4090142c0c40300c0f810786000300629040e001000040c085c4080400d8003030352a5501000034030044d0400022400120b4803c0f845d81c4d03d0f00c61103178010381448081d100e03400c0400c103010010648081141091280c0c81420302c440454008980000f87d02c041201e0b55414110051001861035185000c0c80803145032922840851b2454101e8a9465094107502c80c060510700724460740310740d07000c0c40c1e8101c0e1130301c80000056650302c2c03401c622821700c0e510760030b580d1140c140d0020304210000b0042c00722544140030070702c00f04841d6a854001d5544072030032108019107694405203802241824040d40301 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 324795287 1250 324794037 324794047
    0x180f010f050f0703060b03010510030905070305061f14120a08121602060411061c0204031406070f050403201e030c0105040303120f0605030a0f031d01171803 69
    0x100d201e602840c450760180300e5900c0d071074688101c2201500e0107485007030700200c0c0900060081c1d2a00060401c2d840c21241000a004512039580390300f4494a50320a4560b43c0101c000c01c60b0304007007012440d0711503141d2000c4000b1340c0c0c10300c150802041090524103005480456002c1500d0000b081101c96a03074000e84044d8951042c0c82003c80e62380c104a42c2c00c10700540c4400c0901000b400060780301d02580e0300003520946513048105110b011b40040100001444040c01e40c1940700700385100904c05940074100030190020b418114514005001d400f040c00c012240202441003984441a40c0540703503c240400301d9201020201e4004209002030598042d1648604070400442450b105042b80401d030241c40402c0d02c4a401540d1034001d902c4060003103440c080300701e808003045610404c0c9442040c100041c00c3c07030b151000b0038504640d40d001195201c11840c658030505400902c12403409450858110290940c80002401d543d030441c284e401800103030002c108095260303210300b00c141e0900d4084035151 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 324796537 1250 324795287 324795311
    0x180c030b2d03030c0328050c0d080402130c0507210c030e0d0204050f060306091c0309061503030c05120a0f1d100504170c010e0603090102120a02071101020c0306180f01 74
    0x6020030001c140309003041000b040740c1ba94000c4080e03c840020441c054914440810307010356102300000c200f02d0740170100ca001031001c0141ca200e4801c0506950352616181d604074503020a800700d00e0a9100e56450031241c0095584d5401b03420203446a9140c54080307610008600807031101c4405000096201c2e00b010704020715001145a00c0d8800c0c4800c8040740c0c941d80f5801503003900d80060b401070b058001d05100e0040340b40340c020340026a450f132140100203952802d105403100000a190000c4000802c0344402d80c9c1804410040540e40c080020083d901e000c1c2032007009003002e104290301006005080b50044119401c00e01f002d041142d002d480e520340722540210003000e5902500440c41040c5198050a0240500040600121906131102a030185101c01041031070b4100030504011342d9000c02440f1031040002c044540201c01e02400540c80b0149458203107201d02c20403078614110350100303010300c0456400044054018402e040040e900c080740310320a50500c1074011030402550f003048030014407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 324797787 1250 324796537 324796567
    0x31605091c020f011706011121210c030402040e0a05070b0d0c0905060301030b04080d110d0c0c0c0905060d0803130507060206070206040b10180c030b2d03030c03 71
    0x90728802c0341c81540600701c1400548100300c080100301c040c18419400618a940a1503d4064040c243d00440e03101d5400c01d00440321100943c07142400f80c881c08038420608185031650f100040800ca100b0040300e103412040b08559000080010f0701c115201c410001241d8420700c801000c4640010a5812854407610b110340c1d030754000407608c01014034046010303090b18450141001034490007411245076920799103410025800107841a1050b09003082101d4502403a440b400e031404018088840d118559116902c044030009601d51007840240c0b04090000f45488100b901075a10b100c00005468903607401103540c0c16000b980091001500109000510001d01c00c10191320b4810011142041d40743e040490b22850103862503005a48030380d020900082c0011405513102019107180c486040c1c1e6001c00100613070500380c04100303666403100701c2c031407940d403600544081d00010b132280d59a50302e051041c1d40380c2d0f0366140c0300c0b5000c403000305024046c00d640502c110f41000100310103c80e1a4103c2070130000d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 324799037 1250 324797787 324797839
    0x1a10030807051b0a140f010512070e0a0603060605030a0903030204121103011b17040303090803040308090f06011d0a09020a080f0c04090237081006080c0603160509 72
    0x14032100c1c0325040388a44e1401c02c8554040e03e401ca15055440c20700e41d03080c0130301885c00c420321905000041c40781f141109166000c0c180704d041c2c01d940340f80302c1e000300200b40116003040e40c2000040500b80341003840700302e1304a400c4a800100307400340003d0190407405c084000703000c1d5400400f028900410660b044c40941e001018002104800800009034108212801042c5522054020a45040ca6659803054100c0d605600c580281808504820265144441d40c0d00482c0c00714081105c0e1000d000d1110b408004c0070a20000d0f180c0200340342e50400417860300b110442d040c140241c400c0c90340050301c20141a00441e8505d0f5018001c0b20449881d108403076155924140150711f40d2055500303800d03e528090194010716a000f42c49259490300d241002e61786026101042e160300c800000302d090404140e1001030000b000050090113400110034840b900380c600952100035a6404842141d5441c0d03504021240c00c00350151b0302d081302010790b404c192440d000711540c0d10b40c044c411412001c2c0045061440d59 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 324800287 1250 324799037 324799063
    0x30e0f010c27030201180e0109052a0412060e01180308090c0a0504020a020c090a022116030216051b0f12070303030513021f080c03041a1003080705 65
    0x15405240c203030038054214a6400c1c40140c004900b0410140d4096124190104801c111403800e568a07582e0100e10a1020380c44010025034800030040600da80100b00000a50f4480d044aa9581c40320708142d15800740f4000c4407203c640c02c4086204000301a4800c111007414103000340080c0341c002188001d8403d008800b50b0220b64013000045c4503c001040c11540500e0051070720074002e0400081c40000d4019541032025403140620381012076907020182846607200314000b40c1c0d40c0e8104004003904000a00010303440b1811031090004000c0d10300c140032407084003071070700503292500d00750792028110318980b0181c56402664004e9140444204410801030000d90790000f091220780c1c24800c1428800d541000b19801000c02880080e12940101e6004400c400c02408429581e130006031010303282c001d0000d802d001000100000b26006a0416440700f201480c0900b185455201e2900d0740c1080040d14a807403030f00500003415481f0b40d00004000e5508910000c0c0c0328015464890f03580c3d40195004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 324801537 1250 324800287 324800297
    0x21e0d11041103010605220306020714070b07030203091207050619180312030b040b060f0301030c0909020108041202030f121b04080a0f060219050711010e011e030e0f010c 75
    0x404282d8002c00202c034100c0b0455a1044c0c5400b0b030728401c8107102007803104080c02d0826540000400302d905800541086400f0b10007801c0000e1035030644526120842d0b022100908045c012800841c0e000300603101010410399500c510381185544060a103000368203e103034403031000300f085e00c2070804154540c070381c1a0050710341d68103d102084903081c1000c0188802040b00c0003089058030712505c250410005d4440240001c039100c801c0b98009945c0381c01c1300031481c50a0401000410074095061188402049440f100704040c07100707900000e1001c0310040c8080c003411484110710340d1031352007001181d88201d10780c01296225890104019076001040e24039280a40c1d005e41401030101c2c0b04801c0b1000c80340010002c040c5034040f40d03580341c0440200b04c0d050712150b130b09004d0310441a141545001400019985090390b55800345412099a2030320200c0904201d0f00b280100c0031030340c00103072802411817910420003044c04101803c8015241402c00107040340101b4400040c0304505401407076580380d02d40c842d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 324802787 1250 324801537 324801551
    0x10c110307080615153109140123060a110303040c032003030406030b04090606030b06090a09020a03020f1c2d0c0e0702150127020306090103021e0d1104 67
    0x1c0000040c1240011740c11008104000380402c0410185130b40394078541000c0c02c2d485141102c18112148055100300446034507500144003107445200d0702c03070160600307c42d9240011904500405508410607680f4002c000c000764800c00741c1e01680755812221403610882c1e950303140c10f1a010080e503542c2c0c031085501500640403890100038100d038102a028020300218140362400d0402c070043c0c4a500082030300240c0d62106440032032401d004800203980a0301b560788807814800180036002000030030381c0c031149203042c0300c0000582d601207598040f05d8040f00c407004244100c00014104103c61401c81d090901d00414090800500341e01c10003507841d25220016082844451410040c200070304018444481c1c600d050000c00c850603612504001d0900c112038407400400c0b209180030000fa085114040300c0c0060340d6101082c07581e0100500d1081c00425800c604044010404464044c000248a841a00e00b10391682d039500080350300c010300050280c284010141485140302042001160080e410154 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 324804037 1250 324802787 324802789
    0x4050a020c061906050d0506090706050712050a1403040b06150f0426031305090c0a0804020103050a02160303050f370914030c010b031209010c110307080615 69
    0x825565041c409401a00d41580d44803142c0700c04103032206a00c480195280342c00700300c40d110603c00040c0c241c4610300400440c01d000b400b21745410032542c0201d080040c100b2034800000d50b80000c0c10342c1100300f42007540e121124010280c481709040344090b9040e4401100700700034803004c1e004c101d006880503503001d00c480700c0212100e0303124401c214400d10a020100b1013008904040c56011003000c00c0c0311411542909003010141c02c560051621200e8501d0408003402245400b402003030700110080f4283d0702d0451840805041d4200c000e0011741816a64400680c0c10000364044421721300e0340703010703001001d0680d00c0c0185c010441583d0854034109210001307200701a40d01d400f0203480e4880e42000501141c0c0900c01003220154080d85209180c0320180c102c00910a4030045110200700300203103032603560388062642110707603500210344250700c2411200d00741828079080b51801d8000b8642241d9070800c0b820000401d10f0b0329001d05400d4420504002540071010131803500864100b0804105039103600 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 324805287 1250 324804037 324804041
    0x20c0109050301110f09121501090c170a0507090305190317011a07030e09040606030201081b1606060b0a050403150209060a030f140f0601030c02010612170c010204090b04050a 77
    0x401d031340e441380c402000b11412040245002e440c0c0800f000b403952551064015030f030f9040082c01171030320303c201c16605c1c01070142071841e00841c0b4203000c041c85d1003da001a4559800860a0064182c00380d5076654404528210310464000001d99001021a441032031864805005a440e00340143c00142900350720b51098003103a1900f40c100d5500004041030303650712200300788140e400000100c0c02e00c4000c00125496484243d900b41c421401890005030141c230314000036010440081a00340e2103210030840b0400c14000409130f50380c080010b80000741c007802615180c002014143c100040003003010411688040c2c0c00f10041003a6489607189a420b56a48103121301a07005412110b0f40c4408140f088140040c401c0d440700d8040303491810081000c14000c240316807141400c0c0c0d00c92440c070030312208001d815605802a0301000c1c1040c03008001843c68044100040d03220200010040c0c0c00b401148c2b042410060700342d40702101480b00071569142d0700c0c0d0307540004180155016018034101030001e040c0c14114 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 324806537 1250 324805287 324805301
    0xd0605010c0f0318030f0b010302040e0a0510050c040909060509010c050a0504091e05131209050913020102010207080307030204080c010906050a0e0a230a090c020a030807090e07020c0109050301 85
    0x20601c2c01c4000d020558050f240030ba6005010441c4c603850610000100707003440c9443c5046402004c20010550542c01488141c0e45011740c0300285078061862500010381c0020b00c0c440c103502c050b00015150311400c0005003288a56485058004d00782400c440c2400175552005001300b000788000c026405d80000c00307036503e000e40712814010a0091008011418054002414800d0003403004503081c610040c080c0f04440058917002842140121074a0410040c40e0700b810f0349410a05200e001e4610f408005803120740010186442c4c0e0804503c45c0e002c40e4000d405a8907900d43c085e0717815880e031070304501c0140250006d10580e1118400ca00c04911154021041c8d40c045e151103544887c500310840c44142c5d0031300301036030485410005a82c1c3c002001c0f41c0b141c84d11002420380c080d48850b00000002082841225508900d240c1032030a07002000305c0781c00090425015a06080441481c0d072030410039103003030300d495109810108a840030410f039a54017140c0031006800c2603d500c0207030368450b01414200e80c11 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 324807787 1250 324806537 324806543
    0x206090411030f010602061009020d0915090c090204230303070206220902070b07030902010c050d1701210209090f060114010f02070f0501050702040b0307060c0506091b090a200d0605010c 82
    0x103500c00d004850761a0001c041d0101c1d902d8000c0cc80c4445980c8102158090398410700807550384400d03035020040c0c5804071000611442c1c40550400e4180f05d0202141c0f07140301c500a0185e44141821070b010f440500540c1e1100350000e04075034a412010411084148801018035640304403840e02268000451080d2200190080301038261955081d10a5000307000150090341480156981200005c108000e5660b40c508665550421506d40740c2c024450400180c01c10412500d402d900c20501125582c0010304482d0100e60070800d5440d814040c90410714140000714440c004c00c000031030803040c81c01000e07441ca2001e0f07943c40d04440500c00101e8490306103000300c91241019810810041d88124050006e07540020000035058444100080c90080700381d104d1004182011146001e0000c24040070ba84009500c01070312081e044078900356802d010b015504c43c480c03900c2d040030421034403060740320049100b14840c811600c4480c101c030000c45500302c13003040d1207050b040100c08220355109509601d00c00f68 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 324809037 1250 324807787 324807811
    0x4091101020d02011b1b0b0a0b0a080c030a080f0c0a0303060320090c0c01060b0c06181207061e050405100e010b030a02060f0c1207050105130305160206090411030f01060206 76
    0x50721603000c41d48202006d0300015400103422419001c110610082409498000070009a64858206011901400c0d500210840d0405440140ca0340c030042111904581e1202c01076503103e414110b1b00302280503110149890303100d607504078801c140c1c0540c000002d4902620b040360703000e02d555030004081400b442c0420740080d5980041007406100c1340180c01d1440380c000010039265111700452200346c1202c01801c010b5408102801140411110303004210b400e69000380580d0581c03c0324500742d5205414008285a5984c0c003c8407454079010010b20869442d40b50038041d504260070156a109289031400b5055407401c00c90501240d014421100e0b9401e0250150800681940030006070340c0100e8070550b0541001c00246441c5075040c88004c0444d04070910160701c5650905003182100d600424007200f05140400741404250018140d90405100076404082800e55201240c01801241c42040d0401e092014428210342602d000d5886a9510700a0803890780c2e076a40100e0342c404054403210030700383d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 324810287 1250 324809037 324809081
    0x1b0f0509060f101b03020c09060303040602031209100e03070303050f09070302090c0d091211120301030602130308030a0204050f100507020d0303140403081501030b01021e0a0204091101020d0201 85
    0x8100b0000c005880702690030310780c00c4c2241007012566181d40c291411401030308010f000c90b1071441d16040a0360450310a400650401c0d05041001e556445205040350605645070005507200004000b6018201c4c0c80f40b00a00642c440c2d0512140d0b41e8008100c21004a802c02e400903a00103003000c819480380044a0040c9003c0e80b440e02844580013001e010401c484000b00a081041861400340500142c42842d80b500313020307a110002404082400c0d102035041e0000714074591104000002e0302c0c1566000030006035900c60142c0f0001c0041c040d03a100500e1851302108005443c070842d80030304100d90701071f0703407a13040718003d10104158100b10910349004a4030510004002d41804d18120814074403030b007000650b4440b40401c1f8000d61900b25412000a882d0a04204101007030000048014a086c241842218100800070f910751500c1d208410580c500e038500380c0440031081001d5807406030050010401c00350103040c6040101071001e130781c6015104a809070700c0c2480c81440b40702828a12600084025 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 324811537 1250 324810287 324810289
    0x1d090d0e010c1103010c170901090203060f0a090b01060f2d0804140a05100e06090607050a0302040902160309060c0305090d111008010306050c04030b0103140a1b0f0509060f 76
    0x41180c042e00f66400028800b501050303841c244104012032610703072121000c019007407070000d0072403034010300b11111a4141103848006850000300b0940101490488207419a510030882d8004d1030040c0024100d00031602c00007030865084003032030b021a003c95881403410303141d03580d000703c03140b5090034019500903003041c640d030825110300503690b0032921900e00580d842c1d001c100550b04d0410103060a881a422515820700d807029140b0900e83c4004864014003800e150154040b07440f290024078540600c140051002e0005200e54115000b03060003500454450a070400754a107814221241100420748007400811418040c440c20766101d980340da5441d15203410034041c84410f450200c0c088403004044ca1025256556181040e2252001907403913401561441c00c002c41603880c05400803411f1101040305101061102411505413500312040380301c80c0c140c4072040e81c43d2440030180a42903508107201034041d1076541c0c2c03445044403801d06400300d080e5156002c011002c0343c184c42071790340000190014545 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 324812787 1250 324811537 324811547
    0x170a061a040803030a1a1203120a06030506060f0307150c060614030307150f020424031109061e0408030a02060703292101090c080105070e1903020a1d090d0e01 70
    0x800c40c2c6c140300213440100c2440c04500c80a92032204103c0315000414250000d0307040c1d40c551030f40109124801d000301e52440c0c42e099107034031001e170800b802580c81c000440150303181009044001c2111a0b1840c94022910100a100c0003840d035088075680c3c141800081e4040e05020154070b00c0318000e001e5403926685039251542c90071014100070096031146c1c3c01d24150a41d0344050030040c00102103060100260703565010341c80e0369a004150906152014240c5040d81c00c105030b801c2c01c80300b81c42c3c02d5511103652584482201007441103400120000401141494001c0081c0040001ca07800321110750b06e402d081035064410f44542d03a60a0b00071f07181c5582d072103800d100d001c000303811003e44000c00d007106007030306003846244d0803141400f81c7e9110b200c10020080405001e50007001500d000700110305084900070181e00510821902c02c0000d8414a0680001e00201e20025980100441344003540d0301091080e280246503074904d000d0080d03000451682d4003003807140c50748803030707985500b00400c0b22401519 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 324814037 1250 324812787 324812801
    0x302041415010c03031104060503070e030a0c0b0f04050a1427040b071209051b180109110f070b010303091d0f100b04090b1c0b0412170a061a040803030a 67
    0x4061b12005000e1090b10740c0b1000344042c08441d9502e070b6403485d2000000d800982d00051190280e07002c1090b504c0030030f40c824246000c0e5011000b000781d840501c4180510f160180381c101546c4080c080706c00007074982d00c40950a010540c103a8101110b2400700c10746000c18640d0070001c10703a040708040080d0004095004a503805001c078106141e81070690804001142d00b5000103c0d1281d005034180c44030451034090502c2600b41c00c442034420040001c0460043d14010312581c80140c0d01c420032101402c001d80e095591f0625072064242d2981c1c41401c04445e8400b0030f10055000c42c6079188017007402d1840103a15a54007103070201e084075544a15a00018192009001c02d4420f40c4c4150b01107607904590001b4401850918004140320106504000c008e501400303103051a012810040d07000207800720542584150003c002a01c07854020906446540c524a5a01c030400420000c105074240329a00580036101c400c0084e04403010001f15100441c426401100c82e960f1092002440342801c1d500600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 324815287 1250 324814037 324814043
    0x14090c0315151209070608010f061b0309080303070c02100503010e040b0907080313090605300a0206040312020c01020f03160f17030a05070507030f0818030c070302041415010c 77
    0x42c03500c0340c0142c2c5203c0d0350740c0503501d218641e0000c80741005850780c40b40c549800351040340c0b880d000703d80c80d024011300014821043d90000f00d0b8102d140800781400b418a4130f0060950400342c85d964a41060020414406208124803a500c0744a0040149100b00280c07810f84842602d0071401d61520340710b40425203002400000c540c440c01d24040f60040052028224024a01c0c4581a049d0b041125107003d5801c143c101d2800741c010000402c0c4840710031248000501140c201010900e0707501c000213802c0460640c0041d4000324000307000001c100d042182d00140c0c600315400d40d900d90500700012600d80701001a41c400541c030034001d241240195900654100f440380003101c1d0510007503640c14140c03940488822080180100410210003502d00840d07034854090300d403c5d031070710502e035030098119080880d0b510108018072001404881c6841000700072807824400b12078482152000d82a07950003203002c200d001d02e04202c01c0e00c4200c00800401030186650b1030f0134825407000e03480110b07000744806c8401d03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 324816537 1250 324815287 324815329
    0x709050906040c120206030703091704061101060e04081c02040b03070f1107050105040b0c0a0510240509010b09120a2001030510090903020307060203070c030806011d120a080414090c0315 82
    0x140380b90f011203400900c001c0c40c10340c446001cec01c885446c840d400c584595100a00041581c0304000001e5801d004aa1005649034540e0120f0010500c0b0300340280600c0d0088034203090004240410b5035081400d44041d07141d9607855490044034207400c0f0b515034030503225407404a101803006004029020f00a03004400501d4102e50040c0480d0300c840380b0300030b0080440303501070390f48480036842e600d40a100c902c2c402d03085c840c41c40c22691904011030040c5c2070511402c00840400f103081800359503407058252001422030308480000c02c80e810843ca0714203d000d80303070a02511110000c921540640a05e600c00d210400d8070f00c0e426840e0104000c050500110202e00b140010010341c0c0004640e803001e54040d205a40d00d048000499190180c0760f070700c001d80f0b204d0602c0140109441848400c0344104002030301546c1c07010244048a41b100c0c41c0c2180e820000300030321710115011030420317103a1030400f6a6100441c2c6080894407443c41c46001072205851001c07001c100d00c0e8152800d0704142100c010a50401c3e018 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 324817787 1250 324816537 324816563
    0x60901031806020403020f120d0516081c060504060b07060c03060b0c03090102010501050103022502031009030e040b0111100203040c0b070605160f17090709050906040c12020603070309 81
    0xc015503180100500702d039096408501441582042c40a00d0f02c0c90340141c1d06507600c1c901128200d941c4684d1004010100440040c486c0e045045000c10703c0c3c207007540a2109501c44010300c6a1a03078002843e0300ba0311500380340004c0090540f8260085504807042c07443d41501e0006651280c00280c012400000140354540c40002000ca59600091032a408501d0145071192040c1000909484041c1d101c0b504150042c40076440c0744c040c499500300b00c8a8034081c05000118103202190501e03041c50b1004045618042c0713100c00b4507030070540031001440120340401c071103818040107681d1428482664945640810030b910945c203901d900641c1c00038041c000c44a0940d90300d100649140e4000e22003180c03115161001d001143c0741d017005120300c146082c00e04101e007140b001001858280c42800c4200084407001c04508904410301c14000a80444203080c4494980890001c3c2d403198103503021200602041c80000311500c0c800c44500390b03180e0090010f49075444405080780545010201a00c454641c0c0003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 324819037 1250 324817787 324817811
    0x32a060f0608061009140f0a020903100e1e151602070308130503150c1611040e011e020c030d020306040b030615210d03020f0705010c0512090c0307030206090103 71
    0x40300512503100131003c43d200906100008007601c2001a06c8803681305c00005200d4a402015040e81e448501d00d1030061301c801840380000e250240c4074444418103407170124007102502c0c010400c0e0400f01585440c01603c24250000c5a66031541107406140c030421a5010607420816103000340c030814054411521480d840792145d0345543d100a003000c40205180300200581d0070306001c0e04007222080e0307c55100d2481c01424240140c41641c00c92045c404098030440c0800400c4044401d407000003803c2045281d0108400500901c0c1e800851801011000035804091440f40200c501d1603840502460030080392500580280d040541031544c040d40312003030030703000d9101000030600c070300e008025004414800c1018040001c003a1540c3c08240e052074240100000d02c0080e4822000701c052a005075607000750601806a030085410090240d424035003508516644400504050001c424100e402906c0d4924400c3c0e440790580708258140c2c10a030401c00c0549400409020301c48030605010800ca0041d403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 324820143 1106 324819037 324819043
    0xf0114030c060d09060e1005010510050901200a1203050a0b090c091f0c030206161704020604181a030a020a090504060209060313032a060f0608 63
    0x110f010380d00c0744941c4548850340c0c0001041004c1c41d80802c41d03e49517a001c03040046010308000012a503440c0007204403010100c0781d03d88a18000c1e203400191100019000452403160700b04001d1410325105021401d100c61060042d94810401403c010301124005400b800031203103040c841207182d85a00360017036003010903070390440c1e106d004000c0020301d40c01c14005041e070559440140080826000000c0314100d5201c3d03002d071841a56414044486840318401c00c0d4001407410100540a80406081380c1d003050001d024149400e88400c000c484403c4200c1d1016101a03030f561050005002c0d1b60a1802910f03400c9000e06031242140c1c0000384011220b01410311801d50f510082010400c0550440b02c1c0541d02400c00754482c5404a10340c44c28450b4042c095002c11200c3c84019074888800c0190f00f17400909100c076001c4a00280c0314040206030141e004403a00f5030307c0038017080c024010 = true := by decide +kernel

theorem cover : BRFrame.Cov 324640287 324820143 := by
  have h0 := BRFrame.cov_init 324640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 324640287 ≤ n) (h2 : n < 324820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
