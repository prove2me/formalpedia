-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2884
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:01:40.843305+00:00
-- url     : https://prove2.me/submissions/0e085581-75be-4c70-a12e-a470e243b975

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 518525179 ≤ n < 518705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 518526429 1250 518525179 518525201
    0x203010e060112050f010507090506071b0b0c16050f090a0b0d0c06020c0a030c2303032d0414090a0e150610110d03110c0d030507110a05060604 63
    0x903851101102000d01440028002d0a0300088030000384010308046081c1500752001085507450403040040f0b0300c0e088501c190a5950a40d04980c071a8001e2034101604810081e050803070302120030380044c2c4c030300b4103800070481807500409503001420700607544041200f55004441c4c1c0800d07000c2d14110242081e0803c203511148454000c982405001c01041c201030240c1c1080d1090310f08008103200c1c1c1c9804120000b00003000b136490441d81403075a240c2855800f03d034040c000b49103d0b1103c018a4039007640c8800b03600014014181c0c0e548040c0945000001300840d4461215a1224940c4e0701912100d10242d03421a00c46140300300b80080c14034200110500300911002220b540d40f120000455810020810800724800344400c46017880f1b0100100e50410407001020004802c00041c4140d03000300c0d200515401030304001c140d401c05426140c41c03034040d0946e81e200171b01c80c4060b01c19003103505410030303401a0740a444100c00342c01a101c0c0309480b003031036280142c001c1d4443c002080b114241580420f180c09 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 518527679 1250 518526429 518526431
    0xb0409020724050612060402030c100c081b010e0303040f0b040c09020d0c090b070c12051219030b12030a0f0915030207050d02061e0405071809110301020408070909020301 75
    0x4032060b00c41c410351840b007802000308036a07501c04000c01424801c00c3c1c001e901c8809401412145010f50000c1e60b80c8240140c01405100030f000d0108885000f8482c080d00103511080003a141d40040c1003440c10400c440d45c5078016582400d02803506500d000c02100d01540e08912410714040c125204e5400038280900202c030480b9104400090300000c5d44040e03c20002c170b008021481090b00203000f020850960840c00e0b0071502000740000084200103804221000c03081103240c4c0c80c1080c102a0705203214505103044903200042c00003c621040340d11402d00b0103068130704002110903001032103036401c80000b52010b994010024911414003558010700d40140c14a482044540c0b241c01c000b800342c3c54640d00f580407a030041400000c20000b481007a40d900041e01c000d1400b803402200d2048000301e0301c00c81d500100c5101f0041014014140440c1005e0704807400320b00d00c015281d12440300201075015041e9540000d04045d015a89018003c581c222400700c0b0080c0403407400c01c240304d0010907410130b04a0740341d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 518528929 1250 518527679 518527703
    0xa150c0c050909030915090d0209060f10020a03020f1911030a051606080f0c031b0d0501060e03150f01150c02040903031415010503010e04140f061006020102040b04090207 75
    0x66454280d0b031031090030300c03002841c2c84121030001d01030645107030b451000d101c89003400b4080c0075841c0c8028a00035075804980c4111181c8650020503400102a1442da400c400f24a005008403038002079100380c9584a40e085400f841e50303d03030f01c442d103604031054050001c0c1c21106030640841d0f5885600c6081302c40090545030b55800c0e59403050315207488c07440c450a42c0300c0c210b07404029464120f141140e1100e803044d054426458603412a00513403000a001c1400b5603e102070410040003a0320941c2c0d00300842c9242002156102d4070080d10310b0b030040c18800c0c880d00c515031580082204c0481024001c41040000f1181642070000041100f4a8240d04004000780d07102c141c0056a254029a04014040c0e2400119080110500c0b22210801040c4113800c0b03d1141ca124240d0f40d016040728119040800c1d44081a01c662910300d00d20034400c42d070b2060500c900d115154615030f0104a05004020100048960070313078500f41039090f0f020354400d162400100380003c1000070b334207800818003544900d04880345 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 518530179 1250 518528929 518528939
    0x3021c09050c0310241a03090316061d30131d010803040f050607080903031b161409060324071b0f1407180b0a050a150c0c 54
    0x113401c4880000311903958441c19180c2003a40c107507007a00b94202c0c06a003c40180c6003448440315090000c02140060b40e9000800507409880900c141c0d03c40d03880344030000b85156920300b4850b000e4030300300780c0400f5030210381031013180b6003c0000744aa11100c902c00081040c1c2d95040b2403141d054070b143c5101c0f21400c40410202000300c2ca4617180c01c01914840c000c2024031444207421b01d1030400141c020749441c0c5c3c0b007008140040090f0b2070206c0c08549048580a0780d4214914054499015200e076407078062201040f5070ba00103c00d1300c100c680051100c0c04442d040c4a0790b03200208600701c40e116010320315108005006103030500030030310f550043d00070f000c03200d804485290405952490000200c292034814043c0300c1c81c0c0d075107c5003007204445143c24402c559486034682c0c05d5442401d00300140340718611501c2e1051000144420ba0090038040b0101b2002507800c0380400c0541200d040f0180301e031500400110351460511042c1c425503170710f1961b6001c0c403400000c05a5090381e20b43d209981c4059407010000d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 518531429 1250 518530179 518530183
    0x9230f030a06090c0b0c21070c0603020c250614130f0e010e0f0c0a0c080c0d030e01020a081602030c1f0e070506030a1a04090b1603021c09050c03 64
    0x340340700345000a80503040c0d080c03c450f40401342c0c00004008504000c100004c92001880c82c020a00290040310041484184400c40b0b01c9150001800002040b000003015a00b41e0701801c103242d000d41c1a1407200c0e101c880c00001d0050060740d8100c204031100c1d02806002e10426204224602924800b071400048481410304980c46500c100b259075011141449064001c03030b012401420035060400240c03c0801c0b2a640d20000140801c6020728040f9031003010500c541002100351350004030742541c900c0340c1c401d0591503004007042d42000c01d041845000d02100144200c0350404000d40d200b01098591021200a041070400c03400e0851000b1b00c81e14902c690244842c01d00f03000c480e103010290528902030503058400c034010396415504210f01c01c1080e40c584000b181c1e800f0110982c0056480761400d030318202d070369105016640091506411904000c3c03070030200ca024130241513403042d9440103200e00b202a8480d1607400c0c850311300f5040d0000c2030b441c1c290700040c065510031401e0f600c20850f4940441c1c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 518532679 1250 518531429 518531443
    0x1b110a061503031e0504090c170406050a0c020f060f0c040b16110105090f0907020a1a0106090509040c0b090402071a040209060a03050a1b0b0c01060501030c09230f03 73
    0x40070510711110800c105500020520115404034400300c2c04180406406069401248a000070f0a0349a01c40c01803079030300c07501800e61075804008000c8207604060034004000c10301241c0d00d04516142a1101030310500008421400740400c00041c034891f0b48117541c444250001a015800c0c4450a010214000130b00703c000e07000070b442d5808401d500008a003881e01c16007400030820381c10300500f0042c01c2040d03111700300515101c4100383c802212039118804100d1401d000108090000d0002010808072002d001400034108d403025516012100d482d001000b541c918251801015900c0301c1104011521021002d444401c0000340010b00709066038803060255111441c1e40e9140d88840c00410003145000030742c2d41d4100c03900703550400d061400e44d6203150f0f9804003080b026000391809603514001851410b004c40c00b40c080c0c05900c2e5103840b0010b000714040d14150041a02203410520b080300080e10400e4144126002d06d92040c46010b01c4000441c00c141e804001c981d009002d06009402580302003140f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 518533929 1250 518532679 518532701
    0x31f030f030e0415031e020f0a0602070e1605160602070213090b0f09120c030c1615020606010c02040b0a05060307350609150306040b0109050a1b110a06 67
    0x90030042c400c1c00400040303030010f000c048140710000d181800421a02d41c80c106011452210000d16402d0070b000144400d02114665648000f401d400440e656a02148000c21075881031480c00c150341300c02040301d1100c41240442c10002c1c4c401d1004014110030010b140249602958005181041c9a00481e003400e541e01c4040e6080b940701d00c1d9030700400560078034a030ba0111050042c140d203820212240e50301c810058070310000114012031111035401081c0216112009140210303000d50080020314481c1d0348083c883c4d2080c45401c00c05818042e400403c00b54031a2505a540c80f80c0b0698903030820000b07005034566103030456a4404042510b0301c81c1c0d8000e41c02074441e1703118030302c5102062680030840e4414040490b2814807251003800410354040e4240d400031811200c03095580c0c0e8500e0241c03161002041c90b81d40c140b1600092105204c0210131690594004182c1408280d9854001c04240d518000b01d094026404004114000384105043c1000d280801d0a41d118402d50343c035084140c1e00f41c4051 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 518535179 1250 518533929 518533937
    0xc050409080c16060801290d090209070c020d17070b0a020421050316081e0703030506040b1003020a0527010806090415020d0e0102120121020303031f030f03 69
    0x9000300b0300100300100010020302d8580b624065091020040c268241171052454800201d00c90074140d08907010841d10a00e50b412525841e007807050421000303402090703070903800f481c1448003281105100d1401000d8880d006007803400b98407071582da9500035800000c2038038080354003400180c2c00500e5220740725001d58400180980c8450404018140c00d80140104105000213800420002800401a41e00c02150300d5804080070400f810081e0061144400c082c0d080c003030060018800f550000080d1010030300039075003007082e941c6207400d0104803445140001d034803000850200159520a800500391420755140140c200040710300c041074810141d900f4105002064410b002e074a50344a00100d0b44144220784070318060400380c6440803080e415580c12850031b0f800041400000c2c442d0f412913841c50720035030000c40d03848401d4084445926000c0c0a00c051030411658059400c10080190b03200041e0002d01451840d00c0e10a0100d240301342540130446021030070140000400d034a0440804039038007940b1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 518536429 1250 518535179 518535187
    0x4020705010e0a0c1d1311060a0207300f020f030f101b0c030e1f180501140d0b04060b0a05180102010507090302041a040510091112130c05040908 64
    0x502000d4014045d04554400d40c00202070101080744030158681064055014080d2070115091841a81400718201c2d0f405c8580000e07512921580064848200c031840e003098403040110002902009103c0790f41c080340440c288100030b0124a51030951180c4601c010584079008100e440400c0c244241c1d801d803216603422a0b2484800c5245138045c00c660501d0b444c0000100c096140009002c060b03c11303c010b01003140c24441f1141c2c603242ca042d40040d452440f01500390915040130003c0c0490b2030010003031001741503907000003069402030007501e13a1000c40e62010b07401c0c401042c01203801070004150607075105d03484100004902a40d04000c00605403030795140340d910384050240200b402c002410072411603150a0401c58071303d502096000941c2c2d411a004102800304690200b0742d0700460001543c0245000207021002d0784c0000e08108503200491b0074040c00840c604150350318080c142126450503400800100c3c15400300001000f400e111703001d007104094403100440d00322801d0708022550f00b00009 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 518537679 1250 518536429 518536433
    0x7021e10050d0b1206071101020c060f04030f030b03060109150f12020102070f0617070314090c011710030b07021002030408030a0605030616030b131506080f0108190204020705010e0a 80
    0x3000d0600c0c3d400c0d05603080750000380540e807516510b140c01030074002004140c00c06250903901c01c0d012079a41c4607140b4110780c20b60911a10010003c1803d840480c00319691803214a0340b07500900503089040801400781c50709a103020014800b51020492110005403421804540c12543c250710f03c016100800b05200c4200075440064a0500d03140c01205005094010800c1145e60019285414281031001c01c40d083c3c03510b20b0250064840d4802090003101540c0402031084400a5404418102680c42c0b0000043c400006405020155070311407507031407052030900115201c0b480c1c0b1a004541881101c095403554000041260802d843c115140d140c000240001940f1384e010381e4001e40400c802806890615049a040b0b58040d07461110506407148003854580c1e9a00c28a29088c07080504240150000642170015407901c03409101c003c40e6400c000300340400d42c1c3d48607050617a800e00e001049861840100030a120035411000c9911a030200260000a4400e00840103000070b0300008120b18a428 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 518538929 1250 518537679 518537681
    0x6151c0204210b06061c05150a090605030715110601140901050105091804030306211403190c06150806040507080111090d050a050a050d03060602011107021e10050d 72
    0xc2c40300142c5030b040c0341c030080085001c1590440c0c01c1101224010f07551903107070b0b03050ba0580d454544d40c01c210038600340810a518031008500352507400100c8800c125a84c80d222500700302c4869001d81d40d059400b2001c02c1c86600400a40800030f001542071000009040300c203007a180003403d130400007100c080c000c2c40044030304000d80e003940500380900f822828589600040754030352007421610104c04007007101003424103010364460406890000174142002105110241100303075809001c0301d040311111041c2c00c0443d0080240e9545a048503c1c01c0304916940b42c08071248004040c06855440d560740001014998403080788005121007005007a10b031a00c4d0500f00e01340b6006a0048010307905100d45260802c09a0084904401c011103c2c441408802d081040c50700c070f1240001071052050700041020700030000b03114036141c903895806008003034403400c04030f007038458000c03524034601420f2042e0001881c0ca46040b03135614151007001b45030038032801c000521100c54002040040745000072030b480c2c2c050107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 518540179 1250 518538929 518538959
    0x41503060b04050d20060d02071b050901030308070201060b0715050f0705190903060f1b0c0b04060e0a0c060e030c0f0a03030e03030c01020d0507110f0606151c0204 72
    0x1030701070505040c5418085440d103101c65000130402d0f01060900b80303812164841c0c05c04a810090100ba44036101e500c1d1410095000302401c2d245a132400e0541040034083d0410f450650300040c0507914241d1966800b9a02980c01400e41c20955480302d030049004075054000d070a0580c040c0100d03589415094107200c08580b0003419a0881222500c20003001d103810030b0031110800c0484d0760041c000304100300c081301c06d0a11a04002c09560134405940070003136482c1c002c0d0b1824940e0343c3c00c01420815013a800e442039408040000c01c55441200040c001c20b95560140000314000403e0b142140455607400d031640c070080d00220701044100301010b0f036504003000032600d44c1c00145d510b00403200012002078200f030305c0c03444001d00300a2009100d40e215201401510852141c00000f5510303400703402c1c0054090003044a028001501101603240303039800000d10340e8042c000c848082e03c00c1d901c0f000300f403204060072210700c0e40903103504206c01340c40e03030407400e84100300c43d00c800f4801a141c5040902c010b0007000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 518541429 1250 518540179 518540189
    0x1308060405030301091d0c0f060d0f060305010e060103050a0201030b041407030c02010f021611061b01020403050d0503060117090f0d030b030d1713021302120f09030307200f010204150306 82
    0x59031540c012803003800007100388407c0e03800c58000081081250004003944a42110205194200a40c618840c0d010f03402a4058034807400003440546003c0040c141c1d6010248400790455124030008070141d402580b08030480000500003040c07910f010014004180001c0d112500000c4c0c2d211011000e4903828030035894001800002503151a050340900d0040491035900603000d50019920350301e2640d105001c0b00c00210800d030b2140307a5058482c600764003d4000e0705c4155203a000d0246500744041c41401203910803c4144c40d06041400081d070041080117000340750300c609100f03005e25860301140030882c1c0c5c1011403481c0d4010440404200a050030400b03480803000070302645840414001ca85a101d140c0d00400042c1940c400d22030500015005502025034601143c0c400540341d0794503d009502903100321002e810b140e20584507650003913a20320044030058002a8901203a61707103828140780602c1309103440300c00c82d070b0030000116000342241e0255100c180131202c451407e014041d054040c01000301 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 518542679 1250 518541429 518541461
    0x30206090c1003020c100e0307110a0f090905070302130c140a08180a0c090b01021501181109100207030c080708060f2505221208130806040503030109 66
    0x14000002ca0103954004402c00245074022801d800c04030001c121724110307006e40c18001e0003c5e00c0d42241070b680300c0c0e10030300007508d0740d44990350f01d0038017400c0650510088031000304006a040b840d2203486170082140d450308444600500c1b0b0000090780c0e1300e0a24a4034010b00c480c0004030054040c20150402001c1e8000c1d030a0000b05120a0f011a07421a89065001c0c15440141d201e4820030002e180c206960184c004081a0140402080c040c54592014042d4a001e03000c07250b01080c6140d54094218003481411b545d40c04051103440076150903004042d11740801c1c8039071350500180c400094940050060a035005910200c400c209004220f03071218001d003229809009114241500c1c90f890b408000d007151035142e140c902007a12000058508c00c0020f0208118200e89820040010000d42c4248503030a16010030206052081c5040207421003202c402d0244d60440701b03104e070b0b60b41180303811a07240920f110040e501d000440c002c0901602d88107034404d1000d9581c4e981040440803c850810103101260 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 518543929 1250 518542679 518542693
    0x1f050103050c0a0804020a0b040305060a0506190506090d08040e09010506180a0b0d120306060809240606070c06020d02013803010609020f032512020d1401030f03020609 74
    0x103a0862000c40c0e440f01c5041c40c049180d99521b0012420050446d800300c0da101200090000074003401041c62070103269104c000307000c65150081000408010440c0d06000303404280e90401451401c80d005010b80030303007c0c00740d0444d03d8551b01e0783d40e05a00181e2265580c91862820480200d6003845001e034014000c0b219480342880015140030100340c0240350f05181582d480740391415549034148081c442d0f9000300100d6808aa01c1c00c014090b264501c20f4001140c4c4000120b0101c401c04105410101410303a58012044116000039115540280400750466810800040821802500c0901504050300105814031a400c0000d0848090070400b1302000306038129840e021181800c2c0f11080b01d446644c01c2040d0983d0310000340100701c0d0340e1020704620b1001514230250800340003c1c0d48102685c4800203c16014030340e021a214400860500c00540380c03003640c250600042e8003820b141000440000740b68490301c88020311120b000e030015101140b2000000c0d0406a04202483c1c0c0140300c02c010b8000c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 518545179 1250 518543929 518543941
    0x4080a050105130b13111e01110304061d0f060a0801031e48080609010e1c0c05100f0b0a0b161a13030f080f04020f0d0203061f05010305 60
    0x6111009001a0348002034840d028040c400c0006d1020080d4000522040e140340b0309210364812407075404155408211000a101740601c40401501c2c11650251242d01c5001124190100a55180d11265901602807040003409841c0c40c0050b00642220342c640c1d038802e505509200c00c132010081140303060005030564990000742410096009105c0c02814400c0c40341814509990000c588a0840c0001996a9054030704405100102003181e480c4025114140c580d035048070b00369010124400134660003140002e03504240620540520001450013401490301d590b9040d050407400203060391f005440d011442441c80880c40b81480701c01d0101d501e501584e240001c20080f602845014040c4d200710b21422105102005040c010603a900f0f095004c40d6103412400b62101d807406000a800007800d00400011103400340e04c0c100c1c0030f0321020854880540d00c650030813415949603000d05401401940c241e00041c2c030200007a0f402000d1403050504800b0800701c66140c00c0d500c691100d4100740c03c2006201c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 518546429 1250 518545179 518545193
    0x4e0203040b09180a1b0804020d02120307060e0705210a02040b0d0b01030c09140138191b1113020f180a051806010f0e040204080a05010513 61
    0x301c500786030744240c40d8509000002e034038201c0314114403490b800d43c030200a16480746a0080301e01c2e0b805620130004140312048200c0700301c0000c40c3c000303400c40403103251003000d85001000d55001d841e5030401c6901d4400c5c15641c580c240d4034102d0116140e5804070409101a2609204000401c40c101c151009510100c0c510203648008030b20703019005aa46032070946c1180c54101603035180d1600001c402c0d0055a480c50301200303070031082c030501004618000848800b6904841014101c0302001545400011070074006490016002d0382075400c8801ca429480541c41c0b1040170749000600b1002c5410440b10341007014001e100006103401c4400e182986410014010440000c2c9648040e1440b0788410540001d0800900c101101c07605c16203404140c0c1c6003c00d03d849031440315810182e5818081a68500501ca0801d8200785400841103280c00021901e520800074051950300a150044808403543e0105049030f10a41040480b03402c044103ca080c0a401d0041075001107880080c900070400e5522a04 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 518547679 1250 518546429 518546437
    0x60304020619020f01062301050c0706030221040b160503010f0605160803091b0a0509040602071112030d0e0313051011070e0115020c01020d03094e0203 67
    0x6481c1d0742d80101007888040c402c03c04d001c0c2c000616002003000315150514440d1318840c0c0400c101045d20724102c007041a521800c19188140d000313000070559a400d1a82c1500a50043c082c4409520040211095016211140c040c0114000d003012134a50801d010950307000c1c6481d240072420b0180c2000100080b928403410034080b81c005240c441e4881c0541401d07000012078044001c1c00200020040c0074041c440484c2090800c0003e4080c0341440051409003d81d000140c400e86501c5140c00001501180c0650020810700e44200c0310300480c2e150640000700e070402c4458034415540d0010034116802c81c900d101e4a1000c0c070920000310300300504001d034034a0011303890107411b0041200daa500c2d00240c0c003800302d4401406801c17090324902c2c1c3c1c440094090510007445198140324034074440302501c2d4004a11410500010ba01030700101031076002c10b502a242c1000100d48001c3e240810b42401c550076080301e05000c1d200d01c0402c180248040500c001c40c00d290700c0007100381c6844136106070220340000c201c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 518548929 1250 518547679 518547697
    0x60903030610050d020f0415020714011d030609010f0e060f0412090b03070206070e19031704051806040c020f06041b2103120c0801030b180d080105010306050603040206 74
    0x1445014600101100c85004d03902520035a40d0002c5070192455184601500c2540d00712142415240d07042007040b40e8915152107286400200b00d0020b2445500c500700e4440010f030325442c2c02d0104244103011034541070040b90166401c1c0d540e94031007210070006000d08202c0e118140010455428403500c072103c0000c015000400752001248a5030312035009034460001000c6003110151280f030820f00194035110200c0b071510014a09145a5007686001e08031604008450180382c1c070b420b421941c80710480075034a00080c2d2a0101440000f6107556182e28481d04010803040c80440ba00300001400b00340c1c0d0212440005540003c0800b413107140d4005080b6900c40c1e0449035141d000008081c4040d03103513405400c9810090100c0307000d204100c80002107004800d1180e52590078804031100d0000c101d410110110b00000e2342d5000401c08103c600c4141d40e0400c5010fa5407070300030f00c2c1548003249000103c02c0d200022803130503030042003a980c1504c20b22008000c00d4400c00d240d89040d80c0022460f100300284 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 518550179 1250 518548929 518548939
    0xb040b011404050409050c062106040207150510080106060e0f040b060a0e010c0605010b090a0608070e0112020c03340f2616051b0d08030a0f1107060b030609030306 72
    0x403030305000742002111f50b1031070080c01403541d0b00c3c42046101c0d443c00301801081030b407680c200007040c8207041c01d200300d4284030b0b006a400744002c03030346a10000c003410b005060f185030783d03040e140701041800e000e00c5480010401e81d2030b2841181409028000300702c406107802d80c0701c3e62030071084a1654441d14201c81e9250f4083c80c1400d54082c82d00c005854440c20590054800703803a03c40041016400c0310000c10148008550404680356669030072115080119113000004040c200c0940180d4007680c09003240c0d060b410409424018049100b0345950056980d6040200c10400b518206e9994051621500b441c40b05440980794540d4440416800e03c4550040944c400c10689c100c2c6c01043e641c282c4c4808801c40880ca0350389251100205c202c03d0312841c240c64500883c032200d00386902c0e03504801c0f4000e20182018200b504592961812a0002032141d2409525201c02102007541c611400c6209038016455584403801d40c10040111154010014002d0780803c1c10f00041040000c2903d07442a401c0342c7e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 518551429 1250 518550179 518550191
    0x1e010c080712090804060c060e0d02190206190c14030301260c030618012723070303201902060903010e0a0b0402042f0901090302130b040b0114040504 66
    0x2071000404111030050510340005c035000c80c0f40d0b81c0c0091b0161200d0301401080c050340b4039505009846038003c0c0a0040980d12a442960740012811246804036000030b01c0c50381405e100c03a402d41544102c403600e400000310511000400c11003284008484121608001c509640c104080707501542007030710982d140c5607196608003024140c1084048007a500207003e590302424a45510b0301907580100c100c100315420300d4409220100d006074180d407801c411305207203465048140c413010301c0e0004080d11080504501c00d1206403405e02041288000c0d40b00741d894003103959552020240c60603003c216251540c2050784641030184126082000b20390b0100e40403079035805281c1c00240105500910f040d500e003c1c441168080c044041d00c850710450081c0d50901036080843c0c810300035030340407007555914a00c4074420b0341103101105c805810041d0040c14601394858a03900000e0b8540e4480d50102e070344a48910303000c1d1a41c100303030040701080035083c00d00d0607500048542e1070200307000b14001c182c021781d0303a40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 518552679 1250 518551429 518551457
    0x20a0809130207060911130e030d05090106030b0103421d300903061609170609070f0803040e090a06050906010905010e040209010519080f1e010c0807 66
    0xd41255030300f40c2d002904008500440c9007490110b540f5040c00742c82142000c02a1101401d24020240c9160307403440a0b500e0240589400c80003810042e0078042c5541d41c80384c010001491140790503001e1802031102c120b0503043c201061201d00f031403040c29043d04800100c80380b20500c00d1f00c80201003904024000c284508114980f00e2540d0400002c0d40003440348600d00c1c11180c881c034000100d1214074081c3c0880000f0700104c8030304c0a06c584200305070964080c900113a11050000300400d96101c0d280f80c0307900341503a50064241c1741082681d818503a41c006005001031040c042000c0b800500d200d8011509203807425140c140c403405648510030520005000285c46000d0902c00d61344101d6020350108014141004000d81c0c0b03c40900502e900b1038038001c00400d242d0b12115216200b40d50081c04c1080310313820306007444006c4401301822154004801e2010521140c2444640c03032044920f0010680c42110544202e07901d880301442e900342d640b4003041d85d129242c2c885004da5200c003ca00f0240c140c1c140d00c3d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 518553929 1250 518552679 518552681
    0x824131401110405040b0f01020c010c0512040902031f05150f040e0403020708240109090303020903151e09030f030702030f04141003050f010329040b16020a080913 72
    0x308168042540382401d902c810b003040781c019205403181500d0800c0841500d6042c4600340049003251030169020010902e010342c4940b4660401d00e02c10029100b80e00400051003503a80c010b03820000c0300c0c03500802009684402c1c0c0e420401d020310b01c14942041280f400012601c2c50205407180303e4040b90003c1d22400e16000c000c121802401c14003040c2d0301074501801d000351102907a010f50407140c01007924500f11443d5011241010420a44003858180d1038100424010044000102c0c2410b40030b00c030201c5603a0301400705841da1801242e546070186810f4602e104898903980441d8404583e0000b44005140000241e8038800100484a43c1d84d80314445c0a130b285000c2e40c002a4110040001c000ca1004d03076041c420703e2002410360784080d0701d042503141542511421180700d00c4c0c41e016000100301103101c020000810710a000c142c1c0a0036101c02020405104d011a01951020600e4050181484521025003d02011880a0b05081040750303503e44480c4111401c1500c5403030042d5802c0002041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 518555179 1250 518553929 518553953
    0xf03030e0c0a0b040303090f08030a1d06070f050606100503160908100e0115030f02130209060f090f1801060827060a1b0c08030a02090303070309082413 67
    0x10002c1649503a03803401a000341d846400210300250b817000c40092406c0c1c100070100c054903011000b4509103040040d00300ea111543e00307817002080f502e402400e0040c0d2103000c000c2049600500f2044240300c182d080161420001806447c0a482054001c5404c1b035440020b59800c206001000c2d0303907440c50110112410410f039080002d103805440300c4503500054a80c05a00d00700000e000910014042c2c8403502c0500322144000340c071080200d1802d000526002c1c0c82206920300f070381c00041c18003c81c100450101d801c080d260980e524070029107045213103802150341c3d030143c1c81111a280d01108c3d20b41400b041240c1031260300c0600000c94081031074034000007407e81e40b44101403c80c021607540d202110707039100d001340d42050410b4509000100c03541003d403100510600781d519480c00141c3e080d0b5075540c041e400100304403071180d03081c40394003040c0da0180014000103020741d44816072181849941410100b0120340300c0881c42d0741c2d014220b04007609990440c0e001207043d210040c0c00c40740342403000625103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 518556429 1250 518555179 518555203
    0x1d03030307020a0507150e0d140f010b18071b1e080405100c05030a051309020705060f01090203060310020711100f14070507120f0602181c0f03030e 65
    0x2022040001c850b41c001448180103000b0405c441030305585100102c544800b0020f100000340c0c20040058040c241011103407080c0740f250701020461a03148126905009149201c4202070b5152042101146800241a100303008804c102500609084102400759108810365a07141a005100407050207942c0b20300f00e100d8196404000c0e9840c1d0903142c5100d103a032140c0600c4d407061003602c401302c40d006d118428500c03c15074003e0046192070031603030059500340c1128800d4004c03031500302c1c004030b511501400a803c89520a1004051504184146100c03902c41600118016031050042180b15513000800e1040007144010041c0c0da0409420910444040c4044541e00489600076102e241940072840080030009a501c020141c1d00c0101400e200381300c3c41d5009001c0303501003601803000301807020500c0324040c03160380900e62540c8240e4420003660081060444101102c1658044904020011060310704500c0500d0f40c110500e9a190b854205c40038501404040c0c2d00d00324800002010411072058035 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 518557679 1250 518556429 518556433
    0x10f0c0f060204030b010905161107050a081509160605030604061d10050d0f110105070b070e010206061c0b040618080c0d090f060503060301060308180102150112031d03 74
    0x84540d003469406940f0920084940b80304540001500d00e24520413680100d01c1407003a4002c01101840403a1401c00168004000e4010b120001032035660b5079507080e0003803601c207000d0150301191148042040d0802400400309410450740d42c2969402c01e80050f090742e0507410b009460307031100700c042001070104d80c0018411040000445a00c0e4550307c50240c4600000032100e0a8242c80c0d4051290348000d5540042c1807140001c80407000a400010003a48880189422800c080c940d4a48c201882b50507203015020541c5100e041000796814000c260388010140c82c940c4a00100400564034516208000307013586402c2d401044c01c005060304082003030800300303025101e80c08550400804036403203880045101e104440403165494000e0321588120351020444a0520340303810000c0c0c50960006041d5036240d5a160004400102c0c3c030b030044d00d42c03007445490050120b002000003a141c5100f004e0000302c1c40c48500010050000c0c0000c600a01315407603c1c00f202c7c24440020f1012095040d500015418 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 518558929 1250 518557679 518557703
    0x28140d080a0e010609180203010b040b0d351e0f0403080d1e06050a12080901120902210c04050c04120203011104030f031d030a030806060706150602121206010f0c 71
    0x1620007200021b4045000b10003c0001c8821380040004a540005800b0742002e0b006184101042c40141c40a00100355840034813003041510300f1201c42407044010400c0714010109848000941d48060141101014003c080c9441c40300501d00310310340640d20001b000c214000400107222012030708034a0b404842c8020040607683e00c1c40c102406054603029184c000c403025040000e694065603400019150028000f628200300c0c0001140c49000b6031138000308030342e00c80d00b2100c0161201654418046e000c40c170f01604000c3c01006250600145804070f6200d0703406c0805000f41140140111003c50b00c440c1285003c5200c00c0c40442d0262190580b0f41c1000e52000c41c0c0002840101709070b51060381d02c01e603542790010617800d50510300301d0120a4500d4040d44001c0912000030300480413640c0001e0010441c2d801c0c40000e40d142002da6102c1d000c15030159010311400c2103080d40401141c0448551042e01d14145a04108091084e0304018100b50400003e14104900c45001e00440f19980707070008048004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 518560179 1250 518558929 518558951
    0xd02210405010e01241509120b06100305060a150c0804080309031603081207050903012a0302160b07032715090203031b28140d080a0e010609 62
    0x280402e0300d42d8140c0b13500349080c44103000e4040c030702176a40c00c3e40e0310910b61402c0e00b4000c02c1e007414841c400541d824003180c0040490801c640703140300001103116120010482c5400ca041c0a000440c1220b59001d040c240818020141d40364510038040e01d000d0410084801501c04045034a00304100014005a00024002c518004040000c140d200010f40c00c5800b104c0c1c1c0f0040764040c3c2005440003400e110010b0102c1d1400301800301c9416000f840c949002c506202e940c1c400642159400c9015000303440590f802040b000c0700c0f0120004040c2c00d5410111306141e5441d4604078185a01d42008245449040024030452301070b41c400c150046500242d8000303410454207003598042d078214180c401201c0801c00303a5071450540100204541d0180c041c0d82041c0040031558a44c070b0242c0c890700da0758040c01c000e92034812500b090345903000039140130501c0c2501d82401c1c84003c0040700c441e074180302d03001070300d10032025a0000b0010f500141c11000002c1d241012001c080e00610b42600300d030729518102281440c0c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 518561429 1250 518560179 518560181
    0x409050102270415050604180609020f0c01060603050c09061c0903021f0c050909060406050910030224120c0d05040c03031106070815010e04050421050f0d0221040501 73
    0x21102c40c2a5800c100010a404048591556a100310f56220100300028460420001c0e00c0b50443e50303108030045411521501c614083e07030001c1486103120500407400c503402d04400d0080b20010a2141420440c0f42049100b03041c01d4410040464007071b030000507480c40c4901b808414010512000c2c01c08220800e407515000392a10070618003010088202040c0205000d03130f0348038000710700119446441c5040842c0b02401301400e0000c1440345c0c095510040012252170758011140b04268080c0d1307081900d07085104204d071400c003640074400c0014002d070b03015203035244060841e10107150130b0ac4a0300039560345c00c0000030300e8850551440c010a090005100410002d440034000f924826101c606601030850450769817503030121741c4280020f0070880401c41d410002030b20f0100861061406444102c00f880214080d11030540c2d007120400100f0000030002e00d0071100b101e004521618000c2d01e000360300107502a240c0100b403195000340d58000388010304410b022404491014000d03548250602e07080c10198 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 518562679 1250 518561429 518561497
    0x70c090501260c0109060c0f150501050a0f051c0f05192009041e0506130515160513241116090c0e130c030b06030f04020409050102 58
    0x31030800c80c0b800000d00150002c14803198062040e56101c8400b4a8144110b0310500d000c80c05075285a10086235202080d1990030428484240e0750001c81c0c01c0d4581000c0c07100d40c1c0c455501c5034054a6002e0020300041c1d41c0c1d4a922403c4403850b0b00c1d5580c13803440713604042119400d40980101540304003030301114210070b882414842580a003003d00c44c0c0741484803603024046018010642c0c0702c2101d000080000c1c80b130302200034030003030200e030501090085569101d02c0d280307041d07408500b010741e0a08950108402080822000c40b064016000c2c2c2c0d05012078120711449440d0700c10010305c1008a801098070107804030341c600500011a0034120702da40309044503880d10007025000001640101c1a200e0a94000741421001c0d03025112840c01a142c107061200400e80c160000c1b00708024001d0a1059680d001a603648150394060006a04d5078001c8028040300d0103c0d2041340205424804c00c4080325130f0000481d1310940507100425922210b00d0f01900a10540340520019001600200f80b4245800d0b001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 518563929 1250 518562679 518562719
    0x30301141c1b05041a120102160c0503160317160c180b061606020708070506040b090d090b04120f020307060504050405061206131a0a1e150b070c090501 67
    0x501c016440d9018001036410814283c01031039403071705048140f41003e201c0007400c09280000142442800011400302d4580c01320305980c401c04a82d41441180350910040082c00d03203d41c500c8070340c80c5c9140c1c0d44500d0034100c42d038a52040305000c10034000f0034114800c1e001559603c40d0326240011b1721042d65403007407821000414015440e1078400700507400c1000c01c90300414410ba00c6480d00e60126526400a90b21402044404501c1880454001a010004030340034601c42e01c0e800348107290a8120a00d09445401c208042010700c034810880412000d044506454a080c1820302c2c0c1c400782d0400c8180c90030400b0b0025018842c41200255213540b00b8040c0043d541c044905200e55256a010411600c0140a1080c020781010f030104240401c51290000b1051040700d010301242d01207151841c13183c004603070048815864030702c01450b4101541030000301c98006002088000031000c020070701030b180d40c003901101d004002084030a018a0003540001054091024080356840300b01050210203c0313600c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 518565179 1250 518563929 518563973
    0x30d14092d010f0e06070303020d05010e06090a180201050307051c1d030f04060315170606120f1e010b04020c0a030f020703030804060c050c0a060501080d11030301141c 74
    0x614200e0b41c803440d2000d400c50b03401e980395004040e5103010400c060303020400440a150742040311035590102c0c2e004585c006c10880c003581169250120900510b07440060400c014140b0300b00040040100c3c4e46100d00c6640d80a1902c01d480e03944228041d2114403030190b0b800c003240e00e005400e11040c0001d1f0010b0900301b00100000c099062130f000c0c440e03640c0c02030303250b1040508418001440b0040c842d91212401804a5015401440e681c0500032025220122602055040041086031504000520743d04901c0810000c00241030802c40d000e8464900c42200b250429840f0807003541e0b0042500141044200104110f607640d0901c07200e16507034404040200c021a0b0a181011021400880c0e000c04498140d1107014840c0d64590302c002c014881c0c40104820b000042c402440025010080640480e10915000910394140303694289001d24500300981007007000d494030a284080031040ea0304543d600400261030700141000965843c05c00300f8820a5000036188110510030750002c0c500b020304184003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 518566429 1250 518565179 518565259
    0x2090105161b06020d121a130903170606180102030903010c08061002010b030304170a06050106050d050f0618090c060c06010e01060503161b080409150503010506030d1409 75
    0x80d0a0340c4405ea0003a225000c5a036858130728172540719640090141d40c602d505625500889500080e005051040c1110b0040740c0e03548030102003603000313201404c0041e484480440185013440000341c0070b1140c10322003141403400c48040e241e43d0f4000c1040c4c81021000500030300050101041c000e00854044482502ca0701030032030380b0b0034428018802c000f02618040d02070342c0f416040261860245640c451001108e1091080381000300c0c00301e2003458068120f65890380e581d800c20510010594202810b80e0049400c00028007203d60303190345080301c1c2002c8620f800c0b800b5a8603034401500700780c0c80da81140d030041400275240e00b4800340072851a040e6907003508001091b0341c0f5504215450f00040b00e09070340140111040c01350490054a0340300d041c2c10f80c0c200303118500b002e6030b403040300c141c01c03551101c00340540380c4500c1c0e04503030702d03106818000d410103400801c124034001e80042d58804403400c0701d0003440224040d11109451803400c50701c2c0c8000c082e000450402980807a034101c180740000c500741c0400b00c0c4d5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 518567679 1250 518566429 518566439
    0x31103190e1b090f040308010515190809010b0a1514040e01170601080712081812010b0102100b060304080702060d020c2d15070908070305070815040b070302090105161b 74
    0x44600e17000d04d8050b51109110382c246428000180c403045007070243e583d010b000d80782c030156a4811030014010700b9941c2d04002e04054034001e081d102c207442101e1280e960940c05200e9080d2505034660002528988101d0ba0303400da0728007007898896034002ca103000749000b001088019500d20069181803101045a140d80c0c0e036000541d032202c2245c007a0108850002e442a0b0204811300060f010101826964519070b2400200290044800c900d0303500d000d07519402011515030b0107000f0b0101914108900b840550740e1600014060301c00208020501d01c0041200c40642d2100d1080e6410065110350441d40d41805030880769440808000100b141030114a601c050b4206109101a05d03445850007814154842048a0a6050010000d01c10448402400684050b04101000095008a0203043c1050038400b809041103070a00380b6403010480d4406010000d0362006415a00450600d0010b07290311002c80120346910074000c0010f00381c4000030799030050020385a0100c0081d510101c1c150303015039440f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 518568929 1250 518567679 518567701
    0x80708221e1b1410090819020909210a05090603011d0a18062007061a0607120809150108030c010b031b1e06030708010603050106031103190e1b09 64
    0x58096460380e8007400c0b004407200e00304818a000c4c190707114140f031207905032200c280b01d140000301c0302008102e0f1000822030041d8100b00411715045982d080282140c810742000402c003180c030030204da0100950010b01c44104505c1002924000b20b07000303000c680d682d42d407142403a038526042d0001886020055011585081c0f0074418074245840361041403003448007079166803006080200c0120081d400040715400494013580003050814071802e0002150f680d17011000782c10380d500d08203490090b07508001040c00b00d000d040c0c8000b921401407902c0180760b0f0b180e0b02c2650824400d40701050010303076158000b003160a03001c0081c0541c2c1c201d140080101000c001e00700756440100308000b0000142c0d401c00c0c03a0b841d040c41c1d507400000a003038640440c1d00071a184003103115039004403907485c006000304005100081e4540921401041c440ca024803c4042100e840e00d0b036448042c040100c031040302c1150700003140040e0418450119144182d48440b40c0d41078a100c4c606002c0c841482c410000c0400280c088103030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 518570179 1250 518568929 518568983
    0x50f030304030f08090a060e030715060b031311061603030e010b0109090b040207020909010209150403080f0a0c0203070305010b040c140a080601051309060f06080708221e 75
    0x2560f503000c501610388005603500c804c0a05401c485010b000000030101e90140500d216195198008603501e45650824141003a004004030110600700300003004030812460540340c02644254035541c050310341c0d10f4203841d9482c12550300c80c1c1200c0c1c04a02c2d81c0d01c007800e1aa14403070741400b230340303052106400080a05089a569070403c502084114405004200c0e6641c082054114080c000500d000115000100702600445041e440c5a400240f003003000e05100118001c41000250098105411592080400d000c0c5030400c8040030b1021454000c0365100d0400c1500741034014080c2c5103215102d081040c082c0c440c5814150140d4140807010348443d2081c0c468840312004040d440d0b081c09a41401100d036114064102410400f040c40070315011858500090020100001c0014510303141015004010300c0315030191050050000801c62aa40c12618080d40040101201148955400c41034800404031660281003900c6202800c01b008003842403c6d2600740c02145d040740d8044000d06013006002c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 518571429 1250 518570179 518570183
    0x70809030a08010b0c16030602040314120a1d13200403020a050d060b060415030501150f210e03031008030a02070905040804051507170c070501120603061404050f030304 74
    0x1c000e0010014103100501a003a481720741030540d18840319117038103407100300c0240c2c1080c0e0310168002030030820042502c2e140d00e10010230300090010391426401c049544e01680b4050710520070b601c1824484180110f224014091008000501e081e02c840724000041c40302d1400404140c0303254003001130000c0c491081c0c0301220ba005140000c01c0e400d01d03003442020300c0f00000c00c9031600e481c0c0030300660903500c40000e07002030805403842282901904e24000d05a50042c4d00c0720280c02c035480c1030b116403103610002c1641101d1035418094a10b00080d0109408100760203a00700b8a01d00d802c10003082d504001c40114000c0c4200690080c00701e80b21a400b40e1030348a222915000b680c801401004034040d245c005680c407e000704803460501c0e0352500030030756070440c451044800c0c0100007011410003035805900041c8204c501803003400c0003816814156619403034002d40303042c42884a54007440703010300d8008102541e48060240070b09404650700e107805020641d02145c0f40d000750080c1655640700081509d1140d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 518572679 1250 518571429 518571437
    0x1c060b09063102090306011217040b0f0c07090c0f03150806040b090309060f070615050a05040e1905060912030903040e091c02071409040b01142106070809030a 70
    0xc2c481d145848800c0e080e407000e060050303001d10130030610341e070248000c0d0f0007884080b65800302c114541c41c00100c42420301c01e00408820043c041031100002c0c1909039903040c031b120000380d40e6980c409040746280c10304c01d51100700380c2810140c900304602c0d0b010022641c40b1030f40340c4042c003105840520020980c9814068810140d2015000802103460381c28440c1d046401c0f0780a8903d010080c10100701270394040c07002c5641c180000514407040040070701c0390f00110032010005058603801d00700014440e01d40351180034465038036a4207031445030106101c0328821104d0003081159010481c41c2c503036100d075001c5034401c1caa80507440d800d1021070240d404407441502103001031450141011100d202c400000750069540744a108a983c121a80b0200c084109403c0781c1c0052092b986441650543c6810410b0581e016100701c0d0140000105050701260640301c1804151140d00f00c00d43c0459030210082e14030320b03074088000f040a106044c010803018040ca10644d5140714075682c800b485030743c0e8840c12525000007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 518573929 1250 518572679 518572729
    0x60806090c130b070807030f05070302100c0e0402130302090711030301051e030609060a0609020702030a06052802040302040506040605031507120c0207080c010305010806151c060b0906 81
    0x540110004001021a0401503800d40d52145480700b0f464005040840d004d040c0010300500b4107410520710200c1ca05185003662a0075215038000f92502020105510026107a607942c52500c0d0080c40100394419001d842151104048815040c030103803148001d82c06000d02c000841c95440c825580350605501d10401140b0356440c101c28005080c0c80e2120305450a44951100740b1603950602080d40102d00e400010a480d003030840603a0b044071059404401c0c1584100803030001a10b021803032100481e0401c10008aaa0350800e0003444d9403840c02100c624401d619080452448a5601901c1a0b9000307440420041c1e40d00403d1100304c030030600440b0360507480034444070f418005401c00d05502c041c142c40c01d160000c06140707401042d100020b10140140c3c1020034140042d1000b0000031119501c24a400e001c15413400141946a881c0640300d600c41003200e48290340542c455440d82c0807002c01003180c80b8404090b500304a0001c040400d0700510810200300070464600c1e200c01030071080c0f103248001c0808 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 518575179 1250 518573929 518573941
    0x1c26010509010b1c11030901060807060906032a05071a19090204090b01080c03160608130602041206270201140d1404030e0108100605161509030306080706080609 71
    0xc40d081120900465000300748142c80c009028051081c02401d45c0c0c106540340d0414541c2d050030358070035410903130310360707101e10003c000d010703400f110501c100c4800e8100000d003000329030103402c0305140d140410b00e03103c80c6803c00c21884a80c843c00410045020f0340c40c940501c07200c3c544202c1c00c09819210451202d0816001082030b090540c0300d0200148014400110314205035185071120030268804984e5400c414615002401c0901000e075154181e001202c1d5480d042510160020707070083c260141660740000c11000304806581210003405070f030044000703a402646083c01c081e00550301d2400c00e0310307560307214002944009842d00401c594141c540c825a1415005045040c1d001070100302c40540d144c800c400e50b40c401c10780741640154081d94460f0401001400090070744c0030054a55040f0800000d001c02c41d00da80320301030391541050190a4014032070380307050954540c4910005403010343d280504940c201034066102404540303550042d15483c0c0c3e07581d0019070700c81308215071080e0082804070010319 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 518576429 1250 518575179 518575199
    0x50d02010507050d02160b0103050115120b0711030d020d0203240a0603051504050a050a0b010c11060708071a0402010e040605060f0f0f070312060e1303030e1c2601050901 75
    0x40e01b501407100814a4030f405803921282c140f4282c4c025510303650f581c08907819559000f0191409030802c0c051161442c88255542c0c1c840c0b0340300410880c1006401032596110300c0c024001c89400c42c019540541d140c80803410407100035030042d260081038030400702c031034940f10f40080000340000700700820786400d035440d008098015000c000c11039910031008282c1c1d034001d55103612541e400f81030207580c000380505e050001c880c1240e003004d40040c14003d00001c0000003400300310402008160584400c2d440d9002454511903900900c10700402689d0400b105040b424180b0b003881c1d05c650b00076a55030304402d90a40910045491034000d0a800401c04c100d40c900400c8000014810664550310395460301030032035040e4000e07400413002100001c894080d48210a0300a023784409005a0640c00ca8035040a400317414061003102d10003401c0c152160602c6480502c240704124101902c40124045845088001014460204e08012040c4080301005000001c003445041c107a0340c0182a11030681d0a11036121 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 518577679 1250 518576429 518576437
    0xc0b0a02130806060a05010503060306070f0e09040516050111150c07050105090d08061e0112090c06050a0201060f0f0314030d0f020d0e062503060e04050a050d02010507050d02 77
    0x210035000c020200c10880c000421034018642c0038060304140c14001c2c02c00c40c801c5019840b0504000003801800305540c0e02141094111145003041c02100140c1c0c40155040140d1994080d480307000c1504010500c540460320700001095040c2000c1040c0d150b00041d80c0524080c0389000c0c950340501e10404900002c2d008003a005401ea080c8107082080c0e80e86c40a007900c4048881c9401900200c80c80e815083c1c00641d10341c0c0082044481c001041140400e0382207986220314502d04002000d441903030060001d92010f07903042d0f0055501d00380e4a0700c034800034040e40e011000107001586400000601020403144c4a0291034000b131440e14590b15580314040242103c50070740000380004c11480e8500d484612440105c0d4000b0b51b405038070307025203c070a4811509920252280c2d600a4010030095000303d040002a601e91036108411442203488110000d0050750406d02841070031a080c041031100005040840714414802ca0b1700c4500728a000301c1c00d0313030350903160b2002240c010300070280740100b00d030064 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 518578929 1250 518577679 518577691
    0x11103070311090a061110180803040213060b03061e180621010506100e010212030a1e0b09070c211b030e242203020d150510060c0b 58
    0x5203083c40000c0000403803401455000d880480c2003c0742118501000344012800107416000c2000b40035440b40d030105d0880444007006180202c0000000d0855413100c0c1001107001001d801049000c5d11562106800c0d031054030341521400303a000b5080403107602c07429006000d4001800c0388110402c0d10381e40090245024000381c1e405103480c29481414007100c91031200e0b1044100010900b410031105000d508012070150703400700401c2561400c12a6000170341e191524400740009680d9030740e90343e0320400521031034001c90f0610310a0040c0580c130041300e410000c201802283c1842ca951250303103082e030311700c01c60842c005c05005426403440300803844c84034a00d40307074591410710341000c0500b281d40502284800b07a0450100b01d41c3e4401c5206414040b07a04105545030000c15a40c0341141d4a0092450080028810004141446c618542004090040d008560141410700b0b91502031411824184240740343c2414185170400055003412402003090460700075842c1e10305420784548076015025401051 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 518580179 1250 518578929 518578961
    0x1e0405090a02091005010e04050f130314160204050105040903020d05030709090501030b04150506061804060807030c170a2d0203120406110109030f05220b030405010e0111030703 78
    0x50050f031610311409110b0a1140c0c41e15584c070b410840090101085144c015005504d400c0c104200c8101c4140c2d80d603001504440f04a40703104862900b107a00210024050b141180003080140e1340840c880310741510f0070304c00c903010f0200340e8980c0706200c220f408900002d80103900401c5910002c43c0600c005507007041051a00030002e42c0c85210321f2054a01c20380c41110b00344600c00401c024000c1c2000040f4111080c00418010f83c00c2100015102c2c2c020b20308503c0100b020012004031550380c0364000720051110000b034518035943c030b080c21100340b09603100d05140161030005410b0780d2200400c0f900d03501e551040ca110104100b1484905415004a2105824100403001d0801582e0208100e000d070f191544242d5940b2070424500074060313042e00c2210506681000802c900280e04002141e00c800341c10310b007054071210b0130405604208001049a00e4510b80c013200494002001d0340250310850081c1b00170322000040009040c221070030030111041e4014140081030040d40303c4d4211200e0307080700410f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 518581429 1250 518580179 518580193
    0x9062a08130308030c0a020d0305010e060f120106080307150506060a1b020d050c0f01030912050a1215050a120f02060c0f0f01052703040618120c0807051e040509 71
    0x10f24010154030607280d110046070040748130040c0c16810040c0612400d120f25042c400d951408120189066000d040e0510400c0350324104000b42c2c4458000d02c21203111b4000038403602c1e44e42c51010f5200d50080f20181c1e140920b00020b00103208071406141c0c040d1a020700000e1034202825000c80c1d003a0f00311314801c07600a9400400c1c80140c2d071440c400380c0c00d081c0108064030180d030003a000c10412240840f0746605050400030300030046005540480a1040341d420711603030300c1d480c03000111159002d18084540c06441d00000c01ca29488a05c059002c1c1c0d442551280c41039911968064400e60000310000c000c0004038101d000141480c101078085020b00c0300c01c0741c100701c03100c1020302d040035002e0707502d0070740c030b039074031420045001c024200c0c0d41c01c6807411142c40c8450015011420341c803445980a0207080c000010034405c0389051040080c0002c0010721f1160100c2007003813901e051040054420303458907105400002c1454a0a1058040d1041c84a0309280401c600101800060000103003d1032950040ca2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 518582679 1250 518581429 518581433
    0xc030403120e1006120c030611040f0f0824130503130e040c1a070b071b0b090c030606011709120304080d27020904021f09062a081303 59
    0x80030b9403445005850141c0b07a9100c0c01440c60007100c203150b001c1c0803500030ba49809408a861510a030058a40020010584544044003503038181301e50740c40034104034095070001803d66510f083d1502650080e03015030b403402d43e10b061080740107001660640c8d140140c10001c01c100368048010b1103c143d10a00035030b4100344003246542c81e000055400b180466070704504000c200401113810001030007142c42083c080303115030245a41c0c03070b02807a40000c0518200e040401e1215005d200c1c01c0041c50907d400c00800d0b08014a490382c1922020b959060861081c00c6145d030841c640422028420181a0340380039200100401110100002a00200481c0a0024200340000d600b0000b103101c2c60082080c41d0341e92011454520807038100c1c80e056050100c003039a100142c3c4400010103a009a0101d8401c400c58846000058031612035aa1030a500c2c0c0103412805040f6030840c0218040300d4440e113a04500300510784901e4540c001100090454081c0c0d0031804000442c042c01910b4414809903003030030659166 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 518583929 1250 518582679 518582681
    0x50f090402150f070501060b04030803010303120e120d0c09051f0e060d0e0708010b1509010215070801050a050a030f3201060906140307091d0304030b0702060f0c030c03040312 77
    0x420848480f5440015240041c42424040d0780000c0100b28401407034140b46440b140032502040c00700a0400a8070a003940b01d071103094100690f0045d41c10240d030b4080c410100504001d5001140191485003824025044039001e0700c00c0d00220f43e806011005070b0001c01001042d0500200d1640051204644101b80740c5d4940300050210b0340c03a19200000c2a00b81212100e2400e0165400419542c0c100030806056844401012201007070420070640c40302440f200507030510303201c0c1a50341600c1403200d0070086040d50007060141202c8003601d40304a10ba888034140a15100d06001c045c01215108bc2d03080c00150810384404142103225081e249044429043d00040d4141650703181004e80d102d540500c18400980315000080070070181010940d4075090100f03840302464032400d00d8855070342d40e4440d00202e403000440100000c00381502d5445469107441d00c0440d00c291440d40040c8104400240c00886002106000d800355003c1c03542950b680c1540100c0b154002441107040000004107079043d8081 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 518585179 1250 518583929 518583937
    0x21539070b150a170c010f0e1305040b090304061e0905120604050d0306051809070b07050f0d0203070305070b040507031401021b070b0f130305030307050a110601050f09040215 77
    0x2441c449003402000401000c0185a0420750010440700b03582d130a90140090710849140080c204002968160001a9242c0781051402030304a0710400f0054984120350340418803a40c46411301c01815102d0406c40c1e940c0e0b000d240209004119007141402c0c10740b2030100c0c00303070500d64207140126149441e000424844401003189040d07940c8041c00340400c105040c080c0da020546a0b2408000003850800099408484004540b21141c07000001c12102403003808994060b02d500c44400b980d0302400c0c0350076552224000481c0c402e82c0a0248004091440842103030304c0a42c055644909000182d01c41c00c0320b6a002034000c9496105050b00000000e00e4000c0c000f500805140c00140c4075490703078008848072015004a83c8079030700003500500c584800f06c010f8400d400e00e401e0049444914901701d00d00c4104e031070380010b002440044200030b5001d070302000400041c04076640c0c101c0202c0c0d038100305647d54502801003a40c003014003c80e200c264189007507076a6000c1c3c00101005294025260203446544c8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 518586429 1250 518585179 518585191
    0xf08070c02240f0d0608010b0619031b0e090a020703091a071e0b1501021f1d0c0307090e0307110112060603050114090c040618030b07021539070b 64
    0x18041022428000c44d4850a0000c2007180003d200c01c10801000601c0c40c402e40c1e110210004041056811a9200740e0080d6807034418400600001d440011003e0121500d0b010700c0e0384242c40c00b10000e0001a01802a2510305601d0340b9089041d609000c810702d10080c1c0d00b420b40c900800d080c004140420000f114007801c0500b507d03910b1041b0401401d0106094500400b00400f164031092a0417650368005582c1d42c0600d4281c1c841841c244510b0480f0015180780c030001100c4a9054210007102d84c00401d60b002c4138842201103503669555950304206036440b40350900b82c0c50700300307210f2000800c81d42050182c01060500d44103260000d418100c03011644580c00510000e6034a000620071004010450102c207074080b9444202c03498100580380452107140106010020702038540c0d458032250500e2800036550000d022201803a0a920080d0303503030841c0d211b018944141c140440c04000f0042c0813080b40c0400200d0311001044918080583c1d150b00c10410661507004211400215510341400b9000c1c0c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 518587679 1250 518586429 518586457
    0x30e030f240106022a030f0a060509010e0601120204020717070c0e0c0c1b0607020d060c03050c0a050711060f070b010e07032d02040e0702010c0f08070c0224 69
    0x6101041081d228000580000055621124150480620709141001403540700000a01c00785441c1c40030034200350b0300308510754940c42002600f40030807640c1e41100784164a2103000304201d10040c0e20856541c0f6003885980010302d10110718a0240c00c01d500103021203070045028034044d02680c005220725511808040e0340d2954800d0040c00761500240300650400c83c4203003081c0c03d00c81c440240d151121100d0040d4200c040311480c07410301070340b20801542d003600c0d0001d00c0c85105143c41d0520a0182896020090000b071820f00060400380b0070101380c62544003165601c03820000f0720798405405c3d00050003c00c0e0b00850901c5544800704a04000b42000b5108070554001549040c207007010810020384418140b5042c00c405201c00e400c003d000481445440d04050855650200c0900080c499074224800700c1440704208085c083d0150050140307449140e41d8900030015050040320009001d13101c02000a50990041e0050b141200d04444e98000ca2038007006510080c10018146600540c5440d200c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 518588929 1250 518587679 518587723
    0x120901140103081c0507140309070801051819030914030703050f100b06070215070f0204050709060221040909050102163c060e0a060e0c100306080a030e030f 69
    0x3002c068440c003132001018030380c1400030b410b01c000d01400040d00c11101c244d4040c000300002d01c0c006020040343d00206401d00c0204014180590b42c284201400d03003007604184a15a6101c2c90700009207100c001c025050341d1081800b038140020201040080c60b02e0300d9152081803404000f1035014001030951400c428018068040c0c1c402e030940940f00100c0d03441703204402c24031019000d03888401c110094088440c9a1302c0da81e0740e447c81c041c801d000095101941007440d000410500d9074000415000b92021a02215000c2000c0103441001041d03005001c05001c01c1440100841d041c0350b04213504051003880007505000c00501e18003048c600e0701d042981d0301c9a20070000740c8840c00d40326050360b50148030b1018041418840c07030503010b040800303000180100c0c0d80b60320400c40b0613400d11031181d119a1040301881404074803048a50ba0f481c08170602403040303450303202c3d140407140240b040408a039406009011792543e244c805840c16601c0100c556094000c240c2e8007460204140030840007403089c9400303a04e030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 518590179 1250 518588929 518588947
    0xa0609030302030d1a031005101221140c070e060603150918100605211507050c0105040f02040e07050d021504150c030905010e0306271002090f1512090114010308 71
    0x24904182d2101c21080b44c103034180d0000c80d540d008402d010114403104004003160790341080301d41c0b08cc12001c0b401f464001091858a800f0040342e003d080b59034142102029880320403c000c0035100c10f41c0d1448075030f10034404801c41c0382464480f50358001a03506101c4203480a14035031600788506c003030100785842d585041c03c0c000c4d0b00d0f16030114140d44181d044030482c1c1003868544240c1e54007030204041030305043d100020343e055101d0012a541c851101000744032034101850201e00c484916001281700b141086c08425111400003800d034100c07480240a2007401e8525020312061291a24518503401810000460078200d0900580117040d5641c8d140e030420515810700038640c081e140c0025040151818a4a078160fa00084680c0c00503001c130b0300c002c0c020f101206070840ca0310100318050a14000c800f030301484281c05034043d040100081c0c4450703940c0c40380703130301040380e02d0705214090250741c0e10a00080304204c8001030301d03a91065901000050300000683c403e0030346e1109034001c542181c400101d1082c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 518591429 1250 518590179 518590201
    0x509010b04050d26120403030b010809070608060d0204020705060906010803031015030e0105010909020117070801060f0306050a03150c180603020d1104140a0609030302030d1a031005 80
    0x2004140c9048400e051605010015000885801010384070844040d101413003040348034070840c00c0051000c0700580c4c80600341c56006203c4400c5600b603011a01c2e015034000554040c0c00c0540c4552a048060039000b81040810b9a080030080e182c503401c860f0640c00d10703005803902e200402020f4040d100819440c5041c5050500c0d040050b048030300c49800610a00c51410081ea02d0401074920081000074a00c10f4414200e00818061107440f40343d608100000599620030392209503218001e9a890cc0040513942c03803030084900036215400040d800000420000d0321800091441c1d211318600403c5544e0707a10000b071941c4800390000d030307985400949240891807091052201442140c00c0070142d81c0000c1d4513058203040244108000d050f0006038411500105502c442c907460700c005a0b15486a445541c07012010081100c0c040c0104c103000d402045040c0035403c0310381129819401549004641706422001c1c00403000810b18400c49826a44100c0d41c06100004041c0c2500e00c00013564540000700312 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 518592679 1250 518591429 518591431
    0xd090b0a0605120d020d080630011805100b0105070804030b070f0e030a03050c210a030e150604021305030d0f02010c030b0a0905100b030c070b0703020301050603060906060c03130509 80
    0x100f055100300d8007401103a80100e10441d02003107908200d049552020081a0014851300400d400d425440701109000d41e20754101003104910715000300a00850802400d0002c2c130250000b510310391040e54803070205109900078100c280e1040c90864184051070b55a42c4039604a0b410031640305e81002c04200029030300400078810383d20780b031402c511180c1c1c1e4000401e494278a49a0050104840010503210540c1c040000310441c0000d0041082c00c1e40e84602c001126800a441080000c1d003051000328024000190f20002d10500f002c3d5805207442e030a04000c0291f00c0b000341140c800440c4c1400241503a0140201440e8142c01c2d02c0c2c041c88460195002030843e2004c01540d000d0610f0701560402c5038541101d00410386140c20340c00907864444101e4010212000d500c0946100380020802c011801004040e0a0700c910400c40b54009854014064080e80800d00446420a10500004945280c10500150010f1024211500d85202c1400703c0b401c641c8042c03030208031400050410052410a64841 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 518593929 1250 518592679 518592709
    0x4180504170f070f05031605010e06160f0c020d08040e0402010909021342080106080c090f010c021e0f0f030d0c11090112050c0a080706050d090b0a0605 67
    0xd14a80b0009508040c050700030180080c201c84c4042202c0410040100115482415070441c0450384d0800380c54440e000e130200407076000e0503014090200700045641d600151280300744c1e407202c00403825030074801c446400a160f8240d030720460750308103103000c42e02200c0144003401503541d5046c05841c09000140105907141c0c003090b4050301c108210940c07041c40580c1c05007a13401e40941c0b141502c102c0c48a00101c501c40d14204842d04004222880c1d04105445286085a1b901d4942c0800350380e80f1842990030945c21a101d0450110030488400e29142104e440c410030041410881155419134000c91040b14000041c90f100d04100c02e00b058440c500f000110340701841c00c64038806400300e568007003500c0d00030003042e0710144414049098104000e50440400050020313100c40d00d01e40c2d4504122190100100003a541c2c0d02030152250030703d081000c07811054405040003031103a5031403f074003254203500418081514a40c0d4141003400101500f0f10342d40a100210702c0402c900c0c0c244010403000750449210 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 518595179 1250 518593929 518593973
    0x1201053303220506070e060f03010b0406121802010e0103021b0304090b1203040603270f060e010e0d0f170c040806010503070e1303200f01061d0a020a030204180504 72
    0x4082c00040d00003c1240d800340b060319004a10020170300101d8903038010400000301c081c00c00b20010800c800303454085c3c001c90304244c0c2e8180c1084450061801141c210351584001c860300d803170a10016500403038079026158410315005140404050303001e60000841c455440440c0c00c0042c0c00c1107001594001c014035900212001040c82d00315010071503aa106501c1060f0505403581c1030141040f02e03500c80902a140c0301500030003030803c01c1c5008056022840000c03500d0910b4850300d08880c200c144295400e0308a00740c000e1a819450a00503203d1303c1410121500f0402c0000024880c2e4031071400f2640070300b801158030340c0c40d142889001800c04d50140c12850180e4040c4c882000801c4440c0704c2103401c003c01180c011400351141c242151014202030490301e00410144098039036401c0040c0070003e101d0400020466980c850300c040c200319010b50300810050480748080340080d0701d6030b030040c00c22003d281001860640da8000354226055802000c142c0300341d03500100814003000c185142c000c2800012 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 518596429 1250 518595179 518595241
    0x1d1c060906050921223b060616020f10050405130c0507080a0201060e0c031906060203250c06050703030c0503010f03060203150406170c04021201053303 67
    0x1000e107809004600c5a02c0b00f1017035012400034058100308500000d8070350520202c0e122070f4208a04034914404004403142c58038440b13807900810700070040090061100038003652030207070400394403c1c07103000305401668420035810007083c00c1e0b510454414200d540b15102e007a140c500c0c0c4000c20030318848018801007911304004884d400240d210b4210341286a224811a0b1244505e41080340100001d4100c045020034003820b018045200201440c464075244000c60b100315a4900c001050300c1c2c440c40340f080580d000b40704a400b020b900b40341684003444140461a4190b0b15920342d18003030341c0c0645c001c2010410005482c0d09041d894050b0305d0354160903040c0b81c0e242d075142080301c4403010384500c0042c19480d8040302083c80d180d4105032100142c0750041c80ed00c10315848080141002074942208602c0c0d11402d102e240040c2424001e40c0c400600c2c050541e1260380c80c160034402c141d0389042e003540340004074804007a054005425950725407040f484401d074403868015442002c504107a407820071900da41103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 518597679 1250 518596429 518596483
    0xc0301020306031e0a06060f090b0a0b0a03020c210c06010608040c050409210f09050d02090f130f0807020418200604050418050c011d1c0609060509 65
    0x1100c804205000070310f454511300030b10b8076508101e40c44400401c114200040000c4848205800710240e501200301008000e002c401040307420a00c5114410340741405000c2c59400c40d01035409841240010030583d90001041680c0c91000c0c0071940382070030b8204c000301e0049101c642c10018603014000a050501176070030142c846101a600718414a072042d500c603920f000800000140341c071002c0308100b0881102222420b809131040c08020a9400001d10f412000140c0e07142c003111500f0f401c2d40242401c00552145401a0b900442c0142001c011540c0d601013000000e2140e148038041078004d0b1038264491915104000a03200414410402c2403845010302c2c02080000d8200004d0100c50300c4101095450140031507003600841d8002544a4a045640c0c02c00401c80c1d0b0010300c02c2c501ca4426070703406030710440c01500d040d2140b4072041c2c0c420800c546d400f00c890030215690098558001d004d5040480c896881c20280e454105085941a03141c000340414002d0400204051800c0700e10b001c40d03060301503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 518598929 1250 518597679 518597683
    0x30307050601170703080d15050d0b0103030807030c050d090204140124050306131d0708070305011b051903060e0a090209060103022d121e060f01080c07020a08030406030903020c030102030603 84
    0xe60500390704554884001c05134000721048c803402001c024000c80b2425016003807150b0420000d1105601080c520000a44c0075846881001100e550a880d980d0401e401825000020100404100e802c1a590400a1680ca80710b030b039214020030341003044104400c2e0b644a442160038001c84c0f1070091203400e00c14411556500350309451224040840007482160340304001e00c4042071099551502e008620000c01c4681c2d012880e4001d0303034001e0009000014458215400c0302c05080301c4040065414800c406d075071034149480241802240c5070118540d51568002043d5150588044e0501d954600329801142403c480c0740f68404800d00741107081582c1c400fa03401d101140c0c00c0c070010a140214a040d1004440320059514044005066542c20314108503240c0721506007110b401101024000010b419180035181c7c1c80c10070070107940b03190064aa0301980d02c6a80c00040040340d1041c04c003080400c40a008001500c010011560085851070751801c010342043c40740c4600300d0180e401042003000701c0d280 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 518600179 1250 518598929 518598937
    0x30b01050409020301060510020313140d0b0a1415012c10051204110306010b0f0f03090f0f0d0f08011a0702030f01092303070302100c090503030705060117070308 71
    0x10a86012400b0607280c400640107180356004594004800300400d00b58640c004060300f001c6107407a620500030742c1c07a01075502d00e0110142e40702e681b0182c01c01c001d10008001c81d0f0f4040d0000c4007041c001c54001004e40240c105000101c84c0005294143e0103400650342c2c2c008104a80900c015100c032030034410002010320b02c9458007290501400203030042451481c442d204880310050190f125001500b171602e0414048034240c11018840c0c8144c400205898000c08100da151080d0b80d1000ba16042800d1040d40f02604002c0c901c460740d00500201c0300c0011014090803180301c440394050302d178070040b0a40281044c200002108100151400117120b610341441401e454188040f4030251100500e00c0003914158460f0f085000950070040d80d442080503481a000001c140c107000001c0907015000d1695807402006005401a407054509a01d204942d501401030400f05162035181c450f2500c011034555404044103c0b016404140100031500e1552000e041d5120180302800200d40355032595415405 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 518601429 1250 518600179 518600189
    0xb0102060714070f06050603010e030f03040303090317100603180213020315060d09020a0b1206010c02120708061b0a050f1c0e0a12050c19051e0307050c030304030b01 73
    0x80184900c40114590b00c0aa9920030360000c00c200000516142c1075001d4030003590803900035800d2010380804101d000c03056900400848400a044d40d0b100e032030440103440041016010704c006001f24800850490302c0551003180d80a2100b84000c0c90500020110782540d0b844495101d002d400b140e00595503025030865615906d1009a200e854101c00007150802c2c03001410f522140001da1645c9000003074009074038050085031079002560b40d82146110521804e4071f20426844a030700055065070041002d141e1281c0040d05071405680c0008880786025403e030060368260344460308010302c0f1101c1040c1107000082d04001542095010304018205000c0c203404591084808252070074103080ca1841c400201c01b00c64024003a880500340d80b551504054142565130078440c0011456003401001211140520b2030b004006100c2c001000c10500004018105c030705002e004121401e0004000900d035410003020041e5a5a01c41c51402619045028600038080d420034001000841c003400c80150440d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 518602679 1250 518601429 518601437
    0x15110c010e0d0818100906021b011e0201090204020c0f061005310f09062a120b09070f2d030b06070501050c041806030f0201110a12020d120b01020607 66
    0x14070501440b080b1350514103c075030b801001c5070070715040859105040c2c400325402e40d0240c07041c480180003908a40000c4a442c680421040400d034811000720210b0422410450300c00083d41800c0ca60006041c0d0b88401084611584001034a041c000307001d01ca2140c21081040c0500101d5180902040c0f20840c502c2130b01c4400b0b14081490200041c1c0300d00c03071101615a0072420003003158200200c00c000c1994a20030b541c4145845411928041a002c6541c2d41d000404400a096200007208540d6090040c140380d188907110207002403251280e40c0e56501403025601d6085841d44035490080c210030380000b0140000c001340030380c45018003441180740d981d071449d0b02d80400c1a0704c610700800d40d03a2041201c014020361901c810010074501c00da0161040d10910450041480c058018031030070340d09180405000b00800351210b900642c0250541c112130680300c0e040da071440145888144a4181d001c3e85000548c005a181e502c8255100c05120988110000c04002c44862480000c0d41ca9000401c00d2043c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 518603929 1250 518602679 518602687
    0xc121203040f050f15130c0509091e0d031107032f1c0206060a0e060f0a0b0f03060f04021218030c010f1e060509041b15110c010e0d08 59
    0x400340c1021490b01494008013110070040a0b40c100968592803090304142c42840c800102d03800ca60720b100b1604c1140e800c0103100c3c418a050100f001206080501624002c1c4203a400585860108071010303641740324110050104c1040550380a01622b001d000002a500000c22080000a40158001075810103150202441e128801101407000016001103401d81c0b0030328049410503d50701c800200b44c000715509443c047c0e201d000038010078564071b0091103c10421100003620134100030040050a03075008024100007a510030000c02d5541c000c524900d00104008100300440c00e01348004c049200c3c007510110b1030100c0103000500320490113411080d601e087e54986060710201001501e2144c0b00c408000c2240040c0c00810400820381d42c2c5450f200c079103d0900e04036402c00c4c40d01c6800115280a41444907540d0303259a518041d203800d010883c29183e0300c442c081540c464484041c88281055140c103040400d121a41e20f00d045000c5c40b55604014070301520781c00d0f40d203560381403408007075101d1300700350326 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 518605179 1250 518603929 518603933
    0x703050408070f23030d2a0e0d020d030c17130b070539041b0807031e050a1a210a122d08070c0204090501060b09030c12120304 56
    0x190022034940307240d04251041109400000103c024106183d03524007c0204020415280180410103c46407140d81ca1107a59500e0540c007900010f50300c0400103215648484490340003a01003510840103600007400388011004028880801c00c9040c0e01c001a418100a031012801c000140d01d8040c03240c0140c40820308070104403003004551070040d218014030041c03000492031203040304249424200d03000c82034504285103052512031070000f15030188603001d00040d004000d03a941100a4030ba8420195550a010700e19010b00000341c8649080100c08103403400e00c41d044000f99210024580103400001120b484c80d0b5890030703140c5e44d414a90382900304c170a003040d80300c06003481455031000d00004e00c007200b0f803084154402c031000280195500480c0b215203901418058031900202040b01180814003c209020b02030104866041e2000f080821110b440390b0745c5509681181c2d201e4540104041040e2100786000d00c4000e890113010f440d900002409808200d649406406856001900000c0444d003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 518606429 1250 518605179 518605193
    0x3020c0735010b12030d180c0e0718080c040b0103140105041104030501020408060915040317040206040305250b070816060e15040b060906060a121d07030b0703050408070f 75
    0x42c50110007480c0a10b9110843c02090b00d1b58040c00302c00e010b01e407400081404505008400b104007640000c29400c6241c1891144040c209001d49600203100b21405003444140240582e90090325614001d4811002c1c060300780010b8031426107074681270508001401c1c00300c0744290030083c1120000c95011a034080703021a090018401c6400141c804d5000140200e4001c0d40056094051480441111454181103a4091140c81c00755070003000520103d00c078000702c80981c0c4486400c03d000510441ca030550769580c4c5071030500d2400341030840c4044403550042e01401d01100340e000b00041d443e15864100181e44070407241c480c000c101364580410903d02002e004481d8403200c1c07140c843c20103e55900b0885031820307982e408220b07011200c001c6000300203807090401500c01c40c001c46019000e01c1c1013034912102503403407554220400c4440d6655105100845001507500010240e88001030b0480c0e43c11401d14050012009200e01c003030500700404c0c440099200d40c05c40d52460f070081c52041c00910513140c002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 518607679 1250 518606429 518606441
    0xb09040f021e09192702091008030f0a1803060c1101020a0f0507050a0b10090b0409020901090c0c1221060602030912031c0b21030a050d15030303020c073501 69
    0x40c611029080321030380d18100524005c1d88078002c03546541241d96074100c040c2c0185240c007680e480d60304180f145c5103801042102809400e561400c1c407da420440200c44a05100154020354031562160000f03c44d103900004800202c6100200a5151080e01c038405000301e01594030303200802000080d050148001800804582a440a03c5003200d003825140310312101110f000c0c001c0e130546045842181c61130f1034862000302035800b0b001000c541e0b190200c1200244051006481444a50009040064400b818a07034801496485030302d2800350194510f224141915034040020780b4200c8280542078000040e102c889504031140003142c80c0301000503081d4065841c12803450750078031080d42049012508202500c900030b41d80f8107490b991910110038241e88451070704d04203401c20040511143c2c401e5000b0010a40c000c07002184800d001008002400700544c015400254080395149043c8000c0c446880100700340c03400b0040d844000b12080b07070000138002c813880015500e070954842c01d08013034002c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 518608929 1250 518607679 518607701
    0x9031b15020a0203130f12020906190f080f161514130614490906141506181f0e0a060804080702040b09040f021e0919 52
    0x29502c90502d0380340a07540760080c0250824240d4801d501082425040800030308503242034240d0b01c44561170782c00348103024a010381465040100204c0200c0005940c0014100601000c90503800c1e551405101c503091281c1c001818034107410922808160305c5500315054156000c50301281403104410740e081e29003888114080030002000b00307a1a1114108140841c126140703529888070780040c0142c112107521588101c0300f566080c64290900c0b5620302e0041101c41c20220005030b84241c011215414094800720001c10b0700380e00c90001e0405c02840c3d0184106410074000d4204042c20180e044001c2d1500c80e2584502031340000c5202c0c0071801c0000b2118040150151803461f00140389440ca445400128100341c004c0342404074110400d05010355001e044560300c1d541c07800d013a20340355184241070303014040c241c0e8400c0c3c0714490b000380f40d541c1c00034080c0110300c21480740408007081e105000340324a040c6104919000d9844e0080c155842e1181120750000c00311100210a08480b40100c0040c0300034585 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 518610179 1250 518608929 518608931
    0x60c09220e0616081024090906090914030403020102030f160b010303120c050307020c04090609050312010e060102010506180a150902040e0606070f020d05070317030708090109031b15 80
    0x34851014803000400001039115a501800d81c1d036aa04084030240d0640318001d00b000211b89242d2000130140041c01c0c2040c001c0c60001c080c2d59403614443e06880d02500301014160f03035216940200301c003140c5c40c00003c50f03003400914201361958001079168043c040004008507030000e4008481c0102100c08030b0340a41c480036a80465842e4107005020061500191030400e1070b0a00540c4800c0c0a034003900e20801c8540d0090000762030101c24440980b00c2140102c6007162101030b0708000900034006011107160300b2402c8400c541c907010100c020340b50041c180c14156450b0a09001143d161003c1d09079a00c188501807803403e03142c6801c4100103002a103840840d0104401020541031840c1d001481240c0d01c801007000d03951608420480d0070310030794000034040c1c55149590340043c240711030f444e2022170017902901e001594a881d02650041540b024110107440002001000e640000f00150030207600d10080000d90720a55000d0005e00903003100404000101092504000403041800b1481c4c8074208 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 518611429 1250 518610179 518610181
    0x11a01022e110306011209320106060e0a060c050307031b151d010506030705040908040b0f0913020a090506031008030c070503060f04030944060c09220e06 68
    0x912014181c0084c0d401c03a0010300c80502070a440134003400742c0108190080007480042407030080028552900b0203000300d00c440241d0003186900e000303100b00b100501e92a1180e00049034100200700072480240c2200040c0280001c41901003040041038030f0010f80e0609084008003d80701840c4072222030400020400041c04008071862506900000324100300303003a5003201c01c845000795900341e50007143c041c1e0309644841000c02c01071400350041030703010b8010b1040500d8035031108410801c07035101042e50132404d071002030308503924106014040c00640000300110b04007454814028554262403003a5032090302d0105c081003c900400141e0402840d4100440759162009400c040d1190f0003480b429110340240000078442d00030564a0303a200b40c4c1d169444450302c5007021401003c1d245400307655000f454000c18652410140a40002c0318601002c01d58588105d00d101000d0cc1d00740020001c1e030302418103110701443c0d0b8130790740b01d803030b411000030b186221003c0624443c0e80014824842c0c54105c5200342c030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 518612679 1250 518611429 518611451
    0x90103060b0a0c1511071514100302010206070305010b030601030e070b04030f050708070806240a0e04060b041a0405040f0b13030e010f0c24060b0903011a01022e 71
    0x40c0e4681843c444d080140e541d519294180c01181c540c402d03003403040c10b010011800007e101a503405800700e8217000020740c0c015002e0712201c0414045036400c8610091400602c10366070100851039110b00d15260034007840d1f042c0050584640806080941407640b51904400f001a09101c5540501041002d07643c460380d403410700c000d00030781055090f2150302805202196009001c41c001003034844a90040c03185440320201c80c101c2d814505900b614180c80b051001d01c1d695140c0c0d20f80402841c002a05440c0b5003407908000c1308403001c51101610440c40c100c00c401c80540c500910000320b20f422030303000481f50b44900b0300c1e522203a0031400060011500c42d08210000050340b41d01180e050095035000d90258014005448401000b1502c0d004140c0000060b070001c0c04011a07103048480c0458680301d007500c4100c800c001d8480c150001c050100c00031404100a090034841c0c0c00f26502c10344440c03078000c1d190300000f035103d0441d4042e250340346010f88002101d01c400ca4081c883e4606d80b070101088010410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 518613929 1250 518612679 518612687
    0x3090611070c0b03060102030f030a0e010507030b03100605010e0d110913170307090b031e07030506010e0603100b0c0319020c0f040b100f0c0204090f0b060307060212090103060b0a 79
    0x1070301119655007009010501d80150010743e8800c58040c1c00641c42e0160b05480040c150f00000c242c102e800343c8610a18590107400e025181c01564140ca01207025130000f8105810702c0040010143c0c0e5600e84182001283c1e402003007090b0154090b52420421000c50070420108803507440e0007070708182c0a80506c94032601808a802d2140d0203071a0856801350199807846051006441c10f10004030260828840451101c00071030b0410518120b0640c0d0700c0403a400440020800c98030b01011a030f0b20010131500b5604054280110881280c0646ca1443c2090041440d550b5030301030b646464001003100c006e4100104110b664023180300f0901002030a40340c400075941c8802d20500b41c060701c00c1c5801c2c0c8000307003400c0c090540c2c44200240700c18010a1403400c11070b600d15000990404201c800003940002d41c40b1885200810f50107580101e10112280c113002c80a00d40241c8050b009500003d0104201d543c08605460441c114415042e543c602d003c1c01200509032030f4108100010000513034401242c0c02c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 518615179 1250 518613929 518613937
    0x2003010b04061d1012060c17100801050903040e0a1d030c030c010c1d011d0a030506040611070b070c08090604090b03061b120a06081225030905090703090611 69
    0x4441d0000096940e0030703050760590040e5108215417480011940c0d0009030032500200d080d060140350052003d2100c14418070100016241046400d6000f04c0a004104083c0a1240e1081e00080150316291910110781440310008001420265035088032501e0600d01c0d044c2a1007242030390044039240e003200340205807642d210506040183d03290910901045001d00d41682c45480c0300f210b10922030306404015504a0b0b003c0503010051000e032600f54055076110002040030318012001041e2500d0705160020407581c140010346501c06051101d240001c13612016940d01017010700d8880c80d14003c51400c3e1203d40038400e14a07600540110f400300c0e00360315039030121100200460454055807200b15009889072580401070282400c100030f5152208030b2000b900b074000060748800600341f03540e04981c504141e01108201c054040010f80e840c40c080655280d4041090728a20382100c3d8440781d40c2c040c05401c001c1c401c0a009141340c0d0005403646010b80d00c000340290304404107100100804030450a9070780 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 518616429 1250 518615179 518615219
    0x1050c1e1b04060f030204020a120501080703061a06091509090a1a010908030a0518030d0e181e040f0c140312030c0d05040206132309042003010b0406 66
    0x2100d0100064606030152901311002640c101071100d003540c082c80023a51190842500340300c0511018100c00003a4400c440c02004410003600441c0d0a500e8010150703010212800c0e820706283c95100c0d21545e6102c116004c3d22412140800070104d5002c6060340e60080186003036101c20b2200401c10100503e401c000c042410300000401010201d0005481c074001034020080141d105001c1c0c0180c1900420040843c0030345d240e07540344000194400a0720b842d101000345400102402940031042c140410400b00b81c041d460003490f40e0380781054050b4498048007001a41801525010a0030700540c00d050030030581e08001c0b141442c070b4a801505900c4406005840c0c02442407400140004450005903809004805551494000c901d105480a00340c00f0b00140e030301410801c40e030303c01e5400b040210002424408103450440c0f02c402c0d44e84110705010b04400340a5100b00d002c0000080b00c441550650058480e1800c00303003548003001c00d00502030410384e00e41140c0b0304600442c00e03a5075010340043c03000d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 518617679 1250 518616429 518616463
    0x10b04030c080f0604030e0102010e030418050601050403030203070201030906020720031b0f2e020622021810090e0601050f03010c09060c0821090f190201050c1e 71
    0xd545404060741d5998040343c40405030800c9000c500000e21904048100c02c1d014400031510042c402d040e24150780c4a5840a0107107501d4080c0450b035400d850113800d610070000d0801c20f041c5407650310040d403640f0850a000b810195136000040420003994151000a50445005041440030007001000080100046442881100070b100d070a294001c2d040c114519014146e0300380310000740c051220780501120340c0c40001d1100f4000040031288010309010000050340100b40905124601c025500c036200846e50511001300c81321000b50b1107107210000d0041c082c030b03210701060742e98000611031034103e07810041c0b14074100007803416030860016423141641c2003110030300f12020585040600f03c8074540c542002180100104105040c02a04102d841a003e032054528000d80c030382c01501c40680782c1428490296405050002c590707000c00240c09450040001890107182104510100402802d4000d041080000711001100d006001309102c0b00101d504007c880e0a260b92619151010000c0940240c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 518618929 1250 518617679 518617703
    0xf03060f0e01020a3e06010f0b030402181803040b04030b150d0210180e07020c04090c050f030a0209040b061503060a06050c0a0b010b09190f051c0b010b0403 69
    0x9400c06100700c501c0f011094680c090803840c1c04981854401003810745a103200c540305d000300d1050003544104040150083e0144c0b20540c10080048903c05168215180008040c41040010380301c4403041d0b1200481c10300349801d1030791202180000140c6446644141c1c0c00041000600f07284500c0c05401620300c034940700740c1541d80d03819040008030300401447d584500341c040d81d18090b041140c40d9241100c040d01e0007000070507030000040d402280c20740c40806409805010095120b41c14400b840b04c0c101c040718148030840060b1100c0b40030b2940c1d40607040c454000d01da2641c0082e82d0400c40044450f5000c0c1c41290503240c00d0806400389041100c1650003500d01034180300303800f1416000c132840341500924081800c1d0505e2000c94080d0003e48404a25110f140311f290041141811442d009203e0f1050082c0d59200c10380038032500e8161420f41c000000398200381070000540c869801801c1c0d0700306480b0010039090450020301601e4642c81c001d0b0000c80c00d4070010580200100051040e20b004040d034004e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 518620179 1250 518618929 518618951
    0x181002030421021e03030706050c0d0c1704110307050909070e061813020d0602120105010315030209010b0f070c09020415171b0408100b0a0504090320070f03060f 71
    0x440c18905070700952003c16800d0075900042d41003401030943c0e20103002c80b1f040c94420380e504801c4440c2070790000c0040303c000c545e03082080010300551100844034900600b0f100c0440c0c20208a084016100400c41140c4a004080b02c2d01c3c00c1190344020900101a1255824070300307541a1544080c0c02a5070004451400190b16814a4229001c00380a60110b0450640e1600840c0300300d4504150100d9100040ca070140011500500292205440302902581075502d00400582142d403919183c0790140000da100f0009070707070b40540710b9044503100208140c0d0381100701d4424089204184000308204a8008003040300a078a80c083d00c16039050080c440c1d6990102d96080e600080202454500174508000003460981e820707162103a01500c080d2490704054407500018107002d00c1010b1240c180340d0b20f01c0000d40340d140c83c0340000d00600040d1030030000003906840c01403500d01b9020b0041507078904007082001040c001c20107900140f03940e12980c1c10054030f9240c04000f80c005208126481410b1400c4900 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 518621429 1250 518620179 518620229
    0x402090d08090a0b120103060c140f12010905010506070803040203010e010c0c1e120c021311120a0606020307030f090504110702090f190b040b0603010905061f020c04021810020304 79
    0x17540d000715000a503a178650307504e01c030140c04603103041000c00014802c080c2c40421024040d1024a41361702044e80c83c1e504189070083d1082050b480b01109070b040000400190300c40300111888260880c140c15620368031400868050408901c03114101d600c0c1c4400403060950015074200f000f4030078040354034440300e0340b4890341c4600c04208020b0041c020501942c08c200340900a0064402e20250080441c0004101d6034005c0300d500c0c80c3e40f03181140c80042c050b01004841c1d9200c507808229400d00b0400207050000096581c0110200242030144000d8185502801844030310014200184144014250100d000352142c02c1600100c0c02a110300011030200340c42410042c2c4905c41803403006c0c44000c40c0c0039a0201401000b01400d81040d51003040300400d465090045028050500300480c1606002c2d0030f2003019060707001c064400003c48040302c501640d012030381c0e0f2505801184c2c05a2100a500103038164045080000da501002ca0546203c443c3d802001800c203d07500780c0b00c602c81c03203400140c00c44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 518622679 1250 518621429 518621437
    0x120201091e0e09280f020a030c0f2c061203070c030308070f02060c0901110616141206090a060b0d09030210180b0414070609080c0d200402090d08090a0b 67
    0x341c04d20009500c01012543c0c2c0045610185010340d0341c89115140b075402044000400e40c00075602c40d01c03603030400e1140a5800040030010901411400e40c010461101e0150f104080a1916003080d100303c0450300c290384100d0a0240992503000b80d90b03448074145401c9840000500c021408165101c3c0043c4039980585400c424140b850780280400741d130b54060b143c045600c40c01555052251051741d000410f101017100c10700c2115003240c0440f51145514000d03088001c05020300560341030030031100c514000c0314807003180c20400079622100ba0307440d26800c0d0800b03800c01340c002001252020404460500c0c00d40c02c038030501806502600c80c1180d60039041c00c2520007100114407058100801740d4002000c244020707600a0041078190040d88100d80124200599980b251000504810041c408514244200b0201c94801c442c1c10071090030f99940e0740030316041d0140d85a01949201c0c00200c054031150101c1c0d582c500000d200010006161900351019005120000e0243c800e80002042071500da404907 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 518623929 1250 518622679 518622703
    0x23100305061f03180f1b06122019030f0203090a080c01090204061701050f010e0a0b0d12050d060e011a1e0714100b0a120201091e0e09 59
    0x1000502e942c1d01c40c0b030701c2c12044250703203200301a520040d01008940b0304507580c07034491040020f1100c28020382042e030060040361140d414246800c01080040c250096050310307124454040104441100c040d040c14074641404900050440004200e25070366040440312003101c0558030100038800343c0d83c2c901400c900044820440660000c42a80040781a0002810101424100100d00c4001c01d5010030b00b0340e4002c0d40f086c40122030702d015001a0070004c3c018a0f0f84a41c184402071040e6150040e900d2001902500c000c201c1c80e52010301454586881c401d003000280c00004602c00342c0c4903500000c1c0181d2200504008084c5401d4002c510031003045811ba0403603004c10806034a9041e1030000c1041540a03424180e01030200540f403016018200c406800d4290261003842030840070701100c2030130b01c1d1112080342c0000346018240c0072580e44c0e104040c02540c0361200503801000f01480141c03041c00c2a80c20010b40d00159003040805034101910f40e2050340c0b09900305200c10385465050b195104101900b03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 518625179 1250 518623929 518623939
    0x603160b0306150f0a020601060f0c0308040b0a0f0e0c030d020105014202030306090114010210110408010603060e0d05040b09090402010306050d0302010903080c0f0f0f042310030506 80
    0x200d086483c0c8050700000b0340507500c0080345400040e0a80c2241d0f64025421680540c2007000100515904507400703103200303242418240c502c4000341c3d13002014044000d00c000c14102620022507441000c5503c10317a42800100790030040702c0314450949a0b01c01c245441f2512900ca5010f8980b6210f1041c003680e8100c61042401c045503182549454680d1401c041100d140b56601c2c6070a05400e00240640d0b4603650001d030041d640d6420188140860444142c1001a115401400b1511540d0707000a90507029216500002189031000b112080e00b881070b0341c00780f46d082d800c0c0b000c0070007400f02940c004480e10404104032410204c101c4001e4846025601c19440c441b2024030448116080074011550b103e1310514000603800e03201c0380062404c540c518400c2d030041c0e540e550714108040e04010110b800030080c17020f503410716810b42c08000e114410b201d40c04190b46404540841b0000c00307802514007401d42100c0e4808500c4030329244120641118400c01d21a081c4400c002014500034860140503250243c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 518626429 1250 518625179 518625181
    0xa0b010b3622050a0e103803100c0507240f0b03070b04080d030207170403081201140d0b07020a150c0e03010507020703030c0c0305060f0603160b03 65
    0x394518007032050079040c0801c400440318401c480d82c600e0b0b98000148102c070041c2d0600007050055000b2200c008050003082858030805503c1c1c03442c000381c6003681c2c07115100b01048034803400324982c9104000008102808034038850341604503055101e1018904801d90403548800103480c084d00580c4d042c0c59039500443d0080180d280852600c2c0030040001e02e02c984c10041595205008404840d40c814503500304659841c085202c13807400b0301240c40142040160903081c02e080259280c0c0382c94110304400305040c0d0000c5c09804012141a16001880591601d10303280c503501d0500e0140c561040c0003070754245010740004100c120021511f01040040941401c803004116a2174a402200150488055203e481d00c40c00c001841c0304c480840c64003138148003090882065001030450058003d40c948281d0508040004582d4005211012240c151070711000f20030040c1028034031042942c002030168002d40302080025801e0b001214003440043c1e040360b18001d41242d0305244240b4901610b100f01c10200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 518627679 1250 518626429 518626477
    0x80402090406020415050a0e010e010e060c10090524130209070522050103060b0405090c09010c06020c0304030b06060703020604030320130602060f09030304020112020c030304050a0b010b 82
    0x1003141d0140c440c2c0340051900d034903041c004c41029950f2050800180001a00280760b0b13074014611582210b0a083c030360300e00c1030940c0000c0c000040f248c030031902a00010440d00c4503400b0411110b4a0103000003c1004184104e090240d101c800d45d41101d000c21030b190001803160394440c00304074454541000c040036204465402c001403080c0242c001400c2001c1800f9190030086101318002240000d040090011442c01e4000350603106658808000c031402400300b0821910355402180d0b005640c1e07074010b030350789550030016034000c1011240940400c0c0701150788208104004020b0040c0c0e40901400b14a50f500c81e000c0110038840c0e40f5008005800c4800801c1c00607010343c10400b810102c096008111003200713a15403000da001000e07800d0f40300d46504410003405806002403078000c804040e1135900340c07804611041d9244001f420003410026810780e691031038655503060703074120039020055a540e070415040c41541d0310b4640c1d10545143d407400c4000200040103108032032440706c0304012548907440130 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 518628929 1250 518627679 518627689
    0xe0a020304080d05151f02070b25060f0f0b0d0b07030e1504110114160305070206031906141014090409030504090c05091806150c03070b0f010303080402 67
    0x10740200c0e4210390600c140d5240794024041c162280a201c01503c42c2141d40c04108540408107008081103094662032550707034180d010620f00d0a072100b400c074080d40d40740c524050b00302d41038807020700d9134805c542d40e60b001d410403200383c11410711035149805c207010610800c0c01c5541101e458502da550722200b070780c01480014082060065000f0103030b00703000071003080e254000c07410401807039a00e902c80340c0b400041004021a1541102c8000c4007840c00c21550301405401045a00c070f03044a801d480c4010b14801002c0600c02c2041751304c001d6001e0926502da04240300306800e2a500e06401c610010700300030011405060aa00e03c603da080001d2151140b000d0b450320982d2030340c20f6058501000c7c2d00401130881991114002c203441d15109688403a604c51500025804036104607000c2402c0010402c4980943d6898000c1c00803011000c0785841c4c095100ca20002d8404102c0b04c030f4060780da0340c0124404846520100142030158002e0761205d84c141e0b101184580c10702001d020060104024401140142c108 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 518630179 1250 518628929 518628931
    0x405040e070f1412061308030a060807090b010f0314150f060a050910090f06111606020303070306061b0605070c0803090c0f041406060306040902040626070e0a0203 72
    0x10481500d404544450400101c1d0304540c000d40e00301510340f1864000c42c203003908281007940c41c0c0409818241400c081e10452080780d1580034011100c04000302d45a02440c1d8413003001443c461040740c1401e540c50100074040c11100d5000740c041000f040b80004a6806806010031011702d0800d071030312a998400342d41e0244500781e03240030f8100003c180321008075114003004042d00003107600c600b078440362402d080000d03d5007034100c03100801c64003030020890240f500c0000c80503155182422624465103403903e5140968420b0114200c9010744c6e400070740150080f00850042000b40d0702889450340303a89043d00d81c184409002c0341c0210002d149c00c000305290381e10254100c0068500f041c02c203400754560300c10076001616858042d402c4044080303054a4500c1031210340e450f00b958144001d00e482c40d4400f100c0040200340a01402c40000051115503655018003030300350f4010b00c104107868562603800903501d0781500d8001c00002070204090b8800c070001e0304404846107982206083c0e5030305010240a900 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 518631429 1250 518630179 518630201
    0x40210090504090b060307050111100906091a0103050f0307081210050604080d0201050a050405060a0c050f0c030316020309030a0303090305070206030f0f10050a03020906152a0102040b040504 84
    0x11000c20340d982c076401601d04442c010a01e0003a01e0500a04160401849500481c103000400c007c00c80020004100b451007621140b0000075840381e1424814050811004001d1120980e00e00e440b4840d00e482111605913401380c0102d41051050305400c40c2c0e41e00c500781000e0f14203c0c0510600c143c08030f000201aa102d280d540006460543d280d0104215420075045010141c02518664007002e034240724a9602c13060200050129090585540743c03190000380140c0801a00d80b8410200381d07001e1000c44508607800001c890740c3d0340f680f03002c050310b03034100fa50254060104181d002030b40d14030000598145040003405090304210302da40c250011b03e024103084086c403105000070409a40c543c4040c602c034002d82c03141215039203400d500d07061000d90024000d103600e814600003840151520003a0310142d80c1d05441c02c1055031180b1300003a040d0410803003007030411440040e0101e50315500201b0145885201100c03150045d2154034514280d01644c080c408520800744410001d5140603001000704070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 518632679 1250 518631429 518631437
    0x60714030907051518041503120908370308010b030a09020a060512131203020913050112020307150518010c0506040308150612010e06010513031a010914040210 70
    0x165481c00030944e4850301030f000720361070080801c03414000d207400071403c10801c800b260b04200980a4804114802100c1d01001e4003090710f091541c9070403400344034490050001a0203d45c2202140ca04685080e030340700d102109010800c044c2c81503000b03840202d402c4a00d84c1a2030f40c200603030030821113012907003005248001160704c403240390016803a0410b10780b0140c199a034446039145c5403c501101d20500c081c0c03527007003d02031440317640c008100c9140c40341d451400b55140c0035a0320a180d00016080811649042003514a0907000060005900000d0701d4010701c00da0a50f00001e03078502c240c84020918054840101d9010001e00411003c40c8900c01014001410601075892240c1c4405251407000c6400b140400d545505000c10f0900300808081910400c0342e500c1d10345401400c03154181c4106110300c0b50300e84100ca02051542e801901519901c6c9040141100915500e042c0031040004000602440b1684c280c00400c140c00725006812405400d0140c03c0c405440c0d40d401e11000105642581c0d00300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 518633929 1250 518632679 518632693
    0x201030b0a1206140609060a030b100e10170d0503150d1b061211090409030306080303042402250302120a030f14010302100e181806090607140309 64
    0x20b0114945102c42ca008100001c0c4600e120b4100c0b5031414400b42086124091070001c100c0c40f559031403030660580381d1012101c0103540ba000041c06094000d60007082d501880242001351040710715404608490000c0412460303c0d079034040b090380702c0c0704000d24600000d800700000340c0300707507a0203580e2481c10300e024041540f8440140c9400400c1c0584c514400c9481654200c2000480d030b001c6651340100d030401d14208441114042e100d10360b88140c910307150180d03071101421030525001e40e02c00c6000b4580c1d50141ca980349082e1031300045801401016081040c0d140d0703455070064102c0d10a4039150b8044850300c04800b4040300d24500c0209004c04120704603c0b4a0a50005141b401e038054041001ca544012545501c4220010191405910129001088a0b004101503036a0024550b242c05185c10300300030010544000c504243c400b0480306032008480c4092000c07510302d19840503003070310981d010358103540c54502c0b81c5c0d905e0701c03030130748080c0c0c00941600c00442510308028021034020030a07104407061317 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 518635179 1250 518633929 518633939
    0x18061508010905061804080a02010515030312090a021005030415020909062e180506130b030c04030f0305040303181401030c0c020301060f06090602010b01080a0e0313091b02010207020d0201030b0a 86
    0x17001402c44007150380b0240460341196584c0c090145c550001440c14944d000024941e0100307a880c000c4d2109180481c138001c000c505400403e001c8900010340240850090341c0c03071004050034550066a0894181810203c9680c004000340f003910000d00c0010200c4026407905c0c0100940c02d1002c101e1200c040b100c91008200c458102c4842c0314201d590341c0c46001d01c07803043c584440b0501e225544110f005100030807c0079080340e00b13440c0020603140c1c0c06107169200c1e00c1d030456400d950b005a400007442e19903107149241c141a0000045e100b2248a5610700f910500082d03140d00c180b00c0548a001c00d0800f0600314520745601a030032141c110481d903c2e00350320f0a000d81d000603003514919480301088801d4074009005599222100c040982590300092001000e4000020814580200440402c81c0d8a441c11903440c00c0070300c00c54900d49002c031a18003001d0303103c01c4624010515a1a1040d4200b14040d041d60a10f00600940303e110346c0003004548501440d400540162542405265001c0c03c52000490 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 518636429 1250 518635179 518635219
    0x180b0405040506060f09040206090103090c1d010f080f070302040c0c1a04030e030d020601030816080d0f0f0905150901060b04060512010608040f06091b1806150801090506 75
    0x449180168010701284c01c02d00d090103030440ea03140e0524050790111007000056155007040395041c1c0d500f03103000183c0c043c0e0380c01c19080061b07031500640090704800111000d0201070320b5516050303d0301442c07104d07401540e031099142c2d50355058070a000c1c2034000980400162420b039000e140d10400c03a04100000c060590744540c0c00720b82c840e01034540c8000381803d000a05612065402003220190f0040001c020b4006000c0d42c2c8200500c4008d18001000079105d08500b5003c40c50028a940071400c503440d41180e100c130300050079a9480300c821061802003002400c1d102801800320664001011348804074050341400340400004001d100e507592203050000d04220468014401040250b4406859501801c5120034000040c1c1c4042c08005101c0280030100c0c05481500c002e241c0d10420000d515006480c0c114412445100310301d110580643c0002544035038861400c00b6036403251420005070741c0b03031802410340352400b0000b03c0001c0c61b80c4005000300f80c0103a001c0c070f400c030100078810007503002251a400307 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 518637679 1250 518636429 518636431
    0x1e010b030304180c09081005060301020f193e0304030c1d01080606100c0309030c060c0203150c1605031323012d090b040803190c0507180b0405 63
    0xc0e0000e000d405140583c0d503020b2294200c01c080c1881d00944680c6060a07044d43c9599048285040c1c540d1a8007044095909504507080c402c0c441d01555180e0211180a80c0c079854824642c82c082020700c8001c483c0c01e85504404c0400080b4024034000b52035a600806030916403071803614000f88001c000c04004540c0561008000707100d074443c60b126000e100880700e9520081a40213a240b41d10141c14400241d42e540032030b004c0e098003450082511000c4d070804946102031944050582001d152010071000d130f01c2120081c1c0c05000b6000c442c450601c001a100134040c0c11504020003020501904030bd014050703003240030840c00b804c01c5905080c1001d030481404151980110058044240903141503040c024021148140908010203e01d0308000b00b0803081307052500301056044603521020a1a00852410340500000b00d0143e854903280d00300c855482d032000c001c0b81c41603540c2c07001010078684200040d107221940710303000d05603a51802241c0010058107030b140307656a6850b0036500d441c6e911244161 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 518638929 1250 518637679 518637689
    0x2070b1305031b09010302010f2001060914130b060a0b0a0c03031d0606061c06030510060503070b090603041103010903180b091f0e0d0b01031a07021e010b030304 71
    0x40315216190604151816a0103a100c1d040d03e07910011070706060f5a928490703130440750282000001e05154a1080303540d03031400c0050420001f088004076000410561000040c3c03410301c1c1c01040035041c0851401c03400c40044591400340e02070000c2d4540011358404401d80c1052000d4202c0100645038402c507002d0340c12503203003e00000d001a00c1001455854003820100c414442c50b080f000018000350192240c10081c9040d02510000884040295140420744c0451002d000100300b02900d034a0110340700d101c0e50308140307070149c2445c50119403403901103017440c1260041843c1031325101c401428412035810003030040c0e40490740c00c900d41455480a02594200c1d0707109903144400042562404a0144410b070002c160000083c0103141e415124030035041040c0d080384400807070703801001c4402c8540c0345050004640002001510004010b56800c0c114162403203060f100d14800d2141c219403050090488882c001a44401c00704500790f51f1080060304010b15150012880107644400f19186500680c40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 518640179 1250 518638929 518638957
    0x20c030406020609150906070c021903050109020a0e10060c230f0d050a0c020d051009080309060c0f0708070c051005120c04060c080d0204030f0c031e081902070b 71
    0x100075a060040c40714800003641702c03540c440d05007400e81d04556240001040d840c00d10480700d081d5001d650b100503902d5134080401d00070300b00203501d030728015000c0c1c508040c00300e02500c8007080c08201c252410780054494503540c904103601b649084e1045500101c00901a40d5400039086030306107040310030081c81e4403d032561000301041c56100142a1400900e10203440070404207210300b9194942c0f103280e210a03280c0490b8402c0f095040c509020b800c049001261007201454000070408005213040914400c14200f0141e50042c2c0e40c2c002c0c3e440451062402c9a120980104560400500342d2400380c020f00f030241d00740c03d07600d54440c1d0211383d4101c81500d4440206601048003051001c0380030300203510808032228a81014136200d005408003081580042848001244507084074825030b05a40c021508511466040e00060801c19803e0400e40402d690115051562500c0704201641340c0310419800902e061078030000019080d40e5544070901d250442c007c5003c0083e451a100e005032400e1044811 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 518641429 1250 518640179 518640181
    0x306040605061e0f130617060106140435060a02090a0503120702060a0225061e080103080a1403041b121203020a0e1306081002090a1503020c0304060206 67
    0x20800c401c030b4810206106041d01c6245081407aa01c035508600082d9130152004082071203441d5041e0003400203034010282040741c0c0c0360f4444056400080030f83c121000d81c4c490401180c00000d030050a84924080e81001a103100841c8200e0b00d0070620a5482004a4542e0150591003a400508150f410343d0f11b581d01da5004900040c540c80c01000e113100a020482c020807908182c0113140d100c40c0a8111701a116140110703000d0385590081c01207840000044224002166645180d0492502103001da1000521031102c00c64108213400507650900005131a060310300c0e0f00e140e81c0c908940d40081150701c20002c410b01c1d400b190b400030310050b40c05944582070b1082c2100311482c4106003c0301d15400008045141a40302010465001e0024a80e042a20f409a541d480c00042500c07001039080c0025040343c4455940706884280354003181c1521650402d5030204203140c602041640290001c440e4000039401040186460340300001d0160605405c002d030034500440411030841d0820f90120025030840c0b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 518642679 1250 518641429 518641441
    0x60e0405010c091706010902030711060403021507030606082716150f140a0201140901020d0e010b0a0902180603010e04050c01020d090e1503070f0503010b040605010f14090306040605 80
    0x1102d0040602800800320380c021400c100740594031780c03043c07144141c400d40c00070100f421942704031803c50700c01d41207108540850a0514009695a071490f419045454843d808100b00500c24020141103c14030380d079522050b19140700003101960b040b60182c0c08911000050081000c06000c00a08034271050856080780f49001c2c072035054501304280100c1081748089550351840d41254504014240141c0300d10340303900f85810240c0c0101284603185803102c072000100220031005400611419546076400e0080300c1e507a40d0224207132000c60f0b050365800000c82d03000b4005042d1503406822101d0064030003034a665084001705800c0d038400e82260522201a40411048c89404c2140d0101010280b00514901c80b9150005000c40d50600445c0280002c0c100410f8000c403002da014620105c0003419201d40640e40d9044454024052040728000d5007421198000d501e0030344a07280484006844040009940c0c1004503481d140c0c1640102e107011050045842e140c40c1040290701c1140700e6840000c0c02e04000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 518643929 1250 518642679 518642687
    0x8010c0306060908030a0507080705012306010f1706043918050609040b030309130509010c080f01030b06060d0f022523120d05040c050a06051c060e0405010c 69
    0x41c2c000020945c004c10900448983c0b1008645856810000454444c10310746001809841d008035002c0d07000c0504100b90414106015040340524800d81325901f2004007a4020348012140702c149800c003040c403000044e440d09140d08000003607201c000b4480300c1001c51810f0404610350040e05244005400712003100c2d81fa8020007694000c0c030703e007007000344803a2610001071452311038204000d02a0340c94280303221481e10b041060b5142c00b60700600302d0140c1440c03829900c00514044452035090360906800c641d0507405448114043c000c03d40c184841c0b07a007161640d04842c8005171030260440c0b42001101000021845400348206000c3c0000d43e490240e1f5450084002601c5108942d0011400441000405480005420b60924184040e180340080662814280011156140300e81d0000e00134000c8a200ea201600ca036101d49400000c1c541c03504284140072140d405000e01081040211980340038a0902103280b14040c0c01010035802c1e200c01d05007165210a03581201d50340e469407070000a035a00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 518645179 1250 518643929 518643947
    0xb0316030c2403020901030f18060507410408160609060e0f01030605061b011103040f06050903070c03060c0f030c0207030303020313050a030206010603050f04020d0809040608010c030606 82
    0xc02c080c00e01a0021503000440388800c4080d440140b41d400602810300ba4007a400c051101c6050880030403012901204100d548050f200c0101c0d1040c1c601390014003124010a103008458002e4000c0008040001c40b04003000a15404030034141041500003e038400c442d04001e0010f41440b80c081c1040281c40540c4201459094100f1014041d148805018260744600c0a000b0442c00300c81c01881480410300603401400c82c0c2d000341d070304010b0000d55411041e625103052449011814002c0080310060f84540401d804141d40003020003001c40f00500c0440d020340c02c0b181d04078803c0303800e032481c1001c035507500d1486050f41e82c0200e400d140c540360400c1c44e41e03401980030903001d40c49007410f2000d0159514000c0d290138150000609055010000c14a80c5090301694003555a01004941d81d20a95080180d545c010902c10240000c1c20b210000c1c1502c4080301059008a6010380144440c0115035101c03046c9820401289420542da0600098410001d001c2d518298010303440003d43c013400c20900400d2a21 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 518646429 1250 518645179 518645189
    0x20a0b070915050a030e01050a140a0c1e0905030a0303050906070905061b03130303090509130809120a0209041202071719080f0f09010e041e0c030b0316030c 69
    0x541c00040007491180102648050000d00c2d00607540d01c1205003d070000c0c6070b0f01441240561900341006020400c0780d00c031203c0844038074882e036801e5a55404d48001e950711117035032200045501046c0010f01040403820700748400b40b802c06456098540300805d140c1b240509003500003a407244280301703101c030050020a4100d01503103020701e40e1b02c3c00c01c000720b0040d01c10341d8001c00c007134440c4007900c0480e1a828010f0302d1450500426110085542c0d04009101c0340880c00780310b20507420030000c10031080004401d00034160f0f1041155060444600800044c8482000181c0c410f0084030241d84c0181d0741c480c01d2900c1035105545415401c040c00c2c5000789440e8080d00007100f0084c1807030140d013008400040300030b440c0341303607254246e1229810f140c81d00b403901603502c02048804004c28071100000811000e44940d40d400e9a90810081d5564100300c10b4507a02c980c098803411161444203084000c2d50041000c2c020182400314030a4004004240341a40020503c00c032011008000d0080107031007090080100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 518647679 1250 518646429 518646437
    0x140a080f07031b05033103081f0302040b060904150603050601020c01020624031609360c080d020106090e010510140a170604060f020a0e0d0f0f03020a0b07 68
    0x8690b02d018100040b240c01691004c0c840c010001403407104003181e070b401024009042844e050314040580f60b1000b00c0e080703011808034009000044a405808000c8800b007000011b402e1160ba02c0c540900c401401e0244080e50441700406c0b10110030744a600640c1c15411841d81d120900300d01d401401070440320044c1042d81150411101300405a0340014a41d170410301000800340802400882d41102c11044a903594042c010b1182a4200302c0c0d0645010b000c50701d08031010700206c070840220600c082a01c12049500d8040321034800c8a0048000702481507501c145882d00c01d003078139401c040d03180401c64121940140c0d1500010703c8121118011030a80c0007030a4000d000c94108414441243c40b0305028682080709140704440c500e0341d40a0411000b4500c0714600c145080958080d603859900841c0c042c6c074038506240740082c40811520841e0440801542c0380c85940ba0344034108484940d03a01d2041d039821402c00a42004038034040240c0e05907500c650024100c0c04118a010391788000001e2040040c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 518648929 1250 518647679 518647691
    0x324010207060e040e1504080703020106052d0a3b0903042112080702060906040b011406041505210f04030804030203130303200106080706030c140a080f0703 69
    0xc1a0803001804110008440201c1c030241704040803032a10950703041c220780da80404810300007408500e00090007002d000e0342c003d200c01d0391034400348034107010010060422071000f803280d42c3c0c40c1c01b484045617103140d02c0100300c0809159075036400800d1206040121984403051070f002401c01c100305202c1c0d1034540358480122454603105100700e80740c0c000d600c240200321784c2d00c1141c410500306422000841c03590001010081400b505c400911802c03003191000054403034040450207598001a8151240d03134801060400c0360300f4240540300e00e00e0304507034880c2c0000091001241a556501128170501e4640e030311191152140f80700c000c203c4803c80f601000f101c07842c1e4180948030001181c0e296119401d420040919111813404a1552045910140c401e41c181c0c1804030800d80d00094281f0a512640c0c603c01503580c484003041d0032103c544c410074840f85d1010a0810825000750001e00300c405147c2801654090041400100d503404140000002072101d82003103150055803002e16040a0140340030421 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 518650179 1250 518648929 518648939
    0x10050a0f11040605090604120b060a050301090f060c0207080f010e0606100e01030b180a0b040f0c020705100309051b041109010c02010c0507050d0305090906010305041e060b04020324010207 83
    0x1e0b0b11650042e030f0b08000002640c8211030301c1b224112401001d26030701c4000d06204a090035603002c1c0080c0c4a185c8102c1500100140d9454140a00c084091304095042e101c400b00303591300d5000b0b16542d6011001e6002c0c1810000c0d400034107004403540601c0f20390021503400d4112000b5030400c80c2c0103000a1050007040e250b130300a50351200c94180c000400f801c002a40521802c0011310b0aa0709080c1002003035002e90030000c081089400100f00c42c001941c00303100721420300d0103070700c01e0f00c011000000060f0f214410401c800c2c607101142c6030580300c1c3c0c5d090000716400f84d034807020b0400c00c410107101c8400004080c14105420a07100d28465401078003600c0b03042c040340c040000d00721040c2d801c01a040080f012052024080d00740680c40c01000000d2001850380a2803070064810780050103000c0c841d840700c0c000200c13154024080e40e4032403988424101001d5184001e0290710841001050703030144c0c0d072025000c00d00e4807688025805030301800d1038000c8044c05107802c0c3ca0341c3d08501e5090750454100e5941044 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 518651429 1250 518650179 518650211
    0x607050409020901020111041415090310050406091e140328020c040203130c0f0305070510020309090f01240806060901030207020301150f0609030b16020a020310050a0f 74
    0x10740e40c10040250ba25100f240040f8003600c8400410301548400103800509450210340c10b2459100540d6124111031806016035941e01400c428140c25400080070101c0390041980526402482a180011214001e459104215018011401c0c03540e506043c0c01c414000e078541c02100e22203c40008600e8031456010502e03605268200003460054403030094030b40d490085c0171081c80030201400031526031400004003500d0400044050702c0014020b0b40c0418854522030031142501c0d00400100122860081400f20500d4002988001c500007404a0075250381c440c014036006020401c0b030303102c02d94101802c070701201003000c1c0804070381115141a00741c2250131461043c0d1050003110050303111502e038001a00607110340030b00298103500c0c00c5141039030f500c028485103083d1001003600116507a01d03a0400c1d40e0602d201d000103403486880c07100140c0e501940b03652440341010144155240c0c0015613003c03070701d8040080501954035440d2810018682d00c54482e80100c40c003051424054140004903100f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 518652679 1250 518651429 518651437
    0x3070b0c031602060c010504030503150103060b0906031e01030c030b061c03081f0b03220c050f060403020301050f090d090506041701060509090706030507081e040507090c051b060705 80
    0x54600c120140c2e48055680c0c16044d00c3c05003d8441c003d00c09890a864007d003294001c079007104400d08a0726004a03294800d1285000303072900d10000e20310b00140d1404000719130300f00400444a06c240c034003002001d6650705044500852150b2011025182907141c00024824001c0620f40a803c0c0306d0318150b1841d0068159803102d98160400500584540c2a00c0600700320490030a5192404601c00054159a20000754402c810102920001c0d004020f0061540c05420b840500502d01c0c10006100c40d1404414456024000805e02032030241c0e02e82c046800d446003141c45840c0014000d08000d400e0800740f103d0040b010341c51071304540441c00d0400295050049018402c140103510442490b103103001d62181025004c014118940c4d4984170860941d030312514007940b00000d0918000c41c80107402080d546000310f1050b5020062030803a80e808940f8017100802c20354043c8100c1100003501c5035180301c0c0251035030a66071100d43e00c07030300c2d0340e048400b00c0c54601c4010300540c000400c010145610034155 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 518653929 1250 518652679 518652697
    0x206060913020f1c03020a1208070503070305060409020d1101090504060501020d20010e030318071a2b0603020f0d080910030902060301060302030717071b0606030602030c030603070b0c03 82
    0x1d43d0421881c00007046003402031030009000b00c109580c40070107261700007444410242c800d00044c2081103204408942e45541030700c1e06400710b507090020a403810b0080e040103a0054002d44005071601080d00010f4400d100c1c810b00381d07252a02c0c0d0a10100a580c4810f51402a10061b80c05010651900000030750300c18010031000e00f08074442907808007019501c1c102820a414400092180c0104944c10740c1d103d60050300c0e16400c034000803c0c41000e104020a9a00071100c40152446100461003452600355000184294402c01c0413102d42c00e41492111105030b01035070781c410000c0d20350304610520007a91741525090307100d007000001e00310000780651700f103c128040903502e102098210800a5000d00141c0070000c2d4000004000840c40d00d515501a511445135540c0c2c048440180b402c1400800109441c42d50014001c400a081d004080340200c00049114142c0043c0c0c0070b61300e0b100c5000700e80068030340039034506000082c0000c0b8035041041d0b5028040507104145000b070460095a6244203503522 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 518655179 1250 518653929 518653939
    0x230a0b03071511070306060e1005030a0f0206070c0e0a1805060402040e0f0615040b01030b0f060a0e0409140d05031003060b060f030906060405160518060403050a03050901020606091302 81
    0xc9128861181074042e0303100d1006404c03115195101c1ca00400580428052034a48080324000104429142c0c040681180c50140c003402403040300b511400307401ea542d2901642c1003c001c00c2144000b9403154460070007818100c10052032030400342c1f44c1c40e05840c41b40301c0000c003245507802c0f148017181011400c0b1340c010b98101c0d80021780d0305114124505003440412507408034000c0c0701c200400795400300125149090119410046d8202000065007114001900c0c2500034048000300415424070030000c1040040c1e900348206195001d80004040c0e03031484604880c01c5400d03000e960341300b0400300252420701d05641800380c15883c1c00c050315109900b85100c0581400c1c0c59071a0f00149440c1c410440f80240d0400490746da5900d03241c18515a40c410030348116008e6807a040000b1200700540492284602d46603854a24104503020000035100c41039080031717849035082100000044040050b0240c0a01c00d84880d1780b0b840c4090006030824600501190092012104101800107000140036440b41d040310303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 518656429 1250 518655179 518655209
    0x711120c0312060d050a0302011a060a050706050a0f060303113708040504020403230304140603042a090605060403031e0917212a0a0204230a0b0307 65
    0x10010b4444c10994a0261450103180b6422044c55410f420141260100040e000210039170b0340300780060791286481007400035105009134400500329400c00354000925100114200c81807040c0a8229407283e441180440c07000d454042c0352440034081000c21095880344598031082c3c2c0030b40d100341b0f41c1d82a22000090654081d5003000c00c84580c0595014000c06041151203c0d01d91400c40b0340380c1c1d078120103249007101c805800c10700110004226000c0d81d04003003100b09442c0d804020302000340c2010b00216035061103220b40030302001c1020611070441c80d030b400c06189401c6c41c0401400c100d0b4015045030340074281c02c000038408644c0140806045c400011008011103075004d508481d224500e403c00c0140a8500402006c00440001c00c01030603c00310b2400003152904003068403039445500800e8000901c000d00701241c05058100f1201d000d1146c506640c2280e02c107500003002c0b80c5900e03844d0301081d64141c40c2c0d070303800110250325990f202c0c102d0308003044400c2807200000e540d031300c071449101408040b1704 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 518657679 1250 518656429 518656441
    0x6090a02130507090b0d0f02040b0405011205070e040902061b060402011d0102030901080405010b1e0114120f0702030403060c031b0f140f0405060414090c03100b030406020f030711120c0312 83
    0x15100c1d11107c01b0b071140441d10340307031102c412510542c02445000d002802c4469088004002841202d025080940310a00f80741e0001e41800040c140008044c2e91100f02400302c02581d178000b0080d1001881ea0b1005807249241c2480050280b8640040c000b03100d4941c4115100c0c0769800000f11003f000003401c1c071000c40c0e507852900a0152800860703581d0002c1c4a0710030150706000381b240d1440101d8003600ca02c00200b040c011700740034a00a2044000034032100801040082d6000c5801503040002481501d00cac1940701e0b100c4805851803494144000f036607030240003000c6120700061180c040424902815400c003503c200410040c1c807a8080d02000000145030305040054000b11802400d01a150540b0b4940c1c98101a1000d280d42e14113501030740c400b00014442101c582c040328030444014a090000d06d003050442c1c00c032a0030080040350315a40c2040b2900420740300c2c0003e103105040720313a2095562000760101c03d040000f01000b0080004040c8002001d450021040d100c060100d0704120304155511 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 518658929 1250 518657679 518657681
    0x271e080d0810150807030f0216060b15030c1309141609120f140a0201020307110102030d09080c0706030e1b06120c12070512011202040e06090a02130507090b0d 70
    0x2e68415480344081030410507041e07400248261040a450b00c0401c01400282070301c009911600c0c030754290340d10410135140c000403400e50148001001c05080c41c06020325207038188603260301c242e5000b2901e04012803119806180e80d0a560054030003030784140a0711501d0410b2194410780034102c010010200c0c82035280f4a80304141d1300008022201041c81002801d08004000c0c1400420544000c0d051030240c1a0500700010064482503041e0300540c9002c178103860b59052400817040c614110300080044054003611750190310740560080a0107691450422001440c00050f0360000041c542041ea900d480010049078a18100d00c1503c9003103180c015003000256184144194204004a03940901944c12041d0740039160b400489420009203445003181a1340c03e00642401c0c2e50701c1d2102c00014801402d0300583c620001c0c0c0b0140011401c41c1c0300a03002810480c0c00c135110b085640c86981c03c0c1c0158030300800f07201070f0704801d443c0c100028188071400804005103402200e41d140030014241c0b001001c9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 518660179 1250 518658929 518658961
    0x1050409050c040501060329030a03080a060e1518070e0609040618090317010b0a12022703070e09031602011404030c050a060216090c271e080d08 64
    0x1000f0420041983c4404002d802450060000e503c0d04640c8400d03081440e040d642818104a402001052030700c00c030b940c04586111000301040d1100b030300d55400183c0301c5608030a031401030b0201098117140303050300014440a0008080603028803107440080c0f04107a500014843e007511815140250b680f161800414050003a41c2e00c00740000744035a102107215400741c0e10624015100b40d6420030b00c1c4951000d886202d0310207005240c40f04604001840d80180104426240303001020000750a00d866018144094500300100342145003c1c00314840c10307807038140030403800307400048500d130030b64180000c0c425a68055040e4540c5015114607910040d03a00035000c2c0081340321001007156903282c0764a06014081c2c41441958019118074401068050010848410210300380c1d00c00e8100602c0c1215050242c0301411161052141d0805845161052a00485410780341402510340d01441c00f07640200205c12401a00c0031840b201c001444021400b02d00f40414841600c0c191400d81c480c00107962008407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 518661429 1250 518660179 518660203
    0xc120c1803380a0e0a120f21061e030807080306180901020903190206121017010e0706020304060203121902030106080906151513030503030f0a0b180105040905 70
    0x300b81001c40900410b0503611600c245264201441850788808030241e6071008010010080f80000403913002881c4203141000c0c2d07110052800c0b003a10102042d41d00421031918040e400f1a0b501e82c441440034180b6a0895481d5401450074000032524644030603041d1f019204000380340c4140003000c160199500102c406c0c0408005071011a42d003080e40b441e500035401200600e00034003591003d0240c09150a1303022501d60f801401080c900340b2116019101054010600078640c0c20604010a030000b03414689464211803c000144403070b100000685440300366442001154401c000501151740d0110903030301030649186800c00d05440341d02e6098810b0002401281c0c4071071012000103112580000e0450050f01030009980c0d1680300c80f104919440480403140ba000000a50b420016400c0d02d40207100040415040740921510395035a41d04542c03050b04c990011780140e02c280440940c01d846020b9490404442003108140000748104440302e05210f41031095a40f0381401d414080c062040c240110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 518662679 1250 518661429 518661503
    0x4170c040509100501050d0825050f0a1406040206040b0d090f060f0f0b09070e04150e060901080a0c171014190204050315190c120c1803 60
    0x4508000300698840740e0f0340c11940c0b0030342031000009a5081c804404600355400140903480d141c81e030490b4107403008040024000351403041e800c00c008101d007804001010b20800001e401000c400e401c25078038086004903400c40326007060080c0300069840000301ca0840d50b0b0041c0e80c0d5114400242c8203001408960006001c4c462400341e8041040083d078403e0040301015841046604403c106404c11a50740e400d5403500810410b01003002d10f4000c140b201c1c005031004201141c031101101d00c40308096100d078002a0f284028400f840320f24a000c000c4107002d802060020f004030b50f001e4840040300e03c0c59104006904004c0c40842c0c01502c0284011a00b0700d16003030303003800500319100c44c0300400720003190103408207030200c01644039981083c000c0303030100c0740010700419680d040c5d0000340d12032000180000c11003440c80d10014880d460340e800303044140c1c41e10b43c440d11010000040c0610548400d0300d240c0080041c08140c00c0448005002c408059a800400498011080e151b030060100240441e0a82003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 518663929 1250 518662679 518662681
    0x506031f030f0b27120309100905010b011407080702100c05030a020c010816020c10030623010315030320101812090b03040b04020607150209010e09060604170c0405 72
    0x84860455141e01541c02c4d0880351003002004c003203c9126410107951000a13402819803155044080009980c2114200c0306440f16515083c0c0c1080450722800000c44482c0d45904080c0b0243d80c000c0e4101890064454081e4501105039540031200d1041d1140244101903100d140a0100d206030404100c10b40d0090441c1da0b00d00200401a580c3c0c0307100031040380000c2181c000a1402c90380044a101a150503800408902d8002000c005400708804040010140c3e0b820002492000c05a40c0310380c036240149052820502c1040010103441c041402c504242d02c08890030400a07600c519040c2074014440910004140b134241a103003032030742620400210a060609103207400f03520701030300003000d4415049140031170580e144c2520054101d104a95089400740000340100321b20491135a40a407005101d9441d0440d60b540f860564200611403042e10b580c041806001c55801400207618000c0860780940309240500000300903101d5070088215041815030070714001d0000700007140c2401d40050081c845 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 518665179 1250 518663929 518663933
    0x1020f0a0509042a080a0209180403081e070503040203010b100f0806030105040b06100203091305011806052103040e01270204062f0d08010f06090506031f030f 70
    0x189801980b00c20f4851841c003062902803c126058503040c4211404942100424800050780c10580040074602c3c901d8003000003100658404030400300001d400c202d0210345041c6810010070007000202001100c0c41500350b003056178106909615400ba1036460410707a25500d610101c0d02400c0d80441d415005540c200f80090065000b6245082e1040540c0d80c1e480e0568a101c101400e0f0343c0c05580c05441401c0e00c5011440c5804d044180c03a1a009050044a01e81a11003002c00c0c0c001c0300060700c04441560302c01c01480740d420701a80c08400200c9a8070280056400c1000040035000034034019201d44881d011922000c40040c02a1340c000d21001000641715a910440030f40881c001c0303096500d5080b20001c0c1120b001c90703a4400d4074162007081e964820240c95030200d5101803002c40302d02c1100000e120560240b0303041c2c03c0240c200c6011490342d40c1e04480d494120816450070450f00642c061180c1d0703080900c01c5860356004d603644103c100d03000c80c0202c080d10304041101c607030641002c0c03d44041740300d031241 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 518666429 1250 518665179 518665187
    0xa020d020d211101050f060d050f03030a060e090a05250504050405010203070f0c0c0302010806210703021002150c130302060d09230303060d06020f0703030906060603090309120501020f0a 82
    0x816501640c84000030104102c04044c222202111406400041e10000ca032207400c0c0414800b604034071980860384900c503c040c24502c1e42d0030491f40e000c20035844240c14814140110945604003007128018010550603950302500c8004c41c88034440da03018040301401146000c10508001880c2c041c02c10003c60030141401800307544100d42d40c10100f40c03101c68103440c00382709825141800b0380046400c0307219820360307004442c0890003602c80c650009803100c6140b01000011103080c81000d202000301850791451041c8140002c151012070b0030354012040301ca040b8025080700036400304155107140c2d512a601845d20b240c8103079940000e07401030303c04140d001207121a9404001030074010626442c544440c410614032038809981d40026642090010660a04008600070800c5200c1d41d005070800c4403404180c91241c120701c0050740000d448105201c280440741c480c14010f008141350030310806009807005481c50301148542c1000e9070282094906200c0c1c2035040c0c2c1e4194040d0441103580c1c20030460020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 518667679 1250 518666429 518666483
    0x18020306070801080712030302130e2707050d081e0a11060112080306040603050d0e011101020a05040b1b010203010303030905150105030c01030c110304060f110309030a020d020d 78
    0xa010384203031004140c1450040c00030300c0c1210355007801468010300304507900d403207011402c604405054017071100d1220b0300c1010701400c0240800b0f141c403e000703190101c0503141e014001c11110f51342d61444003403410107400115008040d01d0040e00c0440464100b4501815580305018618080f030300078000000207401c041004281011055454029818070307601e00607140d203020f104030505030b0169024040094085006942c2c8410000e00020300540d4a450307050809486910303c070001040361541071200e607004800d15404d03000e0440214102030050102810700d11403406514160440030a284849144c10400d00340d9185600c0000e641300d583d20328014004d0800c0300c00459240c00b4810340d40e400c910340d40c0322242c101c0c0c81c010000c016010364500194024030120741c00508000c0c00084005070101d04000820003094940d488001c8a81c018034000c0417a02503c07680c007150b4004012400c00c80d0740005010149a0301250342d02001249840002c4c9121803003040240360b580c0c400850341105043da0481 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 518668929 1250 518667679 518667683
    0x2120a0f0b2e09082b020c060a1413090605010311030103050604030c150612020a050607030e01180b0c060906090604050d05031e04060f0c050426150f01140109120b1918 74
    0x8252980b1703103403000f640c48003031960346c854101034244911618180f18032860041d06038075002c428907210907981c01714054402c90b0800c80d0380c10384a000070842c55a0611a034241070030841c096a06550460740c030182c032030b180a0000790401940301c80400c00d20480c91103084c0c00d01d0740300038204039842d51040c2e600c03020b441e007000170f0b0300c10300c510100051241460390071074900503815640c4045d1039a1200055403002c000102480ba0f001c00c0040208241d641d00700204004041800101a14035001000602d07090006040d8070342900540140800604002100c0008800302c0c208240c032603a0b2518512803901008040d4290341030074400380420300561b54001180c40e01d404900b4001c1030183d841c01d440c244114030851800246010020301002d1902c00a62011144002030f0303540c0d00c41200c1e0508a0000c107454903401d100c450401048001030008028520036428203121000605d000d0650a01c3c070b4029074060454001180014a11600d00e03080d40c094070500401003005081000c68056185008181 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 518670179 1250 518668929 518668993
    0x903031209070506040b12091603051501080a0b011401050d052e050a061d0409031d0d0218150a0906030308340302120a0f0b2e0908 58
    0x200301410030f54100d600b0380b99001c0e10f6619003e040b0320b114070350f0000101842e0230350081400c1200d0803000e4031222801540160010700503074400281c1980f40c0041a48200803a40c0064031460019202c280c1007411070703803c4c004100b28403030568010303100c40c881d13802d035180213602e4101000407420358120260b01c1000350591050703000040541c41811002c590040702e5000c246c244c0c04120580c881c5041c07081d00303964900300480d0914081e002c10195180c94108038041046103c1c0c80081e41c840c00c590f01c24006048900100760751458020a1900e04880680d0002c42c0703205001940038151070218080440303024210078807040c1d54443c003100514440c003044000030059000f003003140c903d0550f08403130260044c44840c0300380300e0000607500300d0400520100501d602030140030700381c4660800d218419292100f0100b002d001c5000c1000444806c02c1e502c6200e001036441040c0c502d000000050b07040504070014550400d1002d50903150400ca81d84000c2075845041600c80e4200121051030084181c0a10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 518671429 1250 518670179 518670193
    0xf080a020f0f1b0301020f0a0302091c020904060218030a1110030608060115090e0901060905010815011e0503060c090307080d0203070b070905131e02041809080903031209 75
    0x81c4142e11200111140d6005502c60204600c104003e580f420302100b4006000501e01034400d05d43d4407841c0c000202c4c490220b80e004c200303691a801c00000d0104c018680740c2640241d880c490740002c0440f040900050500340d40400c64840041d1001d1410702d1b45c030303001000c88200b007025182c4010030b41881c02090f802030221703160805000380680281c100b030320101000f404041e820203115005154506004c2e1b01002080840002e10350700030f1202d1400361030b0820000c5007190074070501c242030b600103904c000440c0d48801e000c4040d11214a1a05065800d0203250395804158508006c0303c2c0c02c0380360001c0354980155018000c0020000000b403102501c103505036100f569560806a4540000340c45901c0583c00410041d400030b0810480c517a400045c42c00c00c4001c5c942c4800102d07403a48001c143c210140c07560380802d04515450454070118010120106614185c00c0800d11040d10810b6402a44056110520301c030401c111203041c1c4030f54807009000c5030384070907480d5100f615008080e00d0581c45402855 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 518672679 1250 518671429 518671453
    0xa05070807060506040b0d05030702090705070b040b041a0105030a03030e0f03040f080105130203120703140c0604050c0a2601060b1317011401060c02030705130605011202071e06090f080a02 83
    0x141e080c0c07c101d40c12501850910806409006c11000000c01540c00c0040c20030110001076210301540703008901404502241c0e14003450403003011941103c41000c40440540104040c0c4d4000440551195141c07078081168480c45804a16200c0b01c10b15051817400302080200d19445203c0c5000102c941160080c40f0b16103404a400700908101d18019415030000c4001c1c1c8000d004840c01014140d2003032405c0307203804540e03401d1031082e40c12002e0345004c0c5030810020705c010701404000f90b80c0c030018112880301140342b5015800481c00d4080080c0d0010144800500f880030030203501402c02408000341030b43d910b44250001c2c5130203804c0f41c000c0d024100722003124007120a90510130701c40065020340240002d07900701441518008042c103400c03645442205008a469100d40d901100c0d00340c03080c800840e00509020000d4408841101e0440d0002d00c188180300100300411900c51440c1d92029100b483e400300c500304400580701c1c40c403020b041028800791040802c80b2400090010244990039681c203105a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 518673929 1250 518672679 518672689
    0xb040204030209010608090705030714011e0f0c080f070c150e0f12030712030c1b05070e07110a030e040c030216080c010e1c08060a0612020a05070807060506040b 71
    0x303800082d400412000043c04858016444241c1100001c400c07258041e9442c00004c2c50140c00d03421910794000c11920340c0c003c65070000280603c803204510455100d007101000140112480410380d01040102d4400c8006c1c8500e07141269001a142d046141c0d0707074509810300350800c2c1c28502c0348988a402c0c8080c1c3d0252103119210300f440100008004081c03601d004001c020032485121003aa030113020412006001403446451412000000d841c04121200c81f454082c05081098003002c06d401003810b02900019000304280c0152a80d4280b41601529251070803a124640312000300064440c90501006064008400c03545040301200c040c0605484000b04a003070780514840340c414200003030040000504108041c0520803244070000070a200908600c5141461005140c2c01862600403102c81c0e160340141c03540d5200000780d803c41401d41c540040200344c0488030710301e01c3c2c2c0c2684c0814001f5820344540700b21131038160000596601e503170351400c2c40703002890180d0740c4074421450505c00602c64100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 518675179 1250 518673929 518673937
    0x1b1e060114040f0204051e030606010c080d1d0a0c0819030f030c031e0e01050c120103110f090106110106080f190f0203150f0705090a140d240b0402 65
    0x2404548500000e01e8040c00007610740030f01214540e0341c0a000c04200380d118105420421a0b103075544201020150040c0340c1400f001030501810000341c0640300d80810916000c1310060b4070a0344c40002c0070110106001d014000710040c0c042503000312605502880380255050303003a41c10b900306039641920014001c80c0154048100100442c030500c00301000c050180c0c0c04042200d446080102c1d840c1141030403d0801c0050251481410fa603070054a0103800e02407107140c0e40454520a40c624004844400b8041c07018140b0004003200300c0e03000c8909007501e60070f005940b00725000d40120a039584903c0041d00d590220100d2820540c40c000c0e000a40c1c1e480012180340c0b145210014051103101010fa45040d1004c41d01c0036a4840d440445d2640103840410246000304042482480c89090500520001d03c101070f040104003c000e00c001d80c3ca40d0b4403c0201d404541d01503800240b043c10103404a5010340c45d0318409020032000d201050321107015484901c2c0b00c4c1c084960204156120394003004200e0007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 518676429 1250 518675179 518675189
    0x507020610260f01060303080603061312020703060513031e091a04051f0f0509092809050105060a050d1208130c0305030403020a150e151b1e0601 64
    0x441c10040056200a010802e55954000480502500d240450b9840c24161801d01c6103a40e54552040080c9640f01812a8200740308401500f2281011380f80191903400d00e0401410298200f403901400900811000d0700641d070010007840030f46040c1072402110380c2080300c2900031030b10f12029101c24944000c003003800b4519a4a50411103401d003a0481c0d00364200908102242508020208007070ba208840c400007044902d07100e1661090200e001401c582a400400c0113101c1d0520204d0b504d9510150340c10b81c03240c0030002c080303038660750b0520340700414101c01180c0c0440e519043d82d02040c8003042d04041d1113000d0590b00ea1000b035644405004c0031100380500a810801c1e501c1c1c40ca00094403c611003078000c0c5407054504040030f81c03600e038400521803581c01100c81e540001401c00440c209040008028695500c40452103c0c554002410b060012000315104115003a08107a0b80c016050581d0041d030160032207944d0600394410380c2070340d5804c807070300d82540a11070442c4c01030034440001d400340c1070365 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 518677679 1250 518676429 518676451
    0x17030405210d271b030b07053a0f090b1006020705030607300e07030b070c1a100e0f06040501050607020616171309050603070302010c0b0c1e031503010e0307030e030304030b011805070206 82
    0x80c80049c0e000008100e040d03002d503002512180c041c8081003401c04a640181c140c6103035000c00c10b281c010003a25041d0366600007406074002008108040360403502480d500582c040034821002d02404070640701103200300d08085041c4c50b0032821b070110000020f040003582e00c540292a16902c40a0055808180d01100140601e4509039040300981c0d1540c01a40c001c0704411216003841c2c0c0f85c010041c1400001c8501e00c0b040b090010401440b8a0a8058a0300418040d2100740c500301c49900440c483d88640c0c81000307009070024500d80c00f0400c614224900000301060400c0d01d44a000c080b046050010340b0684500e2810807002ca40b852030003040750002c4a50584500444144070344d96000e00c40301c02086003156a80a110036400540007011070042046580f081e242c1e24a0f2000081018030b00039a0308070300030f030b240080b402451b090000485042e0354050814075200080f0f100000c2c07075807295400c02449001013a0000035114010310a100300600301d050306003c2c6903540d090483e0b54081c1150704a90300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 518678929 1250 518677679 518677777
    0x703080c1606090c091b031104030c0b09031c0201060801050105150405091902030a0506100903080406030f0207020a0906180917030405210d271b030b0705 68
    0x340b20764001c0040c0c9204404562046996040d900e0031110044201c05d008100e08520a8845d41e00d071090303002d201c00d0b034255242058150b444402d1015250700074030402c1c00001030100712550f01004074681d60081c1720104070034251100402401b800c05071284160640c284800840c0074500250340d00380c840001d840142c10326103080100001d950002d0300c580c151009549142c1952078107070004600c602ca1070f000100d032074101a4240075940b50018014003c01c0800c0a090000841c3e4400310f81c100c407490300c0c0101e50035640c3c0000b24020321500e08000d501c82c0c0c410300005140565070300048125445142c1200f01504400c003000241c1d490076000174800d8050f20400d03c03280320602c01440d08140a1030444010465a00c1000c102d50401174803c20b9940c004030303000001030400e010b480c04180042a1981001c9581c00081c90000c00d5500c00603c01c0c607403540034240500d03465000000540d009000c2008600340b010002d0026440454429140b00504044e031001d2400c2200c0f01c081004a8407002d080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 518680179 1250 518678929 518678933
    0x80d03020c0a08090121091a060918070803031603060812030408130e040c14060403020d080f0c1204050109060807120906020f0a0509030f010c091203050d0903050703080c16 76
    0x255001013a89070501880900e110084111800070700c1c50b418407a840001d0304a2641442801603440c982c5040e02100f44e142000015101d00e012541c0000240c20100c281200180110b402c040c0e1580282a9911002c01040841c19001070400c620a0b02074804005090300e81c0c1c1c030241c9550603803842103040e2034204003040008605078018036034026030b80541c0d1079490301c035090070039010f03c252002d980000103500c00780800442901c140740700002c12110705c3c1c9003524503404242411012040909040d0011920b200c0880340f01040328400403400041e1491407024010f0901e040e0440d014507800142140740104605000760aa24029080d07a01c5240c86240005040c0001d40076981c070484020340c0900030010740c84107031006005417190700d449041c0c4a050040a0514000c1c44800316400c6a0400d07414242140e0000c2c8040c0c1512203603241d03049004c80b2400c040d52140701710320708012401d04e400090000d0560080182c96124131a54400895890b21009000b49015800f8910911003110a800340 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 518681429 1250 518680179 518680193
    0x12091f08040b1302040911090105040218210322060203030c0f1e0310030605150f060705070f0b0304060c030c0e010513030b0a050f100b0a0e12060a06080d03020c0a 72
    0x360040352052036100f803583c0da40c0898141c910700442160140c4400042004602e8005500d5000d4101604c04504040b9009910100480d51880d42c034002c101c03c415000e80b02d0f26110300e1303c0d13a8600380c8080302d0391031901940c004a802d0300080e00c80034280346102c1c00b180c52071010007141e0140c200507a541c0d00b010420000030403541d000c51100f1009500100c4c1314a100000f2402030761003102e00d101c2c220b40315441d600f0490700340c035001885076038000101074080300d069650001c0300b092058159000b940350846441c0103807030036009801c9a0240101c40c000000d886200740011445a44141c005024940d0004015001d4424007016071011910124508519520a0340600402e03030762440240507080d03680d00e490504000980d461044a0b07200c03070412042c102014040c40d080411104d03c484468600301034600c0d1401202c094001b00302d8030200703140c515a95504001e2803501e800c03040d60041d0078800c90b0b9000400c0c4522a0148600a01010743c0c9601d02a10075150411803d0001e0035943d8500e548144c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 518682679 1250 518681429 518681431
    0x806040b0112111509030d03060510050c0a060c180b1e090d0312110d02030a060807031115120f15030c010801050405070302040f0914010f060c02090402040e12091f08040b 75
    0x30b116601d00b4091200f140ea405c0021f40400409601c0004400f41484c0900044c0150403440c10184541041005100b0500082c4050b103260850340014031780b82081c000b19160107601610940140005201140700f0310454010044595400b060380306000c00d0aa10300398901503505003603131000d2504d5a980100740603c04811820050703c1d4005009040054405266002203140d03d410541c04810040f101807180b040380003400340b42e4010140d0629568908602e044101e0165004031030000341c44d04011800030030355408000f04600c00340c042c036146404520000b021541d40f4006117003041811200d042c041044a40798006950740c1c8503aa00b000203210151002602110406030308210001b0304030181c12040700a840c814501140c6403109404a000c54030040e0030030305100c1c0c4d078850b0400c4003542102018010703c2d4142c0c0c030304403140d949000140003130500c1d10051245004140a007500300107031a0051071458022510b56102d270041c0d105500d03241d0107154203413002c56041b40110340800e03491031400b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 518683929 1250 518682679 518682709
    0x90302060d0b120f0a0c080303010e0712060312020c04060504050705070f0c150909050a15120201020115171005060d03110708190b091f020a0203130806040b011211 72
    0x1d00c05080d2044413450200c406005041c10b030007a0740c079001003004000d0004000e0000000540c1594109183d10b40315030809071024041c4201c80103061003403942d94000400071030300080c05a1034140d1805001e91141c1034280003038400c40ca801c1000c0f480c0d00c1e1603c0303400c0c01a00c15659050900d42581d8403150728140084066800b43c03910070703001402404040c5030b040001d1056071600f04240c40c120811055480181541d0b000900340300c0415022000301c070a910440384e40301400840200380307000503801440f60041d902d681d050348040c0890582215178256a503100b0b140704859000f2500b030004401c0319426114164480d28017103581003c01c0c40350100004004440d401d41c3c080d00e80c2c030104249882500b19070341c0e0001200841c14002d029060340d000c3c0c2c2c4024054003501c1c207411100b28a00322420886102c44030039502041080c1098230800540e1b544c0c02d000350f44441e4007901c0d80441d9940f02000c0714202d84032800d441c0040b40b0400380c203003018900380d03114001c0412500b0b40380800a03192000255 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 518685179 1250 518683929 518683939
    0x30f0d02040302130605030d0219030818060126060c030a1e06140a06030c090513020d050c07020319080f0306010c0618020108070c050618010b0a06021b01090302060d0b 74
    0x2c40581c0d80e80b9401e21406035404400503900c1e10b01002c0c541003c154030320400c00d5400060000c100c05844507081c0c00055490303c2d001030b040d0780d10070f002e20303070000160340406051103030301c0001c1090003c2c0100c0d288440c14010800c0c0000500c100644c0e40c0c0c0000702e510203100002480840c4c0c448100c2d40000c0b00381c072030f039400580e81c04110060030800c0740c003242e00480d6100300844604074107080131102c41c001b51031070349018020341d241d070080a005c0074664840e050003a080d114429611074443d5043da002060081d00034412418100403003207498000c0c3e42c06030b03c240118441510b440b002010f10341482076012030310718104501c8001240284d00018071072418040030344c0543c00002d145105000c1c1002c4245004041c0c140d1900006201580040c00e43e000c1c408000701c0d6801040000030129489492015205130407800c113580f039170140125040f002e41195003403e01041c0d4a4001c1518140c00c4207042c924107158050310700444198402e80300183d00b000041040004050880c0c0100021060140c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 518686429 1250 518685179 518685187
    0x111030a0909052503051015050306090a020c01110c0d0203190c05070302040507030504060b0102010605060f0d061d090c03010908121e090a05060a0b03030313031205010303081f0305030f0d02 84
    0xe000d40304846480000d0010386c0d41c10802c4800c140311068180540030700301c121180708200b100040c083e8800070303104a21039801e0a000400f00c01480d0116560152000b000340312030740030794602004a80280f420005580540303814049803c2c8004240c55240c1240c206003194000b5017102030ba42060041406d903040e000c0d40c1c8001c40984c60b14080e040c0510101c1c0c0e00001c2625150400d00110b92890000034116410000d08000995031102923940240c941031145907580c0d0041b80c4000101051360200c20020381d614041e0401280c01602c09110b2007054040d40c01800c5404105800c807514020014801e500502858080d0100640015031007071a680f00d095072003e100c0d000080410701141c1a0380c1036401099400200b01080c442203800c040d40c003005200440a41000039124000100800b110307542d040c0b0407009251184d00f84800d280d14082c0e04011550310382c00c006160a104481e1490191550030030400701c07407060f10281c2c04581e0010091410040e0032060f9007044d6200114107140305400348 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 518687679 1250 518686429 518686471
    0xa02010609020a05071b030506061c230f2103181c0e03010212040809030312240d0c03060203090c150403020103110408101d15060111030a090905 64
    0x302c0185808001500c40320b031201c0c06840c0c01c030603804c00c28980c03020340e8128000800000e600040e0b40c0303800034000c64095060f5103050111525010344218082c000c25201c04c0100ca0007120707142e4a540c403090718400d94484959805805566200740c1d89072601c802c000c41a4401d03003065220140d600310f541000540c00400080440c42e24040d40014184070141e83c0c140000d0a03103070088005a9809030030740c002d60914900e81001e034000d0100070000b8060500c0051005081d81e414002c540c984c0c042807034604001e01f40f1130342001c0c085881040007140d4030721043c01d4062620701180031421456214181031999410342c0ea51801075040980f20441d00c0c401c000b000025a0303610b1410001d410006012544c1b1189580001800d0b07800e07007120418801720804c014486420301048009011841400204a201c030140324400721000d1030b6402207060180074030440141c6540501ca6014120036078070b0703419040c158400315450340702d50300c0740c6c0011542101d01000b0040403a0804c1e540901d118910b102450404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 518688929 1250 518687679 518687681
    0x9092a03080d0b1210150810020901020106030803010e060a0b040806070c1b0e10060309032c09090606011106060a0e0907090207150515090c0702040603140102310501050a02010609 79
    0x702c010080681c01a00d049580c00b80306120341a80c121b80e80c8620000301c0c2c0741c408810348900d40b01d107041d1401a0000b402c00180d9000f500300d400210341c000c807595601c0d81d4a030f103103e80600301a14810b203e4a4448800517070348100c4416501a15124005807815848140781a90604c4000c4003c03650405007958032090350b40b20410760002056400b14002c25454186101c901d44c24003074203c0000d03d464152031102080d07004090b0041d07080e406072000f00d4001010b0064400121003501c46901420080c1041084080441e40501030ac90a07264621410040c032100343d04e1741001c99002d604050b070301904108076a00c2068140d005501c40051380d8003103407181421016030340103007010350382494982c4040307021501611605030720144800a102c8009901c00004040784005045800d2698000c03c80d0820345d1754990050005540c040121000c0d054070040260103508826191529149a031a02101c0e555030b2030006000a03441890903003807207060900550360764000040c02ca0840d903868401160301411 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 518690179 1250 518688929 518688949
    0xc04091b1d0a2d0f0f1703090916020f010b060d02090105070602072d03020d051b010606020705010216050d17070f05151e06060c0f030409092a03080d0b 67
    0x1151802c60100d01d1081a02e070101c00303440d4032410343c07507440420030885c8218035400c44050302e014100700d090150b07031140e04510b54010a041d4079484000807050040704101c14069070031034030071502502e12010003110640c0c2201c280c10003060b0008401c01c1114443c0240e075000b00091007050600300d05188481e11100100c0c3c1081000f00c9000443c0f10800341c5403c0d00b0307100350304100b0f4208000c4a0011242d94002e481d0030410440c60180b220214000030006480d205000007100c000000b04101503458070000d68900880c0b04250240c020032121040b42c0e800355122006071400a00030982442c0305a481102252908032015030700d00061004900140444507900c500c1e902032001050148107550203281c102001038400b4800c6002d01d1140f2182c0e003242583e5907403000c4201e50302929400b061454500700910300c003400070903000c000750105011900364846607865000702c0d10050650081baa05980a4094030807000e800400300300204001040e10008150801ca00300303010810218450116542241c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 518691429 1250 518690179 518690219
    0x519020d0e240c1e090d02030f01060e131e030203070803040b01050405010608220302100905070e010504150909020105090a0608041a1e0c0c060c04091b1d0a 69
    0x81d09094610348410039000b41e0308140440169403601c55549143c203034020035608207283e2204082900394507503545403468003003241c000e0b050b15581c1c142100750078020105405100c1c2100c000e03101068520071544c0043c0d1041d64084607101030a61900c003600f20f0260300007411800c5101c20028180050074402c06540240d104210480007541441c5c02c00c4241ca9050300220100710314402007049540d9046502e120004c12405403c0749849141000c0781845900c20600c442281403288584c200040020410111911810b01c0809a600d40301040259400c80c088021900c4040b0300c18041d48990f0352151108500c141419841d080c14100842da5103580c0c1e80c00a00071a10020402003800503a031300040380002c814031014150319110741402072002d1071022604005c2c1140c800200000d401008031a80c1104040440d0f80d186880f0141e4195070b4081c0c0920301c400c03410000c13801900180e891081981c1d07035060300e915100e05400c1c182e440c0e0008001a417a0342c80700c0318039000103100444c40c0c0d92055404d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 518692679 1250 518691429 518691463
    0x15031113260105070c080c0c0603090c193516061b0b150418050a050d0906080609040f0210020106090b22090f050d050405040606030519020d0e 63
    0x404610161001481c1400c1c1a0315070b64100400c002c0c030a50302400480300c041d4080c102075100d4110031481e41c5418010a409a00540c002052200c82000024074608403841110984210030018040502214080c03055909503010072800c3c0070080b0040c0642c1c03201914202507034001c0c01c9800b03c0030f403070911900040700340741003121000e02c11542e00581614003100c1030b842850864503156210111480014140a01d84003d0840c044081d6503a0b0400f8800c2c60f40603840c0c03025403065040c41c548030100743c001100e5074030601d0300800d186400358a041c1d08880440d26156084e036169414095454401042150013103550004840140d43ea69442c220601580d40005107040c00c00300d050084850b00c0c80b03c01d106048985880e14003194140001d0b1071188600c4002c118100d00b0320304114040e5040b04000d1540c020005408240c0c0c0d40300000e0012250103d80600405540344020784c2115400e0340d42c0c1c1c1d1220001100d0000c2c4481c180c00500c0503840c0c903070300004c45030000f10050b4245010342c0c51048002c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 518693929 1250 518692679 518692709
    0x807151809060f05242209021b210d0f09050c09070804030f140d0c030e160f1a0c07180c030c0215180709021b01050c0d0509211207030615031113 64
    0x301100407462729900507a000401815417415223202a58030340000541d40d6010010300340140702002e4005421800048005001c22507003480d010b9160020924014010801c038800900071034401c003e50f5004603050703112100060680c5400f2200d941c411029190b05041c200841d031441441c61288500039040e66a0001d100d00102001c1c0b414407191001d0000c0c0b45114100c1484158078041d0340c1800c45910209607003406c10545c408406a02074180005020701841c10300203078001d0407008010710743d8101c40b4108080030f0410010350444050340a4400140d002c0c0903140d00850503250069000324040300500050900d940600d03192603c00e800c0018081d401203141e51501c010310300f000c66a00005c0e0000e10032440c064a0100c0d2902810313200c014410b4544010601c0e198081c00100980c3e40340400b01144081402d00e80c0010b45c1c419900300c40240001e5000506031b5200b4072400051b2150b03194007804001540318114040c14190788840e124035010000092207a130300b0030007200200b282d14284800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 518695179 1250 518693929 518693947
    0x504240b1203120723030a0e0a0b040c0501090b16020d02063001061b0c12030503072c04020d0b040905070602160807151809060f0524220902 62
    0x105400242026080c02424103540380403e00d0040854403100c5c01d00400c030f4507a6125844500a0404040803d45a02480c4c003103000740000024014800ca00030119450110360b20300044500103034501c6980344544060003110a1218030040b24000b00e4002080c1000050031900059441e5110b06030100240c200c1080c00580f481c541c280600c011190f03c1d200418541c50140050041030100c1c580e4040840c0d002c480804000a07a25001c0181c43c10150320507098030a13240180c203551042d12035102064400302c80380030040000b0000c0403035404492508900c3c40c0035009000c0650459500e0a4985450b00049403030381e110b5204031000b2a000300c2c002c24900f803034600b020b410000341e481024940c80c44010140b081001c0000c03141c08855030b4403685041c1c40302d01c00080355421042d01041c2405109480c000500f011310b40c004c0740c103442800d440c500f07800382e40d0400c0140c540c0c0a0710507000b143c0b01501604a000c2c20000260034070035008079480b440c0070310354001900b80c16819005047c40c0c580c04266010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 518696429 1250 518695179 518695207
    0xd0f020301141903140f06010f180b01020c060318030c0102030a181106070309081b010f0203120c070f150f0b04050402031f1814100504240b1203 64
    0x10011005031030b01051021002003040c0b41c00298007000c1d085c5104620003001c0305034100010200b40c6000f030140d0f442540c480040480102d580c0c4030303500840a01711210365814009104513405c641058004017070880040c000d01420b604014204660f070100080303d604e100c403041c002050000b441100059907440c020701d20307004584c10102d0080c42d04200d030f41c0840000b030082c1c10b495141e140c00c980d450f4861545180449524503540c000b140d03d4003504040b0160740e00f51803814072000909895212058a0400080b40d0340e00492040300003050013000802c890840c40001000b509000b85101c0429100980358014a03c8441c4062000150b460071703e00341c0701000340302d180000c1004440a0003242800c2e0000380c0c1e52203659907900d41644000d695140a020a58400e00300303115128140c6456000906100040c044071405800c05406406000745184007039104843c8036560007a41c0d103202041d0018440d1b4554800183c5c140d40c5581d0b078000d940c2907540c403c0c808000030000e40080d59180000007881d8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 518697679 1250 518696429 518696459
    0x3031b08091b0409020402040603090c0816060c110a03050706090503150106050c0c15130b16150618470a030b07021e240c0d0f020301 59
    0xa4104032a250078000032074004140ba50501a100e0920700b0400d800c40001030007860494402540588006000079159805400001d00d00b0302982070071442656442c2c42c162070700c4000d5540c4420044c40da0082c8800e40c0102c040d605498020400904114401381c0400e010607002d4006440c6544141410040039900072401c0014100a030301402d240c507406180c01036a103406001d080b06001c00031030140c5001508003c01441c1c44802001b071030510409003809102684181890407007030090700c40100e81d40fa403403000c0703800d18483e00c159600c40c0d21083d194031001075079038090004829140e142c00121500030741003030030384e15102e480001052000e84d008101031015802000c034114905335000386200400340390f24800007204840404c038001c24a80082c095011b0360300b000b04000450018072002b0f0780c1c001001480000d000c00d8032a4180e030000344075507075109407101c00d844402401c05080c20b218141201650040412403d00c5d00380141180d00300269100c609901e60703030703070360101c010040040e80c60184 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 518698929 1250 518697679 518697731
    0x9070302190906020304060f050c01050c180a050915030709050c09010e0f01021002090d020612070f1103040626040609021c0b06090705190f021615080a15030303 71
    0x54519a02d0050f010391a40158403c070010700404a0f01e035000c0c240504200c8880b00d151000802c018030346505541e0b0b20f6000f02080e05c40c0e03442810301d00300290070311000031000d6800051034154030303507500b002503151130b41d503a2411074040c014000300082111260040e240906000c04030540c480d03e58200040c1400f040384081403045d148003902d80341c40e076004920317942225804c51016a40d4100d98011800c203440b043d8009400601c0065403285489041440d00c0c05040c036580e6202581030524404c40e150b01c1da14810007420b030010803003000042d00a20340b5100c139031091345110a400c003850104500c021800c07902075a50303d4075841140304500d0314001002c0740c219200840606152152070314822418000c054901400e10390340801e10450240c0180ea801c061400541109001c004600520461120140c43e026203e2591082c034800c141e42120000d0341d078035003241c54002200c220b041314003080150002c17088076503e40440003500e202d0030035000070398000e45011a80c840710f1481e400e01c1c8008442d1b1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 518700179 1250 518698929 518698937
    0x1f06110c01091d0a021309140c04030201090e0901060e090313060206130f1a191112070806011709031b06040c180f1a10020606131a0907030219 63
    0x24040680c1d0307044031070340d10025100c3e220816034851481c40e00034402d0b41d400d2005512070b140002050703046a007107003c2180b0b0034141241c05e40c845502c08030490099020007400300340301c80e2013400340c40c2c01d045010380c1c481115800481c1050756820140d0305144241c03002d41305500300051a030008510f041c2600003c2102e403000b0b1002d4030306005280c010785c43c1e40000a0020a80d6045030b024010840440440318041100c08003180c101003a054010081445170011038904007496034400701c1080c01030720790352400b0581e04802943c8505003100c024078000c000390306208262407200084a03104034000d100e100c1e0100216030f103800540500e940c0b012002c80e01d029903845581003200244c1e540240c0b0080754015002c1080c114a4812803c000d040c10a94160341c0e41e1078125008802001050080350728078050341c404a8106030300200700c0c0c590b0700841d08260000200c0c04c0c07e444c140180d40c000400c94000311180c000e9444e00a0001e42d0062045d50030303000080d004183c503103c0312945031490743c0030007180c24 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 518701429 1250 518700179 518700197
    0x1507061406100e0d080301060c120314010302060d1401060f111b04020c0f1606030e2a0301090209090f160e070f0504030503070b0906070c0f0206031f06110c01 70
    0xc00181460b800803010003c204a00f4000b40654580c48107450321980d100f90f40c6622585c40f101c00414482c4020b0703090300c09540b030784030709001039000303100d814000c02861a0081c0540e080da028807000d03910030800300c1a4241c2d98404601e40e0745000e20698003805480c0d860541304c20140000501c2c0c18802e954558954200000d0008400d04410120140c1d101c25500580c840301d030b14035500c6c201003488072043c450707000306103207079010204251105050315102c1d10100940c00c40303403127100d80ea400052210041100e602001440002d900352042100c0140140045203140d001d0340440e0100805a41c0240c00f54002c5278040f0385500e0521940f91062401070504444514100a6040301d030b401824003c14007000c014500d640b10301c1901100c0282d5003040449030742d003645181c1302c10103020855100c0f034940519404036403520b100344002c020383e0360401300790b010014042d0200046a132010300b50911000c1803001c0e0900c1d101c401c0485c07030300600c1e0310707242c070b4005c40701503240c0e6810700420500050410034140c1e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 518702679 1250 518701429 518701441
    0xf0907120210030b1002030a02011a1c17040308031905091009060b1f080601140406110a02041b030c03270309030204020c011a031507140915070614 65
    0x1448031815804407030410300100d8a0000b9401819562000f03900504601c0d891200703290000b00038198158507034000c0043e141d1058620104a034030742d120a0707003d4a0b00c00b144140c01c008a004030071090140d0291080c0030345400301000c82d0750041d401180d100e8000b204126006514205a46400c0e40600b418002071801507421034843c40b40c220071341c1c88103076903070007c10900045501451030401e02401c0d1801515503412100d910f03111031f15016000906410004102d940708410202c54140700035001824982408420340740c1c0700034a1a143c940e4400c024511015940d80d000700c0c3c01d00789841100c130300d265055800041c240c500d0110042c0500d420300440203240c1201c640107002c0040410000c02c5000103501c1d003210602d0b2654070180d800342c000b04e1b000b180000c0c10342c05022140c031f208034194181c42c0e2090074146c458007025500403280d4500000100c04c14081d01c00c0100c5d20380001d19803480d02001030001141c0c11660600300040c40004100002045514840d9842610801181c0900d41c41c0c40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 518703929 1250 518702679 518702699
    0x15080609060c070f0b010909061b02070501050d110f09031209090a0e0102070609200312041a0f070b1918060b011803060c140c07060f0e0402030f0f0907 67
    0x3802c141c0044000003052030a00036851160034002d035200701003960959450882e000900b00c449030a0703500a10341910000300601401c40d130098440c031078024014462600740151071540044008407801c1ea141c030402c003504030300280109800c0e04c0c1000d4441d1140c1c03014061524142400d41d10a02d003100c00c010305a2590ba819a0440d0701800d00304020490101d060400c80c0a0b000300d03400101740e01d00b02419002003009030074448502c3c1c01540c0030f035210700002c4005c055a945039a43c5c1d0042c9958100800e000051602e50684040d07440540300500d0001383c0541140d60364001c00064034080d00c0307501406408440d04070b13110000545c060041c4890b07007a0803d5042401c1910308002c03d41c56442caa04241c030707402a8800d45406a05013024419075940f410310101819842d9548400a02200800860b02c0340513000d88240e8200f40006044860410000307440b084002c10702034040c803054254900c0c0766582e5000451050f150120411094144581514a9101d0281c400f2180750000c0d0b00c180000e0040e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 518705035 1106 518703929 518703931
    0xf060b030c0a0b071115030106020105070e04050702100b040605130e070527060a0b0c010e010c02071409061804121206060906080702011d011508060906 67
    0x1580c0070401c50803014040d80b0f4408030148052400302c0c005415850f042031020b000308800701d000441107812900300745e0110005079118020043c199034015008090030005440c103000178280010b019481d5420321281100140d541d2070890566500c035008100105409007038640c240d00c1c10001800a04600c2c042e0814138401c210002400c0e04007017000000c2c680740280c41d800c100d1075600d0501030350300c030103003009074840c540035004150582d415009000704004100000303403024249200c0b50139500f55004540035508100000c100b0340d203102414000b400000c0794071611a03a903100002c1c00704075600884202d100c0b01c4204100400001d01003003000700c1304507110303920203118403211407081d901540210000a01c1c200c00c1004024001c400c65a0415150700021030003901d02c068004c400704584400a100e44c0d12100c1040300030703d544084c6c002828580014000500d482c258540c5e40d090 = true := by decide +kernel

theorem cover : BRFrame.Cov 518525179 518705035 := by
  have h0 := BRFrame.cov_init 518525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 518525179 ≤ n) (h2 : n < 518705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
