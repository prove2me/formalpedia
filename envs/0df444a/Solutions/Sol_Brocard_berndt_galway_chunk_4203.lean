-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4203
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:51:48.392604+00:00
-- url     : https://prove2.me/submissions/59c780d6-cd50-4de2-abe1-8f463afae3a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 755755395 ≤ n < 755935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 755756645 1250 755755395 755755409
    0x4081018060608211309110408031c0507020307240921091509030f08090405010b04151d0d030e030111031f03080d02250309060e03070f0e040f0507 65
    0xc0380008004246900c10701c003440b83c04070072005c11201c054141100d0050068070501c0c034001414801c00b405e014018401d43d04a01c88a200c0031515400d420707102414150404180c880902880d1210081a44d590060000084c4811848000410901c0100c03e0b00522004404004602844c240d2111039042805610305103008414400b800f61594200b007400e4001c180000e0840d61500c040c0700028500400c0e804028200a00740072a20140308400003511414400104100595607440c46604d000b503010344641c4c0005c1c2065031400403480d000754114a600218086000e150030000380401800c80322809040f0148880320b0b1500b81c55403001d100c1c03030050030080c0c0c0d066541c070b09002049003864054803643c2400c0b8010351500384001840c21054401403400244056101c014041e040e80040444039041c80d245103240d41440c05055020320303110b003260402d4566000249685041c141c0764842c601484806105a1000f04414034000c080a540503000c1e80b00d1072402c0c52241da54508020035907000765 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 755757895 1250 755756645 755756653
    0x316050a0c0b0a0e0d080304300f170601090b0c12190e06030c0f1303061505010305130506190b0604091b0305071209020406151205090304081018060608 67
    0x3410244c111000c4d40c80042c040300c210700550015070707500d0414440100014440c1030b1506031400a00340d0802c4c11244085800103070090a00c0c0c0241c02440d952001003010001107071201800309105081000300c5c050881a500e008149040403118180da5010090410140c81007940300203c1c60003c5005c0c00b03a0039030b01040303216034044180c0018550040030f0000d910800040060005e0f00070f1038803c580d4080c0e0596411502c844240d00c003280c900d2200d9001501460510381500c0b40841c2c5000b00d6010b4030400d07241040b06031180880d4684916112000800076440000420b91100003203140100d41c400d24040400c001010344080340c03a0741c00503070000701419203503180c0510002c0e43c0d001c41e540c0515280360800592a107144002c00c81154a20042c070b040b40c0e9003540b8025901e660f0841c03400343c041402c20720980485007000514600e40314022102c682d01e004049148084080200d6040321024030040c20700410003082d0000400c08080300303040e4404440020000943c00f4001d4100400c10100a8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 755759145 1250 755757895 755757907
    0x27070e04020f0315071116090212090f030406080901270b070215151f05040806010504150b0f040911030402090a2f04031b180507020316050a0c0b 64
    0x111840600b1504801d2003a04208420b41c449400c003184143c0c002100d02c5c24046090780106890b05000700350300e84411040d005040400c1400040c3c0003445601030440064115588001c041a20350321640e29142c100e0304100410800b0794400d144003500240030303000010300c041001294224860118404090201c88032409070140039a4003c41c903070004442c000342c40202c44082449aa02c42e0040c180400440e40445020b000d0701e40d46d1220b001c02c10003408128100c0d14900f00540140c11522070381c0c8480c840e1500104050034540504a4001011410001c080d4202038440d49540c001d00c4034510040ba05001c005a640000c1c01228009001410090b51f2410540140041e020000300102009410711f00b000d07101200d102180540000308880d41c41c4c4902c0c83c40c03240384075481203a202505803003401804c0500481407413039000440c0c007910000091b01c5c1d6651100d00c15940101d55000258000b8030222010040b4003440e490000d00c0342c010340c1d15151540c0e5a129103a00150003c888405001c00e40d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 755760395 1250 755759145 755759149
    0x608011508100b150a05070f050106050a172d0304030b01050126150102010e010f05070801120c0b0708041203030603230c0d020409021e0405100e27070e0402 69
    0x700d01400c404941802416a02c5021400e5000340c1c034941d511303803c2d000a00c4001c2620440075608030903800641c0d00f41803030702400d00c2406401c0d58002c562080718007040c00208416110011040305103c3d00150002105034691100c0c02d11307001001e220160702281329400310303117403c3c00104083d501c03c86407211554105800104880e14042c000c2d1501410b2030070707000c000032040c0062035002d60403c20082a403400b06004030301401405442070850760a228884010b0046038003d03a12544403079803080c1c4107a03a5240319446400c028400038200d900340070014090070300004003c16086000301d05051816a8030000702407102031480c01640002d0380d40d2403c0c810800003a80601c0d0088030f1070040340700480b0511075907444a0122200c1c0e4030411103012800c0c115100d81d04051240c40c1c0003400000000e040d4031012081d4076420500c1842249400f00040a11503865150302c1982c015054400095545011060403682804800e041a0707102411500384c521017001a00c0240001e194400d0382c0e4202841 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 755761645 1250 755760395 755760403
    0x30308100906060e09101d0405060714031f032a05060a090918050d050316090e04080714251203020a0f0f0b130b1008070501030c02010608011508 64
    0x880041d00e800e05500700000c9500a44204081c4012203800c40c1c0c0d51514010b000c10340ea0554080030844400700f10b6188909944000c0381c0c072840c015010394803150b45012003214910641070b4003400c50041030000c2088800c250b1070f04903141c001807402485d0319450740c40320254220f00790300180454141d540080c00080781e41501800420090f1400350504110b00780c060b00300e111078080d140c115070340d80c0c00034594203404440804840e078000702901c000b503000000061003540100d511081c190925000f0400c09031040c9410421580c941900f045592680e0351403603480d60003c0c070155030b20760100300341c25424107003070050680b0b6a041c5105107402c80c40800164115112030fa02c145103060100c4130000110342c0200c0d0b0202500d90160000e21085801d107000b0022030003141001e8a24108035042100ca0460b041d132070700c4040d000d0701042c0c06c60b81c3e440300d0003c001c168a02030030700117400504080000794040d4202045a055a000100c0c240b0b40311004242190081020005200741c60141080b0112082c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 755762895 1250 755761645 755761649
    0x1060c0b040f0b160e22022b0e0d0c080703030c0507020406090516080108060f09070308040605031b0c070603020901030204030b151216060c020406080d0309060501061106060609150403030810 84
    0x90791451b020302650010f0b140140c1d801001d9040300341c0004800a4202100070403155003020708840e0108152603591400c020640701c1c40051035441450350508060b8003511400503040e0703020350740500e480c069503000c4010707020040244061060034408100166210b0103a100034218011000a061404007150403211104550135428081c980005016040000c12100d80c0303d10b03004014401509d900044d40d04d005026840a00700e2040480e010038202ea01c05c001318020100041600c81040a000c15101076100b40c214120342540210410040f07035009401900041e0014140142132907039a46800400300310440d070741c91091130000215246445c7c185e0b40a210148a01c004242801c7e43c4054820b4211150054605210f064540703082155102d800c1800504440ca041d00d0000304103800c09170180c0511802102c00608010010890601c0b0300840041c80c8070007401019039031901028003440d60700000761150000240d41380c00001e84810301c01003004610030755420030a40b41a0b00104031140f059 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 755764145 1250 755762895 755762899
    0xe0d0318021c0203120c0c011427060c0a03020a02100207060c080c011e09030e01110304030b1003170d0b04063501060909020109050901060c0b040f0b160e 68
    0x1405900940c0b25a9042001100307003481d04000e85840b800000d10303107460002291140e00000500e10030b01040403c2d0200368071401e80750301c0030740d4002ca4011503440c0250322182d06045010611aa1b0265515160108450340580b000d0300d01040030708003a0030700c0c0c00b0b55000e80141c2d000e44600307800c41c24403103090400c902145c400342c0394507428404020f100407110300340034004500104402d40003880030b610801c0b2800c02c411515064064848101c00a0310243c01d080d400314180e00d000d4100755010317890740680310003000080e5103402c3c00c5a135031000801e0042c0c100d4a028540010102c0014214030440c50003046401c0701988820070301039542c06031100b03004024000c0d81015400c105d8410305550312508911401c02a07403030b00c1d600d13010042d8021800404240c240d82000000a0f05584a0b40601d9100c0e00030f80e40c0d1280c3c20345500600202e00820701c25800003030003031240307513010890345074078943c0140c410140070101d03050581758900e00380e40c180c4910345602a403030459018070b6085170040403420380c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 755765395 1250 755764145 755764181
    0x41802090306011701110711010807020a080f0d230f090102071e020609100503010602070f0f0909170403030e0405060306060f100e120102030f010806150618040e0d03 73
    0x300020a460722418400d07081081048040806510002c0d0001d60016805c1050652121b9103420051000c083c5c4002040c0811785050204a0300c51003c030b20110003940011986143c84c0c0c064402980542c840c007003410301c0541d01d0050100d141104503c0c0076201250403120306030350819400508182c1405040390003168410400400080c20032494048070480722018090112420f0010641170702c200101107178040190740c40341d002da0303401001460680f11140d00f1264059140da002001e1020f0354029100c042c01200800c004180c2160043c0030b40e9031040c010320f5040e00480e8181d0125401540045000c1034460a00c03403010700b0103100b0b580e03100c1d01c200d00500c000d0600001017a1203c540903005c0307000d04450800181d00c24000da5070058074101c0581607080c9441c5041409000350070a59042c1141c01112000240c0340d030002038014010030b02d01c88000c0c0340c40740d4102045002c0d80030020909504000e8840c81c0307001e5845100d01285090881c0c0078060b14004000e006003282e01c0c61072000c1040d00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 755766645 1250 755765395 755765407
    0x1210080d03020a1403070306031b0e0415020705030a050c150c0711030c130e0c0415230604090903020d140414040f02032401020c0904030f1e020102041802 68
    0x140050410041010380c280143c1d2020030840481e10080302104140c0703001000414003015903811f03808803045a004200f0740d041c0c032403100d9054851418a229900c400000c20010a010a91162102c040b03016404801840c0c08503698031542190810080d0801041c800710710300d0a0082c0c14008081845140302d026966450401c800009034007036158003810342420003d22b08420785041150b10602c1d40e00401c4d0208079604040c0200c05416500014542401030003940715407401c02c0d00404141c001d508005003141402c00b0700020503501d15607a04c0c00502c128582d0450981c0b0b8031801400034044200000c982c00040b8180a80740c034130585524010000d1402c000941d004c9200192402e590000f1451350036110000005405000303140f205004982c030010031b00008503002c402c160b40403486011301c20202c0351008010b80e180d2400900c042c0e0000b24450000300000c1c415400c1c502c1410280c01c058105007003250542c401c5e0803807500f03280d005d80c2d8000b84c2405011203c0d915402490b03402c0301d003949400c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 755767895 1250 755766645 755766659
    0x50f070e042a3e060408030103020111100507110607080c04061409060a030219030e060a09061805070f0905130201030c09120f06141608060102100608031210 69
    0x19100546140d002c50030424003400761055080c00d1110309005402400300040e48024202d2034a004420001c2d10307030503100d81c80d4007580414114421504410780904507131a540040d11480000003111200d8005c4080c410b41c02440e1307110b16806280c2940d101043c03201c00802152500d00007407c00e82c180084142000106180c52049600f0f07548c4c0c3e4908510032200c0c0d81f000784620700442c854030340d10100100f001d03060140d150340500209801e0307403c0381000405400d0160225031140014105980020300020200c0585030441d824041c425100000c4a0141c035000750500c680b4207204591a810140c0d0030418800340b101020060310241d00204050f00b08a200440704800000e03000f07040c151070b8100050801d009803400801001c800c0b01034080b0030514500300c030b62034141020840710b0074076251035031100c100d501d032905208100341c00180080c880c1c1c204d01a180c80f08000c00140c1144202d80c0441d44202c130034047d0800130042000110745500012240c50903180340140314108002c0751081c200b20395 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 755769145 1250 755767895 755767931
    0x702150103020f01032009030d111b0a0e040b180f07030f1b1404200d0b0a080a080c0c090f0a0507090b12090105070e030a0809030a0501050f070e04 65
    0x41c2c0e4101c1c0d84102d00c9940200603401703403000150038120850081c03d03080045800f017000b0900e200044050b109111040d00042d1401427000c000000d6540c0500e105207401c0d01510079000d49008024903400c10550b9401c4410300103481140c0484034442140140440c0c40c07415031410030590050001b40c10300756072040f06903603507120b24480548120100303503450041c4000030120301c8107500b1800700c40e0310345900d80001414071660190600d0017145400c1900c95100c00704034040d100d810340d090740a4603003c100c030304900c0a880e04010080d801003802c0e10003d940841005050003040c410406c0c43c0d02c0e200808038a40c10a40c01001b024010044801009200c5081002c050b511646501c0c0024041d1034018086900d08441d0308035070110340d4000380201e4051460700714144544407480081c0140c1c2d4502c041110303002039031402540c16600204080c0f0000350302c0303000352804070707000b90440d90404065140c407403c0d0365040c6d0b2a0b18181c2110400e00810300d030310525108c00300d40c066030240940c2c04c03801e48014034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 755770395 1250 755769145 755769149
    0x7020d08100503010c0c05070806061e01032903011a01081609122010051e0d0f0e0d02010b012c090405101815020307050d090c03020907021501 63
    0x400520a0000e0390a0012641c000090407002d070003044603410480000c1c005030143c40c4140c40c1031007400700c00500700d40c00180e01403203603801520084402000c80100380010b000142135038145622280b202c404164000d01c200e044e540402400350011801200b41801c5490206030120780c5401c5c031548000c0350360000c3d68507030080080c080d20041c500e06501d048035140800d400000030038004444042c20b10241e0040c0001080c158143d550440041004201c200b80c486c41d52031001c180b040c0010b200c0200394150207035480c0c07144c0f140c4618201c403140040c0300b12079074030701c0a01400395500d4032041c92650400c8034681424482c00204160745501002030b00411154502100c000f8161000c450f450b0349541480110300720140003101c081c213080c50306070346882000310f607600428501400d824455000c003011140b2290081964403401c00103804400281d88010134000074400100f1a00320500124411155480d0041c809807041ca030461041020b4020080c055004540c0072405800444080c9205641 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 755771645 1250 755770395 755770397
    0x616020d02190902120702190206130b040803040f050312030604050c0d020c060103020f030703080409110f0c0703050607031b030e2a102102070218161707020d 70
    0x400c260944000742000c0c12203111242c0388030b2071071000280e1035040c4e0040d2201c4407402030aa91299180107040f40d995201c40055000b8a01d0140c45d070016081c8103004040c5030010340a0300181a4595000001607401a802003107a9440040e0030000c41c1501c07005000540003c40c09000003c2102c001c08000c0d010280c40c051160f5580c0010440094090381107580001c0e00540c299110301d9145c042d59144c01d0248400d83c012000f4ac42c111490740b030042040c0342034903070000110741880c4c18800c8080040c0708294681440c00d1080202d6802c00101101820880310540010058107086140c120708142c2d018100b14141401d1070109454601c1c0d44501c14844c00c424680002e51003480200b03d07141039004041300d000a240d00030260b1100035520400d000071a030a440034607507610841c01c01c60b0780501c1301074150600e010f1b0f00e0742403140101940042c103025000420141c2c0b60355980d46400b41d11441641c0007100c021100c60701411254102c10180c1d6030301500d801e0511180341c6240e005e03440b5000c6a0440e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 755772895 1250 755771645 755771659
    0x32c03060420180f072111160b09100e030a031a0604030c08070e04120e0301061806050102120c0c0108040f2003160303080a090204020409051501120c0e010c03120c0f0905061602 78
    0x30300782e41e9403a0b055440f00080c07880064486020750500c860391750349c29a45001c1d90300407140c000d204903029001e00e5941e030314503800075440e0180c52442200101540c7c00e50441c0ba0425150249035903a40c800a8009035029002c90700540b482c088645140001030380c0040d0540032207104220119010075074807440760070241030900c0d001104200190040a0a4000d103937075081c2c05072002c0305035980d036003c84191a000c1e003c90744910210b0742030038010300441150400b03690142602122070b503c01c0004580151080b0014903402c40c107a9180100c420401900711000c544031500b0311500e2408010205405501d504640045400c5880060014000030505041603442c1c0d10f8071401c54a4070303812500204002e242c10401030800c2c84092104801d01042c09000405400302c1c0c40050b40c09200e00100a1035584074200e4242c48000190384448500c107050b421301440242c2503500e0910b82c0100b28441a81e070355803020794000103070301410707108690300b006014007010310041c0f1201a0004d46800c140750111840 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 755774145 1250 755772895 755772911
    0x7180b0309150a1a030106050d0f0804080f0313050d050d03020c0a0c0305060402010e06040b0405090a0e030a030b0102060a110f0f16032c03060420180f0721 69
    0x18510b030051440099060b151039100b005a180b065038843c01500349500e02d15640d8001e4031080500f038075618043c12768006407542d4040300141c17000540c0d581d240d00c10007800d03060a40e1401c0360390a020713244543e00c171550000144036117003201e01402c1d0005000200c2e41030440d202d242e2034280c0c2d02d008814200b0240340c1d00003003c1a01500c04c00c41e803031100d94840a9410b1607510391070055111102641d040340401c0e443c610440e45454000c00f03a034250759845e944076003881d1a250803c190240082e05400c40d2658500c11410801003e00040158035101c0d10b0109282d00c4060009207456070003000320807000d00d40036885442218960441c1c0d085000c130b12500da1a40e000c0071b800100c41c4207600c40010744031041086141059000641c02640d02606c1e40c855170700c2ca200c041410003240c1c0d0302848640c5500050300140024140e80e606004c20840c0101ca0007a19580801040e0010030026040c581c07040828100210601504040c0d50302010034500041c5500c3d105000c0c1c1c4801e003420300c201c229580c860041c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 755775395 1250 755774145 755774161
    0x11031203010b0a0c06150b040305011508030a030b1302070f0309050114222408280507091a0d050604090f0b09030d02130914091e010213090b030607180b03 68
    0x40446c9503040d01004440d602c0c0d0310f140b01c0384180d110b0b10007180c03c0d508014240918a4a0402010454803228080c616210650804400404007000250fa010444104030208010184090626144030740da883d00c0b0b611403420040c00c1c180d69540114100400320144401032a101da01350341003400c903000c02208040380c5419250141d8800c0c0c0080c4900c0b80d1007004440d40300303602c55001ca00303c0d005031600907541d111051f03040850b400010000350721045650250780004111362081e540440350745014221030380c07601e00c555000b4000040300f210607180440d9142c5002014400c3d190010b008407010801054655036601c0017041d400c2c0301406e00c000280008218601c18011110750000394142195141013600c2e101c03000800c60b000e00c0250a16043d034041203000118640c034001d0088100520781c446558080d401c40205051201000355001e1220429103520302c81085e001d0444410042400040c280516260000081002382000414946000c00b240f6030344160342620300700c2811594a41d41c4801c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 755776645 1250 755775395 755775401
    0x1305010b0d080d0e0c190302241903020c0106090203010617090a0605130602030405210c1005100b030901050748050a050f06010f0e010b070f0b010311031203010b0a0c06 74
    0x3190708484244000c5041a546e8075122050305e02c2114050405030501c10050100b07202ca00d4601c0159408004005102d00e1040e19420115002d1401518216154060030709589050380130420007030b004401801226003250f091519407050f004c60780010320f06410080d0f528005024050400d130350f00d90218180e07166030140204455000607080d5a00d042c185003055603041c14004d40e00c07500c91814101030402c3c1c501c808a8200300c003800010008446000005c0004020181c80704661844038800060244410400b451141c4110400040d4501c0e0140010b4000020a800c00f81d4100e44020403172100700b01007141d40e01c107801ca0041c4210010401d0120401c50703503c080058281e01c034082002c010002c0025140035000e08a8003911040d90f03941d00303036180c030b0211800740c0d03c3c1b2241440d0040c44207407400e4028000c50743c040da000329072000144e21040d412040a8000b640c2003034000c0c01d1510300742410849100c03400c0c0040b807098955850b0a00c00500c0d40101d45100c001c01444050351070074000690 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 755777895 1250 755776645 755776663
    0x5010e10180b1f08060403140304030e040c020316140705040c09030807030e04021602040c050405010906080a1d03070521070803060316060f03150602071a121305010b0d080d0e 77
    0x80b5031400b0f1a4442c1e103143c0d650b54085034100d002a42d916011010854440260b80c01198513440321101000c07100c003048082c280c5100c03d8030851005012184162031031011f0a82d80074000c03c007400462002240c4541862440d411140c010b5060001295070705500240c1d44080b00d8000c01c41c540c407004140790440700320480c0002aa403250022602c0c42a01e0701200340e2401c0d003442150300f0082009150802c0c1c40034003562050b180800e11490040240900030313000e40d0b0740001c007020001640740002207202154490b4036107030501b0384d00c0440c07044100a010090300e680c804130b400c042000c000100c040f0041511403000000d10340e45003c0301003251500c040041c44005020000c0301182d880e01c81400034901c541d0300d041c0d4400207050271094005800c14500740d40c2a200181e000d010104d061584d07050b814003e07d40c1c03006028008002058403461802455401142ca0234485202c500a0f81005801c4d981c0c443c40c1c0c1c51141c3d88007104c1d20000b550820488011548216010480540092155040403002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 755779145 1250 755777895 755777941
    0x20f07030534060906030c0908031b0111030f10090e1b0d05070803090f0f06030c0c100c0203040e070513180f05040606030b0f19050a110705010e10180b 67
    0x3010000c43c0207608800403105880056030100804060b01c07c08030f42044141c0b00d00c14031500200318070440119100030b21005011028004a88810800780d44d80513030780308407190380ca010741020034840310214640a0b2401455951014444481c680450a4645207109006441da203100e58080e460364640aa98180b400c0d080703810307070340c4190350b808865450741c2c480f06e04244115200d030b0708540ca0340350000064091b090060400b600b190b0700c40b0a6141d040e400840b01515078881d0f0110b004010302039004042008541d50b0103582c481c0c1c9000d103901c0d10144003400d5801401010300034035000d20302ca09854003c0f01e0340000d101c907104d9805081c007802001c140c000801200e05090801c01400a290040300499100f0b000480040da0b405100000001c0d080d20450300c00010b940d1410b43c0400141c1005420440300100001d4543e51480700c1c40803039204030011503869440e14024100088180850003c1c044549020b2040b520030011004803511001c000401c003030504800b00e001b500c2c420048042003812 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 755780395 1250 755779145 755779243
    0x60f0f090703060501110d1209060b10030906050709051f031116110a0e010608150933220b0307061e0f0e1c06020307030903020f070305 60
    0x224660003000f8240c203014542c041803060841c2200c0c0180000c00a1000c401036a0708100030409140200243c5500c6005a50a03900e841c242e400d00d80c0c0b40c2400100090b61610005840041c0c0c0c40c1400036034400070580b1080c0190880100020740fa0076000c040d212400030100c18a816003418160014012403c90451400011030616082c0c001121106034050180301d240c204c1408081c104044201300780500103044c0a132070010888a8060030364a500090241d6030304422990714400f14500c5041225401c0b05050100d2260044918045002001e008140c2c6050304400d20032021410684002c5044914800e0107210100110165800700b03070a25402804e0324501a07035820001d118001700102c021012400b00c1c00c4151040c00742e030507841402d0140c1c490000300e00700101003040703000c96184201512151603004000051140c402180704e101c03541c90000f05d800c0c144c1030081ca8a5a440300c100d502e42d00c010800d0012583c0003590107060101000051001c0505207140f03002c0107510f865003010070710 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 755781645 1250 755780395 755780401
    0x607030c090509060f01121814070f060503090a0203160509130309050f0a031a06090a021c020a11010c091d0402030a0609021f0c03080603011509050c0f0418061508060f0f09 76
    0x700823036503040024000c4060b0807655110790445502c8140314460180b079105000c00c200000c0d409500075580c8034000d00142d0300400c3c03068000ca8104a8070a03065030b20005210340078801407900052164000134400b500c4440c495590f90050700000e0351303004040c0300340c2d09910403c031256510070003035016540c0032400c1c0c01d01049160340000d41d4101550314030710030001c0500007034000d41c1c2e910170340e0a144a440014006415528414002580070600362810031070720710208440d900d0240030b00d188004040c0d170380d90748140c81c22050b00c00564410201841d000380f103070309200250758001404040d0f0b80c0c0001c3e00146440403803000030508580000b11010f8600b6800741d994220350803500c000990741c0640c03103003103e540c1c40ca030405080b92441c0b00000803101d0116018400c10f11941d215690050710304418501d008803034640110f079904554042a02c00900b4541202420000e01071200140100da52081c1c030002d2800c0050b001700c0c1e00a0801d80179070f6a44811480c1540e8081880a41140151034808541 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 755782895 1250 755781645 755781671
    0x10801181e0b01031d19060212090601030c0504200f07021e040b041b081b04140a140109031202011d1e060105030721140607030c090509060f0112 64
    0xd80b600c8458046498070034810945026217141d0880c5a201c20050003040400ca030602d0140c0b21101010745074594248203032030019010864040c040c1c402d642c02000b05d5031642c5442c401c50920b54006a006604080000500c4c084012044001e0b5100000064482d1261300b241c3e000c034099218041e51124a1020f84010008146084c0c4151001901e00f07220828809082c4001d44060140c40006810a0000b090f40300780300d00013842d00480c1e01c405c01c09081c0c0850103c51841d401ca0b81001d06401030160302c1415500c2c0c1115240c0003044400882f0100101050018040c00d42c5440042c1c2441114070120061620030746c007550005021410300d04c100d101e08403140355610596401d40c02d03451903105200b007001c2c10000d81c0c141210401001080128185010741d92800c11803143d4280110b081d03603540380024040c0c2d1524400b114098000e200514200000809842120000c41c040c0190150103210355190440250b900001c140d640c0032400741c003040100e4082e444510065085450030700e41550030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 755784145 1250 755782895 755782901
    0xd140a0e01020a050901080414072d0f0b0f090406091e0605060904200a02010525021002071a24010311090d05120a020106091109010801181e 62
    0x842850004000c0c80c400e2880351402c03031140b2519280030900030f100004c11588070340b5105030701c28480d014030485e60620395080d43c0b52060641080c00000a40b600b091000768250004850001c2c0c406070340c4000610b00111011151040d000320300704008005003e20014038142c0843d007001320054070400101b40c1c2d959142d4005e201d1034180003807440000e025001c465006000e40000d956008000525241104040000905003c1c41800c0306503a981196102c0802c010050110200e1603000801c0e17a1502d42491800b2040e164142511019004058902c2c03580c00582003480924100005a8440060404003001c00c0104020100040c001007081215041014024071003a044600412a4a0124015001e4460010320070b81982d90611104115207001c9070003000c0c16003e1020f550750f402c0b0104524a003680120b41a00250791500000c100501041c410340040c0300f00d00f001141000c40103c0020096141072003190640085844a1541d240c040e9014000014010146d074240c801c00c00014005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 755785395 1250 755784145 755784151
    0x2150309070f05041a090a110304050c1906080a0504110303071a061e061e03070801031e050a031812030e04050112020a0303030c030209042306101d04020d14 69
    0x800200342000084074142801600c0070301354081c001c5006000b684041c020100346c0284140b6405071180007080c0c41e100000019801503001d02c0140000c00036240c00c2c010442c2070350441c2d00401c0c50740d0200704070f115030060011343c11107500700c00403c1948a030305084c1401030444116030380c140000100c0c281040100c425140400e10480d20040701030b61071100300070f07074218001240f00c148448025141141c5c60302800400940c0034004041050041d04044058141c008803913070404031307442a0050044c08000b50005034111002c40c48141e0446803a03841d140c440c00748510007821b004100c03500a900f2440003150002400b9168800078580304181402403640c4c0e01d605820340614907040000c00c00c107909241000002d40c02509007032806240d035800702e00415452030102e080590078007100e441030f512409401c0d00307804115000c405001d4020152200014050f04c804d108640c02c42c5104c1007a5004210a82c916510440382e40d418201c40c00071030044c2c4227080d40d4810041c6042a40541240c0302e182c4140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 755786645 1250 755785395 755785409
    0xf06060e03010e010513022b0321061a030601030b09130c150203041806031e063b07080609030a0f09061b06140a0c11030310120215030907 61
    0x300f8942e243d10300f200c1007075a0b10794002203460492400741c1490421800c660049040d81d0003118001c031080c0c1074605154104400048204101490390f00540304001c640d0040d01c60200030451078403101e6030501d81c407015a00f804000120020b902c580c0030ba4448082e1040107400c0c0c0003c1c6c54140f5000c05980c2152000311040ea00344d00012403190007507078844801e03403600d4006500c5c090400581d03030000071910402401c4e498803a04003100241894040402c801a031809242d01c144991800c00c0664207200704501004284060780c50101c0071811201110030010b95040076401d0804240608010103900b22620b103203d2603060090340d08000000303001c280d00315078070403c0440d0707505070882d8034007005d03c283d0000030506003038010342c80295400d080038940f2401c00046c140c0c40c100d0f502c09240400f01d4008c685140d40d503015090f40ca40015001c8080080c1e0b5020790300e10326013150300d4902d040300360081595103414404242c0131501c54000210020300760044150312450600c0f400d07950f41c000e81c0030b088 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 755787895 1250 755786645 755786651
    0x706020606040513200a08070506031b0421060506030313031704081207120f020a03050904060314010b03010b06160b061809010501030c090c02100c0216090506190320040f06060e0301 80
    0x2503950720100d1512300359003004054918613143c2201d44880e8480c1c0a100c046a1403080000081c500f843d90f10704208403210701c8040344a0740d686c1c00c20101707c50740100241c4c082d0b0400c11503034005926121809040d240d00590790b554003481511800028099508192480e20614014034440150030740941407442c459030076250090000d0f8012103c080210481c82c0c00350b4042c28101d030002e0b0141024144c0f80d10007500000314240c2d2a101c00c00e80010403503081240d070b550782c2c4011030f280c2800c6c011101050304c20f8030340c641350401d00301d40f10001000100014140c14801d10105202c0d039a02d00c0955800712282c1d444e0710160405a108070700070708003840220f541c0d20341d201001070070b07450318064000c1e408036a03006400461442c207601d6026044050243d011070040e40320160790703541b000c01d11380b024103040d00e40080d56140031818400d5224070040c0f402c095180e196030400020b60f08090380e820341c0580d608209280607405000c1405005250102d00c070701800c110001c40e1a50b4881c1c19800d09080441c001c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 755789145 1250 755787895 755787899
    0x3110111040e180d1706011b080a0906030209031e2d060603010c050d051e0106030f0e030705060112060b0a031518050c10270303110706020606040513200a 68
    0x80e40e5400c610118000302d1a2801c5010721300030707017a400940c03104040c103107000c0682008001d00100c071161881121501d4002c0341c02110507501c071814801814032400c0851130b1051100003c1c0c1e039100c020b28101100c0c41600001c0d07107190400d2200802d0203804030700090707550b0090130040b040441d414003e17800314450100022400c1c681400ba030000024a5100d00b0b01c0e0401e500c1504001e0100148080c0740c403455140035180059110480030f008043e940d60000b407914884c1101c43c150b0700d01c2c0500d071140303601c14007040e000f01e040801d52a044900ba4030b8041031290341751074000042c2240100c4140d0040c071b4150000140b282c441d040491121706200b0800034002d03008407070000006150000785c0182d10a016401281c00c01c00b881043c11001030030b11690b205804486401600d140e04104000700e0410141001010740040d09a15840c00a2019090407410203000a5503640c00070000c80c4540c4d141e03804120242d109910244901c1d0700b02002c8003480e01c264540700c1010314010501ca014818800c40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 755790395 1250 755789145 755789191
    0x301091e0903080103020616020d060608070f080714030f0a05060a0b040513320d020f0d17040c080307050d0e0a1802090315150a0b0a050703110111040e 67
    0x5149112581622407420f44d900b1502401900c1d04400312628180741c8014500b80135079190f240c5142003502c11440452003174208007c150408900380d020b1101e000307052030244121140824810b064800d004c003074400d02c1d201600080d240c035181c070099985a000306141d00b0f041c00004102648074190004080c402c089112040c0402c683c2d049603d42d10340350b6006103600006c0c641d034010b950a030703620b0400d40194940707d07989891406102540080d65a1102554900c6581c06014000307807407071501e0140032900f0b261a005001b00541c1c1007154580c0903000002800c010318241e00101a01705042100d440301c4640c40c0565481102035000d0021400940b201c45271464074a82d00410f4a9140414040c80e00c41d4100d000043c0d080350b082c16505006180c50b00781c0304ca02c40040c252241c600c00354004800b40300e0f07009002050815411014101800b040404030b015004011110030f2035040c9040752000260941c49401000958403648444a0000300003480c0c0d070b40d510314140140003001c0020051602040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 755791645 1250 755790395 755790401
    0x20d0e0904021c26180607230a330614150c0a05060103140a02090c0d062d0504090209040219081c02211b0c04020301091e 54
    0x7600a520481500e08103509410000310110300d18820000d2205004139500c80c03141d20700da4030300c0b0320202c040c0c00310391200c084501c83d444021031201a80c01c54541046070b01c030306100f80c0866242400c606810503203814a071000700080e14489802c800d51000e1858401300c02c80045028841d048540940c1e0404203100f524544140c03401c40b41c1d107219070b038410130045041c440340ca1001002c50161030414040050341180501846d00007604c44c4d000313801d4540c194034141d0f840308644507004102d90700800d4000e0040c0c58813060300c0e80140e007502110361229440d10f8154045c200c03030f0304410001040148411040020300501d041032442c031008035050903440e48180021941d6544001e5402041b00e404a030241c10500980c0c4403003440041075500213911180c0180c541820f02c8400d661203041e240c0c0d00d0f2181c907030600821030540c1040040740e01240b0880441906405104900340b0f40b2407480c900a89071440030484281c01c0c04001c2e000359101d69660540b1002000c010b403606d07448054403500040c0d1125a44 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 755792895 1250 755791645 755791651
    0xa0e06010e15010c0c06050304150203090a06180f0506090c031b1002071505040e0a230c090d052407120207080408011d10020705030f031e0106020d0e09 67
    0x500100d140ba5101401038503190b0101c00058103004442500d10041880c1d015020040c0c03641d500c0e03060352401d140c98904d44076048144201203a5105100307000c950540803841001030394000501051802e1340640c2d0300982c00325050000c0801c14081d00c000704004000c103160303100c0c24410043d0350000f52070001349501e039081d401406aa0041c11000705209280c035500d0f0091688140c030488982d15211b5010300c00304256481010089040400c4c10003025140ca402540d001c007009000340310000814000340400940c10b00c41c1180d124000340001c401e11588030a803000749500034a00c512901690600d2902c5140101f201c21a600b0101418008154242d034158010001d40d078a900c1040c48241103c0002e402c614021595594100000200b0f840c00f4080d036031202165501529440946d29021458142110003801005005102141c0072801c0031080e60004003e5144440d40d0b0780d104503003410000410070300113820846560011513a241d000840071102051500d800d041d5019000030042680412 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 755794145 1250 755792895 755792909
    0x201050702090916060201050f0601030b01022a0a0f0e130c0608070c0c080c0301060501032904060504050705030901062304020a02070b0f070c0f06050f0f070501090b0a0e0601 77
    0xc010840c01420440c00565020515a0540c2c041c1c42c030b80c0908040002e03069201c240140c2d107440910151a0000070741e0394020009080412501178036200203911698040205440110345900e42203446c2e041c03001c00e610042000300b04200a130b07101d00202118121038040d44808013400c20008111800030002010304680241852038030074a041021542540c1c0140131404002090382c0d80b10018110900d000301922050000e0108805802e01341030849990380d2099042509154404081d2940d20288142c414000e80c00b1400700442c800105000d840c01da80f160780c010b072038401002800350748107001d140141580c10003032280d2569044a0101020031100004645060304040c0704a46010380c010200003001d401500e07031941d5a00c4606c0025002841003001100c00004c2ea40c0401c0303210303101c1d04040c0c250280105401404c10a008085019400903e4450b0390700003510208502c0440c160b03584540e0050080c06440d4461402141507802a032740d058502d41044d09070105105c01080c034a05075214 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 755795395 1250 755794145 755794147
    0x908100203090a02090a02090316030210021c0e01020c0a03030201021b070e0f0a090c0b040807080f0615060c0111120f0f040305090d020904080c1227060d02030f090f0a020105 77
    0x1103800300003180170060500511140e0801c42c001003903e0900c4035029000e80c4043e8840c21514500500c40540c01e500b4500d0115080728440180102c41d010042d4140603103481d0510540100c4401130f45051403851507507034020929880001050f60540040034610b1b25000802c44002c0800402d641d20b0301c01d070043c9003100c0d10a20002d1144000b031101d40d80e001c4040c0d2004030b00c4d4000340e158003611403e560403460780b0482c0058184210001007101900511489000f130803c507000b602c625444541c081d10000040f03a0071140a0b05983d00c030000c1d6404071b80524000c0001c80032116906d4280c0c0c0c0b1444058004003480710000c1e20280d003030b96003540302c0c00c0c0503590a26180d07036554007250607500c418041c91340411145051005031f2142c0082d02e00c03451007820100e5031004e26100b40ea1900440c0004082040e00c100b261802101c0d08182c2c01002d60307114007041001c0d54000d0000703004c80c010a20b84801c924800300400c0195082404418010403498080e10826070005881360340b1080c1840001e408070f04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 755796645 1250 755795395 755795413
    0x80903070b270109090203090714060703090312020111031003032d080402060c030c0c03010e010504050a06020d112706041a07060b12060f06010f080106030b04060302030706090810020309 82
    0x70300007080c9003054052403c004440d8899004008981052369a0400340e4041c1c00d082c400c09801c401003440b4a941200c026003807a08035038008180e0000c034080181138030000030046030b02234001d4002654801c074a807034a54503494280010040a1418030040d400160758040c0d01094008412080b040c500c40c0f03546803680d0355205001500c100c4e1003c1c2c07040740c1040c0d041016144c0804140050205c81d00c92401074409a216101094251811980d40b0380d4035034541800d210000c1c00014201c000d455002c5009038803181901e404070f000b0f090032903540d40b10550024008901c3c2850480005118101803c041c41c082202d0b018840b03d80a1805000ea0201018030201c0d50808030300c000d04000c5208043c082020a581c0010649034913407805a094194042802c1c0a9030600070600705522002c04c1ca04810440000300c0c0c001c0c03034108180300e648113255940e140e640191300d8940142e0f000d95005400c44400035640d8000811a0180c1d00c500d003d140102170100300101514001ca0b0301652840340200744600b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 755797895 1250 755796645 755796697
    0xf0e0423071202030c2d07020d1e0804091b080a15091104150c0819021e0f010f021804020f161209270e1504080903070b 53
    0x44000360507241032214000b0203060b0164070b03000951044180391003d50b102c5a0080e1142e21715074094125000c0520700840f030340d155042e00c01c1520071030b0b43c04542c0b01c8185103c605000403000c6510b0210569407803a20480400c0c08541802403003115034150027046030400c613601401e40ca8a250b00c501000983c0c4602040890203680c100e55808001410381500042d500c65900d8121080b8070850b0410480103e01001010342a102443c0d070110306040c01c190588003981c85103d9072046100550440400300112460b00c0d201304203407280c409201e8020343d84210210841551000c04901c0795410350308100c03514221880500a0310f4cc03007404d0740058004031b071840c81044080d401803400b100d2103040a20414955019003c0c0c0da641207405010702442420309003200400035003407904050701d00802e05400388481c1d04210b103410040084400001407124100580b6410300c1c0511b08540e2040c00da82003480240301c003000c01450400700840c07c0398100c03590381141020500880400c01820b12070710000340402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 755799145 1250 755797895 755797961
    0x31a010c0f02101403190b061c0923010504020a060207080a081e03010605091f0e0f031e01061e030804030b060a170a1502030c0405240301060f0e04 65
    0x5100141070007800301e404012048255042254640804c035094581c68a5404040c407c1080c41c0000380d4101d40b9040c5501800c1d03114005400078a099943c1c3c481c07089007403040411041c4940e030a007001d20300e0152511010640a4001070340c084c1d1180b40b84180c000ba0450000810320103c034410009485080280e4031178842680041c502880c2e880c0c80340410b2030300b014041d0000c6000c1c0c00b0f55150103807900070b19020302c02d0250103411b04016600044240c0d504240d00b00f0b48618901c0021600910340c91119400b0905201c002d5004080b201120300052802c0307981900300d00180e03900d9107401d00240000805c502806840c0f444017a11100081105102182c401102c05501980191a01d45440da072001700741000d00345514100c2080d080015014100140c1515106110b45000c1c019801c50400d00c1b00c51101d80300d00c0c0301c0c0c0e0744100069181c282e8070100c12a44111801041d464058481d0394410001c0d120500c01d011910000f100081c980145140034855007104200482083c02d200e150340e9009204 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 755800395 1250 755799145 755799169
    0x5030106060f0c060e06041b060f0e190f1202130605010c030c0f08030117011805030d0c0e0904120f0212030103020d0515010303050a0e0f150906120106031a010c0f02 73
    0x30304d6490304007000388680200000390140784144080c0b40c150380c0c0719036900303003454454021008110840c298120625844034006025281c02c4030115201c0e2540c85041103495103d41c4034101450030352000050000e003012161704058002d891400022400f1108101103034a103019060114407801c0404020070721644001e01c9051144002da82c1801c900e0716030074920b810903802054914101e0501906900c0d085c000c400d1021102008110a0320b0640e655944031300541c42d410100710f81c2c0350481d07503060348100f40340310070000040c0040e1034904144c14401074110110a2000c0440c400c41000c1c110584005002140d00766419016825a429075003045a5115001d03020f860a2140902c02c1700210300f941100b42c0290b2107900e90303a1350f443c0b81e00c8014002109a8041610a884040043d1074640780c1c8920051050004001141d45510890018015019160003400034200050000c00d1251305640000207455181c6400788017404000011100d82c080500d00500fa1042d120803034006041c00c0c0c0440385 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 755801645 1250 755800395 755800403
    0xc020d030813170d0605030d0906050c150c070b060109030804032303180405060a06050414031c050405180105030a0b061302210c030705030f1302040204081605030106060f0c 76
    0x7040c44102e03260440103100c0000d80040034400000c0041c45096a8402c5c00001e1909402074039000550035400703800000039105040a0040004a03c61925070a1210141c500d248184005150a0a120285241d001010200c07403000c0c02c80d000c0340303080d03014828410490780e1000c101c1e442c1604654603441c10031041c003d4862082510032a0380040b44050000e08a202000d20201c010b0b401d64008000544202400300781c0507400000080c02a07507401400c88064540244d100b04070505075001103807420f1503011911603103841c921a050314039035100c0f00900854000311240401034880040c5091401020300c42c02d6410340c000810200040d003141c12080d84400300070000391041101902d54001e907070109107000d42d01c0341c02d0064403003086002e0024581159038144847d08520307120801508510024017070b0441c0036140e4000480c401c50018a0000c0158042c00941d2121340d0360741d0550346e90524080ca510b0b01481e080002c40d180c24148111400c80301c00350b81c3e075400c43d2141c250507203581c121010151 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 755802895 1250 755801645 755801671
    0x309092d090809060a0e0a171914070b070302060a050c160309090e010c08092d1f0609050603011104050f0a1d0106020d0203030f010501110f060106120c0c020d0308 72
    0x18040f550384c078019102241e142c0e1a0b850b0745510307003c100400715105811204001c4220314058140c403000240d801039081c03003081040d105100b1803e2071810728150701840c40340d0b4441c102003c91340c00800350207004098429000c03601140c0f42e005800782075032800c036141d41d40c0c61401c2c08032814054070340b4110780d01c45020381001189c8540312461241501c600c1c1031500503603074480c100c03c1c50640e84410007540c40b05a04000e4202d501c25400300388a02c01030744c2055070080301020340002210209010f5031440352480006000c40301c00310007015025000c0342c030520304500e01d45000a6521b08060007000c401000c114500c0340344c03a0804003000321030f0000071409500880a6013012034501c0e881c4002ca03048942040d0401055854168000d00c0c1402c0d6007202c01c01c64205106002005c1c001000d41410340e8002d003403030440c44641c0c0b600d00e40b6098a020030190381d803107081c00010f141600068001311661012105202e8062480030942d0300225152000f900f005922655001007846075041d207030081c0d034144a103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 755804145 1250 755802895 755802907
    0x150f020d050106030605030d0509090c070c0803070b0105040605030d020d03150906030b0a06050a0317180910060e01031505150403021909050f010506071401020c0a0309092d0908 78
    0x440c044070026082800400c0c0e40d25005c1c0000d2404104035105103280e0310700b8030302d040741d00b5011400105d8040c0801040800208625040150f0108041d0103401b030a41225102c80355400e00f581060800c0c819103000d035181010205440c200031540c82d415148603001081503503e205401c0b0700030030192481d035040e03a071818000b00c1c210300e980c02000000d50250181c4000d03030405012110450304141e100c0b5200b0700b000e410030000240740741d03412a00b040b00c0808843c2c07296011082c902c01402c1c04901c3d640d20081080411500e80303802d04a01341651115600c243c0d54034a41c2005408071002080d20a548540c0324000f040145003180b8610545420390701580c1c105a5298003044080103a083c0440791104003100034000c0b10503030300c0b40301d500c170001c20803c50301945010f0120f2850720440801805082811900f40641d0400b50110380c101d50113001194418a500d0400510890aa02419460900b858085401202443d080101481c81c450581500d24440c8503014000c00c5070050480c1e41305014040c0d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 755805395 1250 755804145 755804167
    0x509012d02011a010c02010909050405030d020f0304060f0c0c02040e0f15010e1f061d09070e150703171801060b0d0e0d0e0d050c030703051507030504150f02 69
    0x40380010250004180d1410410000c600d41091503000c03030420101020078000341c2e034003640d001c00703d03100b18030001550703283c45c10b0023410b5200300d01c20b43c4d00c02800044c81090601c203000042d4401c03409034200300030340300d86e01c00003500b5503000c944108001281d4000540251030240d116100e1883c01d10212240880d035911840d04182d003401c004012000120b004001945982d003181d80e0003c2000c3e880080c0515031585200b4403c40ca008800030440341c02410482c1c40c000421005443c400148240070518000e84000c10b40600708a01500a045603451600e03108005000e9881c0944e140d00c0d6141c07004520106108000e0000345855245080b0300708944000742d0a224540140c0320703900b80603507141007138118142600c01802c1400c2da545e100c07000c1280103980c090780030313009040d0443c0c90b040e0420050a0803854041400b04865040c010300f2400000c201001404d0060303c031480035400599034444409400322a0210750281400f1150121110281c0d8140d1101da0f45c40040c540c01030030440c0d5003803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 755806645 1250 755805395 755805467
    0x501050a17100e0106080715050a0f0507020d120e011d010f0c060623030d020d050f1213020405090307050a06181b170309010c060903030e030706020306041b050901 72
    0x14a00d083d0b81d41d111814050910284030100c041c1c450840c0065030302104140c01003482c41a010802e04201c0c006006a040781d01c03c0c0201c0f82c40c60f0300104038403803004050400300c00e144400d032140c0011400718540f0718100d500030f50041c04969840350480c0b03000350741c0300c00558190b840d21096100700306101c0381c0301000515912500001d01110f00003401030700b0008550400ba034030070160a5209601101148501c60340c0000d102118013098540b982e11848040c0a441ea0740c0104140c1c4640004800204504003680d1108800030f90300803039050299481c1c0314400780d1070348600b9401401a420410108000c10001e1b0041406c400d5403800c200b2030b41d83c190f107030403915041400880350808100141004603a0b841200326902c90380da10702651a0002e03a60018001c055914001000b03252254142014980640c1c84038461000c2c0c102138950328459840c0800095001b10345092099292001c60b041504501d06204406400350310b401e881d18070000d0040da5101c420100ca242d9558290a406078015844a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 755807895 1250 755806645 755806661
    0x3020a0b03071704080a020c06070203061b0c0d0302030a0c0906080109050c09041415040c0c020d050102073503040f020d0609141608010b032508030307050705010e010501050a1710 79
    0xc0040d4907091b00705002800d12048042c001d00c00c2400307205403800360b0380c0444c40c143c0004100d29072054500c1500881032550241003101083d9015181e1080140b58043c1c00a521400078200c041040d03491584040d03c5c0071030103026807000241814014080143d283d03001d281c104158241e082d040030750150000d03042d074a0280e841e5405005038401d20075410744441102d0200d0108540c1400802190301e0f0044c18507031144c102030300c05d05c0d6030b118007014440c00794120f80f41c040e0041000728165091680c050003082d800d070010040d038030b0941442c050900203c0182c9000c2d0380d20404000d001c0d440754080101400642100303944040d911000c6c40d000801c00c24501d041d1185020241121a01a04502c0c0c42d2440d190b00401299040000f0024180d81c0440c4503110042c01d01d48458075002500b0528603004403a8120040307038407000040c0421700e9085405855030b54800c6000340400b200c50321820382070707410038821143c11000211082c8803181c04040e1850b4040b8028084500301200881c015055074548 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 755809145 1250 755807895 755807903
    0xb07080c040807060f1b202818091a0903310b12010608220b0402091608041502120414010506010c12051b101e0603020a0b03071704 58
    0xc5840b61718215000800b030245018540c40d02030f5810316a44809000e180c121207130407070703c500040345000380741c3c0c5050a15451544801c0f03480440c00c034810101d80000d042e8007880c030500351181e8030098540c00500803c56080d5225903403000c110140d8000c40310105018114851034042400814180c150360300c41c3d07401745101c10220b50514054550aa0a149100d4208060764001040302103100020758101c603044510502d4440b021381c2c0c03025032040860f403505c1c2c110300341c0d281543c0006062004441c0c3c03a600590088035043e1494881c000c0c6260103a02e11b6035220085aa46400100824240520000c40000340c51000d442d10342c105a000c00032000c00c640032100001c01d03e51416003105c0c01d1245a038040700a0030107902030001d81e1600100310780c3c00d010b150b0802c0710000e41d84450080a4502185201d50401111240320b0b842c14004098500c4c1040101e90950602125000403e0340c094802225005010314035007500b0003c08059680c0000c1c40c0d00d041c4000081c120007501c150072600f074829401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 755810395 1250 755809145 755809157
    0x7020d0c05100201090b010315060e010305030c100c1d031608010618050402210304050a1203110c0d0b041407060221270d02030102220b070b07080c04080706 69
    0x5000410035491070b0000e1400031680f401e00610009502006110f06407500300740c60f22503944403da41d000103010140c210480e5088884000000c00100201412440342c41e2010f456181914600c0c2504075103001c80c00100140c1040581da140440034008001d40c114041c0699051004080d030b80406100180e001c0d510b217070341d604020030881c560120000316100c0e100d907050006003042d0300010300036502000c0b50b000840040402d07d100b0a020012a401810090301c5002e4040e560a43d0307101c6207007801d10550205e024125034003550701001c544124801401804012580300944030b42e40d400c84014012205442d0b06000811081e104000950051140394014189001ca400005000303074040704041480c4901489035001c10040905062261800701c01c07801c1204101c00000b40071400c1508001e5055480092010a42d01005000c000600142141800440d9642c4140c01d55486880c0010703040c10b43c00030210381d00d1440341c0005030b0000403030a000c90906494000d00c5090505a80c014004511 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 755811645 1250 755810395 755810399
    0xd050f010e0d02070b04030305030f1806070f1b030926070f0611010212060d0317010b04230303030c070309081009140309031b04090b090a0c0806040f020405060607020d0c 75
    0x10b810400760300a042000e1017182402d113556030141c80c1340409000720426040305030004041c2920110442c2c0103103400c90490300c840c00c114102510301c0300a5484840000c0d10b94503411003440307013041d20300501c940c55901c0c850340030310340a50b4082c44045c10100d00a490040c503403400001e10204640b0014005c03191070465010728243d405000f400e58651041c045034010302030001c1781044544d407560b02c44029100090f903138400d440c0c2107403048090040c01800d00849400800c4c0d42100381d0151090302d20740c14102810a21840e5500c0c201e02028007410303072550080001070750482221000d001154860306181031070b25110300403181028004910041e0b0596606864001e00c80d03544030441c000f001d000c024501c6d040c50b15010070b441e01405103882c11500341c1004240d0483d122640070a00e481d411648200b108e04110f0516500c800c0040c40549080d03441101c085a0782801042a40c012640803801034440c0a0310360034480030380001020310798000740520040015895041d041078440d4403801055401c80c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 755812895 1250 755811645 755811647
    0x6090b150901120f020112020d05010503120c0601031704120308042001050306120715020f10021222060905010c02060709080a061814061909110d050f010e0d 69
    0xe5011200a22411884004010125002480c55110340e00100c814200000750b00044e1100b41100c440008424800070380941030480a070b1006050f1134048050380c4191036541e07000120f50081e03454032039294101100410024581c5125508a400c20b18000d80c14113959892840002c0d0141c11301b038000c5006d9070108401c001928010080781c40c42880360074406d40a0000003016400000d0920303020b40c03032004000c0100482001030000070801684040700015507810008e40382c840542c181b0840f44200c80b002891244940252564a007586007150204d03550101440002040c2002101031040f003241d0702c1000c10324038040d89150500803000410b4540241070024501000281b808080110040c402d216841f800f06040e10f580386c00001c0800c2050303c40c2c0810343c40c12541500281400c9200c801d00f1840030011070740328442e0b000000d9003885c00c2032103040d181c162000210001d288030190b240700c04180ca000c07015201c0c2d441c000e60031603843c59421143d89085a01d103118510183c0e0080015040e00d03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 755814145 1250 755812895 755812921
    0x5030114100e01120605071e020c03012009130b060403061a12060a090c080601061e02010203060d060c02010f0f0605040c1803020d0302250e07021506060d0906090b 72
    0xa01c000b4800442561400800540b04584044004c049030303262000700b480f00d4402c0b54801d50441c603803e200c40c000001d10078040c5d651411401c120b8003950130814140035041440b80511404410205840d203000390802c1085092041c0c141c0d4880318554800810400f0f4550380f0260019600c2050001030072440400c10400c00025942c3c0c4e81d100701d0b0310040e00b107000a4003042d590f03041100f40001141070071881c648020b000d035040d0804807040c03007510000105154864410980310720801c0b0302951590b0201c00403400d0b44000c0f0341e2141c105200110392000140c02d80e00842982e0300602c0000b40c44c10500c4000000e603a036420300d1040c4540c0f41d100a02c6140b919101c1c611000c4501e0a00a140c010b141c143c101204402d440041c0c85100d4244003a4203050080c402249074501c1c41c0c250b4400220079840c13814001d00d16008181c41031014400040c2424000686a400d000b124000028542c3e52001001615804600c003076803020344800b4003d0006d80c0500503584580c0c401d03203500c0090700e0300280280c18 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 755815395 1250 755814145 755814149
    0x90e0109061a09030d03050c04090504060c0305091b010c060b060d09021315050d0809030a080304030233070311040b0304021c02100e06090a08151f060507020a0503011410 75
    0x212441000f480005590029150202600500f404100d0b95a030078032014260113594414007006003400e040108000e49030303000b05109501034030104000d842d2200d503996685485907044141c44280480203150398000c00300d4140580c42210045804080300000c1784aa80225410ba0411074451500c0b8045103401d6610707440100c541a01000300305e41e4480004016040f900c1064000e002101c510420720001804075041d80101900720747c0700c140702d45800ca6807a0701c02c40f0700303078010b00504070441c2505d00c4100480307030450700480e000418905280100354882502070621400e241d62401040c1c2c0001811015200512004040584030320b8140140320115080c03c00382a101840c10000134016a219150021004e10514107503507403d0030b18000c18880d101d040c0034640e10146803000004e5011000809810502c9160141e400e0343c2c884c441d2350a054100f10613031076100d86c4003a50078017840b440340c1d0203010315600040401001c02d0380c44001c2070031500c00030680009102601d08100600c20040d0080300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 755816645 1250 755815395 755815439
    0x90a091511250b09210f0702100c0c090c05270a08030717130e040f060f0204090e01091203091a010905070f180501141e03060315012103090e010906 65
    0x44c01ca959035560050720b20000b001548910340417900c201c046c540c83c400c4d1003140342e01400c00c2d0810740400c00f0191502c04030721402c4503500c400d048007017500e420500909404416a480d4039050942c1045c81030301c00c00301d0000c030f0400780101c610700c00103960b034030300c06c40006083c518040c698034281828110400081004119a4200200510340103591501c0c84e400031100345d0080c6440641301d500e8a894901942c0d84040e00711420100d05c8404a040e607030040040b109a004d040015060804a0509031045400084c044903688241107410500a80003698818800c490715102100b448003c0105100281c0049040507920f03001c01c8209a0002c640413108242802e04050301e6440000c5002000d00d1409150304010039041e10744801003c0e90181c2d00980c0c0f80b00080301481140d2090080960012a012403182c819091100802d080100d0528141c0b4060030081c81c2d48805018a484001c42e42ca80c00ca04000081600184090503401d003a0b01074003c49201141803442c2500c50715640003107404e000c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 755817895 1250 755816645 755816653
    0xb040c030501030c03170c060c0a0e0f0a09050603030403020405100305070b1c0b1201020a1d01051e0f0c0f0615040e061f05060a080105090a091511250b09 68
    0x100c08124250031402c04c50703501c25030f08610a0906d51885c0c00901070111948442e220b45ca060200c0c90600501400480e48181ea84012000507030003004280700c00c12500f5900035080884c05d0bc1302e00b6551300481c0e070100d009401c89140035987d5000c101121405c132044c5504205500c024401c100c018000c140c000c1000f52001800d116070761801e04014030f03588280d4038034196103608004107034580c103e81c506160700d140000c5464554449001d0408801c403d05031901b0000c903401c0c504c080d0300030010f03112445070b08103081d05900000040c100d0180d014204442d0b13112000c0c08042c0c4c44c0c21041040b002002d1615000d401603080c0700c1320440a1040e000c007198490781c1001c14002d28034200285017684401c550002e4840d031050001202d0103203466401440c1c20410000b01031040c290007105617412036000b40c400c00b03d19998000b0f034804440204d1340080c0083c0a816100380c0c82c0300c490304802c071500c004030015850b10301c1d0321141f07619003400d0204081040041000560501510520701a0320002c41000740c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 755819145 1250 755817895 755817899
    0x100c0f14130b09090709210f1505190c020a2a032103020f16110402030a0c1101090816080f07061a01080f011a0d020c0a02031207110402030c120a0b040c030501 70
    0x251012580586c00c8201e9002c1c05181d1814003004195002307100da00004408002e500641c1810090401240d801c10303e000c488004005400c194410040114090b9019107201d907083c1e5101c5241041c0354020b00389442c0c4506060201395412203200300194400d141240c1001c480368507501c1d109407901d4000701407510600c20358841e88070314021030359492a03000650322a43c1c594500030365181c1328416459001407021080248284540d4070a5421903059120003800c1c400b11072079503003650b50704000102540c00c00d0002c40010180203000d684c115100d0b080050800d0345494030020141c1125400703851540d11580039602c2c66288606003035440f1020b1820300ca16150000d01001d041c1010702c12008240640c14070f0680b80e9403010250f90346030324183c506544d43e4000c0140107640d2401d40409074800e004403370700e90f202141030000b142e00caa5032240d40c412100c1c103840c0400c402500018074017a0003d80401411820500922002d80314101132000050b0702e042d030006100440d40102c40260030f043ca01001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 755820395 1250 755819145 755819159
    0x1401110303060a18020d110c0c03061006210f060609120c03030503060105070204140105030705100e01030902010c021206070e030c0f09090118080705100c0f14130b09090709 76
    0x60383c41510300c0f0b102c02d26080207940c1340250081c0b00e8a074200c105a450404401090401d9000a207400030481040325a1100c0387c0040580300d501c1030795103400304070201c54200007081c06040c0c601d149461007043d0030000c042ca40c80a5065501e11700c046aa150f03510807061207007540254050010782190340681000900030740d200500350049000180501001200041050707100340100c402c0b05074058428000f81041c00030307070381540c1400e014007440780c01000f4020560b801c011300030003a11800369807400c413404060401500109003a0000ba81003060140b500c80c0542c590010b9402100460802042203142c5a2070080010700c403a00d14034480e0300b05090901c11a0703500c0444910101046840361200d441d42d0392610700412172050040048410302c2c6a00040c0040c00000c0c0981ca4021030aa030b12540201c00c000080712141000304003ca000c0c1c000b00c40e010f600c41c0c500c6043c0341308c5a034092840d0158180d500119070a150748481e0142c500081d4140d8035007000d030030302c3d500f003ea01e0401018003802c3c810 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 755821645 1250 755820395 755820409
    0x7020102030a0c080f0d06240c1b1505030a050c09010e0114041a0d0f0504021f020f0f1b030118030521042d02090115021501140111030306 61
    0xb408108020080000c401030102d00800c4859078100d075213110396168445007082020b40a540300f203104492030b40c0d03038802900d00110800c00c0304030059601d054020600c0d58401c01c541101c42d002411041c210707007011540903100c00c0f00340720b07085c0c01e5243e50b926031030030800c1002950001400045d91501c01d11070940e5a0360000050344480c442424484100302900c40a01070a00031980149050550140038103c2c03104100e0050851040103502401520840c00500c0180c41d025a002908400716054420b0f0522507402008000c09a0348147c0d2441e0030451045031a20340c4050100341150030009040032241009584041611003e1f002482103030703100a10115810060013000c0c00744840007030445046981c1411078054042000020701c018245070801610303218200350044210810180c03144040d94241c00e000301529801400001d8076800c03c24101c0c485400700d01e205045d48a8502003803550000401c8903030103004032803044042e5481a10004107442150b13440322807582c00402c1030000984a501e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 755822895 1250 755821645 755821657
    0xe010f030c0309050304061e080405030301050d1b0e01180501080c041107060203010801050601120504121206080106031a0705030c040302060f0412060b150c0c130e0a0503031b0702010203 82
    0x1080005810307402100c142e0203001060401800c60000007804260390b60000380d40d81e030240d008405c00880201c40c1e1416034410005075800f504581c0184010480e40c0340008007100300d07908c202d1340007110310341c40f040308007101d0708580006009140c50030060010920381ca5844026003650b01060200c0d52404107015120840705070954029500c6a080d03a060750b0440040b01d810f5640007034110361b0ba60352000424002e00054420600081c81c400a4108812207805640d020741e400c8401451654441042a134103100d405041812698071900b00007102103081c0b141d28020f6014400820141c0b8a0080740002800c0081c0814288403040c01880802d9902c5801d9405496041d01c0743d81e0349012840d100940780c040d03a4441d1010600345446041041100e0700071940480059802451032b84103403040710b541d800f03540d44c44400c0e944241d1103c50b061400140c00e84d60a499040000fa04040c589000c2d4105540c0704805d49290b030000040c04208244805032070f141c0c031841c2d0041e60500c0f020341e0000b5101c2c0300e85 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 755824145 1250 755822895 755822897
    0x41e21020a1203110304182d0b040e120909130c06080c0d06091a0a0b070204021804091a01060801032a090e010605011d01090e0901020702040903031a010e010f 70
    0x30001c50080500845419101d150b16070205da48681d6a808420003000c201c4903d10021805d1200c51040010845001c41e00c080e000009010f5130084601600000c04403080c4840d8040c2d11290501c1c4041d40602c0b07180c048145c203040855890440c88244a2580b50140480e20074003c2c504801001c40d050285003020b0b20700718079100e105511035000b8a012401180008603c0d03c0c81d0400000305914142e221185420860039807108040e4514100b1a0070a854414003203441020466400180b4050340100000001020201800b11141010504451100368219600300d00742a8419002540700b2200e4010086490f04d0021503040d99075400c86a540d01c3d010040c00d922010781d09100c8040d044004015184540007080005045c0083d10701030501031183c1404260b01c2200ca041008081501051000b8184c540300f51052404000d40a01007004100306e405543c01d010910059a03a07001e40d9014a00954010680301020b10ba45119041707007810700c0e41400100744118a0590b040320850880f0724035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 755825395 1250 755824145 755824169
    0x1061410050304110418021c0b130201180e0129070f08070204111b010623130c0c0c0608130b1005030618010b0901081209010302041e21020a 62
    0x180e841c01a0010584d22481540242404118041c1001500340c00030380364000c0307a088040032418024090310024410014201c003121200003190030305440c0c10120000e1040c5805410718042d50101f80303802c0e01c5900850380a40d003c80041041e00c100840b01225185103c00b0340d602c04010407031121042c49407220003090030000a400c001403200f070400341c41308a82c0140c0f0502425007001c0f0f0121035644a100380400c00196900d298036585c10510440b015034074450f0f1042c0c02c8003203000d07903040c00b034001c0e4141c0b590014000003007a0410b600c900a01c0c0c0300c01c6007900d131149024241d203469400083c16800007401c0061180411400c181c021006c210004d81008110704e040d00d41c4076203585001660b820898240c41000180001c0c400e80c601074210104480c0000c00840c5180c008106440301d0038451121540c0c8003031800c030b00540c498001454000014140145000d5450508800001d01515420b2400d00d03400030812407900020180c10800e411000c007020002510303800619050158020142c00c0301c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 755826645 1250 755825395 755825401
    0x102011113050f0406170606030d0903170c1608061e04031b023007050108040309151b140d03231b030f07020c01020738160203010614100503 62
    0x1150752118026081b8081554a00541c584616640e0001a5610fa009214410310980400c1c401e01d103103020f50f5032004034120104074000119603c1d8118030b8141c84903010710b600c400d0304003941c00d00c080d0007002180090900c901c2c000c1c61000c0c1b0101da56001c40c031031281203000c00002950100828036810a2001d0864803206a030000c1920364410101583d00540b01e032030800380f48401000182848568101111403898848004480c50801594020045004440180210034054040d01c4448501e0303c2d00e030424006910704003036004900b0505440442d040000c81506041c00d00c0700000d10002403c05001d1201d081c801011620210701e0205545041c05010602d43d6180441401360600107c0905031a410841651a1610400d84030b13a000740c462150340401035400030032140304640c001c40a03c0031f03103c0100d10036a124003a003500c1c0010030301003040382c031980d03000c034400382c1040007482000321aa4405072040c982120141e40026160080045202480780e8540d140074031807507401c0c075040303490391 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 755827895 1250 755826645 755826649
    0x3021c120f092405060d08030105090403020c03071214070506090f0103020d0906050f091b09040f1b060215060d02041e060e0f010501030c090608092a0102011113050f 73
    0x314003920003c1205980141c003901424000703c03c0c0b040314041400801a40d2111000c1103240348400100500c035000610041000d440c1c603200c0700ba8041d00074010385d0400c2c429800041c0c1003918a80100c01c2c001c00e40e011080502047d10002d5a806181d14020b2944078100300004a150103042809441400c0075203610140b6403003601a0340e821482c44105105a40742481c00d0005800110b51103400c41c0042ea0000b05507040000e088031003001810011500901d20805000520790002c00c1581e80c209000141800500c9051400c441c1c2e0045207003852895041c940d0007820704c3c2d000001b800001e4101401d0050603540c101c1d0803408a60704030380000f1410411101c0d02000c0800c101d01c0d201803442e02c00001105055002140d03c58401800c0040107070307072100019400c17904909070010010312901010700c01c0a008202484c1c20410710070840b44240510152200c00c013406c0701a07190b800e40c01900b030714140d58090264111401c2c4c4e107080c4504060500d1200043c03001c02c1e208040c81b9000800d00c1d05419 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 755829145 1250 755827895 755827901
    0x507030c1706010306030b0c0d0b1e04051012030216081f0c020c030a060b04150e2a0a11071a030a0c20010203090c04150504091403130303021c120f 65
    0xd47e44094000b40303518016140c6911a089104c424a401e82044e54071200c92400b400c00c00d001804208991072000b4000040c040140402800c401c0003c025440c0425203180302e040c1a0340e050710a03401030159988034610700000d0f1400d60700801255105140c010a11921010f1030040300080000014114116000c2246881450300d840e6400d80503020881082c0111a08003070600c807030696092091201e0410010b107000309501c1060458006c00b400704142c40343c2014490340070048a0909a2508440c529103005a4404060580400e54000300d041d0500800c0c002c0d40004c08407510100b91540c40b00301d4070001444003c200c0d0721100c0d030301c14400c040e990180b595031450030034188200c0c03041c071481041c00b4000c0d441541c030302c2194802c442c101511440d01e800707005d5101c01401c8400f0368091411080c400680301c0000101d82c031014862028003400030400142ca0314190060038140010b28609010782410700c205010144e036003011442c0301c005600450151340d1103004007000212080382040720001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 755830395 1250 755829145 755829149
    0x603090c0a0329010f0b16060c09050312040302010f080a1103040308090f0a03020318010903060f05040b0106050c030a0f0e1917010b090c0306130f020d0507030c1706010306 76
    0x10003040c8001c04028000c40e828409010010050940c920850908070010302c032209200f9241c0040c000d81c028080b2088440182440d0201c80c080004001348542d1104180d80c1d41c88054400544116001c004524013001010a013007110000c5a00c0d050540d00002c10340905a104401030010301c0c1d000c2000801107a12151000500d400f9041d26418140390040c001e06003030b0b480075180e00c2904018a4402d4001c83c5c1e45003116450b8006600e0410b00300b00044229083e10901818481c01c4000040440c4a5000708400d001e1401700001e42c0b450300307142c800e042e030f40306800010420030180903440c050380000084a410007001d00f0203050300c0010850840d201140c03104001d030040000c441680310852031107a10002e4410100075441c00c2540e000c4230600b00e174107a2410315031040c0404085058801a44021500448042c01200d004102e002d094401ea070940b200d101409903000900406950180c404c1d40e402078000c1ca4203000361180d045009110200301018100310b14601000b00b00543c0c00b035807213100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 755831645 1250 755830395 755830399
    0x2a0504150806120703230c1003110418060501080108032511030d110106051207141c0b01050f0a080604030f022409240c07030e06041806170c0603090c 66
    0x11809440340ba141c07a4403080c10064101e49000c01240c2111b02d8004144c121903020042c000c1c810104180c4000c502900506c2004100e08004020124001d1081261024003110304480032444501e008001002c941c4140d0203050160020b0000d0010b600e046000042c000c002c3c0c100ca201c0c0c0703000c282000008808211485079043c4504214502e0081d04030762000744107004031001b0440c2540d11800d10600f401107040000458000aa06001440030040300701c41444001d80600700c802281844031030401310b82207040e1042c59001d03004100d18500503040f0070800e1001c1d6007000e28540f0700b9891a9541801400003814132082ca164000002d100b00034001803412075241c648030240d03e248402110580c1aa842c045a0081041520030703e00f65210308910810045045045680d414507a0003868108070012400c0240080c0696800d6071100d020b000502000000600102c2d94004000c088a890394800718200f240051240303940070003c601881301c0882074400c0b035541e64a0703016440c10b02c9111500c0e65 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 755832895 1250 755831645 755831653
    0x1a071704090b04060e130b100f030309150207060f0804030c06240b03060603060d0c08100203060111120406030209060702030607020f151003242a050415080612 70
    0x40311011034101020108043c3c078204501502d4941c840071042007140c150b807048190300702c5000014101c0d081d07da44081154407900540d81c8034880640100d20303e5000760002801c181c0140301d8030b84c6d1418040e9100070030307000801020b49031000113811030321131800140910525a000a042c1802015080c1286600c03541c104840e80d01101d03910b0503a4030403180b058440780b800f240400c1c040307116021039001e4035008181c0342c21666508100202040051403c407a0400c115200185120041044140e61140700501688070305c2d00301300052507055440200051944414413048a444d440d004a80030788469240150303030b43c1030510205a1030f218155000350144903c0d0200301180ea404600398003464145010350703618001c010744144802c902076406801c0907609050410024900c2c161480b24503d820340f501e40071034042c2d81030340210382c1c81003001a549072103025018480071106000c40c0111000341007480c2401e00744039a03000c44401002c01c171020321449002051007582e8211942c14212100c06c115 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 755834145 1250 755832895 755832899
    0x314010f110415050315040209031c0c030f05090a03080c010b0d0b04030306061403010b0318060a0c09061110050a1103070507020a1202030307060504150e060612071a071704 76
    0x501e600e030302610604119110702c41001c400944210203d0b8014020b500e1100b607030391031a20410000390f00100c607046c4c0c18890417808000c05040c41c100c124218040b030300d56505400385824064001e480800c1c0110800108110180b9030740d45980c020b10a0b250010070b00c41c0c682c03003000400c0e4018016240c00503405040198400104942c0505440c8281c1c441c2d03030305004c0e06545420030b58a00c0d1107240000503425047c001403203e40111400741d684000c02d203030300d059840a002c441604285040d40c992070010b468280700003800f81c03c000c500d4001c0406182403110b0018a4100949031a044007001e84101d403502d020601040181e00500804030040c03264554034103000d41d01030301e1984540e40c120301030b84405500207003008180001c807414075005070145141841c50f54542e8001d10f402030044880b401440d1000640d004241721b000d0400610b01b0052000b400c0c500104032010900480a00d81036110380030070701140801140004164000d03440040e01da00c1039107010800f0008061451880c03003408180 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 755835395 1250 755834145 755834171
    0x1107050601080f060603070e0406060909080a08070806130b030f0f16080d0c020105072a030308060a0f06050c0715030b10020705032109060a0206060108090a0c0314010f 74
    0x301d040340c0030070085549120384800042c0e11030b8400c4a160340d26401140080041c080034901d0294001c2c46031400090003511092210704440100708203481c40c05001c6141d8001c070b50850100c50b00080e1608101210740703070070305c000381148441185082c80c5a03141d98110440d80c40401c41c044030ba01031002907c0c401d801040c40c1950b500003092101d6200040c1762400070381008041510000ca03881940e541c01564003940040d00c4584c03040c8401c070323070341c0c001c030044035182d01e0716070350f0f43c403185002d101002c0100e62860500600310301d000340400b0f02c9841c51480402c1811805641e20303048a00f0340c28a141ca8500c80b2810b1400d083c466401910703074044181c42191116410b40c45044400002c0300d40c500700c60401407041385e40786414018150964001c0300d00c5104068095132644040e106c0c10306561900300c6100c0410131035000a01008050f0740a442406070303960300b048106a100508000416900c0035030348540701d81041e14400540b01d1504910341648000e0290040500c003000e0072024000380341110a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 755836645 1250 755835395 755835403
    0x418051b04050105040308160f24020903030403121b03020a0201090e07020c040f0e0a08070618080a120906052701060f090b03070f06081501140319110705 68
    0x6180510000c010034208119400109440c190740c0d069403107030300303040c2195124011507002e02400d1416003050040f43e000101004411000c452040290150b00005001030840b0401d41680d006152801409220100e0301e0000c181c60843c1e402c0848030381801c0c141c541c2541c060001e4070701d074048185c00c0c41450003807540001d603ca5900e13100781daa80b0601d0b0b50300c4200c6001c03400d084c2c4964006810140d00a845403502c0c1d000032a440e04038070b80009050703240a04081c0b401125950803124800003058030b2045c40404e05c2a09148221428041c2c1000d40c03a076210b101a00c51804450300703101d01d070300c0740540280b80e513408400400d80c054002c100c01d00700030350104e42e80b050b080b2010b290258000c104401d0b191060144100704c03581034000702001420401a000a04a403488903a0144904400003541c0e4181070010001404d1640703400d006400d141e80c41342c070014000f52686040c000060b6065154082d1a000c03207a00034800b01c0c52809440c4902c0001c4041e0090908100d030500000c50000300f400303c003003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 755837895 1250 755836645 755836651
    0x11100f090221060c03070509010305040203030f0705011506050a270e04080903011104080a0209041a0c0a020c040603020d080c0a050d050909060907140304031407151401051c020402041805 82
    0x300443d90155210b03000220b10340700c11100c100014078144810703003155011b60800c942144c070040c01c0da42403519107040640150000d1005860390b83d110320140c04c031a10365090001c090003851424030300d814500d00300901101c0500501d001a915042583c0300b002e0361030401400078010442101590b41058142030099810102805100c0d510b014402240d40b15540102c0303086078480c0010301005881c40c2c00f008140c4100410683d03403180000b628046841c00c9980c580d1080000c40c1ca216200e09400e44c0007131130000324607103080c003462600500f440941e0f02c1d01425a100c990001402da0365801d888031483c2006140c6038028084d1048182e000f80564200b8003a12030b011099810a02c2d41c0d940d00c04024031600251000c4021460590310111050340030002540d1150190912440c6181340c0c044940c850383c00450242c0b201036032030305600c0c10b924850040464140c1000b142035001d5050000042014101144100d544680c25000d0021504c940d01543c2c028641031041c0b40d030b40b54140c89054040c0600b1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 755839145 1250 755837895 755837959
    0x311120d020715060e131a0a05101a030a022101060203041a04051507020628030501090b01080a020a03060b040b090306010509011401360305010b0111100f0902 70
    0x110580d50386807030581c444c440480301070a64105068a8160700700c40da00300c09040c00d4900003030b1f00e280c402d981d03100a99800d002e0032210340d0010399482d00c4135000b461566250800041c8805146425040c0e51b01242903940040d0450401680c2d815548000010b01045e4041452400e04244c0005101e0750040080e1040b61030381c1860000000780d44101d002c80b88150701a4a512107040301d02100354240020240a441d031004c1d18043c90700f040d042c041c8910424148030760b19290100c180030101a42e00d8011140101204401030182c100000c1c0080c010b404020102c80c1c002d580801e00000e441d100703030001001020b4910f052741d41c49880d4610410654000301405000b88108400006c1e80e0078a40c0e4003034101c4000e000480ca10340c000340f00445550840314100075820000041080072003c000d8162403441e07511b102000203032460361401900b5201800c1c4554180a2a0704401401c220301244410b03664a00410028030007180500400041c10003000107504501409189074042000160140103d00c1c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 755840395 1250 755839145 755839163
    0xd05070c0b0f0f0a0e071e0506030109050a110703021b1906020303100b0301080307080d0b040e030703120b033a020f1207230c190e150d0311120d0207 66
    0x14013042402513904541409071944c0c4100401c0283d02e0131400020b19040140e119255425903820001c0d00319002038000c45031303e0784e540c014049408034620591058559082d4064145206a1006920340c50b0015008880d401c80040305405a9501040304100c8071140c148141000c1d25454000e650781c02c00c585030350b100d600d90000415065000c1090b00d0480d0300c0107000390302e003910a0755012034541050404c1e07036426445810b01415a80c0f10300580050070394010055031107120a003002410070450403148005549045040c0519072400b250b810a01e18000703000074410000c840039003009401c0032070048002c454071034984c080036502240220f0007203110b004a641e05641e00518080c01e01c03610400134202c203c5001c0710740044000740a1608880d044c08162500f030400f1001181112900c2c102c0040304070000032051000301c82140555410101040c1d10032001220351011811141d0340d2440501803000b03801c88000c001804001c03000101d0800b9116544500e10110300f480a50070442c000c0300c02d418 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 755841645 1250 755840395 755840401
    0xa14010c03020c043201081e10020406032f0a0c0f02210607090b0d110c1608011401030f08070203070f0605040f050102010216020f0402070f0b0609010602060c0d05070c0b0f0f 77
    0x615040317141a10340446c050314031131070a10707814041c0b500c0c00c103941e606c14054050403200210041c4081c00090200c0d45010554099514540900400d803400c0c1402c0500103414242c00c800d40a0103a0714102c4a81c1480407408106041050000554020080d4445c1900003c0240c0303c104000380c005000501d001c48000340c99000301518000c68500540071000024002c280031041d0b01e41220300400d4540c0021850081e504800c0350820319050f442d5108001a004100700d0f02c00c00344661040320140015610043d41980e0750444280c03c6041c0180c045000070603220299501409000001c08803480c1c0c8601c603035075882e00a48640c01600c0381407a0041c0c0c801000810754010300884044549051030301000f180c8a50070442c00901c941c50341608640d080c880c0100240c0d00c1d0307001c0e0906e82d011303418110740ca20300030b401c104501005030001c800f10341041c4180a01240f111080d20120305850b000071840c0d070b4410b802201c001214500103483c2c0b0388070005100044040e4280180142941140b6000b995 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 755842895 1250 755841645 755841731
    0x80904110301060c12050403140607110c0f1212160302100501030b07081f090605120313120302010207021305060906010509010f05030c04080a0c0e060a14010c03020c04 74
    0x80001d202e90743c0860200c1011a0018492000600308024242401810191252102ca400450591414843d507200c0702c10b000941782c1101c04402c0880c0404000c1c4140740041011504014801d20703254002c045005001c3d030a80d00c00e00c10510710184801d003483c2c030360303c0303000c0c10071040000b41105038050700a000300c80005800c0c500545050725000b000c5540c1c00d0b243c904e021580000e00038000000300100c101c103001030f002032400c2072000b07104a1b5808181a402c007410824800041140340100380d108000c0c545107100f40300016812116410180c1203110100e080076806441107800c001d40c0b001801d8014441e11b14158407490140313000b9520306c0410b5542800542e070521070080030a0210729201008035200d0312400007141e224015080041c00c0980c0e0b00107031807800302030b42170881d011550304c0018000e02d01e48070800e0390b00070400c0b40c10400316441c2240d1000d244081c2c05400b410412005180300500d40208502654003001510400c00c001071101540301d0001401081e2401040c0d4000d001605 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 755844145 1250 755842895 755842897
    0x20c120f0d051c050f010e18060c070c0b131a0c01061d10140607140d0c050d0503060f0409020d020d0c0501020c0402030606040e091005010816060c050a060b04090206030408090411 79
    0xc5c9100031020045909042d003d01070303210010104100c2065590071405903460600c04180545c00d8485007980340c411601c5d0001d020045c40d00300c400140c10600091800c6144540d1410440d0b4804494207251064024142c2c981c1c1f040001042141d0b090000014200c21800f10904030240c0300101d102c0a5101c03044050401d006502c2344080c0405c1c043d50481240c50120014070340c0d82d20038010b48181018014006040c00000021103000c90f4500c6024410720405204c0c00e900d4a445160031440c2d0700c1c200c400200c00c520180059030007595100b2000085482d401850b44103030703400501446407c2894507152003144070600a860041c051000d144409050034000d03a805804010303d05800d244c01c001151800380c030020110890b40c407407405c0071840c8041600c9014080e11090018140d15032180340e9a0f451860300340e004d1001c114240d070714400807a07808180d160070700e6072082c4040745c0c1706400b80026000e00107034000a90b008400109200820501c0740040102503020b6800b809201d107246250111 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 755845395 1250 755844145 755844151
    0x50f060a0f120617060609070f09260a140709061a03060a2315040303080a0c1101140a0f0209090403030905100905060403020616020c120f0d051c05 65
    0x108035505a0560401d0003221a0011188082c0340041c00680e940da07010020007108130800e0030358020703000340038803810100c08030b41d480f004600700341183c0c000c4001c0043c030000541c40781100e00d01c808600b06006410100e810319070890f018040b070302c109020f820117070020342280e415006248940840000c0160b80d501aa6007200c50081041410f01900c601c46019540018601988480d105101117114080480308251010b200300103603980c040c0601c18040748100403001401d40c100240300800010384d01c404900d03400940ea003004285c1d03030074460040c0c070f110007410014040c550a101c0300350b401d5122104058030440b00c580b018003585a03800341071812880740c240c600ea04402c89200280110b4081d40208090620801c101c2c0c2c005802d80e01c000c01162060081143c103500b1079030502080c11750422445811286205002c040355090940c0a9600c240248a031f41c0034000c0303402000454501403003051507081440c0e00780d40324070480840042190f0700030758076042541110405a40f038034400b4032540744 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 755846645 1250 755845395 755845397
    0xb09071707020c0f190519091a0603040201030e01060506030c0c071203020d0c0312110c1005240a0305010e070630052e14030a0236070801050f060a 65
    0x340e050000340174445004010b41740141c04001c600e00c00a000e44843d20784e0420300c0c5c00004043c618500740400803003a40c10700c0c03000c400c00300301003e040d403202e5880600316a082603090070005150840e813500b85015052a1b40841d6100801108000e118008040200382240c024410741d810180c880d50140381c552042d15014005a01c0504000c420901581c681c15402d8041e0600c5d0541c64503c11500003500c00c55040d00d000c403c80400c072040100800c1140400a0403080b4050082c0d00e40410030280a80100003589510140c0390321840076511090901005940c0020091011012000b400355a465031449401c2c00141e0a19400e01b9a40303800e40c03414542c5140b101850000b030f1000c411080600f074060720070700820307031000d42c4084000a03019500031101039800c8281da1180ca40600f44240c1810700c0038044c001e402c40004000107039a14407100444800042e100303150705124500d0000d403482c90500f01c1140c48030500500451076040002141211700031030300320110105c010240f01840c040c0110f900 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 755847895 1250 755846645 755846659
    0x1804110102190819210603150902090a0b0d140c1512010306050c04050d060c0f110a0b09120301090b130905030d0c1803150608060105130f0b09071707020c 68
    0x15001c1044d00b80c0502c4a007540c64110b4814401e02d15644100310300c0d001000d40790790364010420030004280517903e03540d000c9000410200700150080b81191900400e0006400e50f13803100921070703035161032468542d80d810140c2c20002c8540321003000e90f111a100082e40c80f0b2084070b07002e8103400d1105021071354030b07480d03868030541527900c4c41c0d5400c00903100240c1003402e0058203000c081080d0311031400407681540105404194016444030150600c0300d9482440200882148590300111000a031010036a901030201c1002e0b40c0c1d411981401d0071444400300440d01d100000009041c051034000e1401c501040b1100c207040008034441904031101030100509540003800124007800407540b00c2c2c61380200c58213056590003a19100c62003c9007494004940e0702c00000c00c00b062150051040c080901040002000d0365410300300000c503c0e615a82c902d00783c0300d072641c0e0395885559031074201c0444003c000d001d000302802d112030080c04107468405025040c0c02c9110001c0c1810b4030000d0120f0101c08054030171 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 755849145 1250 755847895 755847907
    0x51c09050a0b030402181b030c07030e10090302060c01020d02040e01091802010e1e04020406050a0318261314040b0406140607020a0f08031903140a0b18041101021908 73
    0x40c0c3c1c1d001b60043c043c21503010b600e480c841a541d5100010351086640d00143c65440480d4600075001150006030740b8001c40030020b00300c00b119040700e1400103403501116800c0c0c80c1e0b91040c541c6030181c4213400088820742d00125001941d1b000d200c0c1000d0503164080c0040c04103801d2040307a078854112203003020b80000c101d0000c200c500e0401140040307021090840391014412540007083c140e0f48198417180010b01d0014180b001c05a00d48110080001071400400c1c400240b07031109501ba0310100210300f00078203084102a0082201d1301107910b030041c6030002484042c2d0743c0119943c0d2040000440340614108255031080b480d2910031b00058071890007a40700380c56210381c140615604880c0040307800905040000c03851100c0782c3d94010041031031a00841d070311140b40041440170300400c0d0880c020705040440780c00200d04c0c4000041da0011001600060420f0102c0004400905012083c01684001c005000611000300500c510b42102a000c0b9000d11925007000c0225407400200500021414061 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 755850395 1250 755849145 755849179
    0x2071a09130f1a3609030705010f140c09151803030412140313051005210a051014150c07060f021b01020613051c09050a0b030402 57
    0x1a526001c0714850004141c24480c04000844541002c0303d00d4111044041540514081c4c107803100c1d1460324003410000129001d01c50110180c1c0858062000c20040e00050075084100250fa00c5550024002d0110101c81030740c003801080c81c00c0c0010920351a0030300181d619400c0030103d600d0034001502d800342e14030749024100010381210854031400d8001ca50154002e54081020300003030042101d801036040510b2500c0700f540c07020052a214240c000b4001c0808580804040d982103407000d032110f510040160000700ca0304c2c89a2881d902c0c803581d1007614042400301d0341821511500d4000320800080d02c9061501c292a1194840c4241c42d048050030702400b418071300049480d0000c000561800e11841e200f0043c00c09015400c074500054010900c00b1841c0e60400017121111514000899203103503000000307460364001401c050b15902030307800714000c000c0708100e2541101220b030031082400d01c074440024140c00700c5110f503074410b0880c00c5011400320004000c0701d009a6006004c1c10584001401d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 755851645 1250 755850395 755850409
    0x30c0d02030304050d080d0e0114012d080105060102070f0f090f0f0228030507080411130e070609090b01020304060c05011b0804060e0a0503030621030a020a0302071a09 74
    0x40741c0600040c44005041e0716086240d810300b07440340b20060b440315a48680203040b03803a80304104c0340c240c0c10428000341c0c049403070710268107580c80c088408140308089034814215171440c0f9481e0014a0602070f00040340c0806520290003100e00764255411a82d40341c8035159003001030b025011003010500020410300b140d40d440140e0a85010704040344e0585019014000ca0300011000d0346002d1825146d400560040300f0031815400ea41c0c01e08205034184600020308d03003c0010001003100400030582c4003265280503c0b1041e00000c12410700113800707040d9070036483d40014810200414086440481c0303412003802400c850310010f0b8015800c1500c1c19000f00c502b01000001628103550703410100034259000c0c910348090703101588605046080500d007044c00c480c0341603607290450300b0240c99031000a0000c8126600054100e550690040e41940369545d1020f460145a9441c0f100040c050340131500801c1845609000c0d40a407900701c1e03664120032400881e0b0404d4200c0041080262071214a0198 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 755852895 1250 755851645 755851669
    0x10501120e0a080a08160302180d060e06011e0e09121b010c08010f0e07090302040c27032f010311040506070f05160815060d1a090105070e030c 63
    0x6084a0082c642c0c1d4039880c055500603410440050001801c0100d0f5940c2080480b060302114034046180c032200407810541040e510104a205640a0010750140a000c1d041810046214401d82e00a07580d103982014038911150a0300c1d4032083c1d0840c0009180041e6038019106010a01c082c0c02d02194103400f4442e640d2003000a080484180b401c22203015000348911a5282c10350707100e440841d41003101c050716801042d4489103850b4040d02c00c0050342d45e4014003140481381d0603100890034181111007a10b0341540289007003100450a8440f54201a690040b1000c80b80202d10220360352943c000700302c003280e4034501c0c081070b09120f98000b080c1a512039848114000400c4011608040d115000076040e51701462040ea80b2b04080b440c22420700c88107004015628208050b1140030070300d06003007161501c00104510f1015a210303800180240c8855040c6a001a030099114155120700070b0042c42e0002c0c00d844402081d032030071000030a4540202e18414020368024010b04a16212004001d10b5043d18 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 755854145 1250 755852895 755852921
    0x20312060d03090f030b090c041a041505061303150612080f040905010b0706061401120906020403020a08060412021b10031e020403050c0a030b0c03040515070e01080f01050112 77
    0x200310000c1c3c41100c4008810245d440b07405000300324146101102d1030f0070384942009105034604441700c059a01003060079070480c60162400700da68403003211041040c0380e095020a4100303e0020b002220380004240c410180c9114081d25599140114980070480321680035004400c02038400700b9002c034035080042e00d0041084051a8a01607d8240e10300668100380d2240c00c8160000c2100030412806000c0c01c0c01030301c1102c904080301120355000030940003003061000c0c0e0843d682c40849082c030840750100c5000e1034010308012992a500d4841c60b42e101c05c00c980507648140d0002003508000e10124607034442085080040040c1020300c0200a84680703a03c148006041e0350721030b05035100c1403111505000c1d100d05040161907034034608049040a8040e00c00317501c100d883e514141700213881545110340045481201d40c5d213960700c5203001403a021550020450300d1103c40c00300081550700c400d00390009842a078855a0326202c80f0316566443c00300b80600c0d408074641c0000c1204001240c0d200600099103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 755855395 1250 755854145 755854157
    0x120714070c150807030507080a020d06090903020a14070e220b0106020c1305060a030f260711010503090607110a022e02070b0901080712050906040201030606020312060d03 75
    0x4140e0361948036040591240c55001141c0a800c40b40c01c0d0000c034100d80c090000e081c140104c0c03030300c3c142c010010740000700a514200d03404a00c140001e56141c0c0040090682c8010030840081c2608010350b0312441b003202110311420b5120322402074400441c5040880d03110406da040140c45200000354081c0d08103c0c1d20b8607500c00362280c000483c400700c942e02c1c002c0c803640d0041d080840e806070038045405c06000d4130100050502f002c0c001641c40b010120f00840341c110051003000c20365072a004d0340d003100e500114040e4042c0180c40b2500140c4500c01031580c68401c10440811004920040d100da0000f1100c0782d4040e0842000124034a010b40545081042d10380d0a0707640f0140b40758002141c21951080440e50703684402043c04540b01d40030641042e6005500050035810703e402039001c56441402c180360304220307030500400e11003402505401c1034001c3c80013007405a45000c281e001c1d9544011601030f80040c2c10020000ba507540040111042c0c1c0300488004002541d07440c0900c9a0000391020480800034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 755856645 1250 755855395 755855407
    0x403030f091209080c19030b0903040806010f0518241201110909070e030a0303091e030e031507091406250605100501090608060f0a0902070302060a02120714 69
    0x81c0c101d1500b00d405020f0b00d030002c07454240b0700014a44400701e4109070207508500c601050700c116240d81c0c203007100d90000c00c054040e50360b0500c080c114001d640c04240380340720700702c00851001644990342043d20010382d0a0003081184100240c8606c070f080e121018040d071820342c1e00c0200000c4910007000c0c03001c060300c000c0f1001e0006c0c00440c01c680010440c0040d000000c1103c50092801500b4a0f800402c01c0ca0b000c4100d01400e400a03071a0b8008a00040905540c2e625500401045100481003001e01c50f142048100c1141405001641d90300c80040c481e00544e00c1615044603840806030203410255205505a07090901050361a20001d054a43c000424004161010480b050010850f2000754501c0180110fa203407840903035601038503251108178032441c244021b980c0140080f08030340c207c0c0b13880030b842c0d1a040c01056502980605040e000500004049040800c0e0f030001c0171042c0c8240c0c212112542d40c100034100328003414281d0050f942260f0f012440301031150f500c15161607026600d0341c0ca440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 755857895 1250 755856645 755856653
    0x61303090501050919090b010e03070501020c0613030605010b0706150b030106030c0e09070504051503130f030e15030115141b030409020301180617071e120606090c0207030b0403030f09 81
    0x10717540d80038084040e16a5007036501d5507405100900c03d1a17040d0000c111140c14000003035240d01902010a0164201007400860003045191b100d005541040003040556113600c254034199001c0c01c0192402401c20045400c0c8070300402941e0102ea00c21074105003540d08120f0304901504805404e28100718405c10121020743e9080180c5000b5a9540c5900e0b64a0b8506024024030000705007030941550307030500c1088041d40070201510060341e400720103011411943c0c9401c2c0d039040c130074411103500000e803100769080041d0300304021810b8a002204075800c000301c540c4201c03100c8508020407041580180f020701351300e858420505448160a006032800d0a40320000b031401c03604240d20003400c8007951711030038440c0e400502c2190050600100300b0b042c41072005c49034035500d1000307118420300013580d120b420400324030340e185140c041c0c4100241c4d03101450513403c15a020f4523903809901851840e0140b49074920340009400d0f000c6a91081d01c030251540e07907440076401413186480c01c032040c68440034054005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 755859145 1250 755857895 755857939
    0x12030c030c01060518011d180607080a15031502072301060509062d010909110414090601021b01090f0303180b1305060d0e010507110613030905010509 66
    0x1a00d01e00000a400746400104003186407034840340c00442e200f281c01070084540c0300ca030401400182000054541d2a002e032190b50840c055162400d441c01002c092011560b8890640c038007451980006001e448507a50440790780c249544001440104038613450714014415401030200180130311074515080708652410020301200440612450750b6950b17062015250030307105290840c8051b02d06c00b0364045500d00b05076402819441c0e503101c0344400410400c4d45da01c280c0c40c00b00648852941030010300510300c900c02c40ca80041c094049416403c01e02c0084034100300c1450751046205a0040c2a20600320090250345910001c4250400101d10008101c6d001050003400046110741d4880f100f00c0400403c8001d00001c0350040301060004124051241d01e021032610245c81d0129a010342d622000c1d06848020500402848400c0d401c00082248171a0000700d008e0801031b01c0c4041e21b56030fa072410a00f0000c24840600140450b0300181c3c188000d5100b600a400300003000f420006604583c0c2e0204100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 755860395 1250 755859145 755859157
    0xf03060403020d08010b120103140c03030406180920070c0e04120f032009010306030c090207050d0212180f0904150c020307170a0c08120612060f01030212030c03 71
    0x26a10025400a43c0f80e0f210702c3c52401085004455406c00060240c0210400c03010b120281c941c0c0c03d0410b00321000071040c0310791003009600900301c030742d5075a85900c00707420380901013540144070046000000307410005010310070040080c9008000c0c048084000c598a50300128016218599403000100382c1d0f0752256040c41c0030b00d001c1c100c00440f406a400e40246074841c42c1203282c04050a101c1002001101c0100740b00114800610040d2a01c56100c0100c000708210384c4041c250308120301d00001c484546500400b0f8840c080c0082d580002d100040c03e136551249160320b20a4410100410b002007560001007034000304c002050780120b05405000511020703c1034809985010540300002c08429851084618201860015508003000350b00c0d11510340640c814000b9240b8000221480321074403d403a801da000d94840c041c181c85161804605030040c104481d598003641d4610301c0701d4410100020514030504400c0e003803c44030f0382550300307110407003d0004404146100901180803440740031300240c08 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 755861645 1250 755860395 755860397
    0x705030a350103120216032003030406050d02031005040e010506010221030a0e0a0f03110115081c0e120105100b0c060c0703020c2206090e0d030b0f03060403 69
    0x80341981d10450011000c0a903100001d62060419807841d14012541e441c504590300841000307460020b000e0306908101580c84400c0c02210700c00004001c000c03008881076101c240c2d0000d4400112000030074940d881c0b145004142c0801d10030703c09510030744420380096a0011407002c030b100070300c0e80d40d4022a05540f020342144000303035150810846156810044092407240108a003040340c41e400c00070f8049840b0181c12035060340e495132850240440f04000358022203510405011050105040090049001c0e4010310300d15400c0840b0300c0d0084080007c230390184c40350f5030040d10040c1d0002c811211044554000c500a124483c040d54a5664803c0c15544e10039034134030000f10756850303c0d00c04107001d50102d4114a0320070318140049140c2200000341150702003030300820180c0da0741090038160700d04100300d11515444101d062030480140700200c0315650307215094205010450f11540800d0070f4641c8100001e030640c1c041d0521460151003500704105610b400340c9002911800407002c42e041c10300840c2c041d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 755862895 1250 755861645 755861657
    0xc010206190b0a0b0d0509030906070b10150c0506060d080d152606090609030307110307150b0102010509070b090f1f03020909090705010207060503090f010f0f0f180204050c0705030a 80
    0x4505801a4011b10b0f0f4880801c1d000741d803030044804005001401041d5000e808060f01c5000503407003a603826148005030a2400e03205d008620700c004024804c05404408032442e000e00d43c0841c80c3d0342000c81108440a5000307a14a00f070044403994480109008903600070808500c4200040a102540d815181c0c1100d0a00c44c500842030709900f145414800b070007020042d0311a00810003140030100659403c00818a0240141c842c09086030f80796002c0c0d206c01a00808841c413800301080290343c0000010303d0280c0003444195a544c5626403503c103a4840c0c4401030f0b40c200141c00c05841c01001c1e03080031407401003280403100c2200c1e83c56014050303902d40100c0440c1e030002e040c009914080721402d500410310f50042500c10300707180c0000c1d11010184681d2040c42004004650a02000c0c00707031a2070762010702c0c0204880034000105001520401880c24442c910740a0b4220840c42c0600440400c13100420751459824030300c0e420b0000905d8020040c2440700818400d05000030824002403141c0d14080da590 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 755864145 1250 755862895 755862907
    0x906060306060507111c060e010203010504270b07020115090905060124030504020402090d0b0708010504020a0905090702120f090109120f030810090c05120106020c010206190b0a0b 79
    0x54211a10394102d00705110050042600041c8041e0681c4c070504400c0e202c0c1900d584500c00c000039811038240008103102d091140f00d146030380055000e1030403603104460134402c800e8032110b5000c24100100184000d40901070340400410103059006070410f00034800000c00f480d8020b860501c6140d0b03600407402c41030301e03003a04e4800d115040082a01409070503503202880c9000da0302e00c83c91040c010196806040c0c4500020b0b05654495040c1c1e5030412015084240d0b0103002e15207801326100448007000480c103042e001250342d04151003580d2200e903550b150b5456940c00c041c00c011500c44020981f030118800c07019040062003090b0050420b224500707070102c1d101c02901d80054120b84003030700490040f4110040d03410101c0c00400c2c50300070301c40d00740c1007001050301c4020b1000c00c200555003044041500704420f681c1c1041e4041d0050039181c081c5400c183c03070341e621884200d864887d681d07106d82c0181d01060100d0260a102c80c4c584106401c02440001c0c80484900420b0602d1202c0c2d1048484003804648 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 755865395 1250 755864145 755864147
    0x160801051e01182d0f03030804050c090f10092c10020a080711030703050f0319060f08011b020606060f1306090501020c0409170f07021f1b020109060324090606 70
    0x13640200300e80303030600e80b54003030804c1100b00641a0600c03000d03040101101c0890103024090000028a40c40036001e60b1a40c07a11404841e04400c040d01c0c000c003c0c41d2007060011700c0d01d42c03510a0b00100303000841121030780f2a00d070004802131050001c482d2403c3c0590f01c1c1d098021800d520040c0549031040e2500140c0389030150014003014402189406c0b01d420800c85000065801030440d200940400315094480d2100b00e00c080c50011b0065100d642c4c580f42600c0807480e41142000c840c00c0710440402801001203940c5501c1140e100ca0242c10056402600030540610380030700607040442da0004600d08090140392100301c0c00c9819030000001c1584054244101c0d40c5c140403070441e08105640034806042240e440e40005d14118002300480c100203d17070310200c1040c04084441c1c080c2c00604144603031041007504040090307100e10501c040341c0030121101240c004030428020050b016120b00310301505d84081035008d8244d0004800010301044c000080c1945c1040200011b0603520030005800317410040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 755866645 1250 755865395 755865449
    0xf03180102070b03010e0f0c090a0603020c070515070308190f0501060e0d05060c13080115090509070308040b03061c12200304151e08160801051e0118 66
    0x202803000f401c100014045160000c0c80d050700031040d814092003a80d51035040002034002c00c00038561041c078500c000501c0c641d140c1c0143c035000924000340c81c00c40317070744008010b818600d00141c201c0c4080d0502404001c01e004c0c10f0b4603603105c502c0310540c2040c4403100a19008a8100e26101c03448995680d0050100d140d2041c21030300038540071b943d140a01644c68880740d641d04801480104240c400090444403189507000010060500ca80244040b0804003140d02200c1c14600459200380c6c50a0300242080c0b8000030f0103c1240d400c44800ca24050400140c1005075000a14098218802080007044030001150900f00e580c00340c0d00304a46401ca041006201d4101c50580301482ca0780d60682d0751140001004540c1111202491102c1e10050030505036039050a00724881070743d68000d4944005580c20140062180c1c0704480c40031850744020b4810b0b540d1035001c0c0151340d049000c0c0348800c0409501c4100e07035905200e050414820b980d0042c07240092205058101070703a0280d0001300103821618a00c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 755867895 1250 755866645 755866649
    0xd0501090c0b0304050c10140f04142b02010302041706070e09150d05070317040314011104030f020a0b0301090e01050a090b040b1f06030b09090109021c050f0318010207 74
    0xb01078694180303505e941e540c5a443c2060641729400008108400703c1c041e0b03c07142c42c90b050f103940381034503141e8000a03004150064411009454550201c1c51050f1a000c0c9400d4400700c40b440d0340403038540480500c0360619486e290100d05140d82000081500483d0495031078042130300100600c440c0c07030120801495140303c1e040c000d00960701241809120141c2d910101a14541691207041380340140c101186000c61503400501080030410b211806414201c0003082902d014a6001e040b40c50031040c241e08840d034043e461001c1100500051000808000540000f513000800c003e003805c2e11000741109a42c000e9004c5400380fa50b407440c3d100304039020b0080507803040d00e0b400e0030000c000468643c00080c1c00c0090004019107072000024440000d561402180d0f2000304984240b1581c8ae1a40030b8020043e02d00b446c2d200d1040308000078400ca0050168078050307130b0302910001d6981c0040d0140741644401840846983c02075007a0456820802c0010381070300025135000d0258400700b0400642010415 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 755869145 1250 755867895 755867909
    0x50303071b080109060e0c0a0302100e010311040e040c0f1409070c02030d26100311030f1f0501090524060405180604150e0c0d0b030604030906030b04091509080403020d0501090c 78
    0x2340c1c80400140e40c0398410300c00c0754011418503054080706940100d004015982c0b030303400112004580030403107845000e1424480c1d0301c00c2c03407580c003095151810014022868403c0c0c14143d40080e001c5221418810186a0002d0741070528003602240da90001e8108080c00000200042c5000400d03040b90b40149c07503203141c06e09045c2d0300c10414140402840708000e10b9002c0503114501c60b500d2000c85460401c60f9000221919064500e04400101c0403123542907910b0114aa140c113100001c0b52014847c400c040c0115216010000e50038808a1408150081c11020941c41001408001080e03110b44003010114205980340b0341c00e0789005400c110845084407224088880148010b1200160454155400190034451681c6400c14129841e010741141001c0d640c050060b14144007c05400c90192019210b0715103051086690110030301048a500c0c03400606032404a03210305103580410b90056a00c00d0084551501c7c003902c0f90041540040c03111011180e683d03440d86003d060010700800c2c0701c082e00074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 755870395 1250 755869145 755869159
    0x4110910080609162313061e050c0615120706020f0106090204061d03011805010c03050601180e1906030c140117010e19050a0603031404050303071b080109060e0c 71
    0x201c214005c15684840320211109010f40f5411900340d040d86069440c61814242d24201a43d01c50304000d1660710790003250545502d405104000c8140140182c44609a142c001072401d40d548020210100c036000003400e40010800d41030000104003448a80c02074040c6070001c0030358181e4102c00a00316600d03503011400c003a1040c0828041e01c6c2d8421111241d00517540819401c5803c0500024010300d54005d2100701454003010310003c010042d0410100c020442d202000117030380c1c14005660012808802401e1051040c40a11412014024080d0400c690040c0071140c11800300c4c20300c0071a24650070656080111f01010080101c02c042080c416880c07c0c6840310007002d483c002d00050f0031040c01244421150300c00000c0300b80100c2c00c40d4407000005d4000511140c100000c40b00f0040021b4001580011150710030046050a4002103800721000034001310b1804580c0d854091180109511810891b01400000158000b0034014804e141d4010741c0c1c0040c4094004000380d01d0056142d074024000d0307078 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 755871645 1250 755870395 755870431
    0x9010f140c0c011206140d060e070312031815020703090302100503041203020a050a0e030f2a030601080d0c0f0c0602030a0e0906030a03050a0e06120402040c020a0c030204110910080609 81
    0x44d1843e54400d50381019114071801101c14230700080178129080c0200c1030b83c420800d00006120304101c20009046058500b0000c000280444820980c28454090948900d25a40d400c0308901c90303005041c4c40e4020300c3c00310b19003502c9a00280d46d02c2000c40c0041d00140000c0140424030180d044419914011414218685608040b01400c4e07400354507080020f2284900740c540280d1410300c0708400c100c0701a0159a048039000d112030b4500c1107840c500c651200c000c1501d0003858180064860f0680314020018481c9611982c400c407110802740b80102c2d0403d0840c50007600040e01c01c1380c0e25000d01703255006141c03507180c1c0480090040d142c2078070441c0700c0c4d0a0141488110f443c0030030007041c2a6014600b0300c2e030303441c4090010f580c2e0708020304440c0d07080305000494044850348001c503140280d208460a020050704d5050890f9200c10384c1c10040d00e0300c42421400c0005160582c402e840c0d5a12404116007004522400695504480e50041002c42c0c0003200b002594074205412a070f00030100d142e080c1343e0311 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 755872895 1250 755871645 755871659
    0x3080d11040317162f12060f04110d03052212030f051b0309130b061801120507050304060507080c0409020306060f0408030a140f09010f140c0c011206 66
    0x10243c1d000300e01c410009840c245084914086085250b0040c1c4481d1000c11140c2c940c5089010034140088200101002c2071454680340e00d09070303640a440300c000c00507511549803100c13a685c006081140d02d5103d071440300541d522440341c6c851449009407102d540366805015580b405c01c00d11001035403450146103051018060498492050301d8048c0740c0754407482a111000d03181d07403142e4111010000b10071120505d549038000b0090961041c151140e4140031710500c00e00382940d10000180740d00800031b0152081401d1403900003044210145410840240036074041000c071001518031400180001080205000c170501070f0b15044060752422442d5494100b90071072080c042c41c010001c82e690000003144442e80c5007405d070b802c1c501d140724003940c2d501c0e5a0880d850f40d0f80d100f51113030408a21001c0d55505003500401c1a500d031864001841441c10411800445411882c0740e030344c8050262104c070260507280304001510301c0e0700103040246500088540054400700380b04060501c11418030200340101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 755874145 1250 755872895 755872913
    0xf0308060418110307050a0b09040f05060303400503010510150f17010b0c25060503042a260a02101b060501060806010e01080c0904140103080d110403 66
    0x4036802401c00d04010141d00002170030064554845ca520240210010412000810041140040480f4100913441a0302483d105442e42229a1580b40d0400d11041c0000c043c03480c3e1800101d05003c10440451082c0f0801d404400c01e800700d600102200c0000c18070803410300b44581070300b2407403c3c2425810a0b141c031400410001c0030400301c4040042c0e15410007505400741824800d840141c0c0182c000b50740c0c46201c4907000740c00c08032080d1913501c10007026618008460780c86008185041c1c85100c40b06007001015034159101420031103025000b0442e10041541108960f890720860004d110035152405004860841d00c12600c45407504044440010301c14000403c00031a070303816240780c03002d01d100007805e481b9070f820703c5000c4511081c01c4510600700711035503102506844142d21114a43d0300c410004480104906205c107010030095008070b400c1c6583c0c000a0004c0200003403000ca41c2d480c0b00052520f03200d01c2a0f004540041010131081455581c1d800b0b00742e0300e0b0241c10044c509007407540e103413071241c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 755875395 1250 755874145 755874191
    0x1206061e090e070806130201080105090103120302070809040216060f0c0905040b030f0f0105010e1305030d1a1c021c050a0f02032d0609060106050f03130f0f03080604 73
    0x901c0c0d6620140345070b00700501c1240000c10000f401c0c2d445910304070b0311280d100b0103c40c40c00c0b40000c060100201701850803a0480741a25001020f00140b90a00c1409030029402158103690305041400502c19680d2180000c0c0700091a02286c405070303900a29020081e9401010300410080c10081c40d80d20540d071041c0240e007111011a000b142c0c00c1c9400021900b441d0100182c51013500415000c0c004c50503054000034100c80b980800b1000994400e1752192040c3c00c3d0910052080c0c2040108441c00112a006074088003804500c0302014000500040c444000780c02c010001e0208046511382985030581208030621044008402e04c030080e55142034503116540d5009103015404c1c1c0c5200d09544040005010352000411001c1003010076048030713554900c1c0e0a803180d17035a1080c1d1001500207540882c1c214121501c42c0c903210f0a00400391883c1c407643d0001040701c0c0c0b1800380312040d540421600c490040b80c80e07014500d22850b8040f14107000b81036910040650340618140452501d6400105204d00c407 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 755876645 1250 755875395 755875409
    0x8091e120d120f06120803190b1f02071509060801050a0b041502070504020414031e0d14090d06200a05070f02040e0105010e061215010e19061206061e 66
    0x150000b0701c0f8000c1c1c40141a5038002404103410000e07201e0800502030300545c01f5856150303c0c1e62943c00000f0480e42500c0320084100d07040f0009074084050440c00030202c000004290040c2e45501d070300e07800100001040071040100144030480700300301294000d5074040c007410007030300d0044005091000c41500761045d8860001c0642d0100203a451303d620030b004000190900400940d52555115003182c40c0f0b60301c0c0200d242c4640550030001c0d15000e0b205082544540c2d0001c00b80544007600201510945540012000c40c881d0400c14031030310b9a140000da9040903ca000001810a10003102c01c42210801041800c0118200710740303800283c000701500ca0700c42d400701050505031144d1003c10041e103541c8075500d0456081c50300100d2000103081ea01849040140c0e551280b940d401f48a503a50f81d007846107109040201080144190441c1030600e661000200e00011050b540506600040714060380c044105801c005e2000303c200109806007100504000408107001c2e280300e0f0f035001608401303100d181 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 755877895 1250 755876645 755876651
    0x9031b0606150c071203030903120b2805180403021507020a06051513060317092d060c071805012106060b070c0905060301020a02031608091e120d12 65
    0x61003034030130031480001d0100400b040c2c01a41407460007502510700914114040380d2800c03a4405098814400d8443d150001807184105079840c0d01d00c9440c481d0403101c8406c01c20740c4580c004c14151100b01c4041140081155840c800b803030315080017400c00d14084114212502402d043c421400d0340054404200d80d0000e500080700e03210000384a14548248414540000d0481d03042086500140d11000c1100c2c00303030000800c00f6003a00d83c900d031a481031010240c2e10030000303811049007058090b6240070070076050303c01c604a403501c0d00000702242c00c90b04450106510080d0213105030a028001c0050385120008244015414079170611002c0c0c3b1a202d1000444403010000800d202d12070301302e40000c152058906603070302c0040c2841c42810540b40100144c0b542080c1c0468101c1c10144212440c5414560155091a41084000c011001811010303601014184580c0100b59136080d1518203244054500940307c03e1610240102c43c0604801003117184c03c0320310b0750300c0506d401001c0d001111082072000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 755879145 1250 755877895 755877907
    0x40803120a090f03020f0c03011b1409150304060e150703051b19090803121b0403060204090e160311330c0712080f0903100509031b060615 61
    0x104051000540782240d40801c3d41c0c24182c0100e01402005500c2c01502c440e00200c0c400d00d801e07206105e06004060b01c90007080807102d481040c07100c0e542ca5104c046c0034a0129032400007401d0a0094009106042e070000a000401042c0d1054500d40c81c400c0c0301500c5803aa00c10300114192170000e203250145a11203001070407100c610346012060242002d01a501c585200307000e000c40c14092030700b1402243c0300000c0803e05050001c141e402864106c1002d13680d81e95801d1940410a010f020204002a8240400700015001e0b0014001902c800f0000051603014a00f42c0b034078102407030041c0d4803448a00a014004100d03103040c009240c40d003d5a007041c01020000380c0886880c94046500361808003a5203000c8100103403402004401a40021504070302d85807001c10001c0000711800030300240d4104003411aaa4000300076081000c001800d88940c1602c030324410040c1c95044600e0344079604009410201e6486ca0362000600704800720051481d071600d10041000620582c0960306c86003008541 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 755880395 1250 755879145 755879161
    0x1806060c14100509030901020f03130303050919030503090f041401050918060405060f2503090807200418081e160308070221070f0507081e1204080312 66
    0x50b1018110300b010204000d103001407000e83c0340e030404002640140250f031120102071200006486540c0040c42010200354079640d0150383c540e220b40041c542090705138480380310914004c981600194025006556200559820020110030b400d40b1144100d19102c400d84000c1408070030281550b40664614507142c0707425000e0003c002c140d4034a0341061140f0310400c010450040303880b0b03000745081c051000240c1c40c0c0c0b1120000d0804260b0b0b807440c001c803640d0001c0140a11035001921058090340a25152461a40f62a0064800300005032000d111041000055040a00c504222850612100d01e00448256104001446403030700101d2900c40c0c40c0c1450000d110004112061184100143c680c911002d14014104010448046015008169009802c0f54100da81005241c44c155040b500d081c60542d40c1b07090490038000250390321301c00c00001003001d990412800d004030541203510b0382c1d6120752051080c41c0c12000301003400c8001c000c1c8002c10840400005842907400b042c20380500310394132095 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 755881645 1250 755880395 755880403
    0x71b0f0201020316050f010e060603030d0b0f0604030b06030f010b0f0409060f150603050601051306050309070902040f05030106080703260f0703031e0606140f0c01060605041806060c14 81
    0x1c0400ba42c000341c03500f00d40400c2000907202501b440000000d01c1840c11518809445036402c40d4102d0309a0410003030300f07018880301d030302002c203110000301004000d0003410003140c2281c025800031075103c5c46100034081d05280400a003d084012040203000b89800d81c000300312489a01000640281c2c0c48000980c01c000b15500101c4020020507020800941070003882c00703404d6504e104d411701080c0380c84045800c035403050303084070005540024010101450b14408035465880189940c400d80a52080801e04005500041c0300414114030f0060707000e81044201400c5406941c0b200c0507640c80308004100050710749050702c0b110a04100203240403404040c00000c10322030f40d114008980b10001c1c00804240e0140d11135200d225450703a9010014000c2c4200302e00b240c010703004144c0464152800b4542031100c000080c551400944201030400954070041400d40d141500314101186010a091041d101c2000140c8000000f00606000c11803801780e02609020000d01c2c007400b1080d03070044a00200034100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 755882895 1250 755881645 755881657
    0x110c04020a030203100902040f03020d06090c030507050f0d0b0105040e0312011e080c010c0204020306040f090803011e06050906070314220902090315100b0d050708071b0f02010203 79
    0x25105550300c4010300402402588100c2c0c1021543c4695500850000902d1080c0d4040d1030140c009061410704640801c00514131202045800c40e8840e032801c0c1c00110442c01100083d44034000501700b447c200b004001903608151600c9005605403811000801c1c1020966411904203030b50001d104d400d00618182141f040c2a00001200003e03c00083c1120100401c814240800041c401c000d80c1c59122450700c40303562442c0140040e0204141c5405803403d5401540c200700018000508401c501d020082680d0090f03800380c070301a0340407004116450342d0760030414514208603009070049042c03c102601d603000d2181c00e20b0003810045031060415015000c2b9031100e8501880040e2207040c881c811100c4100d80d50b00c0d925604180f4a000144001140266019400028054901204000e5825180c064001d1400c08500340508000513a201440c0003000d8250341803402140510303140c800a00712440c0902100100041c050f0000b101c9a4001c84443e13034a54002200450b1150300d00040303155004c3c007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 755884145 1250 755882895 755882899
    0x1143304030b01062615060405130209090703061a07050a150c02010f15180204030b16110c13020304050f03030c07020a05040203100b07060216060c032a110c 69
    0x90084140b0030103550442c101c0d8069030720110b5803013410010751803008014401c646a640e01c0f00124a007103100c1c04018403020f2015203a00c0c1025a1a030000310f464118044900309254001449200c1d801e0022841e0341c020401e042c18401c0924001891604007694198503505000c080380e80d2003046001d2000c2da200c1c80d0445400000d80e14080514001084894045c0000d5840d100c01700703482040300d001d60441014203000445025207410440d07540680303e48151600b0560800000c0000323540342c803000d4001c030b443c0030b6071441c022a01c07200034000804003a00040246e02c0b800d800e0460307070783d9000c0400001c07404110240c1c80c0d44a07840c001b03140c68140400c490140c08003204200e210748024024001c40380c003c0f91404d04055880381031000301c1c4030645014001a0032090188405c0c51550001d12249115000051800140381c03510003440310403940480d00a500d071002281300940c0750250b8070201d40b01130301c0d60703000788001c07030703104c1c000301400403440f030900c09c0014a81d41c0446003805080d03098000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 755885395 1250 755884145 755884147
    0xf011d210a0c06020c15180f0616030f0507090303080c120a0c02031216260c1e0a172503050601020c1906110d021005060f040f06030209011433 63
    0x851524014a401c01c9445001e040e600c0c411f005801c0600051040c103007810130025160070303240c0c50003251f000e04200c8a090203158441107000f2402d0b40d00c1c4900c51050480760f6407111013a003903140050001c200941070198030340060210350100ca1454041c2034110740c1e140400115602501e0b026429401220a441c005400080400c41c82c492030b003418068082e1903a941603064580003150500c40702000040c0999100084001989010030100401c1243c40c519000c4c0800b804601110714290710104004001421202484a20300d040c0040580c11804a1040100103043c880e59400100901010401055200c20115074035034024403444100c004007500c0c0000c0f2007040e026040d241d11052140b5000513400030000d55040401042007801d000c0182c1c00303000354081d00d00400010f0140603141c1ea5000c12100030b40c5074144e88a1080d1882a20799181c0800c4031b92440c01000601d80050f408079040002000503001d0707581d210081d10400d4414009204804410701d044018030050900c105120000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 755886645 1250 755885395 755885413
    0x403111501082503022701060f090f032406050a03050609070806011505030c09060408242a070f1a0903040e0403050901020f011d210a0c06020c 63
    0x40c900c4035560603a0001e1040b82c0710400e542c02070501010007003004105912400d031041c001031500c000348850340c21500d41068003150081c0075504030100c081e8404000300e50f0340b0341c44200700d40c2c009601000030111844110129442e60b150043c2c101c080c1c09100c00c2501e2031a02d034401100305a03000b4400742502404020155440e803074003d98a4905650031000b43c8541c1c440082c0d00500068403038141c813140c0160b01c813500c505c12b0341170716540c002070000103000030180b001c0d01c01e6071503e0700500014090103009061a0216461b650b02c0c04c0c0604454403544144041003120f900840c0c0c3c80081749208080d41070000125248522170b06000d983c41c0100850300121281c41441800110399140450740603401120341c4031000016a42e2180d48070b0000c0c0310381c0310310009000c28000c802a181910f01070058403440c4501e410510b084400e1404402c440d402402000404640208040301105224101c00071540e02201d03620f002e43d0080d410010100014003160504208180d015164a00f68000c00c64500007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 755887895 1250 755886645 755886673
    0x7030b0d0c06032426012319060f140f0d03171e0406050a15060801080f03160209060315090c011707080a11120114090705180405040311 60
    0x3003121011800203c5a05014100d41c868004c40e000465280303004182c4894003118100404500d018040a01c55580366480d100b11143e00c4014558000116011201840d11f000e0103004c180031717010303400310f06840e1107000d10600c08a08008010f135100031205080d41c0310074400003020500e68181040d000804240000105604100801c030081c138000009040c07030392078284210b42d2080d240e008492842c4568081000318002c0e51003942c01c446400008505605030312241c3c040c0e04000da10400c0011141b0004100c0740b001809800c95454840015510b40800e07004e071885141803200c0c02901c14942c09020640c0b96804001c0d129800c01004025441480d0102e80191a407020211843c042a01d03056400410b00c0340c1a480c2d4452000b03070700c1708190380e107843c10184024400e860300b0345601a070410210491000c1540b00a000b880c0110105504180c80d100703000c03c44601401440c140f140501083c140c40795620880c0419140551340043c1caaa51410704882d605007482e60900d0500070329011038118 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 755889145 1250 755887895 755887901
    0xc100e0f0601290c07080d08040804050d020a0b030f060a090e0703120504080f07080c01030539070c0f14010512060a09020f210c1602181e091507030b0d0c0603 70
    0x260f503446c1c260340d802c500b641c50941d00c07850304540040580c0003c00040c0060b16280c102518954000340040e405640c6034030100019038405e4800c03404408e8913038208070640c5400c200c000080c2104000500002000000c0e4568481ea58080240242c400030880702002c0e21401c190382c020504002103414032100c5080054549009000e061114002c2e0a809046940a4001c55010304103403180e0102000141c03103400d0a00c08140742c5000640b03404150459a405001c003d40903443c081c4518121051401c00302d11500c11040c0e0024010102446010501c2c2c4e8006e402e03691403202c1032000110b5582c401c4d000414055098128007007052006ca0480c43d41c00005000c0e00460000481407c01c5c840d28015071084a58111200d000701c0100304090015030840910300107041d4030140c5500e50085800010000f2000c04492400440d2510b02005003154460510380b40c00c9440d4a011b07006040c00c41c149031f0500d901c02003800062540318440c03d4455101d0314a400070541d040b222048080c0e84801e8011b010f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 755890395 1250 755889145 755889149
    0xb0d0204050c0c06070801060507060f060e0106050903060a0c0c020d060e06040819080606220e0103062c1011120108071401091508061201020c100e0f0601290c07 71
    0x11445480d0015044c503011b0252241616400e0f22881e041400c169215005008591808c0a2480c1c80e8a40000e40e06103081e1850301030300044d00c40c262201c2404040c10f19065000b450300303051600f0480901001070300442c0309840307180c06440e03030034101c02c003401d00c000909012601070a041c0b050404102c2805500d8001e493340718541e0341c100007a8502e544086440205c207036a04c0340e00020410000d900b40006000f0025280000303024410540d680d00c3d50454005400d900a9840a84400016000004100000818100c60b04120307400b0500b20a8856847c001140310f8a02e03541d0342d82109440360030300029552110180020780d00d240da12960384a0303c4000324480c0c800c02d018070186000c2558014402e4809481a4000f070410010f0000c904903119540500b1554104460100b4000007420a000928010154000030300000016007241c2c8100c8010b55080003c036003100301609000800424244e044540c007a00501c14205081c0e240200c03003445040b0841040800145540000804a01442 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 755891645 1250 755890395 755890417
    0xc2109040605010c031709010b040515010801050a0f050d0305040504090609030f02070e041b3204020412140313270204080601090c0c080304050102090906150703030b0d0204050c 78
    0x40741e44500544603101c0100c802404907824101c00a003607410501c0311503100401f80c001089000c10703c4086812180c040e180080c0d141008040c140403941c0103003150740101010348400b500c03613240c56028900702085c0e00070700b0300c43c000c1d146000c01070612030350581d00501130040080004120328940080140b01e0141c0444c08580c01c5c0d890510403a0000c500003040380c4241c800c1c101d856845070303540b52003c0f46e07083d88811140081e00011a00300781b55400382c001c2e0100701c40d690720f83d044281540039000550300b0509100b180100300900c0405200040d06408541c461034070500e00b070440c00e0480c158040c240090001c0031021400140d50320000000801282c2040090710a03660309041d0002640704030f010f0303007005602c0f0400421100d625035000e65512040c0c0e00d000c642c0384030640c3d80c0300e441e68400d5400b030764542c1d004551005a844c00c3e0300c125400c810101d620703041d42c100b00400081d1501810743c001e0141a07407115080120340351510401c9006500410400c01494803440200383c0342c1185400c0300d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 755892895 1250 755891645 755891651
    0x180b010602030a021207061104080d0305060901050a1701110f0a080117030a0f020f060a0c18081b0a08060a060305060c0c0703110414010b0d0c080411060c210904 71
    0xa40600110455030111804c0e80900052505484548016400041e040b1003850781c440303402d0004200d00307014101624694014044140703103000024103460000d17110a10a407c414010000746c2d0f54402440120707040a004003007113003116000e160041103180c80c040100703040010152885070110000300740802860300c1e0141280d0f00d40c0d80003110402295881100c0d0380c0100071585440d8090020000500e06a10440c0c2c543d41800301c0c00c42c1441c01c1610a007641c1905d031100d0303c4007941c2000041c0c1a034021a83c450520901d40040320f81d6409404c0c054020280f202c00030b014280d04d882c4c08200190814104440d580c1c20501c446800500d410700c000e0310140160340100f400c07061110100ca102c50368050041c6030080c25178480c03081d0a1025410103610694808002445d00900c1100314020850071041580310172020a5010645509201400c00c01001c0c108100000303881a0a403a0703c00800e40c0c030103172620029407003c0d240542d24460304080e8408000187c0078059800e004042404040c2c07014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 755894145 1250 755892895 755892899
    0x9051606090b0313020a090e0610050d0c0b0d0b04020c060a0c050705030405090a0f0903020d09080a0b0f2a031906140d03020c1c0b15030a03030b01050d180b01 70
    0x441e803150041c000d000c0311030030410101e00c642c040c043c03995004070700040012000903030344d0b0014003c4841c207610903005a08150200b060b0500000c07050002080e0940e07034079800a2407542c07642100c0c200340c080d0100942c000b042d80506402035a004813001341001d00704664a00c554928a50382e1042119482c00c95410b08174003500c000e208000362003802c2c0d481001541000e040004000700e04d0030003000d401d20288e58041c000b038170350028094081c0e568000d401801800d40005002051400950024000c1e40d008024201c00540400b180b55031024801c1030034032003600e030010b206000a2210101c000c110851002d142c03111035a06000310b002d0b003034281c0045100610459050180c80b010b10580301150060403408400703050540410f00340c28400d105840b482d041010024001b01c030300e03001741c08000640c1101c8108102502c00925041341465450406486668000070b59440340948006e04050b01c81c40300d011145d0060041e501313044110101405024158000071b9401c5619003410b480303010f5a02c1c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 755895395 1250 755894145 755894147
    0x1008040c08070320130f0203040c05100f0c0f140d020115180506120d02100f021603110a05060708090c0d0809010315050402040603050601020f0106270f09051606 71
    0x101030300301c82e4480040e50b0502d4000a400d254003c21413080d941000302c580300046070760040d01ca001e0b14115004001038580c1024245080c0860440d040280101b041d041084410b0760415885001c2004525190ba10380c125840c0c1000740002c50040103001094805daa941c100c0c2011415038015400e65008010110350000c5640045105101e01f00c0a0542001c100d004000660405a40208082d0030080075480011500e4602072034444518010782140e8030200c000340c7e10303014100822010303140c15418400d160160001034201c1140c02402c0c03104480340400c61800502005014a0f004400e903215441c1201c0082d040704821610700f883c500640580c85024682035052000340da41001c501da0500114a005400134111491946040f190241000416580f14001000503060b20398000c1060f090100c006441c1c403d11240c40701c240d905065040c8050311080c1d40c1c034000c91012140308070f2002000806e040c01401c05032031f684846030034546c422050000000c0c180249603400c0005207000c1d40c2d1650 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 755896645 1250 755895395 755895403
    0x120206070906080c0a0c0f06051006030207080f1b0d080403080604020307230d0207080703170c12040c050d0c05090a0b0102061503010b06210106030e0c1e1008040c08 73
    0x2d960100308a0000705016070400310191203242c1440c201883c81d20f4403034036030700403841840d0400c172103a80e10782040005000c0c142100d1001084141025820b100560382e90680d28040d45860000f11140842c1000120407486c0203102d0322441c04080d6000350025000007450701d5400c40381500458141030208210b403d0034800c0383c0c4210082e9071142038404240e014092245494480f40d91417810510851010350114070051030458840c50480e0341d160b880e40307009040c5102e010780b814a955001c108008000c4030100032110b5100c407000b07031009656107a1070174102017845604000c1d00482a60006030801c600f0501c0c5400ba6038088420642581d2030108103011b81d404110b640340140c00c0040807545242001845100c01c40000340045000d03005100131482d180c00c1600410b07500c000a24070744841d0505c5041440c00360103940703420301201c0c43c03a41031280c4da0034090304401e0092400c41040000340d02c83d40c000340b214580080034000c91400410000308502d10a48080c0c0300020420310000300800005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 755897895 1250 755896645 755896649
    0x7080301090212010605090d1112030c072903070c080d052a031605070204060e1018050f040305031504110d050f010602120706021312030e012a0f0f1202060709 70
    0x2096001000803540d42c911010b27580480d01508403ca060400c14140c000b03002800e0140e94110042c050b01e4600a1405000c5400380380442542c003641c6030707442c00403800d0000c8039408112800c00f40070641c0c0d503190140a40c0b2070000f01c140c0040c502024014405d801054108101c1c411015000081c030074400e86020030300c0305581520404181c22001303c0d134030b40140050452940020070000340141d64070425510200d01f01c07008406101c00e070070705014a0359011285c84001c17000c038004100c01d1801d4454400424400742c0090305101001c00003405261011a1803814603402410074009003201c0d00b50009660024180b501805050400052040a02042e0141200c0042d402084580360a0300c0070b5034207511044061303030b2040e004c00c8050b100b052211804001031204114214100e195414002c00e03503101c400c1d29504018082d000d07410040d440380c5c88082070078001c00340581c2051603468000783c04031008400800520341440c254080c0500185041403160f84c13a002d0b10301a6840d40f0003101c100c1654 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 755899145 1250 755897895 755897899
    0x6180b0d0b0120030a110f0d090806010e04120e190b0333010804140706050a080a0b0d080901020309031e07150c03051317010614040606090b0c01020708030109021201060509 76
    0x28040c3c1701800d481181403660714a86181030b02c1090711040102c0c0d080c03c5c40804050701040c6040380401c2503d03004c10041c0d004002000d0700301954117103543c4070700c0210004021281003002e0b03241c80f840540e40f0032401c4401d186c402100c124401e941c1d00050841904200c55014604000d244096810140040f071600882040c04000f00d00c21040300042d16240c1011b070013031324088032002e406440300204000701e101410740d07a11919201c0300446401483d009000300005040d80c142035603590507882e6940080307400b5902219143d00c3e00d001200417442c600951a450781e040c42408403035000144401c80c07a801204000061b10b40264070b5047d1103003000980d1001c0c07000100260780d040f001c203100f0405840e1088201543c80019640d81e180110000a0501f890210b80d40d10281042088840c40c014942c04400381d505000700c81c6400c1300036052304040e02c80c004540740001a614803195082d811030b25429800101541c80303503150180f034002908420000701c050760500700040b0b40280240148c0d01c3d0f042c40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 755900395 1250 755899145 755899147
    0x5150f131406070b0a2a0c41010e12130801090b01120809130e0d02010b010215040503090d0507031209140409020f040c05070204200406180b0d0b012003 67
    0x80344c1400703008252070706800c0c1646c24580c0c00101c5215540e022036a1300d000d56a03c0303901c0e0041c9414903041c80007024140c440021000c035030825428290030300e02c81c0c10503520301030721301c44802c01d04215014003a444198215405202d4a404450180001910301c5030300f01814000210b4441507418200e800018014100d800418010048100040c51035050584500c01c5e46042c42442e1000c01c005040100303030f10034895104e401980460004004858a00700e151000340a03409000c0e0010751204a0000300030b440c10035440c00101802010411280d03009030191400c08a0326403400e209031605400d0000300c8032902070203407030100540b085c0010700586483d41c40600c1008400007c0100928503041c040307808c48804510400d050307869210b604074668898454130356442c41c52040004448807081071040e120b8002d2042c0041404150a86041e01e100c1e003014041781101843c9100e43c0145640710640000c400036100b4200301441c2c002400081085c1c8608079980c680554440c0517001002d03c510060344 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 755901645 1250 755900395 755900401
    0x2309011a0301060e061e040207080304110a050604170102040f03030804150b060a03020a210b030d0305040f06020a0c0f05030a090b030417090f06191e080105150f131406070b 76
    0xb034006006c003149100031103664180b01c3c031140403c0503600701510a5900003c044100410700001c0e16400d070403010125140c01c440303400c140006d503207400f82e401048000306541d031030340f0103120b003d604440141100c8082444400d030340317140040126008550485400c003103101102000d901a008001500c000242844c0c01d0015841d41200250070140c1440300704042c50780c0c000418840e16005695820301d03810081504081740080c103240c80c003d0030407081054a808104004100c60b020388043c01c0360b00010141c2d60702e0b000c000c112410501e01c80b010308014001901407040010001c018002d01c04251101c0b0038032030351006111540d00080b02e001d03150340a00013519020342c982c480100700d81c07031004240e01148007514002c250307035070030003806904248116000c1c035070542e4112903000806080040114104440198000c01000b4103120b00d600481007220a07030027820030102502c030074480d141c10717080d1605480d401107902d00d545482000103440c4030301d0710100c0c5402d0680c1203542d0140c1060300544241c07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 755902895 1250 755901645 755901649
    0x1090e0129030901060f080f0304030b0c0f0a030902040b0901030f0b090106091e0e0c0d0b130212100506031c1404090606090e01050103050115032309011a0301060e06 73
    0x60520307148072200107409403001d80d114410000346004806400c00058043e00304079030240712102c542c0080c403099010ba9000f080e026000412201503c0e8418222901510351a044c0040d134040c0000a180741c20001c10305c151019403550001142d54002c56042c809a200c06080c007000c008203010203071071650104040f13004a001c1d80700c15900054480000685d041c0d0f500d800d002241c0100044805003101c9524210440031540a07162a105194000e0001c8131010000140c0142d0030420041031604003000258860010861a0504a4004d0844901629643c00d007586544203420f000d0001e600e00400f2405500300040e000141207000000000845140001569500401101924034001c00c0001080d4004980a8a002000c0030707101c4001c81030808081c603036030300c0058001904161500d0010000d10695602e0019140b105040000d2200348018000c003881007021000c207811003859003030001d5090150300400c2d62540d80802680b8000c0c907401007601f66000351140003e2548000d010500f00c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 755904145 1250 755902895 755902919
    0x4030b15042a0905090c0d0f0b011e09050414090d020c06090409060e0319120209010f0c02190e150102190209071106040303150b0733050903071101090e01 68
    0x2042ea4200580d05541c0c80c0300041480d01c0c2216542c1c0d10074401718510748200e070503000b01044005055014000c0100300c00008048000041d01444040e090ba001129154010464000640310251040c4940c40744004280d00e880405c0d1580b5896100d02c031a00c0111502c0410065180d54006110780c1c0741c103010004000c080c0034042c8040c1c5409541f020b01d040101c03410402017854a160821844100035070141c040c013003203181401001c86a00402455106a0780000e1800040c642c40c1440d052400c03650005c2000d845403581c8410b4001012030300411040b00c4000303910f20a1068903180b003801c140c44001242c03038a551528180b04140001c91f00c6006203052944551720044510300400607103035000702c052034020251001e03004260b40e00140880c1145400462003e40341076180e05103041c482d07596040e18601c0724126400d542070808000310b012403516812802c1404c90907418842c2d411b24100c03980d141d80c850300081711421602500d0700440d5000302e600c0011603401000a40d00e581c60118400e6076 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 755905395 1250 755904145 755904221
    0x30f06010e06030708070e07020c030d020c06030a1d0a0213060303140c0307083006010c060e10020d0e010c0903050d0813021305070807020601151805030304030b1504 73
    0x305004130030000c00d100300108030410083c100e05030102c1c1d29040c0340e007019007021000c409050090b009210100324450f00050902409001595000d0b039903524007820000400340300ea401420100354000c2e4080c0040d0006086505034001c640d0400f0803084201031070100c824500c4014085442100c02c001e011602e940540708018022003580d150200c5503072003980650000e158102c220004c10303600300d10710052910440e0b0391452541070f14400e05050001030100161110001c01940d114100300124460a202d440310000c4503043c255110405003090740c02074a1540c0e01c4041c0c40d13180180883d00b5501c180e001c00c08490b0020007412345001c41031801c0300c0880c2c4c000c3c810120401d0745101c07500142c0303440d140c020896000329000203c0b4109003100074000710340a0299004c5500410051040c00002651280b859a032402c3c0207d142c8100c5250600030445580325a42c140004203000060041404130030303100e100400240d08440c2c2c5203504200440d07041c0c08001010300f6120300c08100243c408440d80300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 755906645 1250 755905395 755905399
    0x1e091406130e25080609040b090c09090a14190212070e040f030f031b0c0c17030301050a0602030c1f0b040e0106090f0b1008040201120e1605030f06010e06 68
    0x401c58586507207100040c0255102c46000800c04a4a5030345080ca20201c0030f5074a807894003400500f0260001008010081e1014012a0245d00407075102c1c80100511115480090848070940c42c00c0403c0b03603283d070304c00b038025903039070405512100080384041401d01c1c264400c01c8103c00344036025001d0000e401500418082d07948900580800d41601ca09070140c81644201c580e070011080c0303131600034000c10548c2004818181000c4402c004172101c6817409658000a1800007400d1015080447e07500f001035000f2140928400e10080304c13100088011416148155041c08425988d900304903600d00c82c4031081c0200307411682503440b00d0041d0120450500800c0000402c100302441d000804845102c048081c0c03517036440004120586031070050003106031744d00d642001000f1402002c566000c0c042c0c2c242104100c06140007908580c05000540600001c08400300903e050b0446041c0c0d80310180d1400c007629080030440040c2c517103000034104c0c0340389480501a0190364a411450000500040d00c0c290f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 755907895 1250 755906645 755906677
    0x115120905031222150c08060a0b09150d0209031c020721051903030623060703031410210302100923150a05010f03111f1e091406 57
    0x1501c0c0071888501d40801501445c034032510301c18583c009904a85403d0300d100b080c440c1e86c500f002410b554080440040f00c0040a0081c1c0d2040300c240081e145800c00c4181450142c03001c9a94081100f15a0207082500816001c0f2007030120461900c8458418011503400181d20454040c4610a0380000c0030200c00078032100d10388148410368a09003000b43c1d4041440000601d003855405240c0e00d405142c00a10300c00a4280d8480113410b8825119415894154061000000d680041600c070354004d4900000e600c002030780d182030103c5051b0300c401440c0f05038108441010100e0030a00f0114250354180e6605030000c168192104000801601060006803808140b1400320074140905203007903012401c3c0c41002d082c0d00e41003107011116080c8050701c03400c4518034141c01449040500308044d0300707494200380c50315100c454450008981d17074140e02540507103024500310241440e40042c04502d070036000c420900314208915030308032000c1c1110700c2980f000c1c59400c50f0030405420004010310714034290303106107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 755909145 1250 755907895 755907931
    0xc03110d09050a0f12060b0319082802030412080d051602240402090411040f021213050a02150f070c0602100c08150a0f06090302210a06021c0501151209050312 70
    0x880300611020b82c0c01d2b500050001110580b5800000c40740302c0c0d50440380c03da106154800c00000b0350343c0c02940100c1801564110600050102d10000e50380d9103801c1e5807060265103000c0042c9101d001d0003d01840c013521070080d01544c420500350004131b103d070301e80340d007071a19660f55001c1182441c0c005d0300c15070301150ba401c8990703030545490280d040030003161407000da5502407030001c5200c5420000c082c03100183c00f1505a000081c3c0209903105202d40480d01e601c0c4003111450101400e21135004910415400050a0b00421103000d942c070040703881c541c083d00c80b683c800c0c00c040f80035102c1b40030640d00080c01000014101440c4410501140e6001400d60108161a050414400211074100b813012030161082042107240c118404130068044a070300ca9800e8060809256880400050080c03401c4e0300070500306044c4c2e04c402c00450068004281c00d03c10b650703648564090840c1c0c0c0042034800035400e90030f28952040c0314013884401e668028019450300202020390380108101a0071900320031005125 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 755910395 1250 755909145 755909173
    0x60d0c0c02031204080705120607030b13020c01140c120103031412180d0507030905061809040f02090604020c03040302060a05090d2a05030a030c03110d09050a0f12060b03 75
    0xa007512590f040c2c90b80c950a142c00a813420000750b100324400c1c04002c680d40e183ca5000710b032060300264a410085101c40c0100c0010310710208001e429850301c0d1001c08e090f012042c05410400c20a9002040060740d07450341c3d00c0c241070b60310401c001d81d80c92800b080010030002e885030914003103001c60000c15a0030200d00c0800d0004100b02039886039002402004203c40c01c002c00e11a01d070382d5503000d0800300d03c2c00700d81d917401504c50100c078400d040c856540452031070b0300010541c010f0300d44440c0007043c440d0f5902d02468840d40d0488400000d03030040c03113081d0020700c1c02e081c10b101f212060b800c0c110045040c9443e43c1d080092552100380303100c04001c3c007031141c0c2000b9110052202400c2c0c0c131a91050a0b51002d44181c410500642c0c540f00d818880080d40c00c103c0c9440100310103178515003500d4107904541d101d090541e1041070b5400840c1e46403154440b030208465101800c002641c1086424500ea182d540d9040b03002c01c01580952040b524540b1003000c0050704580c090f81a000016003900e42c1000c40c080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 755911645 1250 755910395 755910403
    0x30d1101061205070503250e10030209010b0d1a180604020403020307080f0c0405100e130b0c09011830060515240405040207060b03070602011b02010902060d0c0c0203 73
    0x2e0101c82a900c200e005100d146020320901e040844a03140c00700c2c0030070650200c0c0c4008800c51281d050703001c41e02e20104000004461054015540180048209507540c1c480d60710503903c07511660050500c0c1c0601808189070030500e0101d9010000c040780b00d0308401c09401ba0300e84202a1540e948a982000000010b0320240008030040500b000036020a40a504009040041000c03615110f2840c1004024401841a56210030f41d03008440310a280d82d00d03060001c110040118001d0044c1c0c01200400c0344603014480100001002030ba030b00f0f03014080700c0b407a0a15081c0d440c020415422211906101e883c0d401921461861102c0384561440e0110b41d11403804490742078402c1ea050312800510ba00c2141461031055641968105140e10480d0341c41042011034001d5002e403a1180340c0001d404814440d694010560300e1380020103459181da52220b01078000c04445008075a03c1c00d0460502140d04d0040c41404030858020f00f0b071034036242c4804404001880da04240400b4400e0502d40e000258800300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 755912895 1250 755911645 755911679
    0x91c1209050609100506130b2101150504020c060f0709090501060825081803120907060923040b040f021614010b1507060e0a0305031b09030d110106 65
    0x803002d440a4140f84240c40d00348420b08070403001443c1002c0600c519a1144080c41c0a401c0c00c4202c00180c6040000000c3d0b212030402e4054100d0781152070340c0c00c41d07200c810b5000c1d4400202c5507085c1d0356001d84d2030302800b0030b0f4054408444504e41012000501c500480615203501280d1490561081620303007108170100ca00a030040400100354004000c1003501c0c5100f55180856080c0b8445181e0340281e000401404005001c10b41075a5903041001c03c0326810000e440802200110090b22413600303a2906540e01c400e849020300299000c0170020b01ca042d43e0456041c600600058401e02b10305040c10b004c050011241429081695442c0c03034181041544068040d414103035800600c912107a003130000252407002e030307005101c3c0d00d03240708002207075991070b001020004030702c00d6203841d03040c1070030114010121110121020f010b500e5071201050303070041c01940700e80744100140c082d40003a03e00b0100e0030302031240c0c06030b0594011030070300c1001401040c054400c40c0480d03001103902a1070f1035140740040052 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 755914145 1250 755912895 755912903
    0x30d120c020a02060c01060806070c050318040b03240c0301030f1e140109030f0203131a04030206030702060406050f040206030117011e0b030c060a091e05040213140108091c1209 78
    0x203900c1c1842303070341c10030301040d40c0107411490030300301a09450702c90036102c1c03103500e030010700100c80321140210a03103880d003014440d04402800c0d5043c29034564034240c07110041c51041c2420b02c00305c100140d149895072090b80d05898108502070640d80196480503008490309040c480c1649001c88400c0010b65841e8105185820900011591100303914000c0c010070750710b410030030554109000c020721034000101000c2c1280e0301000f0b12400001030351001c0d21644116000030390806800804c1000440c1c0000d0054041c0f4401d410401469a070708a14400c0722a059400a43c4282d007040100207140c8994582c0341e006c080c3e03d000041500ca03210081000100000407802200d403074000586c030500d810701480c454048281c449a1a10142110041c0189403a0103001e48921580203403001e00400e42c06080040c002c080d108550302c810003018000041013034460010000c01d171008015641d441038902a00441c07110b002442d00c3d095520211f1035280174080000200030200480e002003004c5406800030160203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 755915395 1250 755914145 755914151
    0xf031801092411090f01031b0f120209010804080918070216061d0d0f050118060b0102030c121e1b0c062b0f2306030d120c020a02060c01 60
    0x41800c0384040e6800a601030b1403461801400c01c5900d0011003c56050010840300d111250042500580043c01020b10200c40c50a0049410305129040034125a911400341c450908505000c0701081c203a200d02c80181d8006403a0402103400165440054060980028000d4000c645950b03041d0315401802c440700380040e845507001c41404180165010081c02503482c1038070540c03060039030500b02211034400490041d0050708941c0c040c440e94030300f00d40d085070380203000344940c0f64445640310f1003943c9110291005860300780800580d6000004545600c7c1c045805001d8800403a480004e49401c102e541802851010380130703c40315000d4200400703286650011050610800c04170003880d08803a10313840ca018182c00c01800054524100440b00e14540040090802241c10000c02d8080c1c40c1c2c507014004290700f40454101c000c202a030280e511a041400b91207025601c0e1006c00d9035600c22941240d0104010505602c03d03c51030384c204640304c212500441e1110301c0c2030350103c1e0b05503204445000e551b0359 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 755916645 1250 755915395 755915423
    0x40504090b150316050f010323061e01080a090507091d0f0109030c0f08040510030b030f031305040908120906100b07080a08060307031e0b1b0f03180109 67
    0xc010301c2d8a503604182a0001c007904a5507601c0000e5100640c020a48542d403210722804460384a6007040c100141d03207010056400d5000d138040b00c40310748255075051048201249580c1404100060080c40002c169134000b00f5843d03460201c0000e048004c8280c0345c50040044c0881c02c0304c29400354101c5c0000d050401020741c0c0c00880d8031030800565002440c410f90602d20a031001c80d6000c0c440c5050160807814118a418003450040f07244e10995101d241c1042040103000c2e00c554060f4007840032001c040e420344e445100d6071140700c1d4607481500780400e079241a07039100340b080e400d240e0300014a030b13031054031111316002030085522500181210a01c3c1c0b143e02490401080150300e040000040580503512814a5803a030342c0c11009009064001c42000f0003000060f4451707604001d140001d40d00420101c01c4111520810101c1560110302030310005e0b01c09010500200703900d0140c041d46040c0501d410b0800040b01c0b584100c07030344080d040c50000e9568144095444070284540881d1702d02c5501203101d070389 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 755917895 1250 755916645 755916661
    0x201090503010515150f07030f02030c01060e090d2c03070503011d0d0518010302220801020c0d140a0e2803060f09020f0114070f15240506030606040504090b 69
    0x2054140c481c0c10622420701c07246d450300e803004054401c0c6c1135250615544140303000f00d00301c1c0740d8001e000c1e18040070742c2008000920b0000c0c885825019031506026500c15a80300003007601e41c12195907458601240c00e141d0010300e980d80c3e085030800d1800041c151000e20741d490700000e080d0f0302020f50200b901048120030b850141c20401c4812221042800d201d828107030350213481d031003100c08900c415061540000d0380d0580b003c40d0b02c00e401100407911840c000b295440e2031781d050003500040800e840701e114141d5201d01d81800703410301e001c607a440641c0d514a02041404122508018045450f40045108401c41c11040810380580c03d01524102c84108031861400c08106555289800542e69880c0c00d25903000740c3c0760080d007800da050081c24040ca14841c61016009588070b41500136140001c0c1d81c840e6001c110714080305400c0fa000d500000c2c080300d50a245007490004a404e4000b41203079507540100900d007420405076600030001040e0320300b401e60b03810114003510b160080848201002108212000e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 755919145 1250 755917895 755917909
    0x70203041a220f05010810030501021b1b2101021e190f080610020f2d0303060a1a0723072903040503071b0315050408160201090503010515 61
    0x90550b848120340c0d07103407922041880040b4a400b90904228040c0c00064280c1ba2240202c001103600200855503070400300145100084042d81d882c40ba809507500000640110300640e82c208407000f0040741c040e01c1c1800c01200030700b4017010f1001241d5000c1c400030360312185401c0b0709404c04840d120f41c1b5540d001c4811500d801c49175841e803040300b802484c0141003c40750340401442d40c484c0b0113072101c845015200c8801d9281c410322001001c0948250395116504035a64040610041052041c04a0791590b081200762a80000c80d015508808080010003000c0c0c42500495646510310130b80034035084840c1c68104c9103070281e55828912003001c41309020f210344100310507801882c1c0340c8218191220012000b40d02c600c5691030f1616a10804401303e02484400c3c01203503000c90f0700001750013801c45070b000c010074810360500c02900e60030380901d0308661120180c003d007031213154032060061500342d580c2864208252050700903410031010303c0f07022845403401d00c640f60061301981200400034082500304044 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 755920395 1250 755919145 755919187
    0x20a180f0c14070201110d03022101080a08210123150a3b1005070302210c0f0606120307020f0d0836041401030803070203041a 56
    0x200030325140c1e21030411030307000d4a00c004503070804090550b121010300040301c021205d180312040c0c5001e074a201055168041e401450500d00b00c401d8884120406c083c070a40324070b801d104240303098004020100c00038126400801701041a078940d4450b5074070700c41e00a00382c4802604501410503078a10b034104c080650400312500f182d400c80b081c042344924035114517600d0046e01c58000501c50400ca12954280e044251400e4201c201350781403644c1010004204482962644a540180c0300c0c4441c0c4058144950110341e29281c140e0020800d06890f00748800c1d120b8612220001c0b203140a210054a80100703001301c0f40444040c0000b08400e01703101c010452142040e008030700141e0b10030000840140c0f0b400d00c0200c0d40c120700329403074103451000d42020341282c414107e45103584600d5030b110104020851080c40c0d14128980322418480c50301030244000c0718403e100d25150b80c0b400d807004000007402e1000466000359184180c0e030074240e80b0f43c210a03103024110300c0004032402c082640000700207400c1101403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 755921645 1250 755920395 755920421
    0xa0c020427060f0f240b07080f0a05040b0c060901110406090e10080a050d030507080613200414030606091009020d090c03061d0309010e0105090409020a18 68
    0x4074214010a248200d402020030060a464403010a100403103c02e500c0300c119031504103003d010107803510881080700e241840c000030824004040204a03103841c2d50955852640c0b0901c1c076840c0101807002c00c0501c0c1c0019548204100c8208001301d88101a04041e121b1440040010010360a0600d8560b0a450805040310003503502440200304981c2e0002d00f5404440c0c80103810941c42c0c8400031594680015600060394038460010400b040020016a038070441c506640c2c2000342d81ca803044103e9080205459132039100300240d90312440c1c2c040355407054420b007089440d080e2820a40c5214108070b904260f00103240c01e1002070001c2e22600b0240140d5a00400c100c80000780d0740b52402d20403110302c40703a0044200302e075408100420130300e05c251f01000a9a40100c041c0b8981543c80ca410000340520485e94843c0e410500420001407400200340c4000038016120903150b1110308004440e0754201c156525401500c45c820f42015894607400072024001d540703e4030303034a8641120b10380305550741303490001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 755922895 1250 755921645 755921681
    0x7061b030b030c0405060d0f030f08010f050a090216021c05060a090803182407020f011a19121217040c0e0c0705060a05011706060f01110709020a0c0204 67
    0x244003030b078010420007003041c0300f12000501511204041081c0c0306190000800e1090300c0d01001050507000380b40e101c0114543e0ba600e03086e603a02c504032800100468420300d908140c42080911580c83d241e00a010013100409010820300d181da0009800c003803d09078583c000d0003072000c22109120080c44100d0348943c0e54041800303c2181580c0c0c41e03010303101c010260380551912400400240005120b40290101d9800e01d06a00e00d00390644c62044035402c1c2c035103030051304c203000f400010078a0600642c500006000c40c00d40c680480c1c00c2c04e0205543c0850350316403c0c0b1110203004100d0b10b01f03040300314a180f0300918942c0003000c000d0320090050383e000d4012103541c1044c1c034200400a040840359034140c82c41040075010540301d03143d08500c1c0d406500340081060180c5820010101340e1640418102c0c0c0c10360300138074201e1450740b20300e9480f50004c0c1c5805400c00115502411154011140b2801752014102166890356480380d45404a0304000c5401000400d018640c00551070705001d40d00580032194054 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 755924145 1250 755922895 755922911
    0x3303070803030c0301090b01090806192403231002040905010e0f010603180206122a030c0f070c030602030f01240804110316050909010506150c0c040207061b03 70
    0xa0f03210f0f010510820b242070762150070140d42a440703000240010701d805404c591690038040340d41144144a1052049050b1404074880001e50a6581c0c1d00d82c2214a140641d0300a0b0540e281e8805072480c10814916580a41244003a008410880707006451080f20380180c03034030300304840002510300617480108403100e240d05000c00541c101c05514115046404d00260010358454600c06d900c0f04000d001e07500480c0824110543e0488a6000740b00b03141940300381d101040d40038041c8c0c84824a000d0000708423141031000883d64551607006101000c5220303160b0b400d10320540d0b074403114526250000c948a036000b1050194800c1c3d103c00941c0900400b00359a6100d000c400c1c04500280314801d149810440d44402207800d108070015112100314018068070700006440c0000d017101c400501ca0a40540c10800024141c1d11040c410140600c40052007207102c0f0355000c09401d6150001c0f465040c4034028a01050303403a50311703480140303002ca00c01c0c40046803000640c0c0d0b442000c2028a109002490300700624 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 755925395 1250 755924145 755924161
    0x60609051302070303060506030c0304030f0f02030d1d0109120e06090d1209080601171606021905100f0e15060a0501141c0912030c050304030305330307080303 70
    0x407001c440741a0110041c1c0768092410110058a11540225040300001041c0050340d03a200c40198441e500035100e00d0301a0a5000e001c64102031100007180043c0c20a02514072640c080780c0240e2412400404580902500d91034403900715a00540c044031140100c88a80005a421403000142100300b180c0880c101201d4801288241b0342d003000082a1500d02584002c205006014540241c000700c412120307591303100c400c9040c17030305240c20700542030384180c10b29404000700c8001c00505407036641e0b025195036121b40340c0c0710748901d1207030400701c406004030342d25000c01020620030f0f0a0380002440002c00d05050099000341031000d15800035500c0c2c0060f504100e000e0b181c0030340d060203c070000e103840003103c40700c1d6400084a004911450064004044d4000081d00c070742d82010700218010382c61201003040d801c1050b0100c803031407404000030030000d00020f808070780243d014a610260030b4070103801c03103400c4114410345055030641100010003c00408a1681010001031028041c040002d600e14100411 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 755926645 1250 755925395 755925409
    0x1110121505100f120f0219020d030b0604030203030f0309120a030b090f040317060102011d070e010b04060f0503041a0405061015140c0111032a030f04150b061c06060905 74
    0x441d2000181d181d40448074044015030480300c041304080c0384091f0b2045a040000c0d01c40c1d50002e145000a0700780301d01700d4034610b803d008440840ba4020700552074801902030009440e000108011a103001e0080100a110a00f50041c8100764150381e00080b0110038004001d0302c5d000103800e040303141c9a9542003100280d001040c00c1303c0e401070f00900c0c1c0c41030360741c40700101e000d441d924601c1e01c0300c540800c448803890000024800d0940707214000500342c1d0780c1c0394003c0c030f48280201d2155030700040b40c515211201d0740c09000103542203030142c1d03501c4404c000600b8203020480e80a40b0100c0c1c041e440f00d0700700a00b205900c0319030000b515409020361200c10005a00074080b601d240340702d43d0b078110009448010028250301c49690740d4001130110b81c8a04d04050101910048400c02003600b050003e48400038200c8441124031030007003464508042d0300d454a41c3d852510900205101c2c80e961015180310540d921401b81c000c000c0180b5000c900c0e14200d804c0c26060b299141d0184040c00a444400d0200303a40f012 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 755927895 1250 755926645 755926667
    0x3040c0302180708072d02010501050307090e0d0c060603080f12090313060e04021902030a09060915052d1b06060108010e0c041a0a030e0601031110121505100f 70
    0x201e8107071400e10fa03c80d41c00d188068500d1840ca111140300b4071b254286078041d0010f41c100e41c0114141c0300ca055981c1460b50959890043c0070880360003042d000040b0741d014016029086000b1b401c00036a1580725038130149207a0100490100c24600410b10708103100383c0f165000d40c8030121070003440c28100707010301c108600c02d0107004000070710200802c00f0160781c0300d690507a0800300000d0040003140210300800303512580441c0140d0700003a10741401250980c05000c8040c01c4440e8440000c403205c0c1c5031031003110342c0d410030707401d200d0740000400b1000c06d0200da4003010305018039158022580c4443c5464854024615500d0001e51a04802c080000c1c503030700300a0050440303004c115400155511116515140d102e10380040d2685c11020f0020b41109680b00e006d002c142910780c03000c000e44540300d0002640d80b0b809100046c41040085900121420318400c01080b402039400c100300042030401d100d1050b03a40280a030141e510000074104103600d00340101c841030340102d04040401c80f1240e0b1008080154134 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 755929145 1250 755927895 755927897
    0x3051207060b011107091a030102070c0317040e0c0706150b0409061a030a051009060e010e0c2a0709020f0309120f07030c020d02060706061a1c090203070b03040c030218070807 77
    0x2da0080d034280c0707c401c44000d03001000070001c640c5c51000e440c11150b0902c55010503a04a051010541c1e0440e603c54101d60903140300800504440e62a5100c59080381e009440c11994141c136a00c0c4042c03c19405102c1102501e04098001e440e40d0400c600b8800b1240154031820a000e412410f0100c41c4042000b140c0d00001070100102d40c030b0750307441031407480c01c1c0c400d9210704501440c0510000300c00a200f54801d050b9450000600307915164401d8200e064011030b81d0440100c03000b00d410200001103090303c0c9044d00615800d4444036a540c0140b50200d8004001e02030714004004104440140c0a000d2400004042c070421410680140700a08840c06002801010302c05e15415100955442079070420711650300901142d41c8107000d2504030041c10741d40c800c204501d8449950a12450302c0c17030382038a04068204144843d01041aaaa00094541b03004181e801d800b45a00c0465480046001584291302951803aa02ca03031551052003401d0b02caa840d0811a2015802801040b0740d103d2070b9260481c0075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 755930395 1250 755929145 755929151
    0x50316121e050f01020408150106081f0b0f04051512190f020403050c090603341203020f060c1606090201030b090a2a0c03051303051207060b01110709 66
    0x28407051a01c51400500a819071240000c00902110150010420790307a00900f0b403042d20f41d1441d0700380400d40003030150708042100640040c0482c0b00c5203456901d1100c01c0000400a280c0c0c8050f1402994080c4d50843c2140740001414071483c10601002d10303241d1040030b03c0600d8540300210851012034003800307040d18002d440d16401401340c0e80c0d03004a00307a100c00c1442155115681d160003a640d20b00040c4044c042c10b801000980e0b689001f26000c141d40c1070071158028598200c060305842c0c2100024034450080700200c010800116940b8400d5090b4402d4004086c2c1e80002c03440d0a24001008101a0180d0800c0220102c0781e2000004410b945501c0f1001080050051005801030b246603201290000c501c401004102182500301c416030a850f0b442d080c40340c00800b5019500b583c2c1c032800010202e03a000030040300182c8110010314900c0241c800e035806549d169521241424000829002d910300045103503000e01c10343e441413044403102400c0c0000038105114010703440e022144070f48001e0030303a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 755931645 1250 755930395 755930423
    0x140a0608060912042d0b04091508120c010905070e071706060403020409050a02040906060f05040203011505090a0b0c0a0b010e04020d020f0102010b060301090203040b060d08030a051b0d0605031612 86
    0x1442405d00306401da036046a08000740e071980d0549855810a1044480d07403410110000010710100340301c1c40c103a4010001802c0350243c01075a00b543d6500c1800711004641d039804840c00800d03003e00640e0003601c81c0b429020028100014018a011302201e1000e040e185a10203120f40ea95910044404885c1d0503200800c4204450400c14244006a000030350494103000305101008050750115040d41d801600c801100343d111340600013240401d010748620304810501d0780c060680502c002e041c0c0c3d00001408044240c0d11600c209a0940100c0340a05d02a444041100c007000031040b80d99014080004840d0b907907141980004000051080001e4048c3c03941c001c281400b64807e40140030a40c0f0081c1002d81c1c1c03035030360f030410a00a500840382640c0e000c9000c00410b6051801d0034040d80640c0d0802e00041c2592120440600284809072560444010405c0b446500c00d1006010700401c11101000150f01c9140105150034900c18100c1021054815002444204214001c58001e96000405c4012804c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 755932895 1250 755931645 755931689
    0x4090c0614181c060e0607021c080606030c0c030403054e0c070b0702090603010b15130e0c0d1b0917010e12070618080405040f140a060806091204 64
    0xc1c143c510260203d4240680702000e01d6000412501031b041d80e0b0b080740c00c280c2600c03413480c215810201244001441c0840840c5080c50014060b582140d0815001392400225101c0103145034410350045845403c0380324407a0002d5809080442c480040e1840da050310400043c402c5064542081c4500110704030b1000148524144c8041e222501c000c8800c95902039140c000e103150716000481e080780709440f9040041c0103810107009040c8201c0c0c003e0480c03180b6600c0e0385030900707a80e04042958010949000000241c0a07101d694450103a120a1212541c400031307030800750180d624039441e081200c2808400a58036903030240303030002200d4500720030702032549400440c90701420381031803041003034171400b0900881140b482c40100b10366880740c541007101c0001160025200c000a000c0036003684c000b403204005a080c40d40240112055510340010200d4036012210b41c0b10318241d58840034540e94290512682404009168110301440001c001c81c01c0c1c0c21070100c22612960045c15407010700702061840309 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 755934145 1250 755932895 755932939
    0x80d0c12180b0915040f030e0d03030209030c031b12150f0f07020c06040303050307180305030a020f1612030c12020606040b1f0503060f04090c061418 66
    0x1050240e0414420740c00030a00040750350030203480a5038a091542c010a004800014011620519182c81d94401d613491ba02c8110f07459002000680901c40d0310521074140d66125281c120f0703014840e0720010b859404200c140b501e0250341c104d03114080d6000e454171700400c5840e1414810407030702c00c031a40c03054204aa0143c44c103080000040e205210100414004840c8a50500901c5400c004400c203400d0b6648a20880e44d5034400e070215500500200001c0c400300b442440255401005e508088039550103026015a80200b10f1340182d41c0c1e40c0020682100e582d5040c02101c1c2001c0200d401000080b0200344030b07011007501d0348502200c200391501c130310b420980640350300c403078154000313007a0349414441306070207500c0d6401101c80350b100751310348007907105c00e49849202c00201021036480b410b074081d9410f030281da65520160185030711900c004120542c640c0c0d10302404003950310a81d03d141d4207501c0c20764060801c02c40d00500485034001030007105e40232112006285c000b200c00700c1e043c96048110410040d84 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 755935251 1106 755934145 755934167
    0x105070206040b061e12010603020a14011b0f02031e01060b160b0c091003090b0c0304020d031412090c0102060708150925020717010603080d0c 63
    0x40707401c194408017a645a14184016903440301c000041000c0350081ca80707101a03440745018421401c00303140c51001024074620107482c00160b507002038030f884074410216040b00c1e0305006410034000000c0310aa6142c0e0060140c1722170751484100c5d032228250420110001e982001c1000900d000c041044540018180c0c100020f039111903500c40040d52409000c02098103c00e000e61610303540c41c54890800704203a5103000a0384c10007803a080810100041c00180d10740390500402c005070320380d00d07210401c8661500c0d042034510340c0c01d0001c1c003e6019603184810b01c80c0000c4100184680b0000710210107040980846007507944500302103429a004840000300d01c40d40480c070740501c1c08e0456101d500031035555038a040c0c0705410005200034031240e1996400580c0819010030190804000d88280a403003d00288003031415601d8a014501c00e03009500ea440b999900d40da01624411442951 = true := by decide +kernel

theorem cover : BRFrame.Cov 755755395 755935251 := by
  have h0 := BRFrame.cov_init 755755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 755755395 ≤ n) (h2 : n < 755935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
