-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0250
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:44:06.903999+00:00
-- url     : https://prove2.me/submissions/45f1a98a-a10d-418a-ac1d-2f57e6edde0f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 44784177 ≤ n < 44964033 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 44785427 1250 44784177 44784191
    0x40f02031506090c0405060405121501030305090a06030c021005060f030307060504150908040e09030717090301050603010b10032301150e1f1d04050702240106080708040c030602030f040501 83
    0x4221014031440c02140e47c40113042c03100703111301d0400c0e40c0100188003100d811143c400120003182003816100740c4c411800500d00241603443c41c2482d04c0b200c070003003203641024842441c00c114081d4969611744c054603040c540c0d07800012450380c1c8011074413400c3c02d006000d0701e82d03810040c00c15402a140c02c81d0203490221144a100041d280f40c0c2c0301d100d06071608406102d00705401e04404460300e1001030030700740b0503100a2050070302040c108810024405180c011566803210880c0c24142503410007800d9900c82e926002500c00c040c0c9405040958a107442d00e0002110502d102c040f004101f000c449035040441224004a41c194551070360b5003040d182601c2c1e01c003140303d882c8200301121842070611340222803004240d4606a001e000d1450b1aa085201016280400d60300454100c0d002100e850005a0243c541c3d21082100400924107402c50b6010340a00307503040aa001d0140f82010b0000c1c000c20600b9000213051003031012800004c0c560200095642e030404540c08030054800751801d4459501e0300321 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 44786677 1250 44785427 44785441
    0x90103020607050a0602270d08070f0302071e0302040b09071d01051605060702120c0a06020f0706110301051005070507031e050102030405060609010501030912030203070309020a03050102070c050d0c0e040f0203150609 95
    0x1523501c002d0755020444c01c0c0303401c010b965040701400f04840114254801c0910202c1c500c5e84240c20017081c143c88003030b000045482c5004000a0310b288900c003034003642085007030180056004140c4103421807000190007050b10309000495081c8101c8030000c81440c0c0d185490000c200c0c010400d940112829800c9940090b82c0301050f5002d40318900001041d42e1140c04803a00084503a0040c05015860701040b43c200300c415110801941d4a8610b511030340780c800001803200740380c0401c41c5407502c412468641d041c0001c65841c107030b0b581018000502008000045084241d250018000d10541e0040082d5200d040c07910300581d07901c00903240248130b41e40e80700000c40d86501c644a44220075802c034100080d0300e00710220a0f0002d52007d401a020103880c3c603c000f000d0707119014114015445100010398a0190f800d001240d0300e00382e003203148140c1c00300c40d0b03040c0800c1c00c0881d40d1099510072000c004c0725858030714110400301c5c000603000b90180159150b00c4505e0910146440c4a01c1c000da41007038031f03075841207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 44787927 1250 44786677 44786689
    0xc100e010e0f0d030b010c05030c070e0903090a0302131d210901050d09050c030f060604110f0301060302030a0f0c080411030601050315040204061a0301140906090103020607050a060227 81
    0x8428041c66112481d43c0789018801d0300301103000c91060501603016001e50b02c17035a0450f4014010458154810b01d0104412031034031070f2290340103144030061810318120f000094064640d510020b8030840b02c0078002c0346198115071104042c1011204421400000a80300319144c101041407000b0703043c010340c1d088001400c20012142003c405950b010300c0c000c41c5d440001c0c0181040b40c0705549034442d0424a60882c0c508105038920103002e400108000e180041c10071080d40c0c40c0d0707420900021030500c01080b84888880c10f0b01d056416600300980c80c1ea64244202000701001010000c0345030403c410b5054003a00682b10502035809a074042003c82004030505584040a100f584c2d0944d1003401c4000a03a041d2580e0107800600c000c3c800f050059860050006680200d510417103c0f400010041002981d0350560303c0c01120140c072021046d141190008070314040521010303014240000d0440104101440f441d0b01055115804546503484c0d160510440f560001c1d01003500d42c158000e4108614142c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 44789177 1250 44787927 44787943
    0xb01050907170405011b02010605150702090103031d03100b01030c03050f012d0f06090608040b06010f0513080606040b09160507020d0507030f0c06110a021002030c100e010e 76
    0x80e0301d42c921021540e14021aaa450080080d1410f540e116032034024158080c1004207035554680c0082842c60800081200b82e4900c40104035a90384101700c5540180c62344009141100d03014200410308005651180480c80c3c0c0901c4040e40c5401010030042c541c5000d82d100d042481e81c03c1c3c2e020014011040d805604441c0d05441c094004140e0740300401110804103490f82800e101d54011514050700300035075807010000c81e000704910a4030418248034559021030080010126840d2002c02c078242600c44d1041040050129070402c00d403100341d00e0340382e4018011140c2c2030106003060348659588450032500c5100540c1c90794826401c00000300c2141c6000c05e10709000b4030940000c440702820301801511158400c0000301d80000e00f900040c80400c0013031114800075030041100c0d0410407110f182556883c40d240c1c0011090040d958100e50319a4000a03000c030700d003907041c2c500d994015280d40c1d00740d21b140640c040d40340c6a440f82c3c4010560034aa15004959494601c41c02440340c02d0001c20419214110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 44790427 1250 44789177 44789191
    0x60603070b0a0e06041205150f01051c021314100311040b0d0b04050d020c010c11011404150309060606030b06030c03100f0303020a0510050714030405100501080a0b010509 75
    0xc654014030101038890010b01030900d0a080c0702440781c90050115060745c0043d441004e51181b4104d600c414400c0a01606c1d0340124900201400342c40c10004010060806000d200d0140e45000100390003100c0021184406940042c0a0a80041e1092641014281103c0f21214061030b03c2c1c08030709041c14200c103810503aa449691140201900d80078000200001c0c4445503002141c0c0c241400401ca08408240c01103001d1b601820b00c2c0c4501a1000c1c0c505280c0d8034034075040281c00d010b50004240920040d5168174400d2819100c4010b4080c450390b081c3c0200d03040a07955241e50f80300f018095406a1021480c64443d0340b007840b425603201026401c80314500c5080350803020800001d0203d013040c0c03000b950712003126450304014a454643d08036480e4819041100942d00080d00d8a061102c2004402084544600180024585410014100400000059011280130020a04000040c0401c9400f01d2140e502000300e984d64440103640c0d030030075500079604250702200220300c1d1304088550500c074040d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 44791677 1250 44790427 44790433
    0x31501022814190314130b070303140c03010e0402010309060203070e09012c0403020114010f03020f030607052a0d08010f06080708041103033105060322140303010609030b0603060603 80
    0x3c8251000d6a2100000285044000042180540746070451083c40c024000d0400901c4d01e034015407802a003102d81201058803c880104100030702070244c03d040b02c1c1910700f00c81c1240019290780c401a000303050b0700c4000400050001c01008031890303100700919401c8004894969059903500c40e040c0702c940f40f94926449030014641e0300082c040d5004260b0341c10510902c000664440c660581d00312b500b00a8010342d4003664100000c000394a07288210285000003280545001e007030100c0c01030b046114001504080c0c8002142c00000c031226000314030440034954041e00e011a00915000700b1100d003d0184007505804468041075003440790000f01c0c4902000d07144c1089648980e21419002203002c1e410316407501c410020602542e0690548000c89505074100e034404200410400040d500540c0015024a0f0148100513001d040c0042403030100018400c0345c24000d80c0c0b400c001c414842134000082d6113200000000407840d80c40901d41c0212402000c4610042d1201d20801d030b00c0300c03815039200f43d040e8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 44792927 1250 44791677 44791723
    0xe0d0809090907080d08060f040212060907050906130501020d090e04030e040f0f0504050f030c030405091b0a18060309020619020106091a03010507050906031501022814 74
    0x81054441c60ba04821044200c560b9079030344003074061804060340c0f40c000028000c03500b8045181440140044112030480b804e60812040500286030060021f00181c400d2410801040540c0d000744221901818090401661108851040406040706100722801031040200c1900d2451240f240071050b01c80782c103e03181054503170791411908c510007541c80342d074020358511900341c40b15041e208004680280031804201e40c600707403d20760b0a00600c00c0304507030b140e001000182c41200c000310480e4241c50003120035003140d480b070380c0c41c1c03c038142a808d10502c280000012414031258202500d50000e0102212101007551540c20841c10346850050007900180306010b00744425400352403811074034036039100000c6d806645026180944400c050307020401c80d8180316a1006040038068a40d108206003400c515101075080403528074800109144044046035005904581c424400401242140341c40036501119070004408080102801100c62a414507002c540f440310115425105020f000c1d4204c4502c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 44794177 1250 44792927 44792929
    0x30402150319020301030506040b01060f1b06020c060f100b090a090c0c02040c0e0109081b011803020307030623010602190f02060a02030a08090c03030415050706050901020a0e0d0809 80
    0x40e03040079042d00c48074158644501000c0c0e186101550003140500c00031f010b1420903007094042d40c8010b8010404129524000014183d00040c60102061144010b10040744650408200a010745201c08015001d1b4a040c080400500c2d240fa0340903c0002441e014010b9584040c2a541c2c4107c03400c55401c41c03c101c808100d021001d51100c03422581230308181d620120f00360b00140c100d40842100102003026011400c0c46540e11540b82c1000d480890011301e03081d400060580100106a00094100003130f030f40040303450001d240002001154090100c600b43c03034891038241e000d070039888804da15001d903c0030807403903001c0d40703a410794100c482c0c0360043c0200ba0392602d182d91502c9001c000948000303464200c2e110050302c0701d00003014500c3d00b503806540c840001040040550102520780307612a80b000d9090305441d80c0101c100d50844d807011440c5079029450341c4041d40d20380100034018108518220403c059418190020146800140d0312030404810440c104000d4084031140904490400d109900a03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 44795427 1250 44794177 44794219
    0xe04080304030e0409050106060e0904020904290c0a1202030f040605060402040314160806040c052205040c03050f010c08040f02030a02030a050a060501052e0e0415140105030402 78
    0xc0d0003480c0078000c143c0040c01040554424a400300d8a6a640e01800c03c600c0c1c1e48180013610500f0b00710381d00d51403410550001106003802070006807610808c112142082111603400c0701c04004040548001c40c6001001343c4055080300c1c407444045070100040e1444c50285200b2680305028031090920303240c0723690310341b00f0003000e00400300d6400590800000c00810803108400749106c4500b8000c001c404d0081c000803c2901c015800100650300030002e0200040180f02101e060303c006031480c0c1c541182041640344030060281303500c0080f42c0307000e00b8002444102d00048095034021001c4880f40b410b00b4502c0d60880d10510300c1038001039112008103002550540503144131a000408a81b1000010713000a418a10991000c54441d4403011200040100c2c0c1d0140e140144800c840ca4141700750300c10343d071010029072002d2107004054929000c0a4403401400c0c0340788213440140c0b0400074807220711030320341e0604c4560042000700b1400c2003c9581962280c812a03205543c00385c080c54400c0c8405840c00701c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 44796677 1250 44795427 44795431
    0x10605010905040603050d0e061b0105010f0906031509020406050a0e100e160c1a070519050301060e09060102120a02100b090c09090c04090203040602031e0402010e150915040f0f0e040803 82
    0x9d40820104840d01034183c080f0407001e160180c590000903107500d07210b0615104001680003100250605008201043c42d00080e001d00203066500403c4040381da100050081c01950449903210184c03100209030705200c505c0c00d51194005c0043c4410182e1644040c1800d80703003c96020800e450080944840700e481000071304040c500c03640703481c48076003081201ca054020b000c0301c0c03202c0080c0d008120358018031802e103844504c104250070183d01d0f65042c04401408040d410760030394000e612240206507164800c02c420800450030041003616a0790f5002d0080d2552030035941c26095909110034414549460048a8011103c100341185441451410300c41c4100c1c00915042c0682001d0100040c1c0e1001400254401d500c20400140e40b4900103415032060040b800300075000c031048408020050f600300c500e01d80d071510100c600450403034125141c1032346c0344504c008103031300080d4040000c2c0c1c1c03803101c0c5000340c419a449101601e6030143c98400c0f08084800c1803166030000c1415101107004208140c0080d9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 44797927 1250 44796677 44796679
    0xa060c030c0503030115090b040b0a03110c070b0d06050a0f03020409050f030406030902090108150c13030519060e03071a0c0d090b0708071106040803090c12010605010905040603050d0e 81
    0x1c1031840c1038892a0450704264024008444c0415910f01c1c17040e40100302401400140700403a00382810841000355600a02c4203010625580d8040c080102c148002500d41e104061404ca500054452400c0403c031780004844a48140c00c202010800e40740442d2190103660f550b1908080040ca50b40801000d00340f07980382519a4064a015011032160500003080503003c5604c001c25103412620500000c4c42e0140d00850700f40d000700e4980580c403100d90030303c140c005006008043c0c690404010405c401100e42c2d000030064800e104084040d8610b020b4081d810b41d000710010444642480c0c5a0381d120306c54140010701c0c1c2c40da1024030181c212407945010b034000c8040c0c1c3c54542044055002c00701100c2107000c042d140c90b560034040152890340588042d0303000140d49060000c0b00d80c054103160703645202500c0101070880100c00500ea0801c100441d8452010003004404c01e01c200058083c000e2a842c019540040c1c1481e41c042460b00300782c094403044130361100050400b140c140c50111460030030a00f0b21 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 44799177 1250 44797927 44797937
    0x7090605060405130908070c1d10080a06090204020405130501050a090c120207033b0a230d02090c070606120f030f0e030601140102010e0d020a0807030302090904030309050d030b0a060c03 82
    0x40400b148c00180c403040a440344854007030030104085212a0401d01c014100b5401000c4c2000030701400c8000b14440c40240c0d407000011070f181c0b030030740b001401030700580c0c111030340024580c8003006c14103071517800142c101c800c02e444800c071803520303541020140d80d65a18000701048508412502d1404650b00800c2241d002e480d2104054840c103080f242814401c240114032601740200382203041d030030b04010070a025012505800b400303142903100c058201c404000c0310202c01c0141c00440c1a41c54680c00040f0807980108801000d16091200c0481500f000c6c01c103459942c6090004039602400400012540e0780046a00c1c1c20690701e99000c0b036911010781c04050070040401d016084640b0b08104903400303070480710340400c0b03c045c00c0e400080c00c4590038100070120358410a10b07420090f1b0080340030701a058100031407640d244c0172414150003034450070006640064484003007005255041c1c1c01b01ca81140700e0025203d0304022800101c0c29a10550440d075031000c060070781040ba5174040cac036042c0c1e9414464102 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 44800427 1250 44799177 44799187
    0x609040c030c032001021b12011b02011407020a0305040314100e06060f0108060603011401051c150b1911011409010c020f06090304090f060503060907090605060405130908 75
    0x10b808010100c5600455203840b0020707250940780140500607a4001e801e10007003256868546030076040154140c11580200320a201c44401d688080d04242a441d0400d00790902c4a102400300038000c2c1022582c0802d250b000e800410802840816848440360305581d0750b034200b50868940034a00d201d07002c3c10f13000510031500b100d03610b1140c03405242e40300c641e0040504810302e080d809000c040240111040e040008060400040303a517000207681c1910744204a180100d0400c10041e99640b20342d84e04c11041084440702002d00603174035017200c10f0034000c00e80e54240c01c80e603541020406000300301220b103a240424514070b6105201e1103141140c00508000880c4c0440da400501c810307102c040d176a05400341d460740403210026404015020754040507100502183c64000c2129440340103e0087d01c81458990b80034040040442c4c103c0f00103003d00400f62400360808114940d1b6600d05440340c6100c10703040100c002254509a002d68003101c03009000e40142a0340c03074820100a00516070f040f1158501489 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 44801677 1250 44800427 44800433
    0x60e040b031516050a080f0901060e010b071505070f03090206040f030c1403030307090909020d0602030c1c060b070b0a0e030f0301140d0c0501080709090c020109140609060609040c03 80
    0x4034054111003451031501c2603050148800142e0f0309081c2d200c0c1c0601c8810030143c4645540091700c0b603445803403ca0303507001c182c81c0c808005003d00803c1d80951804900c0c0000480c0c420042c1004200b52803041c3c1030f018003003841114803015941c080710b1041c046118601d43c01a100e003e50011007800384018160391505484102001c1c0c15852038001351180402480244001d40000103003100b0024110000c5041d0300c0c044500502c502094002c1c400750540340c203400d004548441c4248038601e50b001800f90744a140ca181150600d411409003a09820403a400003004a45644120000e690070003940c1c501c1d00606442e0509282405001201042d40e207587c601240c01c82480a000424200c0005607902e503d0b200141c141e100d21307009058420704520380307108001004000500c0031220f003801c01c1891542c508100781e0322225580d010003001414400c46015565041d070006251314072803901c0c204150000444940c0d62075048075150f6040d449003005c08d90601d091912103078086e104901c00004191659 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 44802927 1250 44801677 44801683
    0x5040218060f040f091a060706090512070302160803191b0506010501140c060106032d0e071e060c151a01030f02160206030a0603020307031505010816060e040b03 71
    0x221024202c020301060500c000007505000500922011500380300700502ea001a6030100c902021192141c0800110142082019080550401c0e0888191403809520510203107103a40300441c1100180986014681048000e1212500392a1194019801d14a5101840c0406145d0054620912440b42240c036000030f1a9043c0b03c541d00d02c036002a1282e0b5140400142224034600c525106100050210b480080c100140e018110385c01450046402049444c80290207001c2030903001440f07000311640c044d2403425400c1104901103040440d1b815668840001e45801039170b08e01690030007907280c01081031a104d0303007c059000d40105072890788441904402c000701c80400180388811440c070800d4460560f01440380400100c00c0303180075850100040d05000500c1034215000303105440200c0440e01c01d100d20791000c0c02960303001e001ca66180782c880c00c0c8400074410f054013800000f81001c001003896240030407410000d080d00d20090000c28108681a114203040c0c0103815041541c3c1c00c02954541c0e0700b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 44804177 1250 44802927 44802937
    0xf0c1305090a0905010b0604030f060b0609040e0f1c0206061014070c14010c0201080610030f0207030201020d0c0e1e01020a1502090102010f11161a0705120f010b040504021806 77
    0x1148001418000f6150190a5075200781e900ea11406050004001142d5001c0003d5840c5a000308005003c00c030020000d0b00f030703002d03002400d904245003240248803207800040010741e0400090403145508460392001c00d840e141c0480c200c00580000c000b0071172900348840510342e50262828200280b00c076440038441650410807060301c140f0203a62041200c1c50307080d4404906901c0a1804000310840d0b600003901000018140314001d0130100d004200c3c45129610085c0da000c03d0680643d0b03680e81a0070000e000c1d4010101c00d803042d928110f44000034038000c1c541c3e460603440280101120741c44904800d14042d0016040a041d40601451803000034807942c40da910354030070000d00603259948080020708442042000070802c501d084d260040c2e140401c0d0075900d00c01c00c0113404102c03a030b2183c40d10780388013140d282c601c00388146450f041c000340702e0b044405000c02000e00a100401603440504030f6801820a119200b0981c0e010002407004d828290014003804a00c42458000c40c00f501002c02d00c40e07404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 44805427 1250 44804177 44804191
    0x90a0306092102030403030801080607090b090d05030a03061a131206020c01022808010b0910090806070201060e0f010510080915090d090801060b0a0302070c180204050a0603050f0c130509 82
    0x20000b0181b0405810940781c03405410303040e0040116180842d0301400540c0c4d60b0240081c072040c003107482c000d6640c4980402003041d903c8000d490b220944540007401412203409491102010780500c0050f41200d0401d444c841321501c80c0030340f4014030700441d48100c2d9a0050342622045e07001c00584007856000d00090034001801d83c1c011407100c0c030100d0050070304000180c02008011000004002e00c903110070640300042c10450302120403001d01d043c155001c41450b440040c147c010401003211131901940000e040310000d60b8041ca46685040c400c0381200001d001c3e00e507000340b0182c8100041c0b403049000d154080d100358122100803a108e9000048110101c80780c040541c0030441901200b03a0103c8400001e200a0380244201c40c144241c1c40b0300381c010403c020042580c003040701000d04c100e070310440f0010003010410350307113500385682900003941c400d00486000e40f80078030340010014481c0c890180302d503a09800d2000e0580340c10301002c50350380c000c90000c0c1c001040c2c4400400c880e665003039818080c010f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 44806677 1250 44805427 44805433
    0x7030b06032a0406050303070b040b220c050114040602070603150e040507090b010302120f0709031406060a0e040201050307110c0310020706050106020f060117030d0e0a020f0303090a0306092102 85
    0x42c5141084203844003504906e010b03030800e02030a070014140364082c58020754050024030740d680d02c10804c59116030b0303841100c41c41009040c0d9a101888042c040c01c0702550000c0c0c0e9411811501c00c034404800e0300c6207110350300060340f21070000c00c6128840d81c040451640ca4041d0794000c15503502c0d501456a20540d8159016001410f080000040c14400c40119640c203007015401c00e60905070b6600d000800401ca13918904000000406d40d0b0b100b03031100c001075680f020f081041e01c02c42c42140384e0707504022100710b401004902c0c00070648012400341e0303c4c880e6038140d460758a1039403487c004660700d0310003041542c40e030700c5884450581507a0a003d41c4021240740c080060301d035095424600d003a84c070103a11890540d0400792076582c0b01813010030600d0540f0030f9203529002c8545e100080a165100e034039601c017030035032074650901302c00500410510b1300c0e40c1c02110f014401042e204c0070142c9a104030b05203a5481000a68104000b5041360824a00940100c3d000c1c0d18a04404042c82d014000101c1e00f0760041e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 44807927 1250 44806677 44806753
    0x50604090c090f0c110c010503130f0b01030b06090103080a030e0c040c020c011e0c0b1306051e0a0b09061903050714090f040510052a0a030608010504020307030b0603 73
    0x7500713101d144180d1946140c00d00d40036040c055116120607040d9030352030400c1800000100b14540305602250424ac1c0f11303048038000141c908240b034901c4020700049070b400e00103070082a010b203080b02c0014140c1741c2200e4803900c0c0141c80f0105800511101c1742d0b244090040504004c1150355500c50608105140c1d0054100e01c4c01d80000108101c085070207000e003c42c2900141550641d009140384207aa40c032042c20312546e1a034111707201101031400310040c01c050a1a080141140440b001907200e110040c0c00080d150300c803a80124280c40ca2219000d41084074800012014a403c1800b140013a6460540080c0291291a041c0c113000341c3c0d030080d070840c00c01d001c50001142411491039903c20202850180d0030301309a0b4555484103a84001600c22985920200d45141d19110080070f110456040c0500b104891501010300c42e04071340c3c1c1501c040f80c0383c000700080780d00381802802e2007540e000f006848220709580e1800d041c01b00180c4100d4061050340b0340503006600410207208482140c1c0030360004a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 44809177 1250 44807927 44807951
    0xc041806050a0f1d060a110c030412030e0105030702120d060b0c0604021c08090906060d050a0b041802030c13021306030603061118101202070309030c0b0901050d050604090c09 77
    0xd50060103c2502c0d03019541045131140c4000700e20203801059035003000c80c04440c485d0b401409405840601c003c540000140081d80500304031007203010070300c0ae4030b5046040ca420310065a80d0702040703980c200960812804240c081d090034004054140100d48001115130312030100d00c9070b58000c500c4d4141580c0c80703901400207610b00381c0400264880c1002503e140c80c0c006680b211410700410040f00e0190b8414030100e4070a9451809941c2500740000702001549441420203002d4202d80c070307541e805240340c03100c1c4060ba58094401001496009401000048500e038140f003810b100390080b8a40c0306600b8064048481151441c03107005005a03503001c0b480381d0850403c01c00304d4241d130744654500d0703800304138030441c80030941400304418904580d0390362981000441949d4840c103000b624040d81d440041c0c030b603007016081085103050300d001d03078943d0070425100e00540e8264881c641c9803a021030380070b01039031801c0c6002da002543d1020015002003070315002540d0342e4200c00f040341c000349902900c40c0a007a0301 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 44810427 1250 44809177 44809181
    0x903080f09060903040b090406180902130c0c02060f0c010c080117150105060a020708250503070302060f0a031401030f150c0e0d0201030908040902070b07020a03020c041806050a0f 79
    0x880040341c080d100c10f00704070146550300c0c0300390310410410b40c03404110140f40e55200d038800b000501340c44040107240c030280b0700380310002d000d00141203100311a800800d1415460910901e0320031541c0c0e0b154046d038042950200306a94100c90112000081c040114034803a60081c0140e80010340b01741c60311030055041401411015603400c41200c141e61003115000301040f409603105044807010b41e4010398800d80c10204a04124603500203014612481c00811051302d18903040c0340011450400014004d5215010140c4030342043c800030f94000400c0c0a4090741c281c20360300038a210031080c1800a03002806582d8079140f620300740e000790307011020801c1c10824451782c482091400c00744800200b011010380072019048450760040c090044000003003007801c69000707034004c20803660405c0d480b2340c640d07545170402e0010b0350013905c045403031050010100f242d10303000081c1810f025070706801070305074400c61400740002000d07484140c2c0c60505040382e010010030b0b80c0b441202d00071000c500000c00c81d510145101c0003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 44811677 1250 44810427 44810431
    0xe0106030302150c07020a03080f1e030a0b120303040b060319060c170f07031e1a0a0501020714090709150f09060c02090c0d09021809010b09040812040302030d0903080f 74
    0x30f681d00800200c5c0c0143d844240c04801d036640a0070701610b41c00503110310003440c003078902c40400c80a102c030703594082c04807603001452080a40c0401408521840401d02180500030b110b620829031060000c43d00084050840c5a07010f0170250031503100b828510441800400001e0044c0e8884e56a11444d84585521020708841c800a40710190840e04000c01038a8000d400240071a04040e0790f40d0456203041d8000c000c80d11080c0c9007400600210000340c001c48141512101c003244500c01d1094002a517500225569048401c5000c480c1001551107060003181140101070700c0c1000030b9010003041030900d44c803015000442035a640071300526512009840080143c000d601404041d074000d100581d00e002c401e95004598001070740d01c0b281c0d080010405890384810080d070005100c0c050203607484022440c0f40c0304229100007440002594400d10008010070f44001d40b04200c108180d01011b14070300b2190740c03c070b442403048030310f4240c40010082c1201d40703600048000401170424810200c0c07119141503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 44812927 1250 44811677 44811691
    0x30e060a0e10030b180105030d030b0303071202120313060501060801050d030309050703020a060c050c100e06070f0803130605012112050906030103030306063f0e010603030215 77
    0x40c5000200c100207008021805803092261800c00b075a1102d50788039030422000c0ea003000d40040c9000c0b600f200b111480c80400d0103118040d200c0c2800c2200a14464022640000c0014000d0340c6440cc1c691108000781402c80c02d82000e5118405901c0c01408009004502c503041c00c440341c04101880d45810010390304183d100c038041040e1100180000d945021821034041e0741800c0014031888285005800c0c003109500c0a940459280e0300054030030b801401c2d10f8801703440784c03040d6014a02804200f00c8000792003070003100055024a43e00c561402c03ea4000c200f203a010f203149070819140b0b44d0701e1400e246d100b114400380c00104003030024200700c140e00038240036003450340760304090382408848801c480b25035a101800c21803078481c11208450180b070840d141d2074409170101d5034071340e1682409000f03041075200741c5000a8144c0407444000c0d01e0a81d40c8100da030f21340e513110003101042484010f58100c85545040b0708594442d00780d14001024400d1100661081d00a0140d140e042d00c0c0e24031344090020404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 44814177 1250 44812927 44812939
    0xb04150806060a1b05010908120117030405010503091615090b0f0f09060403171b060402010801090507020c04060f030b1b030601030f140405161a0405040b0102030c19030e 75
    0x10103856910b9905480c00304002d072800c58106904140100950312020001070550751a00d094035061200010040c403841e92412100362450b603841030b2040c601c0004050003a0250000e0005024a6101f100250b41000c0c80d841100d07144114109100a5454240e000708184075101540580803a00030304181c0c0140715100340582020f40c0002e42112601c1151f00310b030245c00000800c0030f42559441d09a0f0041c50f000f458591410400f000340c0f4015900a21455800d0001d080040c070074204005003c9201e02d40c182e64001980c0d103000140d2014240140020007940200d000c0c81031140c945105400082880c0700311300805038590704003a607104002510702401c070403039800071243c0c00003140c0843c2e801c0301080c43e00141906100042e280280524011158842c0703918041c4403d00400180070b0f00c441031400350782645680e548007125070010406501c104d0000060100b0405031402d540003c011400c1801681c1c60301c200d90840c0d81c2054810800280740c59000b0440344285944040d004110490a5a071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 44815427 1250 44814177 44814181
    0x90801110a02120706090b04030315050d080912010e0313090b1203040b03042609030d030b01090509040c0504020f030f01090b0604150c0503040602071d0402010e0114130b041508 78
    0x7000351150780c000c550b1100d006001920500f0000e85038801d2040c1500404205c0301130400b45801800b520b858644900d004200c0e61001c1060328011080310002c0d548440700c180303001c0002081c00545060702910040340d560b15510014400c0c82070004101e0030400103522840141451039400440b505c456940c1d000b0010902c104001407800400c5a0640304d030304540a4603035480d132503c21190071700e404580c0039800700c0d54607100078140c0e00030207020304c04000c03400d4070001e0a000c0c80c1202203400002142d800940301080401c06170416410113a00580603000031401c1580f01c10204003030381e102402e40350340007030000708002c0100388100b04240585808801800350307445817000210140114043e1103c880012803c2c0c1030b00714011020888030503804401d80c2d03222030b55688080d45038000c511454108200300c0c582080900c0031685894840d5905031a00741c007500c0701500454403007607400d01c041032400c410040ca03028200315080c00740003400d1080c5e0065a40341401c0c481161800075040803400e00c290001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 44816677 1250 44815427 44815447
    0x240105030a0f14030f0703030c020607051602030c040218010801170601031103030904060f180605031c180306050610020307110f030a0f060203040b010e1e0a0209030d09080111 77
    0x38541074040d00080d041c1058015410300302204410005494164400020840c0e8403580300c80103846440c0c0130740c808100340c0006140070783c0c44c0d01d42184c503a00001c204000c02100788008040d825403990001d0b0881c4c621080403408a003c030703440706880640c00b030003d65505ea080c0d030f48140160302501c04a4148400d55860700e80ac50f17640d64040c08005c020a41c008800308807510108140c0340c861600a205008090fa500310304a24120103019202906121080c1081811650b00506040342c4014000f0800e804032243c1d04841c0f4a000c0700e1305420085e0300787e0400c8200060580340e601850103004005041c0c00d08104015040004c901250700b507401c1070251401007220460065044a400e031102a03080e1a0400000e04014110100403e0841204a01000c2c03201945c044c52055201d280303159000c0c1d80ba82a2001c0d0918101e94046061060b41400c01340240c0350340200e50000345504026080500f80c41c00a81801184001d80001500b070a10400c58413400340540c0c10503580b5510042c0c03900c11118 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 44817927 1250 44816677 44816683
    0x3010936080304020d05160e0a0608071802040f0803030702011406010c121806110706020102040506040911040e090a02030c09160c0f0b0108071502010b060306190509010824010503 79
    0x62009404030750040300041c1507403150701a141030789a00400340c2c1d007410100200241540c04d20f0140351811001c840000e01c1d115400c0c4034070011348504c00001c0c04100c3c5840704500e045041d240c1200d080701d030288400105171100c00400c0f805041028040c40c1c07641340c2210f00a00711281c4500f03032045191b69030280a12660800c4040120603000140780280d10701c108804d83e007070680c01489458944180000168043d80180402a504102025a0007803a502c3c20304909070702a5004069211104000411900c00b140d4440459004000d1f03c01d401c003651072031100c00c01d0304101c0d00760506d608003071000317000c519041c4400000888210f0701408641402c910780c01402c40e01c01c5d00c01003440b0001702c904013841600c2490b40303901580f20703428609640e10b461a15031285018480d12003220043c490101d03030580103005001d0703040f002428043c210f0343c6945c10000024120741c0340c1e600c1304030720020108103501ca4600b041d010303041410003080b41c40b003840d035041240c40c010b003a00882410b00000501c256a408 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 44819177 1250 44817927 44818031
    0x304030c060c091707030308090703020918010b030a0c05040510140105070f05030703030b10050a020d0c110301050a06051302040803030a0905030d051303140c070504020f070602030109 81
    0x808000350050034020b040e14002440e40240b04021140f00c480144210002861001d8070b20980d00c11032683c444c10700e002d070340300710a020095112811030006038034190200101d60080e1158400131800501007404241000907108040d982c407203032800184600e0810b0700450b50049480c03049007828600d0081c0401402d403800f9105810440001420001e021954500c4c4007030039000001d403659000c45241c080e0051900c036001c5400b0720600020050581e026000361010041c1e280c028280207500100101c2e09100340090072130f26141d008000201c0d585003441603510504800a00099950415041103042c204000041d544140101b0091200c0007000c42620b410a50542d03020990b20113900c0c00d00e085004491f92840041e01e0501004268840c10442510142c000d444d02c03c0d90100308090782e480c86c802c03041450120f9000e80c1c0f0820581c00d10307038000c1c001903800c2c040d01d508080b00c580c0c030103080c0c0c0d000380d116002498032080703e6040841030400450228000805001c0c0c3d6401c1001583c9940c03402e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 44820427 1250 44819177 44819183
    0x1b121e020f0a1202030d05010b03010e1b180a0803031e010f05010e090c04051201090303110403050d080405030408010e010912020613030804020307150807021011040909050705091006080a020304030c 87
    0x40760700c00f1140302c0c001c2042d80c08190090009220f43c1da1100300c81c030342682091281e1405421030b0800f080d2840d035001c1700040258001040103103080500d5500c500c2d519041c0c4c030343c240c101c0300f107160000e8207001c140013443c001e80c0f40f110548440440c24910b0034001c5e4060300410300c00c0c2c2d00c0903c20880c1343c0c0c02940d409203985058a2140e0035907100041c002690103154001d42e0003000d00350f44030151010642c05041a18402d441c104103c0440c1034130b1030540d00503400010302a40c010403200050b180100000d6500c640300f14122458a9210660b0600f510101c0284540c1c9a4668501e04100b2901c201a1b111110142c0700032b0074640b0700045c4880502c90081406014044404041401e54409000c00380207003407180e0520002c2010030000601040c4101d40310001805150071180b00391006004e1075200d003041c00c078650b00301400d00f000c0c0002010045d408030746a20451000281e02d8642e1510140319502c0c0303900000c402032a000d03002d06420300003030416001d10710400c20000005d07000304a40200d607030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 44821677 1250 44820427 44820443
    0x60a0803120c1603170708010b040e09010902130b03070510020601050114040b0703050406080a09080a0e13050718060302040f0902070305070b0103080912010207050c011b121e020f0a 80
    0x2c52104140092140c00720900b032400305100c0c208207161300b20808014494a0314096070580d92026801c940d00788082c041e03604010002c0004100700c1c510803141e035400c142c5840001843c00d9035680002c1102101945062585441d03110341e2495140500050004000903110400f18429040740251a400705000303250501c4484c100c4c40192107486804d82d0050000100d4044e40e41603142405000351b0018440c60b400200e22000054524000e4000c503c103d55110304c4560a18a0060096900103104990140c10010103140b45503105800c2c024280034101985a218407000a07203c0840c006840d1380010003858010072040100b41070b12207650003152421640141c881103980b50440302881203040280c282007910340040300f881510300082513030030811540117040f908800c0c42ca44c203074041c3c85800342507a00040114900382d40100c0e6802540c110781a20503d55000d950b49a0301c603c3c2c03c00b40440700141c0450040a4000210150460a01e006000a20703580c20030b008120340c3c0c0d443c614030041c40e500d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 44822927 1250 44821677 44821681
    0x3011505133c05010302030a0f02030c09030d08010f0b090121050702010f06030b040602070804120b04020a0501031b0c0c080a03050706050703050f010e04050a060f02070b060a080312 80
    0x2841101500e540a0001800380310507a82d074003501d1504204600a04005030006201c5124241495010003201d960180441d038480c2c0351500640080d00001c1c19543c0c003540303a4100d0700d40c820861000b148116601c2c4d40f4603460700d502006140c549034a4840340c07002d012205d4018802c1c0000c0d0307009801200c0070103e0880d074402c4030800407105403400d00da00c0f44080c024000100d2800b19035810072440b584142d070081000c00c02c15101c10080d0b4581c1c1c030025000500e29008a80818000c1c0c00414aa41c051304145290560b0b8410003071a40107900c402703840c0000076800741b104510788220303440010b03c424039007880700e80300400e6a1159142039445240501c200c90011200f08100c100307107080100702c0101034900f805a80d0a0103012548840c8044074014505000903072800c0c00b07841514001c020300c82e4810f00aa00341803020072010000b400584503803183c81d240c0070008420740904580d00080480150b22100e0078600354146036400313001e5500c240600f140c244003c450000a0340d03510f01c03901120728025 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 44824177 1250 44822927 44822969
    0x403051e0c0607230d0e010509030a02030f07180207020108010b0a090e0702030a090f06080112050c06030c0c10060b1c090512131a0a0309020103230108010b04110301 73
    0x4003401000940040003c60f1a000f841401c0c003203000d0341e0602500095450b20713188205521030160000c0b100101d00107204011540d403044019000402014044a94140c550b8000902c1e021048040240540c004641030100b01060b104548600c80d1621007541800300b5540081e244001c14003a5040c403503404101d001d244c0d84503040070001014030300138420150070160350094480e8001030004000c258004400220709110b810490101c0d081c42c0d1344d0020b5642020012000c1400342c0d481641e9510a8240c114226660036008500401b6030b00141581ca44040007161304000f9130041401c0b5461808004000d480301f070b03208a54480b05480341c0582c406817015448001483c0803040540301e4840d400305000312010600003008000f004600c10048680c1d1250300442520301c04543c0700c0504428414540d801d07000b80c001100c0b0620506000c030f2410b510350480c0d11100704500083e44052812401086255000c1c8500744960740140d5082c4141004041075001d903100601c01c0a41981c401e401403000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 44825427 1250 44824177 44824183
    0xf010c0804171b0601170a0c03081b0129180609060d0602040b030f0f0103080d090c0e0907090e12030c0304020f06121006080403120f02090a0e01090609020403051e 72
    0x108100d9072960030010f1441d001c1099441c02d003402400040100080f00305030140000802c801e005038440700f00c20000d41107660b082010f0b00119000000380c0e4a400e0300549071442801205014802d00b0f0788cd0301c00c1030911030140f0740c8003445101680603503980c1407030243d1002c84080b0035034002803e641c5a400784c0c440101284e0580d00060024200f140b01103000305081c41ca000040d80200000b610050594894002800005100384001004400c1c01c01c00e00d400008560801c038685c03806440040c000c555201e042c001c10300422a031220503908041018002d24216102da800802c086400502c044901580b02c000e440c40080c0c464403540c0408400501103584880c084150040003401d015100c4020309078402c025402511443d00c600c1d80d0040200d8814400d500c1c0c28421505556400e012044100804008025010070340149580803c0350840b02c0d200c41d00c10700c00914803034a69031425858245078504651031904400229801000200049400003d1552900344030144035041c401070103d100749 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 44826677 1250 44825427 44825437
    0xf0a0b0a05220e160314030909070503040611030613090615030b180309010804030f030b03030408071701050115050a09030c0306020315040e03030106030e0a060905010b01020f010c080417 82
    0x82c0c050700280491100c6009022001d1108244070002d200142c85804481d4072401040b608100c0741088810400101d4091050460040360740c9081ea40b50190480c0402c100301011035068020038030010512013040002e10414020b0b50a09205606500b003450014a800e02c4c002c1c2d1a00d01d176600c4644440c10700c00304e58860360584070003160003c101a5645070061210004840030180c280e12050f6130014848088125551102c2c145d50f01c07c056034403990180d510407482d0701c0d203904150380c0340d151081c50b8400300024000b403c0001c0080c52114541000c030352029840e0300031750420f641441d004110360b44450200d000d095115080203900c54251003000c5810241c0c650000e17100c2c014102d00003051101c03581c000c41c020005d522032552000c54060170310056504000381700d81e0550080004002c1e443c031942c0410b45203000c240039280e07000002d894000a880303510700c06403116550b4441000e50307036030100700a81c110b0031130000a00020b403100b00046c0070044002c1001c0e12600411150f011980d8030381c0110b0f4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 44827927 1250 44826677 44826679
    0x10918020f04080f100209010e04020c01020910111e0c06210c07060c0206070c02061317030406230304060506120a030e04150f180207081b150f0a0b0a05 67
    0x1500d0b9030baa00d000d0baa0f00c51020060101d039010f03a101560118000d4000c035004440180c460040c40b00458003880002e52021034030b20415542030000399030507a900c1150030540c03000d695400c05512040c030000380c100a020b100c9003c980c080d0030301c2c403403800a02090550075107808a503105c1e143d604803002c0c5403058112494212108031000200300c150f501007006412124010320042041910f82c61090382c2d00e404c1601d0720408a02e00b500740e04010314189001300356010041a0750140d9660340c00b1418152820041000c0041d00041420320040e6071080c1031440c09035941c4844d00d44207417180e4000303026100180010740843d0711080040d04940310004800607541d041003c40e1090701d21800c0c024100c3e10240c2c0d03000e2240e0b0400728a50f900e04500b0801c0300544138000c00400c0c019107010308148042c50440000c001d107a40a004034000b141980b07000d000d1955420b4490104d0545181c1494180144400c4080755103020000344400031640e02c0381185e008443d02c20008014510200040391201c0551140d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 44829177 1250 44827927 44827957
    0x50408040f15081506071103010b0a060c060b0102070b1902011805030c07060905030d080a060e0c032a0306010305040c03080301060906080a020a020604020607110630040201091802 79
    0xd2685003402010401c2c51150344a01c415121102d0703020300104240603099000c9024000480400d011000c5010100801070000030b0801d04100440c40317800e80b0741d0011020805880f4040140140c0c1e00a0040b0303081e00348050100035003450401081c502131020003950040001d00360004250007540000f80520140c2e9802c5400c000928280d5036960022004050f640148900044c203580255a410b0076a040200900840f90342604204e9001100500c2402031070740711900020a000715134003060042c08520785142c4d581c0b41c403040125144051101c2c1c0300d402c02d0b190603c20841d000d40c0083e00d420440034a408649615a070402d03800c1203450790000380c07d00d18004000501e86400812130801c44140e42c58818031580c0b500c480030228000c010819000d41c01401c000b900510f0141c005120140c0705807090650307444090041282c0c0d03017000303c11282880416880082e0b0307104000020f16a03050510b03401805180c9580020000c1070684103448152080170307001c000060454043d1005212440c240f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 44830427 1250 44829177 44829179
    0x4030c0503070c0b07031101060605030109111204030309020108070c0312021c051008070806010506121009020409020d1802030d03020c100e010b090105090c040b030c07080a030c0e0a060e04050408040f 88
    0x200350700780d40805d000702c005c20205510000b0284041c01040100c88080c0c030780c0c4c2c3c1103030710b03004903100681000b8008001032541007103040c0c4405810600030303000702d010796000280c0c1030f11480050107444014081c40140200c290b1044000ba601090101c040807c461015840d80590040001409a02c15030641300600b414100003051110700713400301c11030b5003c078101c51146988003603590b150042800b0741e54105100b0030400c0340e00d01785c1030000341c1c11003600da0f080b80070700c0d070b8a143c40340c1240c02580280801d150000f950f070f4000a141e001d0389e2079207454180441c60b088181c0c0d00280d614031510398600207054010405481074402070248464805d90070805109800500c6000b5000b03110040c1250300c541c0700300c000880d040c00c080c040719100b80c10001d078180ca0a410140c0381c0b001500001c002d0810000c013089200c0c0010010400360a01d40c01035103011610203c0c208010341003c9003181e045010343c2600c1c03010815280c0c00400c1c00450344055800046a8540317041110903449103400002e00c1d0303244188 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 44831677 1250 44830427 44830439
    0x26041e05030307111c17060a0807030f0501060911120405010f0207050304090c030203040f0308220b0f0903090307090b0a03061b080906060907080a0608010c0c021206010e04030c0503070c 82
    0x50b011290180f0100361501503600568100c0301d4405040058000f400980700c6c2c880e24254144015040b5000401080000d07981e455024907000c25a041204c40c00d101c10450b40801c40e00340240d0028080e580070901000401c1c41e442d00d018001c0b0307914001d81d4540380011800b401001c2d400740d420040341e41c00556480320315080143d0350f50700030710442e042a0315014020344003501c244203507030040b5030100800707120040f1520210b0b00c100c0c0180c8007500c500c0519a40c071104000c040e4028032941d1061448040a1510716503203a030b4002c0040511070150010454059203548c0400c8100c00c0d9203030311400042c109809004511400e0b0f9a420003411145403000d042000d038201c0b10703460032441c40c5a464074207a99450090f0b239100d40c426034a06400100490116070b030740c0d0042c05081c0d482803000800182c03855031044400d00392290300301c81c04040b401c6c0787d1000095050100040d040d142c4d00400500075940761540c0c44111440081003d0100411607440a003000020300845406d00d400440320609035484117 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 44832927 1250 44831677 44831687
    0x315060c020909060f0402190e2502070509010b0c0a0c0b070b130830070906020705010c0c0510090b040b25050a080309010e0a05070626041e05030307 66
    0x19060b031281e1002000503915002c001041e0b44944c002044400b01c40e01c0d550b00b40003900b0400464003496640004001c01d5440d80d520300280305031601c070402441c042c044640c00d0a03421303807611002c045400a40c005e11090711503a004504650381240d1181e07175079880c1594507040500d000740007880001d209400044513000170000d4400b10303015814002542d110740c4c0e0440e1240806140040080710203211900d8140c880d203d601d01c40300c902a0480c86400c460b05815545210129403400c04961030750006d200650341001588003800080c02c02207541844d40c1c980140300902441401c0c410b0070107821301c1d20700c40c1c40390f0120f0380200140d1801645554841070260300b941c001c0900ca0040b0213034a8100c00511186421a41031142c10001800152050391144001a8170041c6910a550b48406181492203002c1100300300040c042d101509500b410554024900f04110003207a034074025450240210b100c40e400c100781c01c90f40c002140d0320010b0088011294150318000c01410b40c0c00080204000d454000e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 44834177 1250 44832927 44832947
    0xf0604060e0d0507150c03060e1015030b0306041704030b04050705010806041a0907030b0d030e100206041e02041b05071b06020c01051803121b010603031b03031506 72
    0x6400303890400c1d5a02d84125034502070303031303001420700f00b4141078805211083d60301ca1000c1c44002c0c0380104445840303035020400d00301c0664440300141d640308420000620750203002c0040c4a0549410700448042400299403020060005050743c40f040601c000100103000c2120011036105403040343c5842c0a0802c60388500c05c0d8410310740420f100318000b034504e01d40b51040458040000c0c01100070a6050010301101d048001c00860505560765103100d030365a540e2448031095486030f503c89030380c00e0b40d00d024040101861a0301d18159403205040c80300040c03041540c01c1c491010311980d41601c010030300006000d01410407861541100401e14030380c001340e206004200366409800691900c05040d840002c0d100b145100b03010050b0040324000c2c0b200d602c54001408501e1400301100b680c1000200000d0414000d070f0301140040c540000c00410719005c030b610714100e041240f07000b000307001e280d0348000d442c1c1403d03486921050801d1107001401c15010342e008030346924004c0188164580c4031a000342541d040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 44835427 1250 44834177 44834201
    0x9040510060b03010b0a0e01031116020a1719062903190506180f0d02061e0103050a03050a11061501090b040b0f0a0c08030a021201090516110f060406 66
    0x1000700c00700c1c10750061001c0307078100c94050801a02c4c10f003d080c81141c0e0411075000c0141010340b42ca0b141242e8164040180c0100920b003156541c003500288100308035481990b12190705e540c4118901c0300b0f00300000c5503074021054207240425001142c1d191810043c1030809030b091054140403021240c0b25156001e5a00903031040c1c0840d903490340c0d11709040c0f4603a25421401070040c0e00040004507030b8041c4051444000c0741110445400681c0301f030b801070518204506150041e8000310800101c1004510318a00d1a08002c00c0320005506544980e5152000d0507009811f11070000780054504c0d101e800142d00000281c1d0582d61a410075081604141360500849400115401070101c2d010940c0c6003103800300c1e0314151401d450040c81c01061072964101016020030b1000070000c1c4c4000c2144a0011489105d51603401659003800c20440640900180c10039110a494401013028080a40301140000042c9080500d06164200c04851803c202010b0b0051180a1302080c4000c000c026009415030100d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 44836677 1250 44835427 44835431
    0x90209061903030e0105070204020c030c0601050a03031b0f02090403020106080f011a090a02070b010608091b0105070b0a1d06040209060d080403030c03051911250902160209040510 79
    0x80d04000c11034042a00301c0070003003000d03040e8010000607000e4076065180d450f042c1801d0707007040c1c0103400140032038001450544d031903000010024030110301032101c00e01504c4203c6100d00c3c00c2c1e055480003061000c407140d910700c1e0740f16080d041000340841e0741042107213198002d01800291519180080c00390010f80728014043c0300d00326a1225044042c00b0710000c580700103000b003810803481e20401042d240c02400c585a0303968200f20b0744010848500516000e000035441d89003d0381003130f5082c14a040140d24500c041240355448a01d0385a91150854024541100e59040c0b2900c42003082d00c0200340c540c07102544201074888404445101280091250740212000c00c1c03d640c4210501c030340012510002411040704001c01d00020340286450b92525000b494014186036114801d191002001c90004000c82c1c2c2c1d01071100003035081040700180c0750702d2960540151654841d904201c641c214069112840d40101e180c8654810015021240c190010300701540c0d82000d0900c140c5403618807090b044c1e064 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 44837927 1250 44836677 44836681
    0x30f22080313090e100f02070807050601080705010c1e240903080907050607080c0114040b01031202010e06071409040207030c02030d0206011503051e240904051207032001090209 78
    0x5015101d030103010b2030018040c01e04a0300b0005404024181c0842800c1d0031b80d07082c0000404075080c803000c1e154240c403580c0100b20550402c9052441c02c2032603030000d810801720030301c420700191500c402e13803440704102a80b20700580307414505107580785a0240f81d14a90202d00c40d842d082010281c100c0700c0001d0081c1c86980c013541b500c45020341c4842e03a034022150828000c01c00c103000251f00f040145034200b0305500018000c0782c0c50f4140350300038400303480907180984900018011303c40c0d80c0d0725070f00a40005000800804401003441d0b512020010051010700090018101c039120400d801c94900c2800104115a140c0140ca0f014108120400044c2e00a108010710210054000a0f929040c1c0300c1007000081d81d942c07060030807800703400000d00c21030b00080c1d285100d048019001500d140220b81205501c0000050400901000701e0224031640c810144c0c5014480800c0c2d000c540b01100c0340700054036680d64070090405961460204c407141280000a0085140194065104001c41803007101d40484603 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 44839177 1250 44837927 44837939
    0x10e07090b0105090a050d1401061d0a0c020a02120f01060b0c0106050102030403051203040f020904150c0906080a0e0c0303160302060a020703120b040f0216020405130302030f22080313 81
    0x540140b203891500034900010901c0075181540c00d101f0340398410516100002c00036070302203003503400640c0f00e0380040380040c0360342d80e045021a010310303031110700102d04100040070828003d644080c0d5203c040d018038100ea600e604001c0042c400e00d548004100d000380103180d51041002c2e05a841030008240c2946421004202988040110790440360800020501c2c03c60300c0d519440e503944050421507010411800000058484e80c03000ca00c55402490b000c0c8115075454080001d45850207040000c00005c0001405603c0d0030222003030f0070141005001400c100d803003161a1900341d02e0103c9552500c00480c40407002584140ba5480a034403a03030a949280d00d40c110780c2c105031700460034028081000200915a030030310355485560500c10003000487d1450000072801c04030b0b44114032036a51341c01e40509480c00d6007407a00680d900042e0030b40d0300010640c03203500c000391240a10000743c038000200044001cbd00e11000e1016000e9407610048100c5041d0f41c0e107600c070707940b07500105807100320401d501030014038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 44840427 1250 44839177 44839187
    0xe030c070f0e0412050927041401020a210204090e06090106060206070e120a020406060c0203120405030d050c010b130c030c09050a140102191101090929030a05010e07090b01 76
    0x925400104d4040c0e548602106865a42280d41c825030040361228600c1c03224045540d101c0d03400c4290900c17030502c40c146402e101e0075042c10703500d00301081d03801005000301d2590b1280c2c060240181c2d2001880c040001c0c116140064403036076100c0340810b8141545c0490740140403031a130340601542d100030407110355205410f83c2c0b140404c442d40380c0414460103e1841c5400d201006020740584002071300d0281c4141e0b4001421070709190000e0001810a061210450404000122200040100084c10316140000003551002540001010030130b001c541c1d80c2c6c1c0030078250407056030104004c00600400d60000164801440280d04500009040404291207903001d82040400e680007e459840c0590410b00014251400007040c1070452140000c0c41071610381c041c80e0348054034420018656000c507800001003103100d181d04000c540c24a42010003c4070b4800411103542c02078078040410b071800c01580044e003001c500900140003075003050790700700e00d0603008145182070b0f580303900c41002601500001110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 44841677 1250 44840427 44840431
    0xd02040e090c03061314010518160b0414030a060507170604050402030d11031b07030204050105090f010909030302070f050706110a03050301030602030a0e030403030f02010f02180f03010e030c070f0e 87
    0x7405410882c08a08001c5e070714892508107500500b202403c5105083c03606085540c1140c0d010300071100d610311400d044209010f81030b4480301d59444201aa0b08100081d42d45d480303107102d074110507000c0040080c815101403000350724190700154200a9450501c90182000d036004110342081c01c134400002c3c01a10341482007500a50300a00244a9552150010340b4804d000207100505440140640c55800295600700d081d10910800613040080c40d61060005942044e001140300e0940e0004003d00f407088054640d0440b00c1a40c4081030001c01d908040e0002e00c17407440080c01003108401c0300418008005019800c49045659000c4070001a500321510340c802d845d40100042e000300f0040001c101650003441c0c01c4030a295000801700300e082141417450740030781d1045012581107141112095028810302082e0601d0320750951030202c0c040809210400e0b0000c96038440c03103200c1e42c001c0d4503132001d40c4050340348100001102d94a140c0041c40a54901481c49400c00781c0030880c0380410101011680e01d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 44842927 1250 44841677 44841679
    0x70b0a17010512061302010201020c0706020f07060f081605130b0306030d030501061409030f03031906080a03050d0f0b1306051302070317180703150f06080d050d0e030d02040e090c 79
    0x200032174440c42640118540b4541d400e904644d02800420321304241800542c004049680050080c1c003075804d805820318150b94070031780607c01003050b09000180c10040c5a91300c00903642e58290b211010b070b40e0595041c022181030781c1070701072039600108020b9500c0c0011401369108a007200c52425010504800742d5109008210016034040381003441c651060024101c4810020183c82c074111480d0440b514541045640c80c2d0082018403508000c036950703200d80030107000310078041d02c490050342d28041d12912036000b2040906aa40355100404a41c0360700420100c0e400514280b65108030390890b4024100501400c1c0c8030744c2c1c00b6446026200103501c00c07180b06a505803100303440700400084054048100510b2082d440e4949240121009024400e10340998410b0440840541c001040311003110100c4107a05d107081d10380842402480300020b1240588c890500d0f0080c1d807107212242e404003420301316042980300d11012071403c103004042d80241c0242c48008480920070342d5640030003030350340c1d003070030202 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 44844177 1250 44842927 44842933
    0x151404090519050309030627060103050d0807050c01050a0b03100911060c0304080a0501020d06060512041101050d0e01020703140f07030507111201060503061303080105090702070b0a17010512 84
    0x2c500c80718601000d003420602a400352400c00250002090410300304898846140344840301a14502c99040100c001020b50340d402003400750f040d5503034680e81c1e100641240c2c041c0034440300058141e501c14812521080c20b000c0003801107040000c0d00b0000340840700b181c1071107402452103a03101c01c0c003288580d40d1599040111203022070400b4050081c20303480203a083c500380c0030400021034204070411075408040d10800006039580700e42c0b130542c0c00f00d5540340c10640800c40c0c100012200851250b82036a00103812104503d800104400145d4092042c451722120349401c14805290541042d4040c2032000d02940341e80364054203402443e0420b1282d021803094810041c0f11000205c0e1140e00078001403803045842202c42d0910f10001600c0c0070074a130003c590380e915800207008600b81401001c2d0480402090903240003199a00030b4001d035014001e044c0646c68840004031224800c210000040080b51801036541c55002e200501030b11000da41c1321105020800009007505003c4142d5103550540030203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 44845427 1250 44844177 44844193
    0x81b090603060409020402070f08040e0a1b030e010b130608070803030c0403031101020f07060906060503030c0a14030906040314070501050906030103060b041e09061d0d050f0403061514040905 84
    0x30040240b0b04144c0998005509002e00b60004030704614201841d801401140d07166031a01070b000b0b9082c2c0005114150090412180e11206000100940c00710700c0c207402c003c43c0d490001d5071140d00500403000b5159100c545142c0844928805603c15000e0b5009101690704590300d519256589110507120000d0445c000c00003000442c0c801d41d25419110360b40400540303000c4080912002e9034100e07010a5603003680c1c62190808000c01d03441440c0052106601440c18518014030b4130740c40c1c0c61001c0700980017022800c550b070f18221062003101d4005d0001410952a40d8582c00d05d096039002c14800e8500501c2515004641c03907010302c003170303824043c0c0c01030413070b8650382c03c1d0b90380c00c00509110003440e6000f41c1c40b04c072640c10360307c81d1a103003015001c0301c010b000401090307604200d015100d03144e03010b9082c071401c43c0105007a940d021500c070344504558280b0030b40d00c2c034100000c4006c40c4a681e001a100d03620b042c510640c442103080700e040c1110103481c1c031a9004903032602000115070806030010029808814 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 44846677 1250 44845427 44845429
    0x3020102070312050c060403050a1701030c15050d050a05040c0b0c0703060c020f0d11100b0306270d020c010f030e1b01050904020304050d1e02060a09080415081b09060306 75
    0x103d00c44807600545841810110031074400751402c40c00f550f0407800700c2c3e004174068440da036000084240803d2540398040584d403440d00c5684000096001d008041030007210499042405501215444040404200446d03e1b00040000040000341c0d81100c0640c0300d03000002d40b48402d101600c46400d115000361400d24071f9a5602c50081c003a4440c45000e5000d0304100c80a2448240f14911a0100301d86030300c03c0a04200f412141401c10242c01d5107000c61410544242039200011206d074480c000d11000d04050a80131800c0e51840e040342c0409240d0720030700165000b6180d0200b042c0c2188542a00e0314584aa000c90007174069407241c02071092103500003285900c07c11218080380190302d0041c180342d032070320038904040b8069a0007260140d41c0c503840140280310041c0d102040e40b0b50f280742000e140030060503282d002510303040050003010109888420010074002c0200465009114041d03051004105103d0081c00340350781200c400c4080d462040544104440b52421140e00301c00007400d0500c0c507a2840 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 44847927 1250 44846677 44846693
    0x5030d0f0516050a060507030c03020c15040503090d0507060906081e06011b05070f09151404060918020306071b03050c070905090a0512040b0f031f140108010f030201020703 76
    0x8400da5400080b41c1001c10118000340084840035004090100b441d151a10024081c0c3d00b010300c030b1008141c810856440300d0342d000f048101400104e080541041e8940703043c40c81c558000e82110030b5008a504600008000700050303800115405520340d00c010540c0c1c2d074410341d59504102c0e040316580704415062001c48020840150307010005060042d08180c0e481050a400c0840e0741c1c084500c0d07440940d061040040345122440101414101800b841ca072448458050803000e10650201c070900049282d1160b8440d0402c50240c200d1000420981d40c4900b01c112224041c060141d000f0701a980200355440d11400100b04100b501c1c0e00c07054044215507608440650048040b41481e0056441c040b85022060213150300644500e4020249074108d820158101212849102441d03a0100400c104007100d0009956054407002d41d01900d95888a100e480d0444952105141d500c100d52400b00e00b4030b03d01060010900400e9803581039070380c0c9601195030030404900010340903901601c0c003000014051 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 44849177 1250 44847927 44847937
    0x103020901080a150306021303020f0303191d030a08030402091b040510020109230706051c0e010906330e0414190302030712020d080c0a050c1902040605030d0f05 71
    0x248900145145d07261161030480e0081103a00d185690456020019441d00e10903004281034100c1c00740d4034280740300c0708220803144240c0051040c0140902d06d00d20540d0b03a00e40259240c0c00240c00c0d134501c40f0592514800c0caa2088404034030602a0501180d02c0314003000f000c144052040030a985000e0818040000e41019162031204544d01c1d08007501c001480c401000f170084041c400414039140f8550704080c10403045400c20410008107100005100381202d89510481c08203401c002540082c602144c0d01400d91224040c01d42d50030166150b6071010003440000014000b44441e900d104085440e00c602840c0622501030404100c00124010508020411120a001d0780849500c5580c04951885418020030103401580011411030180301c624066a180c00b0510320140041c00f40c1d020016003c40ba01800359030840602291010030039000b142140c06543c000800c490309550004550800c401c100700c1d04a0142e410040000743d9800d001401d07803c0d130a4907841d2003201c2820303118211916004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 44850427 1250 44849177 44849201
    0x503060d0f0507030b09030c030304020118080d0e0a050102160302040c050714010209090f13030807090f08030d11070309060c110406031109010e010b07020405100f0b0403030e0103020901080a 84
    0x44102880c0008501c040203a02451080e005404010310f1400d051030414001020182d01e600100b00344854150044101c0e580242d090a250300c60f681901c4000c068201c072038128015034420203259000b02c58000c48100404e500451380091001e481d00012a181c012003444a06841c204050a00040c6001e400c0007410416901d0301c00d007416995220303889030450104d0451090b941c0000c02540d641441014145e11181d610f006c10810304050f151002500441c40c405030411000801154055102c0c01d00da00c014180005c0014080d500c4902042c0c0b01d52005070f850308107a00d0130700000004801c4100743c1d0601c0d078158a41d0350400d031420f0b00945012004031811034400002c80125242c666852154102660188400c1c1c0f400080e0740c4240100044181c01503401084807100420002c45411f0440380e40ca541581c0c042010f0f20f075020804014801c5800080014440040101d4038008000290003200c7c06691600b410840040064040344528600c02d1300050050f0b000402e41c880ca500980c1d00081 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 44851677 1250 44850427 44850439
    0x1a030304090e030708190306060e0d030503090c10030c020c1e010f03060504140105041802030d0e04200a08100f050f0310060f1a03130f140a0303021e03040201020d050306 75
    0x101e9600c0a0746903001000d40641890086c00501116070b0520030a00070700428240300303c05920b0701d40000c692113260300d401020864000005091560f0a1003241403070300300a0301c07101d00c001c601e0a000c3c014007407010014005101c2c001c48403a641c6801d40c500441039140c01605404010104011a141c00c44240184c0616481d0314000030325407035070b1207076a40030074015802d150294180410003060311a4000c0b101031000301d8542c13050140e034011404003082022802c140074041004804140a8180d0030f01c0c04115941009006141c0c0b40460000c207a42c2510b5681c0c2c104981c1c98800b1150004020b0183d040317104907030f28051215081510445021003002422a1024000600440240d175023940000c4540e22100030300708400c0891880b00c075131a1742e203548540c0c19172802011480b024801014058035605a078409281480000c0c0ca180086500c21000e4a01c90301d46401d02030060761003409900e844401410700c858582c2c050b6401e0720b0007076605070701901040c820144200d440d81c0026100540c4a9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 44852927 1250 44851677 44851687
    0xb1309030c0506150a060f0905010302160203061008060907030f080702010c050102030a062309190204030b1807091418030412150e0c0a090509070504020705010b03011a030304090e03 80
    0x140b02000268420403481120024020010080c445800500e030f00c040188441c0510310000d05412281c54400e0701e00a10703005803200103030840440c1c0d0824800340a0b4050140c1014001c3d0040803401710400e0312800341c2107403015181e03581040d41d117009510000d4200300303100d03022900095128008189103401450b01402250f19529168220380c01998403d080076581d010400040007007018101111101c2c3c50751101c115580f0f0049240e10800402c0301e4000d90030f22013103811004913a815100690b410030001e0f00303c1e01c0c1071040d03049501c040400710324041c1700746400024011074a00a04850030740080e07082c96280c075400d142c01030103040c030321580d001d83c0000d1002054404440c0e140701d0446024104002240e83c0e2041c500c0121151800e81d5031240c0c0001140781d1458a8000c840e104981c100d020014441e5205461503081541c01c0e00155881400011402cac20b0010540205441480c00c5008210320200414204450f814021090350940c02c2400104070700c103201e40c8400103400244c02520b00d00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 44854177 1250 44852927 44852933
    0x7030509040c0c02010e090c1602150c07090612030c080306032a130605060f0a05040305060a091a04110f040b060c160b090a1701090b04080903010c030b1309030c 71
    0x1031420000d040380003e40c82010001550b920461340402c000054440718094104a11400101d214030016100c0c01c034149100c0800319100ca01d0f00d0002c41c140c1080b0f05403942040c1c2400307a10b92800348200d100c2c15013841e901003022240881c14005e2550316444a41040d01c55560346c042036013000f014141e0600450141e501c4668149401154400ea8513401c0c117007250700841003060742c0c50f0040a50541528107841441582c484c0c104884480f0144e154154480c1c0c03000c201150180b00303030f810080c00e5015000038040500f0482c1c11a8940a11400d03175200811848504400300d40c80489001d001c00c855802000d02d141848644101008070240021440e03a1603a004200c0d07540c44405803a0079644568810b2407000d58a14000d0040c00303008448518100e1890001a111178041c01510b0f520301c82c0c00580c0b647c248095002e03c002c50b0b0b0010207549189028100b000c055007100400c140039500300132190404900ca441208880c80c802049980c1540740e104202005207500d440407030074800d200d003851000c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 44855427 1250 44854177 44854181
    0x7050703030e0102010f020301050901030809030a211704030801050103050603010608030f0d05010f0b190e100906030501080316060b010e0d06090c0e01031208100906060305010f0b0309030406050703050904 90
    0x510700030345445084a81d40400242141c03c8001d80e04001441400184103d81c2d850201c181100d41107441d6035280d00103240042e00748400c00000909058031202104c12214000741d206049014a440f51001c09032400301c0750510860855008000900300c000502c0190300a50086401820180000405c1911026500d142d540b0a0240181c0001c0204814800e00000d0068a024200310703900c52aa003480c100300c050b21806003082d030103098841c9a08070541580b242c10705000c04080201119509516140c014219804138082c5000280c286000424681c200208039940204c040740c065240240c1600c0300f400501d10246014100506941103c603981d483d07982c004051802610300140220240c42c0441060300703203a2168240d1040d200040001c00c0c080c0c481000000342900306040240d07240c1d080442d42070b28640040840c1403404c1000308080b035040d07001506070307210150000d440c641c55000d0360703080340402c440c0d60940358010001400b25a12460140c8200c0d4428100641414001000070341 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 44856677 1250 44855427 44855429
    0x3160303060f0902120105030c090103150b10050d0c030b030d03180602040e09070501021207020d0f02090a020432190302090109051911031303090914160e0307030204050705070507 79
    0xc142c010407115141c0301485e06150041104400406010345010089600b0782014800036060414214140384034031910f40002003420001032684000743e0020300c0c0a440d6410a620661400745480854115213000f4860791110b40001001001c441076003800440203041e001c0709114091034440320a2000a10b82c8c0007400203030031200003010302c52400303145061030a1800c0d48824110f40c44081005002d0200a0440c2e590540503142d1100d40381c003605201100f00043c2c5002908141d41b082004500d1740a42d001e40243c504900e5031b080c0c03484107000d2400704602c0795221911070100c3c4074940941490440c2d0500e0002800c0d4400d003080c541c0d6034000411480090f4030801401d602e40e4100a035103982044010800001d4013410800c42d604808501000e0000602101a900c03814496006244c014003803000185400c0d0003c0c041c074030782c0e114641c0743d00100380c3d000155003503a00b00c0d886010f40207490006088030043c0050003a00d02c2d640070000940006052207090060400c01e031000b162050110318 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 44857927 1250 44856677 44856689
    0x204060317030402030f060403080402060702030312251403070302070c090f0b010f022409010608120a02060601170a110d0f0621020901030b0403051204030806090c0a0203160303060f 80
    0x19140d02d004d0050508020900700004690380004080000094100741d01c0c0c0d030003580603151213864483c0c920120b031851103401d40c04580c03080418104240750380041c800e036062500071000d5400302010302c0350036180000c11860340d00c041d1101303000081c2c80c107200340d01401c54140100030124403175a0b214a038500302c62418404410301a1601000380c0c1558100041c03000405907172000705415001c00720321203401c445101380820fa24401001080d0000c0c0c0035080700010307010706410b48480075201130041016034081c60b05140075028080c00034180c0e6000f85240382c101240000102200d6442015110061144104681d0b01c8101480746c51103810252142503018055000005182c2d400c205000800c0c1c159494481c1c00c50715200d01c04c80c01a2541c03080350b41101e1380440b42050b80c0e00d80d480c060f2094043d503100c0c3c00784414804c1c104014158820703030180c0141c00c2550b10340c4050b00d407546040301c14491041c048026030700070041007150008110a0220f4035001e0310300041d041e6258a1009540e0308a64025 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 44859177 1250 44857927 44857973
    0x60402010206071407060c050c0712020915010804060209041d010e0f0303070207050108060a0504021303030305070c0309030b09070807060504080f0309010e01050a0e0303030c040603050f04110d02040603 89
    0x100440d40c040000c650483c100b0b0030400c551100c00304a40a951141c9800246503940381c0001c030440c14060f0068402e000c02c3d09081d5803040761980c03882e01401d41c8154007644280d03023410110700250b250300f000d80d5500d401039585001d07035511510348201a50043c0129a0415542e8482d0003080f102c40d45c4840c00700d10030b2000400e80c60700c10303400145402221590000160070070000d0104290300054002d0496000b0f082c510107941c0c846000902c004229808260001c0c00043c849010001702c07100305064a2081c0c40c100903545a800c400c071601c0f05482402008681007410074004507800d1600e865024150504462006840300140c030700305801503100c00301041000c2824024030380c0034048940080b00c40c5006509001100f00000d040d84921204981400000105880058824280d0070b900d410090212680c0b81082d1201c01c1c220f0b4824411940040e05d0203010500300745600320039501540c0c01c841c101603250b07499020464010307522603080380d10550311100000041c2c0c0138260301d0107003145603c0d2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 44860427 1250 44859177 44859181
    0xf020307090e0d020606030309190506070311060c0703050421050d030b030d110709020318030c0a03030b090609150301090c08010606201c051c06031502040b12100e040506 75
    0x1481d4505403042c24143c0079501721030200480b94600201b503480e112821240002c120182c654584803070801074100c186c01c6400000c054090680084800e90070a8452046a05940c0c038148802010301800b4001070004404000410100c03001c1c0800e1501a0000d815034600b440b021364801e0f213000844036103a40401d0712078a01d070040785001c0c4092442d000c1e107414540054001400c6d100e071100794501404170060340c0440410344451a0030342c0c1011101500007202d6803040302100c059510a030b180340c110002420182240240d00340341400038010340c0f01426141240c0c64103642c8500300112041181e0301343d03680e072030711a000c80c4c603100f00301d4028281c84000007803c0d07003070000007003180340c18040800544130042c0510001c05000100914450001c441141d0b402008000071561446442000d001340c52400ca000c07400403140c1e60001c01103074401c03083d45070665007800e1a541a4015480340c661001c03400d0040185803045030140c2607114120080c8204800c0d1503008200250748140d9050740c0b03642c0480c00b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 44861677 1250 44860427 44860451
    0x110d02030f040b01121a04030c0203070e040605060103020f09010c03121107050d020303060109031b0506031503060601110a0605060d06020309070e0a060510051b0d020c0307050f09040803040f02030709 88
    0x40700d83c00b412138170103606480181600e07142405500000e050f48200c18a41c009030a161181d200c406401d640201a5007031242d0f40c030401c86400100395030a840c581c0c9040d01155582d0300900c2118070b4203458959072030a0001c1d42c4019103207010039250a800744100c41d0a081c03110015480346411804902c50056194020f030b0600c81e107408004143c6105660080007402038503038100f04190100da41c040e40c102d44140d1140e40c0114a03803000d0340320380c0d0801b60120034060682c0c5601c1c482000400e0540c00c441d95542c0341c0b8011101c81312034010706030862700301000030b5002c100c042c2c003c82d038003040c050101c00e0410040d81da480101e0b0b2080b107030301170103030403591051000110402c815a04050000c100f0f001203800c0100295044440845010038401c001409080c0301050310348040344101154282c450340d40b00d0300130180d280c20944011920901070031801041c3c1d458482080c1e80c1c0b5410140140340556215a40d00050b944094400c0e9000c4040d02449401a60100940c101030510600046100c40c5000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 44862927 1250 44861677 44861693
    0x50702030a020c090f01150302040503030703030c08060a0513020a1b060b0310110a0503061c0302010507020c2d010215010f032001120c03062c090d09030303110d02030f04 75
    0x1440c901d1065138484240720261101d070103110f0540c0c0c08400c48100c4280100400e5000b481954040d9406004c0461070109042d0181d104007120350071911140c05541e1084100000a03103203000340d0b6031000525007084491001640545045501c80c03d005080c240c55800300e4500074001c1e8011030b0403640f2200494160308092060b080e10f46142c4505010418404407031441034007c110010341004404800136005030384030401d00c003074428200d01c00b4103080c00c10304000f4087d0504407414405440f5040f0b6403071382420402c0d040c80001040300c1c01148020011144d20b454036848000890451240c02d00f030300b851581001d40c0e5030082c0010880962000c2c0703549000e41e00381a1403c81107454800501007070403c0e036045000b00703100c80c1c20700c0300001b820b066812080c0c00811054000c98451110440400304a0170f54048403c121141901c4040f420341d1202d014503941c642c59003040001880806081001030302941203031505e1103c2e014641d0030310161304030782c004a8008540388444058110184400d101d124 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 44864177 1250 44862927 44862943
    0x90c0603040807051204030f0b071b0b06030601061d0f0109150f0807090503060a05040606080a0807110306010501140f070605070e0406050103020f090f040f020705060a150303090b0a02070801050702030a02 90
    0x240e00c442d01b03280ca540c0f035000c041e0110700e070301030850782500d00000c200d584100708035501d107141c0000070103804030700741003607145104c04a5100340a446010b00125806005140000048005484036024a5410800c0c02100c0070440b0701281801610400824900d4ac072240f802000c51080d0f86000c800c001da0500200070020180c1003805100c08007909009030340300841c2840d0302c0030610714041003644403441c0c075030300800b840e0384000c405001c2d41540c88104661107009002e05400307402411403500400301015150310f828030a01c0e020640c0b0580340c0c0104140b50029100c26000740308114241030032510b99100b40d030411a03141300020002d036880c00c460718241c0310310005880280780843c102540803000010380c6c812001b00c1481000245026041c3d03507038503080180851800300080d921400d007841d000713549101c00d44400c058030f420283c510003610050b00781141202d13059906c01d40f030030340b071b00300400703032960107503901c8002c40c01220000b003910f1009000e820302500f0b003540115560031404000900304008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 44865427 1250 44864177 44864203
    0x61b15040b160e0907110a0c090606020c0402040f03140115150206070906020c12030c071d09030c030301121b0b0306040c02070e06190f140a15020a030503090c060304080705 76
    0x243c1c82060042d40c4035100c200d03038072400d00d040115038070080126151070000300072001001244054800300751401142c20203800c0b160709400f00c584801585003040280d000794020000012070201c010008920481c095800b04018000001154013078101d01c0390305071065403c007590f5941d101e0100010694104006540080e0601d40b007580380c0e0030080f009480301c103a0341625204052207406030320502401e104450039000101c04440605a03902d05959014050784105981e4101c00c000003050900c000c000c90744400448000f9510356802e110361652003c9070b8200c242d4000702c0755101d00c804404000d0b540d1b009071604d068030680324030b0854200400c0e02d203504607580454103c880204800424070b24030359000501200c500b841101300c40d00c03141c0f03800141d500161400c1f00c0030038006041445811411490075054504a50b50758a4030f00d516001c510503402e19005900010b1300c0e00c080303441980a150000c0c02081681c100c60404c10005c0c10582080d5425502000000384981c10840d040150243d0010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 44866677 1250 44865427 44865437
    0x7290105030d080601031d011409010c09030b010e1e0403020f01050603012c011103070306060f03051603050411060d0b03010c080601091701060905041406090c061b15040b16 76
    0xb41410002d11425014202c60b05158480c144d066120407200031a078604400100200a581c289110003030103020140e80705201940703040f40304240c19201c1c461150550b5041400800d080e403820007405481e68005150b505c80911503c202c24060802e500880d0049001c0da00801d840e03080464141c2c00c451000d032015100e68540020b044568100031f10320500c5040105172455022981c1900320302502c4c00140c1010200740010401c4401501988480103803020760740d4030381603850a10030540898505864100040e006d200b9080b02ca18800e4200d82d1b8001e10034035400410751903000c0401c1840e00f10220f2001100d8440e8101401414240300e14000c4503007928240c02d0905100d80041d2060a1130b0117022004200c644494050341e01c01d4011600501c4c0d03281e0b0411003881d040c20a054855070900340c1d00a180544004134010203000251200310300c0c002461140780c40640c5400709145406100011090300801c0500455002c1562110748128041c44100082d0b03c1c3c440b8500c03090942040c50282481 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 44867927 1250 44866677 44866693
    0x307150e0a030f3c080f190c1703010b0301090f15060201061e060f0c050c0901062c0102070b160204050403050913060605030705070614010f06020c040902030a060506060729010503 79
    0x410340151954040c1e40212160b0384d0f550a0300008812482007e0000020660b08084880c200ea40300740c80c0054580a03007400b41114040020803040d512080c820009192014001440b10081d01d51062416500036040001c0301c0e85403c85800510036580d01100141c2d554000402001d004a603d8911030800201f21119150400b08045c0035014001c110788101b00c000304c00da00c200403041142c9689010000d100012a44e902d900041003100c1c3d4641f480c80400942c868540f914060100400d0b5008050b00949442ea0400301c854026030405520f03c000409202c8040c0056105c51207a107000c0e50295070780c5a5200740107000c1c400f4260004811403801032925a0800045070700c40103498110080e46030099a50340c09083c400080d2010320840318544100e580009046500c01038030500f25111a020395810681040c02c11048406007140039405400018000d0006201544174907400b24004003007034107200c8a52521191180d828011038180704021540c0711444062a40305401442c0c200c5c0108204 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 44869177 1250 44867927 44868023
    0x207080c100c080d060308090f090402090105120114090601140603010e06040f02040b160308070908030306210d0306060314040213050402060d020f12060307150e0a030f 74
    0x42a050741c104040010041d000001c10011008130313080c032070560074141708031030f264240501c443e409100005d116460490002c1035a04200b070407244100d8000340b1292240c2c0c44c1c4818803c40030020358510310070b9540ca91720240071440c1003141501601e000001000e86604040c102e8000e402d0000850307104000901c010030044450b08485035120304207480200d81c0707000c041c0c1c5070000380c0640c1e001482d6601c000300e60003102c88034103091554454080d90b41d0038101c0d21307901010380d0400454047c1203c1c6820400019520303007018180c0050300c00c01d054082c1c00c03401c001d01d00103040074080446480080d0315080308028003a49030007071901c28207241d01c0c11101414298005900c090016980b4008280c407400000d06658440081d251000c4201c5410743d5502c004440e100915407022080c030601d21000c401082c102d050010b0b00c0c005079100b050854203413850302201641c0c1c0d80c6007402926485220b4503c08000250030b034400c00d103154803e9440b0680003805102d01222054124460307005402003a603c1549 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 44870427 1250 44869177 44869189
    0x1050c0a030c0c0623060402090604060e121c0906080c250209070302040509010b0c1207050c0310020703020c010e030d030b0102010b180412020c0108011a0702040c0504060207080c 79
    0x12100d9424000b400141d50b400c281c0c0d420390661400342003149020030070000312046005540242107910f018421655503101000f00302d000f04000039030000030a000c02e00000d03001d40e01c844400a0018500c7c130046101c0000d0618010f284500351881d21100c10306c0d00c02c0c01d41c002c0e40c01000390030b07281880300152070500c405001a0080c2004000c10307031062444504011096038490102c15000b0f0042c5200786450000034010354018802c143c064080c4c41700000318a82c00d03c0940f4076034600e600140107948050b2459050036040381d5401c0d1038a001310004040140c0e010010514816102c8101503108e410505002e0b0030316070900c0605052040c92040b40d441542c0204001134142c205080000d0042e01c1321004034010800e40540980103c1d14071194032171a021511403034880c910400c18100d8607050031104a8480941a0115004c81d6035200107100c0540100d0000d056014000e08282c02c0a0040c0c00090544400d60b940d8808070f0320018050005c60b80c14400000074280701002014494804008182 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 44871677 1250 44870427 44870437
    0x31202030a0806010e0105071203050106110f060105060c07090603112704030302030901060801020c010b0a061b0b0a090803040b070305070c020a0e10050607030f09090b031c05130f140301050c 84
    0x4100204d88161405c50f80c0078800740e034800d94010f4059008140c014002400401c000e028850128040d00c284102c0f41100041c40001450402c0190180c1c0c1d10388030038410950014940918103000300d0001207a2615a889080000d5000d80780701003036162200e090025085000380d0036405411251040001c00b240b4103280d130b42281d858900144e49640340d2440a0051800350800d4140e5400052208818001500582000c038011100c20b49001d9440c5000d40b40042c509401e0390304145621043c3d03010446120845900c040200c4000c2017551050752044403641c412202120841c80d05000e005000350f141c841c850384500c860a08210410003074001582c2906144174001002825600090b40302c6c40d8201624008d00015060503100c0b00c6524002e0030320840071540800007405401c0000c0d501c041405442034410b0060050404940103c0680380040001c0300c0303020510104204241030031803a00e40703440041900d1420070b9aa0fa04050600800500c40001c0034801e030306040501c031040951070f0841e5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 44872927 1250 44871677 44871679
    0x14060702010e190303050d05070504080706031a0901090911010e030a0602030411090f041103010504021e19140301050f090319020a02031002030a0b01031e0f0b060301030606031202030a0806 83
    0xb031542d180402c0002c0101940780e4601c03800320030708803001080580110140c01d0202900c007041c0056503d00f64111040e0180b40705064107030b44080d104025440c001e6100c44a66000c14008015411841010900d01d070404c1c3d100d10b00c010b43d1101c0c680c06208108082c4042c078542480c2288141b084800029999089590b010b8040d9070f000010404000d40204c62119268025290003a1441c0c103040030040803100303d1b0180e50b0080c0344850368659103030611580f841903500611010603140d0481c0444003401400c0c50680c0c0059100c1200104554440150310042070314460840d114040c0c00145420340358003420184da80e002c0d00062004140703012040e58009940d104180d042c5404010080b40342003028000070b50540103c0200507241d943c1900258407401c2416400c1c4161a0110011021144c40c103000b00e00c11400d10581400422040d04440300185401c0008140c5140381c0c0b000850550082c5e2045500940d81c400c00c008108140400803c42c12a0340055410704c401404080c0100324010112 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 44874177 1250 44872927 44872937
    0xd030906050c070f12020913170f09121f02030103080301050d0302070b0c01020304060b01020a02100305060a03050f0c090601051608070303090506040606050310021c02030a11030709050a1406070201 87
    0x244408002004424000c1c44041300d40c9415503529882040f00e01c4010030141d0190400d40002003c09200300c42203803000e5807007a54032200e041010007030f106507000116821018041001803000c0d80d50340d6540c054032080d08002402078502b0700b807800c1c1b0401030306140000d190380c010700040021400d8603041c1ca0450f101610042130300c2041d4a0104d05200103900810300300c0f44013040444400205601840c41a40306420801c140c0841500680c0d480c3d920301c20003580250b01c0078900003210300c0f80c1c125980008002d0010f0342c00c90340300d60300c140c100460405903a04952045160100614000c10480c3c0c2011003800c00503c1c0c00b2a240d800d501c0c20b5a01e50000d4405c04000540c3c004062082c0c3c840b401c5160040241d80c41c03070506180c00d0001d04014420b4502c1781c42030013920034542c81c462007281e0b0034580c84400c2c0c0840015100700d03200a1741009100000090f518a0004d180c5800d030002503100f94040c4d0b07940d11145080100b00200c1c2d40564000c043e80107040b0b004d0150700c0d1243d004440d0b00d0f980900309 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 44875427 1250 44874177 44874187
    0x20705010209090112060c05120402010e041808070c050a0f06030e0316140c040b030c0f030a0c03050303010806010b04030b070c0c03020a0611010b0f011b0c03080a0905030c0d03090605 81
    0x440c0648030b54120b540c1c0050345030700002000c038000080080d503176100304018015032140704411521801400003031510007410001041c019030140400181c2c1c9080907001207803201c01d000314250104d100e944260350900340007500380b040141d40d40804006c0e0004075081c3c140181071084110481480d8001e00c4241503071445441081402081900d414020b110748120402d201d5107040c000100f00000f1000c00361041004050640c60a800b80e600c40b01c201800402801054000b004009c1940f0b24442e50903005138410701000c50032065040c80070350701030401542c0e42e51400a00a00d000c00503803143c0f04c1d9600c2800148009121110300c2138001e240d600e0444a0341c050b90500e1810f80c106030f40000d46c0401003640006041d0b401802d100c060044100c02001031005100600c041910078107903681c002240d82c421481d049200c031484e001c1780342c003840c03c20007040e0b141c0d0f461821692104101c807001c0f5490045c1044145401c00070810141c0090b02e0b65000d828003a90003070500307800b80c041c14091240120b1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 44876677 1250 44875427 44875433
    0x70c08150f07090b03040c05090f1b1606050703050601170402030318131a040b0a030b070807200a0c081c050306030a0c0311010314070f0503070905040e0706020f0f07090207 76
    0x9028000b401302104420741e241451f1400440ba0002d500c501070040144000241008410b6124940708101100709861508611043c0c81860340c00014000080a840000344011600611405201c5c941c291000146800d060b0000360242c01048045101c0300720715001c201c0123032000f000f51404d040350f030f819460002d410840025401c070307001d08100710014609540d19a5207249951800307120101607a08208583c0d5210900100e2000b40c000076101804001c0450101e034814600158040c4046c0f0300000800c13105514034451646081803d051a4172007641c40041c4594038681c1c0740240104c3c0d00500d0b1130540006041c190380703952080e5105000001c00050b4081e00d0a100ca50090355000c2203400b0007039240d15190346010100e1010394002441d045080c0b14080600d5410b40c02072001d91200035908140c541c0883c0c9580c03006203000c0810074034241c0000d10341c42ea40203551100180360003900d507031428500020310313010840031200101d13404110740540400001c03c840c020381d00c0028001d60b42e060380741 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 44877927 1250 44876677 44876687
    0x20a030e0607090f060f020319020102070b0f09010606050712111603050102120907240e040c1106061905010806030304210c1a03060103090f06020d02070c08150f07 72
    0x12800c0e160700900302007000b02070b446401242078070a010003044000c1d8482c6822600c0d1445064054090380c400c021a144081103041c01e0012010548009403400c885e66485103482142900c10100c070701c140d403003070215665082c001d420150000340f034000d00304082512000c644881000142080c01f070783c840ba07104082401e0001000d100b08580c400c0d03c0d600e41d01c0c07601900035481003d0707a841150140001c81c40400380416410111051280c8a0300e078550000d8840e6507840601c00e6a0040c03202070201c1d80c01d2038969000c0d00d039900080380c580d2442500d050302000d0400300c0c000c00b000e200e4100c111180c0072003030b00100350000380da20a1130b0013055a03880c480403a1861145d60000d641c0304d0a00c4200703560008030304070444e403168030031220344889650b503111400c0181c2000040489951040c0b00007007030f651096010f0b400082c00b40145a517180ba40b62181c0e402c0b6030021a03031000035600000d001c000c0c01000c2c155200101542d0000b07101c24400b10703400159105001e41a1040025a4004203040314403031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 44879177 1250 44877927 44877941
    0xb0312070b0711160306050609041205030910090804030201031a15090301020c1e0d02010c02060105040b01180b030a0612080703050a120509101112011401020721020f031f020a03 78
    0x1003000c8842c40e080550704d50500a145220455081d0f041c08001101800c2c09020940142e6102d5140c4480d0300c21182d0548403a040184900740910440d01501c1901e000c6000380642c89014007219a6114118000101a11400e802081c812418131508030750300c0d100d01d424900400446607155444030020000207000e485000880c80305481802c2c0761700140000b8100c50383c3c1c45401d000c00c440081c90103140581c00e0710210740e81e440243e001803004100e14101904080b41c400c0051400c10340c0700e11550144000c01c03e26030000713102c041010003040040c05140c41040b01a040c10150132842c00c4041c1d892060301d1140d40001810440301086a000b81ca009400c0e60800100d400c1d400c3c4030313516005200507540c0c1c050a420040d2241007004402c07034084020102d80e92003682d1008104540c2c2804030035032694809146e6141144035031000003503160031800710960080140b0455038842c08a5004020200c03050144492098020869461005501c42c2e0300f10000d042c417010150716003005803c154024114 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 44880427 1250 44879177 44879207
    0xb0316080c070b100501020705090f131a040528051903031104030629010e09060a0801020a020a110108070807030f0908030106020f01050906060a0302010305040c050d0c08010b0312070b07 82
    0x303d0303414410f94038104071640054480c2a03080b80c1e1919130318010005c4010f010f40f00007851714a0030000c034a40c0005a900f00c0410b601a01c00c10902804034000201c074100215001e4038a5080158420591088016181003404005181f048041a1504d40c0707500c814210759003403904180c0030303134040416000350450620407606a04658999aa908100000d8143e614038154116100c150b508900070050714001c1003484107a5510583d401000103000e100e1101400041d4080c14100d80000c000d0402d00042c002c00702142c1c041c15441101d45460740c803201d4a5124181840a95010001074a5020f04469880340c03c03480d010a0303440c400c1c00140000c1c6481c3c9805044070500100200e5034130740000e2003026004400c0000c0002d607a41c0441c403515071030183e0301d8039448480c0410030805584a82c2140360401c0c05402c0b504445642d81c000509891803465003118100c1c03402100f0021b07007100780303d140600c80701980901080721203000f4104580c03103602002041c03007802c5404114803030b200788461040c1c506 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 44881677 1250 44880427 44880443
    0x1052d03150405060c0f090402090d0203100c0207080307030e0907050405040218091003030e01120b0406080d0f090f2c07090f090902060706090317070807090b0316080c07 75
    0x1059160040c00044101d82c240e8081c0715000102d4204550078086500b034032898541d041c24204000e0400000c1d600c000340f140d51020021142c0e1000d603405100c06540540d841d42c0020300092458000307801c0c0051540040d031301d83c00c180010b0022a42150643c50450300488501d5042d5650030b400307465070f01039a080590003c1c4081156542100260041440b50200700c601e0602a0b4072061504030001d901e000040c0080d2034030820491950241d420049112089030010176a4403601d004502203500c03c1d0f102088640c001f9010500aa8002945500d0f009141c9440e80c801070802d44d11484a20162049100792100b0386003040c0790192001d144100540741900541440c200904018004c1c0741a00600c1754104038510002410305a521a04800c1603024080c07600f4510580c849000604a001c001d40900104507100340152154040243c4207868580304c48541c1e04100000800791700c1d01da000303003115200402c240315491705121324400d219841d07450134030359550f40c103103140829000e9418010440d003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 44882927 1250 44881677 44881693
    0x607050a0b010e0105060c071a04080a050607030e0f0c010813060f05090c0d030c110612010602030705061005060d200a0201061415070605041e03020102030703060602030301052d03 79
    0x1107030651a0a04071800210481c00c2030b626501080600d1003100c0c0a042c0650205500b00b002d0b1403511043d403a18034803000400e0500c0d07520650607080000c0c840e4102d40030f030089020040c42c02c0c0c0520944d0031880c80d85009112551509001a95484501072050f040c80514400074014034400c207204020341d64810400d1100c1a1201480c1d809810180c0b00e0542034000c0c00640001070510006001c602034044d034420206d02c01e00c0c0c8400c0108260420100d40000003081070900350910002c000780204581c1d80115550400c901742141401d8000c0d01d03910002e0b0300403034100700350307550791007070701c2444003202c00010b450080907101034030400c1d0740104109541c0c0003040309807020380c06501500442e2007655850034422a00001c0000c200400841d00aa404c0d050101c20081a25613120341d600c170348130b07020034012283d61034824980f01c5007549045006030b400004114959605009810090072140025030642d414900001c0c12031030b064040c03240001c0c030a01c00c00044075000c010440f480e00043c040d54409 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 44884177 1250 44882927 44882933
    0xe030d09050d090905090d08090309030601180e061e0604060f08070e091207030c080705100504050c01020c150a020705090108160b180108042402040617040c0608060607050a 76
    0x8850b800070440100d01c820b0707030010300390031039001d95889042102c0141200d83d485807400e481003000588640c0d1a0b2100384540c40058500304188c1d8060000c900b19066419808401a01580d0038440c030420b058022605200c2c0c44000e4140340046503280c20103c0001e9501d9501090003000c40e58803640c034100743c4000000c0c4001300400c01409944c0e03480c40600e6a523490824055a880d820622119080c008018104c082407248200220a43c880c000080c58002940c8945260280034281c5110640e6a541440300300300c1c1c20000c0f041d02e610207001405007540248000ba400d0300704641c4010ac00040002c0c0525010700c00d00c103000c0609401407000c1d90341d503180d80c0100d6880009808050030200c134108007050b0304081e44103a800700700c203101c000d8202c2c00d60100111021140030744121801e211660089140d00040031800c3c40c6070141c448010380300c528101c801000d406c0c9000007080e007407000e60280404940f00312124029101a400d00d06610b80740e52000c25164418071101902d9030241031215020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 44885427 1250 44884177 44884183
    0x809040504060e0d0216030b06011103030a0b0a0608040506041e05190309050109030503032410020c0a14010e2b0501090614160e0103021306050d150e07030e030d0905 73
    0x2010341d404211000f42c50040400ea9541481b0314100440e01111a803c00005644561a660061043c940100764008081c0642d00d540c0007542e4101030741d51a480402681d06086042c1e50040406282c00c0495080c0341c0c860545a801c017400c0500300190b40301c3c1c564103688031507000f03428440c0d2140844485420001013020f130010300c0782c411000a60382c1800024190300c40d40e0540d043d2074004002d5899074035010005c421220028003010182c954911042c851035941c1f4408442110858001c0d000c0c411401d0200212002d080d00100000c403035103241040c060340c2c468a4800364040a494848411700d042141c00d83c1511040c01c0313a4051141c0c401c001081100c19000390304090301ca4107003400740120951022550140c11035420903000e68103140740d030810340300740702844180006040042c60401c649048601c4082d03150001004202c0024904090380124402c905410309000c41c3d86120742e00700b0001d00140200681040101500c44001c50391420303061040700c890f40e0340b128007007000e203400f40f4055407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 44886677 1250 44885427 44885441
    0x1f05010911030103021804020f0d11030d1407030c1e0807150612020402090a17030403050f03090a03021014040f060221090d150609050603160602030d09080904050406 73
    0x144003800d1280c0e001c448030314101603d050300ea00802c0b8104000c0c0302d0040c2c0084060080050f07a00200c800b8043d4140d8603800b040c03140040c00703085911141380f503a02c2403615041348055003404104002844c2d0164407110025610000d0380761500100e51520f0381845c500c4188005007900203c2c0d9004001410012608018102c00c0d21480400c8440c044074426041243d4052040708201308410352600c005203803540c020308607500c009100390358880c1c41d03c80d03e00c80c101503082c0c4440180e00c0003c0520034044c0c10802d5402107480107008520300501031001ca9000007091000900403104d0009580394240a8081090000c3c0100e80300c6407642d50b100e01240001c0aa803144002502074100901c000440924150f244400300800d464a407006032002d0282008209006840340c40302100400d03015102e50140c20b0042907211008900781c00c00c10201070a046804110701c0004510060070010540c0200a0368a80142c03c0000102c0071100c5c104001984254a0000c2c0e1040c0341c02e082008124295100f06 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 44887927 1250 44886677 44886689
    0xd0509030418090c1703071202010518060402030706030c02070e040303020d05070e0a170a02090f010f050612010e18010f0c020d050414090a020c0706090e0717060906031f0501 77
    0x10b4007480a40384030100c0d50183c00c05019034070541010310511040c0c0d103004144554070000c481c036010507a00d43c201c0b285000030b1000c1c0141d4440c020300000c84400c10702c6c40749410005000e0300e00c3d4109903001139034420880c410701c02851307225600d410b0290300901c02c0c04000c108035801d108440c903081c81d0043c005d41c00002152001c601e400301150b10244590224140e100d006064140d10342e0510f01c83c004900070700b4480d1120740c031503040d10701c0050712081e40003401503084021007100c035410841c000d04214420b8002502800d401d003c01024500f0b0b15810504503000c0606100c065196060b0020502208030926203031507003012400044014964000000c2050b10303400c3d10709805190340b00b21943c0c45036109901d0200c0d580c2c01110481d142c0504001d40004040e4401407070101040f43c1c8508100040d801680492a0b081d0200151040020010750140051803e0000c81d16000c510781041c5101400c50341c024a84800010481c0d2010800b41c1c144d00c0341034403810008400300340c0e058050700c0240100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 44889177 1250 44887927 44887949
    0xb0909030702100302040803030402040b03120f04050907030b030a290103120305010e0601091a04030c0b030103060c2a03020a05010e0304170a050a1709060d0203180601080c0607080d05090304 84
    0x203c0c0310b0351080c4292015940d02d00042c40c5140c885408203c0900480020207074580106082604020b510500a16088084001c0242c4a0740b03010200a01c0c00303c02001c0f002490f04000701d8203425036000c079480c442d242d0311014010109451206540000003084d00022511540744004024801207a10071000d0503031540c0c0a0007244c0c2c8544400000400c1a640c25011501d41740c4240039038a00005c100840040200486003425602c1c0c40380301e4603611f82d61081940c504000014810b2107180d02408040400d00d041004030504190009030060381580c01c01d0300000a040c42e44010075101748107510f0100d40100007030107920041c00e011a1254094071907407020150022440010a1021130a41a03868000d000391681045684403e13042c403404c8040146a00c03002c02c140c51543d44c2d90302c094514030003242c00060701c918221a216154403400b4080d0540d56001c80010007140f0760004694941c13a80581c0e07003903205c1e102c80ca0a0b00c0d407801400392000c0c0080c1401d08000380040004007900855640c2c640d4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 44890427 1250 44889177 44889199
    0x5030f090c01140c12030403090305070b0a0e0d020111160807080a0c1a13080a03080a0e060c0c010915050f012306090105040909030c0201110d050403060b01030b0909030702 76
    0x181540d88400c0101035001c14420f490f00c0d25034280d0080901500e13100380c420b13075800e400840440419648111000c4005c0f07440b2540501c181300080200c00003500e0b8040f00103107058000030000d040e051460302154802c081400c203010459210b80000e004c0384030744004540d6503004c55844c44140b0b0642e801341110500c5402000545006c0018000250b55006030340740755400d0a0401c140386103071404079101410350301080008601300d00161080000c10146014104002c101d140043c0108030242106070220704001d00084500c0002c100701b508903502d07035005d9950700b2000e801d0354058440c146000e000080320008030062620180c01440c40b4503100c807804c10a580e2600801c40e20304030a40160361010031001c801507164100000241110001414200c0c18580d95003824410b03104244c80031800036150400160465801c00d00e8940c980180001601c546250050000d007140140e21014146076140e64601c07440d81d000741c0c0714600c201d074040c101c81240c0c40d00e400f085949a0010000700d029541d2005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 44891677 1250 44890427 44890441
    0x3060c050702010804080903150a060911071e030e1e040609150e15040207030e010f030b0d08070f05070e0f0601020c0d021003060906090e100b010906050d020408060705030f 76
    0x104940840c2d50585034603442ea21a900c4856240d0400c07107050f40c16100e580c0003820250401d00c44244500051350001c074038541003170150001e4501c81e0100c40c826140c2444010005003540028414510b81881c10100741c8089003030841d110003070700d00e5480d04a4030024070b00c0b084100c0401340075005401a902402402d6480790003000711b030030710310302c140c0d94002d014018000c5040202ea01c5412500500203080303c12102ea0002d4201d0f805480c084001c551040c90900b0b107560001c80d80c190b411035506003003020301c4030750003c1002d02c0030084000b04151400a052010000800c0740714100640090032101a0b545070380c800740c03505100b070302c0d0764048a500da000642150301c0040d981d41d14180103000349107442066400c2c41a4203002501080a02d600c2e020045000c00c1035221700030040409580201c0c00c0780304e100c141424100524805159a8205800840d00e070340c1101034034080f40c02520300155914400540003009000707503000105580540000c0c40540c541c4070015602400d4a89a0a005511885 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 44892927 1250 44891677 44891687
    0xf080115050f0d0b040302010b03010c0e0f0a0303020319050403140f121806071a2502010e03160201050f0d0902040609050412051b0f06010306050f090c0402130513050103060c 77
    0x40d00c0c40d48801c3c2011000c001810051003d60014401d00010503140e1009000030f00f03580201e05c0d10000600c80a4160072146400f01041004000983e0228040c42c15924001e487e44a00c2d0a00c145050400407840851446581214002c45d040050f242c8020006140306440344452800d19913107100344112516042c40b80000c95180300f00c1410b1000c407810f03c000500040342c104101c240d07102104040010038411001c1c440700d202e540100c288a03050303280030308a01960f444000045046a24101741c01c014400000300b2100ba01c070a11620f840102035500c0102d0740c81c403c1120b40303074030001d0104400c90401903640250b00d51520887e420312141340c50762030680c11610129401f0300b80c0d94a0343c0c10308180c00e00a00c002c1c00c0014200c1c00190008000a841c0d80ca489007801c1044c502d5445a4010028440d00c2d100c0c0b55008100da009003049414614503a5a61b40307100750155220300d6001805540083e0300d285140300510014040002c40f1059510900060034240300c1902c0702400c0401e068800d134864 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 44894177 1250 44892927 44892949
    0xc060d0c170c04030224160b070e011d06090d05010606081b0a0e0111070b041502010c090608130c06020606010e010305011214070e0c0304051b01080a05100f08011505 73
    0x30b030001400d207440c580800001040e1038001c881024401101105400f0300c110090110381d4551804405a40380c1c2e141050000200404060401c03040e045a10960382c1d02c020b880940f543ca00c000d8810954028000034111304c20003251036032203100c40300060200309040d0440c3d400c4071001d0b107582500380e0f0f031307801842c980f004211050f850300d00c0c080005850560081d00507903240c8606141031500c6900c0303a0100c1c1d00e0000c0c6034112109101c030205080050561030300c81c107000b24025100034464001c11030030250402c03505004a03c14810351100003400143d001840e0304020390032914000c030f9165180c1010b51682c030305441c3c503400034640e2054841a94000d0050504945c200c283e4941041c95644031000b11496661500105004a441c00550840d91602c1540258a007043c140c0d0380341420726025152290300035401050050704811288542c1e009203405a000400010100341c60b82c82021610154a2a801030b91107002e48403008510248150701840350031080d40488180b898841041040741182 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 44895427 1250 44894177 44894191
    0x5060403020d12030905010e0714040b0901060c050a05061303170705030a0f06080d05130806010b0f0304020105190509041401150c0c0803180f040504020102060a0506030c060d0c17 79
    0xb4403850a000140500c2e40c2e005460442e01d000a490344890f620b03036013500e840b22504602e69000480c24030004002141010300d100c1c0489042015103c181d021440c102c405210f0360302400398001d500805c0c8181803140e14002d95201d01078610714913008081d160007900810003580007584406281e2500f809400344c0038040c0180d0746400e03007190349498041014110103000c022a043c0c0703920300050300768020048880d80c1c00494039095200e91131000b490f5900a01940b101407294000401040200c60700720440b00c15942c5045e54540d20796036400107880910884004060f000301207490000070300c1c1d004e405090741c0030f001c6070244000641020303000c0c03803024280a0401a1081da101031041c00e40249500c000076885030030074a1074503564900407411500214002c0401002540340c918503460450705040026004440422080c1040e80000799210001400385902c1699000840c0c141c0e41c040191480c00100144000c3e0750707801c0c0381c4e40c0c10050305640f160350300405d03504001240c40310580e8100c03901c130707010b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 44896677 1250 44895427 44895439
    0xd02101104080303090105090c0d0c061d120601090b01030603020319020a03080a0e0316030305090108040204180f020a09061d0a020904050a0e0f01051005060c0f010e0d0201060506040302 82
    0x509014000280a50003544504403801c0000280d1a40107001071442502c0300e00c00001c8070700d00102e0640c10f0100c1121501d1040800310780c1e890010701011a182c0540f0940e1074910382c800d44103104140070305100c410f0640c0c801c240d0b0780f81103440b2a0000c4e0881c1030b02d0240f07005101c40460301d03005400b40c403203034017000358103400c01000e4002c602b01c10000207805038002418922003654070f4a4410701c940c000101c1030009051240e0300f8245042c1049040118280301041101d581c1c45c50314010910700a00315034034104659040803c09660b501d820644058003190300400300074051740b42020174400d0300d400c00c88c01840d2000001070f84000c24841c610845030540c0a1854440030031134840c070804402002d01c81030642c03e1009020f29200c4d4822648220200000002ca180b01600120320f0b020010017070880c40d03030420040214800f040040768084400070340311a5121a03010bc2e0b148c0c14449080e5807014650302e054a008101c80c400517000a2800d42d60b00200249038403507003480b8542c0700b1408040e400603 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 44897927 1250 44896677 44896693
    0x30b01080903040b071703040c0f0f0317071401060909020906060a020c0105030c070506150103050a05060109050103020f1e070210020105090c010503061f0f02010b010e0307060c0213022205030d02 86
    0x4d540d100428206201728100403040812455100e129041036031300352025014040113000b40e009100040000c0c28160840103841440e61f03403003a14264429081041d10074000c103843d804c001c00e1000e00741005000b01e0003800001d446078142c10007001c41324000e030710984810b408102c082c207002c000c40742510070903070107070130403c66035030042d101d43d80007500c00c040401c810000b0802051003070000d180101d080d0201c010039a03485000060941d6030141404c1c4000d45410305200c05c0381c0e08246640100c0b1000e0801684a00c2c1c040d0a05080303000718410b0400828100400c042404001c0000f40701842c800c031800e0741100f00c3c00c5070880c01c0785e40454414406a02089441760300d9801a005190300540003414840101a80d0145ca801aa5501d12900100701d090841c0d50b034203a028058001501c01c00c1c40c050300303e60440743c0080d41e103140f148070700303402c2c004828079000654960440040c400741d865903080d5603500c46800b100c00010541c44405965068101010615180115040b800d000069005000c51 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 44899177 1250 44897927 44897939
    0x10b0f0f1c0501021303060c030507080402090601050c0f0d031808070f020604030204020c06070e03010902420c070b120f090c12100501080d0c110f0607060507030b0108090304 77
    0x404152104101d12210300042400040e100b40000c00315002d00300d5298204078a1868000152103c001e422420305050008010005502c50105540a90100c40007810398481d000140d039144109540b003d5140a00c00c80b642c910f55001450101ca100d00d135030100900140d4407c01100e9203003000c0b00408600c3e00304050030110f11040864102103000801240c0b8141d500d0340094120791210400b81740c00d401c00002c020380e594002030f0018044100390004e1252400030307030001c0d039901d0301c000300094041c031501048044500c1c440040303480300000c41c03860140c0308071942c40b80c035181e0030804d0350032580e11a00750f01044d03a001038001d5a4414200c1d04034402c0c1500e0303038202601b10050080c03148840d840b501c40038642c5030380d07110b07510030802c005580504000c40c1da402490342078400507001514141c1c8030f103203198242a809100c001e1150b800000cad280b6000da0b180f0008490218000005901100120356203007805101d600003800b86c50903440800000b01e040d401541c031075104407105070454200b800100300c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 44900427 1250 44899177 44899189
    0x50303070c05030f0c060414010605010212030a140103080309060a1a1309050601060507020a0902031b0d15031505092a010207050a0803070b0f040b0109091112060702010b0f0f 77
    0x6140310b00196810300c01603842031042da820060f4180701c154000001d000502c1504d01e20300c551000c001000744940350425001039130f036580c40708039164805e100000045e008102030303000d06130300020360101e85101c0d60750b41802810303500240d5800580b40252400f1a0b01845030348100b0700c0552244859070244854901000503015010034610406602e55444200050060220501806141c1c56a03074450314a401408880152600300415040c410018400c04d0700c121265015107242c0d07405040c1c0d13200074900200b0060440c070001c1c4803000307044090210820903209041e82c8a0310180303004002e140e0f83ca000c178580d5071701280070301140903103010b1f07501d0140c002d114068185000180100c0301d0041e81c40b0b0124080e04c01690007208a9000400c044080021080001e034025131070082c4c40080342815105c07806c0c05403040c45842c3d9282d680c0d070364080801c2401c0880c1c800c4403030000d01c00810000c10b1007a850712001c04031841301c01940b82c000100080c0c0382464110000b1400030f071003039440403901420310072 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 44901677 1250 44900427 44900447
    0x10f1b030f300b01021b04020309070312030b1e10110f2b1d040902040e030c07030201020c060f040312020a020d0302010b010e0d050c010804030e1002060906090a05030307 75
    0x20820107502110000400802c01e10340154090280d661100d40703411800350100d40c400f055a60454000c139001001d04035040c180c810f00311108440040c0d0700e403135641d019031400c002c55100030036145011400015994141d03002103c0d01d041600e06202d420a0000800034980c4a041f80590020000c5141c0c0351040c070421804007504020b008840e142124903120030300d03002c2c260700c2c21030007140383d0b10311003000c80080144a284483d0398144600204000d400100d02c0041e4410001c0c01242d442071441e05543c0c0700e400c1020b9001040341038903078030110320180d10344900281c00142d01510400c10380b4001e44c00d18208640705c409441e0b011a0920f411a521810741d220403001783ca04501c00c00785e00b4400b40c1d540302800c000040c0b0a4000190300300382c0d4800074040c25113000380170b40320301480c1214102040c0081030030b0718001004d19081c005a541c61400303640c10070030b1007403840e00300c40c2d00703a05411100d40010380ea6004e40010300440d541070b1348590340c481da91011000010525001400404e04140c001d442d004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 44902927 1250 44901677 44901707
    0x7020102030d0903050409180c0b1315020a0f0b06030115061b06060302031903090503120a0302090316090e01060b030907030f0c05090a0c030e150c0f0d05010801020702010f1b03 78
    0xb0318082d40c900c0303403000303460308180d001c8c01c06d400e2100d80300c0c00c00c1203034100303400240721200ea01c07404c000355075802c2c40c511081c51140e00c240c500c46000704007046200f4821100070300d500c2410301c204006d050900102d81c103003c8030010700a41c41c0890544804410018510403070710300b541e032201c0d0403c10940500e425411203400321803007511028007200580c0c0a100c0c0c55000d400750907000301c880710340e400c1c010002c0110784e1080303000b07400500d0007100d5070700410708036101103140d4103025a032b804c008808a40b070603d0b40f45620b05886a0325034046070350b18aa401101262503490001c0c40702c2c81d25a81265014401a1740c0d00c10780d030703220341403c200054000380241e0205005a01c0b00b944940d0303c001061b0310350000c032941e294142c0e03212114505d083d098440c0d0980da1600c2c000514880e21180743c2c90202910113400110402c0c1c0104619552846000032548070340b082c82c0c024440c1d565100d0015020750032074042280450384621354512464807030711850880c4815003440400881d06a1010b44040359540c0000d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 44904177 1250 44902927 44902937
    0x70309080409110a0f09080601030201051c060306020d0c020c13110408060406090b0708040302070603020c03040518160813020906040209061801140408030f031509040f020a050607020102030d0903 86
    0x82c004000e00c6826020031103448259565400d00c03c00500a500c1c644c4140300b8044403030014841c100703001401c541501d50a00f000365640746003045640c3c0103164800000e28041c105400801004640d0f0041c040d400c1c08942c040c82200c05545050783c6901c0460343c1aa088650400d01030000001500980350390b201c01d5110ba845e05403120f0b403860038100111420358465445940d81c00410542070710207640b11488e4a802d49290034540d07402511400c192080004064000c01c110756021000d00441e8014900244180240d4200d120600c04084046038468458080301e5510044103008000d01442804507038424010b110003a0308200d03121501034005a003003603082c011038105445050060040034080060b0140321a09100010300300181215027280e841d000303010820450400005440c8664901621143c40b0740d14003100c540c0040071482180d6124401790144018041ea12000e01d6807940240c1d10181c1c4d403078959041c002c0ca0300c02c00b040280168010006002c10000960081403c20710a10300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 44905427 1250 44904177 44904179
    0x7090e1b09030a20041806050601020708030a090e0105121005040809060301120209010b0f04050f03031603050a090b040501080109020307031e0b01030e0105040b01060c080d060e0103110a030503030703090804 91
    0x403d180030004081102c20030300d41000c1c02034000314016072941c1907008590500020302d2000c8085003268801c2801001e0503100c40110380c9030303030082c8403100260500b181140e4a9a05903007000340039907014403481003a4460b1400118180c100201800c006a03c0c060040c020680b03890354150003004000c100740c0c2e61000c2400324000c3c5940d448000c0d03000b000240944040e00c005401000700e214410f03804020703122000c2240ea20b002c2c410390240c03811514100c0380c1e50300111405001ca0b05520807212449176200500b41c0b070808250700400500004001c41c2c3e1800d02080c3c8620307a203295485103000e40d80c04908440010400c01c02036400460f4407500070b14010458031003034220036a001604400703450030940c84140c1c01c915568148100700f1f0802e0740c60028081707410213460b0018410010300808c2c007040040c2282d0014400d0820840d01001c0c04440200801591205011103102003804202c0740102d8400030845c0c1c1d850005910310550f41c01001451179a02c81484c00c4e0b0003402c40c0d80045801200601c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 44906677 1250 44905427 44905429
    0x715020c060a0e04150e0a02161704060f0c020306011a070f080405130504080313022b0b0601020105072a06050903030a11031006030902041d07050907090e1b09 70
    0x1010b070050b14020780300c030414a00c511040005865a8860710350600f24266020440e60144070865034100144c42001a502d4098003000d032141c815095000d051690706014545482d03100d84c008100315011944d0b4081d103107030007440444800d0321107040070307626a01a0005200c803051030000c0708140c000714081c8514064140d6500603411156840503a9840c00101d02044541080955803804243c0b41070700308841c2c5056902c5c40140e000150104001c400018800c03421929180800c90174008178280c8001100710303582d80f00591351181941110240a1000444d141e5401401190300822658503030f401c0074248401e5440c0040d08400700003500ea4143d040900104050b0b115031401540c04501840ea80c0c50100c82071410f4030381c20303c81079580000800411450540203406d00f000d45240d464081206511800018040c0500b08041d0112030324002e00c0450300301000070b0030001c50f182070b10303e9000f595074030005880004142c483d0464401d155000201d03001006504144103483d000380c03282c14140000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 44907927 1250 44906677 44906689
    0x907031d0105040501110406021b0607020a12061a01020a1b0906060201050a0b0d0b010e060a0e01090903110601050d020607060908030f040c0e0c09010e0d080f0d0e060402030715020c 80
    0x10444032001c1c0d6440c814042445420b000300c10f03d0f41c61707007140c0307924184c50300c0d00c029540e203c410071030560444802025041603031070208171145540c004144120070354640840d41741035080e424080300c42610b071810150b155080c0304aa01403004051300504a00091a160254888060414041c10003000b00011642004034400c18024007490b5000040903d090000c000413142d10800ca14070074455100510001040300c00002e043d03504440140d403c0c0d8a95034041070402034180c1051140c98260800440c05503207039030000a98500039a5102d10600c03009052585451003030095a030070840c04d61150001d4107103000140242846081d0005920b045600d52142030340082c1d0f46490059039200c01d000a10544201d070101821036180c0c50b903802d00b803103000d04541e8480d144030103045c02031a62410b64680e8903803888006094100351413a40e00e03910f808224103554002d8003920078072840c041440034100000244507105590180007404c107141400b0f2040400f15894126100310b100b28802020039803208 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 44909177 1250 44907927 44907971
    0x2120a05060c04080f0304300c03150b19090b0607050607020c0a09020307050d050405010920040f020910081009140103120e010807050c030d02030408220311090703 72
    0xb002032140c9490904803414245006540c0c0100c56600910091110391030340d43c250781040418908401060b500400880c900000c80d00010384640800140081803001c6005a5050000340d9101005030352041c604210002d2614410b6828402d4032403800d00c80c1000c150301060354840c0c001c1c1400c0c1050780c07a9544514018040b00c102c001030700007403500b0030241810030000380501041442503056240940c1c0c01030650140071602c52902e6110004501800b0007940b0042c1007581008080c41035a01601000c040f070380c2e04291031402286090302c1901c01e01440c1c4203681d942c1100078119541804d6829080340c0b03480c805090a100c0d0802c10000188002551007500c1090b160b107102103159600d141804015080140c1103102400410940401c1c2682d06c018881da01800504006443e43c0d80d000032580b6600503c5400c0c1c690b0751001081c0700a0021500c0600307044203081e1104051540e40070a448500d141d00e08c801000e01d041540200c480745000c010181c0d1260680c6000607080d0000800c8041c856a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 44910427 1250 44909177 44909191
    0x603060605040606020d0206240607050c090610140901090806010e04030e180f0a02271201020a020d11030702040f0b1002010605010210020f0c01050702031207020a0c0302120a0506 79
    0x510302040069040600524009040758009041a00c05a440103921140c1c0107201445600641401c0c9101001d1001d4001d804040500f0b4151180414980913554480320850248150054000036600b450826024010f0480c0ea0740c0b8040302c4401c0c00d00c0040e194100b0041d031414005891800305404004004150081107000c4280400341094140071705001440000c041c0204a0f03503c8d07000a0800300e500042d00021401400821683c0d0000550001d000d0740b5108244081c220100c480388440c403220300d824000d0102ca1403520200000c05107801c0b403241c0742125003d078101240c4050a540200c07a03401c0700604000c180c0e40b4101181d40010219802d9003040411581ea401e842d03e59410001481240018680020040c2600704030001c0e50b00ea0ec00c125014406030006010202d05200c4030a80381e00342183c0009200394200944040d450b6000a407020300d085120000003543d041c800980e103801c06800450408141e41940c00348807205540001c5001a4450590319200080c02004461710a0305 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 44911677 1250 44910427 44910431
    0xa0f03021f06030f14011b02010c110304030314030c0d0603150f0507020606040213030215070312021204060b0409120914180604090309080304091b031a0907090504060306 75
    0x11020402100c1c44107400e82842800d880c1010900024046002030100b05800c030384124902c10100003030340c2c0905294a003401102d80da07502c45081458054020607040e19150300c601214850341000349940e8000c5120103070000340380e825659a2010103000940d0044050001b0303900c1c0a24003420207041d01c203298400c440340a844441c21307180701114402d0700368103091410144402e04042c80029602c0c0d4018000c140319070b40c0041c0c140351001044500f50001c660190401c14400680c08040e495900403000540100303c15a1840c5042040ba2088811022411810007010345694403514002c210a6064581180e81c0309140400325028005104c60242640e9940c85241d007441000c0c140c2581c28400315000e070014100e2601b8289001211941c0030000751800030340d0400c1401c0803503e03042264000b6005020001d404205004540c012b601d803905c000788113400040b01102c08800711b03000446141d84640701268205410316003100d20341d0300100300e40780c56440251a440024200e442c20b40c01124465 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 44912927 1250 44911677 44911693
    0xa08040815060607050705090a0b04050a0203010302010e0d0c0b030406020c06090a1401110d180b09010c030c0f02030306040e10020f04030203060133031107050a060b0f030a060e0a0f0302 82
    0x468080c00d6507000b0b4080d03a80d10308040d59580c0d11a510b04807030146d54030035440400041c0820815600103192403100810a1265041072070400000b94428001070740011180500c04030346060801043d0003980d802078000070034a2902900303002a810142c01224115001c1000d00400801005424001c0a00d00301501d03001019251186040c2e400d071043c0d640d640d05025400214580c504141c0e0f5065041c1d00c0040303860403107900b40f030000002503d0000e29118000d0144040704605502200b1703c0051034404000e0038048070713030580d0004140d242400c01a4004c0002413040d04050700f245001c50380010072603104205000c521820380c1c010070400c001681e8085070800c1903160801849005060700d0340805501c202d44045603c40c04001102101951000d00f00004024407a90240c03640340030105080d6240c1017249865622040c4844040c2c8201d0b0501c2ca202c0c4a914000c62280d9041c20010002d200d410082e603290b42c050110038816101c1d6000f10340b284400b09500b081d2051303055110354090301e161 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 44914177 1250 44912927 44912953
    0x30601022d07050406140d05030c010603050d09120c050607020406050411090102070902040506090d031701090603050d0f050a0c140d08070212070305090d021c06050105150f03180a080408 82
    0xc510380c0c0200d11403400c00804004901c641e01030508801d40c1a04c144d051101c7c40c2c01c0052941c450403502840e0f941c607080c00041404404200c2c560303a040d035580d448804c556103005d1a440c0c84c044480c064080001154100007611b489030041030561310103131000c201d0310390b0303000050100c1e110302480100006001038040032942c0d040c0480c42c081c2041c15401c40c181400c3c034010074940e0042d00e04150051a07003051500c00d1500855032845100d0703100380d000c40b03503603154480640a00342034031040301c0798420080f90b80340880c00f81c4240032240405035215030a15411010071511000000701c190380b480040b201d60203900c2030a01a107007400242d92200c00036810028402858200c02c83c1099500c4a420711081c80080d5024080766022601203403071103500d010600001d1802034003103d90396015001030700c100c010440d16412041c101c07801281c8040f514040c480503001c10744511140440072110820001e5403019840702d000003180048011100721030314640d600c05190b030040d0402001c59000c64094158 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 44915427 1250 44914177 44914183
    0x7120c0518010801080d080603030c010f0c03060e060f01300c08060a080303040f03110607021b060a08061504031502040503010b0111060406110c16211205030601022d 73
    0x120741081c40c12206643c5400c1109849442000c1d4120820104401242e22664208299a0740141c090020092a1100103210005050880e04500820704091000840725031440301a445410060301e2a07500031244401100c82a03400b84810325001d10204141400c3c0901b41902c01da18101584000b8210080c481d016209400061400d441031b004608280f2800502005407500b16a105006440511a501d81580d40c0785040352143c3d55840341c40100003503140d00103203903215606541000000008917000340101071140910407008642260003150a41c2006a0f003020001242040507050075100c0d0b413940140c1d40c4c0348600180030394021405100925007132090144100702401e00d07881500048101e5911494000c0010b4461699240080b55061952003142c400e1400034050f45e6040b103094205090102070390040d83d070440d0500720007050b100c0e000c400e940562030b0002c03a2040c5012030ba4400701c078a0741c4002c03e55411401500781c585030310f0b124842e03e4a40b00300984d18903071081b1460740760740386 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 44916677 1250 44915427 44915467
    0xb1c0f060308070b0901020a02030403030c0503041d0a050c0408071a0409020a0503090601050f090f070903080301120b16090b0c070f030b0906070212040603230f0702060705180907120c05 82
    0x10ba580d104229860700107800000b02d8bc200c90781824841c054201d2401d00c03a05601a41e408550002ca078154605070740780035480c086208a00340001001a81c445100404244c0554000d40d000d130b6211000074080b55415420f04081c9032802a001803520707443e42010f40613030704005210000f248000c81400348220003808114090320069802503070501c0b81c0d00008020140c0074014098040c60034000c28902031088a10201444c3c000d000642c0d20b507034407503250807203154118040d2403201e100c1020175a9003e0610030744a40e0040c0c2d644040103070b42407141b2016254451080c2807483c0c031034400002019030070460300500460003110004d00d0b42c60907911050601c0360040104007190041d00d0308096402c030000646065403801d1800091015440029181000c4c1800b41080801c644004114110018410591240c003960342aa001a00c4603107082d50b190041c044603501c40c503c12104120181000690a036210045142522040d07030944081800c40e01421480b9001803c00640c6190300407298030101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 44917927 1250 44916677 44916691
    0x2060711010c020a0201050319050103150606090b030f091006080304090501080a2a050916030c0206040f080a0905060d060303021204080304050904081306090e010504060b1c0f060308070b 82
    0x40b100048070400252a0b1000c1c5000078180700011010403010f4441c09a4a031440000c410100503650316814616461400d1b030144148840c142103012684905c02d041c800101c034a22100e4904544508188852a41e002003881c54a03125504008214a4a5000b04030003003041002540e615410040280180c44050300946907a03408103001000081d07410350f20000309000745901e0500b0f4180760855448440403a4003c030f2340805504148811004100310385854404562810441485080416621000c0c00c8402600000c0010062800b06941c100101036450313091500c25070454903800060104d422450140340034540e43d403402c4c01019010009410700b40618241682010315140c01c80d40d807803145001d581d004100e08000b281c00c00800c074041e20b0b40580c00710010341800f034442c100280482414450703c7c42c0710f11f101d000011f603804d01e44580ba09852030f180249103017812900340001c000e500c0c241005181907a91068101700e0406224000c05903105175070490742e868050426054440e0090400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 44919177 1250 44917927 44917931
    0x80706050a0e01030b010207050d0606140d02030a08030603011506050714010501050d060e0106121a060603070903200405011701050a02041d130f0609030206180c060f0f0a0206071101 80
    0x16078285a08030106070260b007401d1801080c0c268074000100d0401c0030301e5100d5030300520602c8a020800c4040e400250685403089005007580c404001003085070036407000c3c06500b54000e83c0710040462004401161300a078060004940e0041d109002741c4907064030360000d0700040e80840c0d00b904014060300c03c0b4a00e103000400903c16075040100241059440d001e00404c13060740c40d1203000010702d0070b400401c010070708403d043c221780c00e00342000c80f000b880c048603903105a18000d0001b407c070b01c2e02100707683c025855581c41b1004142142e58120030f480c45144101408036400788070401940d6940a400c1c0a052200c000c1103403821010350f41400c5d6200680960b03d803a00510050115100d2508048030002c0428085138580c2c8900d00944801c4180d0600036144859040060b02800800c1d0018402140700e50701b1948140c1d17401120080709491103040090940041c6030a0009182c001c0141c800d0241700b0a9442c509220004216000d903c400101c10141e00020104401550040c1c01540e5a084080003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 44920427 1250 44919177 44919187
    0x102010b1f05071721070201090f02060a120e01150807080a031808010e03070c171005070314010f03050d0f1b0c0b2d070803040b040303200408070605 66
    0x203040000700004850810070030302098810500c00020040b5132000c110600490341d4148100004018646408640700c0381c40045020075141441442040d40d20343d00100398400d0320455034200f21a5a01403d24082003140680c11045116001c0c0710307640e0b1480c00c0b070b40002900c0038020b00b00300c544002503016a109400c250f00401c0f04610109151121340c0c0c0c14500317600003280c100e110120000d2a0380010b000c640ca440c0028424201c000000d111441c09804414011a907803c4005c0400c40440c0690b0469041800c40810b1110749410807a0040f2a80c240400e00c0400020250040350b400d0b400001f081c640d0300f00400c1405018803403000d54042d945802200d6074100b600180c12041441c04440b01110301c03600800c00c1c0948078556070b010700800440c195956003941300716000b10000140d0150f084c04641013014200a064040b681056846403140d407d6554a40301e00d520030000400950501d84c0303400c2960000d0780c40c503d5044201c41184805503d4030704004449140a00d5508030340140001000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 44921677 1250 44920427 44920459
    0x8060306071110020c011119120e150702010605040f021c090b011215060303080906091908090a0504020309030a0f1704020919020a030c03140708060603090c1e0102010b 74
    0x81c258043c51550303070000d0382d20b000040c8803030b004020440642d1139003000032031800042e91203201103c001c084a80d0b03801c0191040000d6280485000d00c0010f021039101120450050a0806890794080424000014400d036500081820b981c030000944041da680003134900000e00003d01c5046140700c0700c110401c2500003980d100b00b0031440c107004a40580000422100400035000e40743c085001480005004036a52468060140402919500c0c0716004841c001400329800140000c3c043c2d80f642441048005070f5101d4407010740c0045100c40d0000c0c100b5a000c101130315540019800b4400c0200107540c1c9a000c5440105140240c17044c81c0c00700640000105c100303410400b4401d17002034040303840240b25120601c80c08074013003a0b40c0e01402010300104140b51b0842d010350104d40b0070a2552018001c00c40075140c1030790f1543c400c07a000c0000c505000049030b02400c200e00699413100c1c0160031650350788040d1001400c01002002c0840e03c44030440c40c00420395a080c0251480079a003503131080b00c1c0c018556 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 44922927 1250 44921677 44921683
    0x3090706080a1a1c0611040806130203030f0a0e120c03070609050a14030109020307061112030f010603020a0912060609060509040b010b0f0d060305030c0d020607020703020114040b0a080603060711 86
    0x14083d1442000c54000026440440a429046a40c2e005408005112882080004580191040000500603400011449a500540c4644542c0c1c000c02441c9402c11082e9442c2064001c50340c41c3c41040001d400a01c0c10b07499190418a0070882d1900601043c030920003010316040e81608110704000300400104a81d495040b40c40c0c0540c0e82e0084440d0000c1d0060380428014010400301030f5262044141c00200960441d0b103281070f0301c41c0b22007940c14140d4030003904007640c0f1080da2175416a6004000400106200c5e6015080244141ca4070408280e40d840e0310740f0301140300c0c01d016a2100e6950720104414600d80c4120401052300b9201284203103001c3e241c001041d04140b0480b40c0840300000c140301c6031800f120403541c0e0600246c6042060780e44070304005640341c0100c4808103803071203422060071a5034000a1141e11445040e4020400e15040da4011030b604203120380e204641c410107102c0410310002c01d602610f10f55080390398120340c038038003d07007014540703000504034406002c107040030041030310404 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 44924177 1250 44922927 44922971
    0x6040902040f171c0e04050f040b0703020703021c0e060c0606040c030903021c050c190b06010503010f060f0504090c0203030703060e0903090904050a050a0f050f1612061103090706080a 81
    0x3c400c040c5080086001d082d01e403813010102c031750390140c07070b100400480c0215071015500490144140d8001540c07212016002c80c40b5911028002d031307128604080c013a4071a04010400102145004a1074503002404628503800808901206810190400406040c903129602c02c03042ccc01d01d014803600b16241c030044d4490a804440040700050381d0350010b95240104c1c11035110120704412200c0401008a0b4210000d0031428100c84107000030011418940c8100d065906841da410150341c4000d15141c1d059a1400c3d00b40414800c0c01028000000c1c044464882c3c004812211b8014668034541000010200c0f1901d810040101704a041444106103002042e0380341c13184142d802155580302c0d0f06159150540302e1300010f2042c40344159036003c02c24068184842103124408881070094403840c1c490f03c1e100182d800031141403484104200f0300a00c5520100003502403003002030888a000500e02c683c0c0d108848850082c0e20800e0100081a40030440300c2d070005009004100060004066003018110 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 44925427 1250 44924177 44924203
    0x904090c0918080d02090307030c06050705160b090909120304060605180115050912030307090509010911030f07050912030307090603021905071a04061407111c03090206040902040f17 80
    0x3011806c22001d071000c20450001c1d5400403010510a80c3d0345100600c0b0f0740c080d110844050042c0403502a10310320180c00e010986040704441401c2949040500030342d01801090302d41248602913941c1101003100c8010340c007450241c00701003180d9040500380441001a0318100c0350710320024004014940c86d591481002c4019403030b1056488100c880000d600c102c0c20918030780140400401c0c085441e4001c01d40b10f0441e04281d4108190b130b0307a28524941105c40c1c2601e0314240742020000a19180340f20706d455944144a400d0090600b011100451300303407012003001031159030001060104160700018803400a11702c4c0c1c0303815445c000f541040c02140f00c00c2c1000801c03c4c00008a00c0d034040215000082a15a00003500000b0514003411f00001506d68103281c031540814800114003014400c00704403074100d810400610350820400b940340b0354041700506030000c040d038410031000180c0e0b507503009000401c08032901580741c030700740440500005150380c01400c0c1c2214501c1c0c0a14407000214880e581e07211 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 44926677 1250 44925427 44925431
    0x3110f0306040b28050603011d07030816080d0605011409150304051e010b0f0603070e012001060603090c050d0b07050a091701020d060b0f090d080904090c0918080d 72
    0x2a0101c944408128182c405845803001c2ea03130f03d046000055100c80d100d41b50072002403200180c0320f103c038407021445258440c0d6a8000f100184040b51040004000c900a01d00608800c014144c840c0c5a00e60401e960b20001140c980408100700d60303000f40841e07030784110700500301d1902d1504c0f00011080120307959131031850040400000c0c207011082c04104010548a01c11801007410312070b101e40207003409141140300320b03041401359071541002c6003030700d21a1150f5140d90030282001001501d0754604403441e40c0f428104c041d502d064040081c0620001008151008580e10340b0074500404140701a070403050017400040720100118902912064101d05141000d99032800d45410071211002e42d6002800f043e001c5c00074010103820158000c0005103808101000f60680350b408aa040744143c10003600700d05000e228107485071624a04203001c15105071031140c0381000101c08039098420b8110300741c41c070710b100c0c81003040741c3c0b0f100340640058040d4071201e0202d130307a42d10b588908142c02500c1403450b40d1a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 44927927 1250 44926677 44926681
    0xb040b1606140702071701060b09120a020307080d1d010804020907020c0415060f0f020606010318050601090213080607051207020c090c0307020c0604030c0506030c04030b09030403110f0306040b 85
    0x4003a40032982d20790001c0c01c00c0e8100c0c542001c000e0f54a42c41d91144806c0118003000e9440c68103c10f11413081600c11408503d480e1403844010800707810041c03280603d0780d0003041d5030500142d804103c010000c01044c0040d0801074171100d00906078003a140b1024443d8525444114241e0f80e00400716a80183e0446501c41c4a032a0000124500000e0005084d0040e10300075480040b40000c16482d0b08407103460741c6000f002481464110b40c482840344542004d40d100201040041d030094003d42c04607111200640351615158442e02e25241081e0300986a4550001e00c119031500041080301c0900114801881c0390704001c2c600030b00070320403c0e9000c5c418210320300c04104010b2080c04900c8030701c98020300049041c18600c1c0560b410380d0040e140c0b2000340c0315401868042e0704004042d20202e03500205890f1040c0d1600040c0115540014209000c5500400000c0000303035545140314015014800210344807411413810034100321000924601c900341e404541d0b1510350740003a94a80c031590000710118030f6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 44929177 1250 44927927 44927933
    0x1030201180306181218170a0b1008011503080304060f0f052e03050312040c0807120b010504061809020102010f0e0105091908030403050901140d05040203070b040b16 73
    0xe440741c2e40004024504100201482041041d0700d440102e0050404101401c040700c01680c3e0f00d409120b6000c141c0340003000800180d8141050509000398110030f640400249503180180c899084910944150585505008240091140c5000381c0e80403100400d40f82d00f10b450f400c04030700005000a1075113441e051140314601481d0003008201c40760440501050805a210005000841203070800040a03000701303130860b66880c0c940d0700c1200d4016019510b803014070031044400140c01002500d1108440c000051103460802c00c82e07008000c0f003a02003050b0384441c6040e032004823060344102d100c0c6003070103024850715594100441c9070f1410b4050000c1c0c848424030041c0d014203400248a110140341c400c4c2c400c00500e064101034030454800040d207d0011110481e440007032100700c0080d1083c4014000038000034080d4004283c030400c141131500140c1c19211007010325900c011031003400300f500c88003071000310704003040315001402d0141a0503090904003060220745005019508054844144009040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 44930427 1250 44929177 44929217
    0x40c09020f0412030e010809030906041202030a050706080910051603020a091a0d050117030708070c0806010306021b0c01020c04020a03090c03050a03081501080703050702160303030c030b01020a0b01030201 90
    0xc10754282c100c044582e03c0d0401410080b000d050150103c0e50010010300c00c1d41022007101c001200040906081c1030034450050204c0900c84000ca030103104030140003010480401494004080c1c5179100341079850258182070400d1002960740307141d28200014084142654007a920901000d07180c01030311a40f07914401c842e4004580d1054005a00d15a6080e444034040740c004c000e80700d5100000e01c20360343d03030b465022a42c0545500c1d00100f074100b4060302c80043c0e1403400074441c0074095050000029124504203003468001e900444200740d00203011002015004107405d250546c00d00a0b0011510b190300203502c1d0399980200902c215400a090324240340640d224040da2900030003041001030b02d910b00a83d032100c880d44141d0116110a000942c50274044d40010070345a01a5140c03141501c071450700341e010342409400d61055008009580044104282c00200114026500807400c0780240c0809801c489080404904540001c5001001314400f003000038112a420729221561030000610200 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 44931677 1250 44930427 44930429
    0x3120307020a0b0702160603051806090601030609150507020607030b01020d02060a0c05120117011415060a0e0319110a0501020307080c01020c160306050c040302030c04110d090308010f0806040c09020f04 89
    0x101903481a008102c00e40e1690181c0d11892b079240748104a03a4041c00c0c510b903507450440d50b00d0703007507071240c0010f10000303071650062064a0301c00c00c611200c2c4803003001543c040c1e03203003101c5242c01030784600c0c104010660300d401b441642000a0002e8122000c0c200e034001d4440c0001000c0c00038054503034652072210341c401da04072620803411420042e80707540c4446041c03101c4900c481e01040198209842413058030790744c03640c99000f4581d1114209091099000344003d603041001d10106004e40529244242c1e142484442c41d17564600410159030002171510b0b115031111400f481d40500403280091042d070741c00104607800a6000900d041d242e04100c04080d019200702c5104503070034061045540c122a2040c468642070700e00c911018045540d5030300948400d401580f0001c0e500d0b500000421b692818185e002604504054107030518025001407080241c2e00840d00444c0041e07070303640c010484d40000003040409050901d000c1e04d42c1741800d803107010f0b115805006043c2c040e5400240410031030625800c41e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 44932927 1250 44931677 44931703
    0x20409080c0a0302030408010f060e04060c0203091305040b0c03011202060c120c030a0f14040303050a0212130302010801170a02100207030f08120a0e1f0608070e0603120307020a0b0702 81
    0x30b8450942454000d440b50450312500729150301744156161840d241c4e000d20000e40d0b5441005610780c0c6c0d070f02d0301c030748002d041c9403c40e04095006c00c2001c0032841e200c0d040d003e1404c0c0e88589020442d4107181c13800040b00c0d81c00503d04940c003075041c0b0051041417002c0d40b44042c2c5a4044038115140c00c101c02c80b00e800c180584c00a8102604006109824680044007070800c4060b0368030b070b400210020100030303142c0100b070203144030b0b030010f080105000090040010b0046203540e881101c00703408074411010903a034016080110008c240345010411986e101d610507002d808284200d6418140b05018981d035101c030184003c1c414000032600e20a05403007045980000c0d60020500d40d0200c1d840e040146040d800000c005000c04000720024031603284501481c040502d2f030310020029180c200c051146005210071051420303d44418000540d004104001c201a1244220f020307202e06003c010035150040120440c0c0e106482131040100b05031b004900d40001c02d4003e000c144055843e020101e040080c031201310 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 44934177 1250 44932927 44932933
    0xe0f09070c02030f0105040b06040207080d0509010605030c0117041e05030315040509030c07090b0d020a0306020904200d0c030b0d06090327090e120d02030717010e04020409080c 78
    0x75404060411a18000e400350b841c0485038458450980e201110003420040d14980454402e09144d80144071483c05071311050b003000550240f20b82501d0041e59000443e03915910107111703030720b0306114400b8083c00034242181c5240c4046424140e50780b0007440902001499500546107414044401c1032030781c0d0100940307a992070072034100201d0038103415410303015070324040c005400c5080c000212200c500402005151251424803614003074540907079400d4000c00801004401070300c5260184015601c280c00268440c0900000d101c106d1302034088145032000d100c3c20751151050200d04540100d000d2070300208500e00e0b0300c1010340140c130310301c00ba8130b410041c401101d0040c0003d50b0302c60300045101e5520135245054402c5401040e820181140e42a1400000c0402c0340c1441980b042e0318a0100d40140e555681404811400d107420055444258540005c20408120341c810784502c0c440302c02610140b01035050261111325060010300017406a81c0e070302d0814050000403410f86400c0b0107001c0c11 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 44935427 1250 44934177 44934181
    0x4020a020a080d0203010e010b0408030306100905060409051501051608070204202809171608031b030a1704171809130f0f03030917030103051605100e0f09 68
    0x3c60700a500900c00e82e00e04039403200010800c0e100f42400c840c2243c0700c030001582181c40c0d80081003250070114000c0b105009242e20000b90a03103446010700014a1266400140d915140c0918510034402c114041d0422804000011038501103415000d0810303001069180c49440500c00305005028480d6040030f5041260907080c0040c0034400108140203844940344081007000c0020301c1300321201010000401d040340428850500892022240303800c482c81252642112882d4589401403242c112a5031600005040d445100a070070000300c0a0038030368019441c2c1100c80100501c0d00d00e28068009041d000703036000c5418084803d4004440c140d101c5889070755a8860702007901038400d80740c100381c003442c461000200480300204034507072100c0c1c014048000c280c485581c0c105054000c00000c40034583c0c0c600c0204089651481091085455034803969a02d504500b00780d403400c1c0d12000c1c0844011801c803400e00c816140d0000d80c2c030071706441d414100703042410031f00061184031941e8003003500014820300b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 44936677 1250 44935427 44935447
    0x913033606030b0a0506040b1e0703020319020604080703030e0a020312030106020d110c090c120702070609051207060e0a0305060f040c05030703080703050904091406060918060604020a020a08 84
    0x2480c004840154504102c1c0300189802c0c49140b002d54440d15074810010300c810001c0d0b694000c0203280c2180d408420820f50f061003540c0f12840d400802040d001680046055103a030840109890f51500c40343c0020622481d00303a48080c198418990300404041c1c48211030001071500304500c0c2c00c1660700034150368042c01400b40c2c94045800911819005129421501c003c0a003c0c0036406500e1500d4009054410f200d1030611003008009418820045030410500110310342644502c0c0c020880c80d4041d2000518001008004600c550403132440740050602580b0600300019140d02221090301340060b91034003110002d180032107103510203402030180604220762012661103291095220340103103074040343c030741d002d041d900d22481c00028410142000a180428040c4000d0078004000510104503081c01e82d40e00310700d994400c03804507041c0c5e001200f401524500704824607400812140c0201e00a07200a12860340c0e01006485d2602856000420040f4940700b481000b40140d0030000311584c2d905400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 44937927 1250 44936677 44936777
    0x905180403030501050105090a090c090513060303030c0305090c2202130f0602010b01050a0302090604050a0602060a110307090b0306040e0102120712090c03020105130e13020f091303 80
    0xe4003100040d1030000080303450741c002da05071080004041d011703e08007820041150010320003d8180d8062140c0d025000844ae901d007441c0700c450211189002c58011b255280c0501910f81c2544040309042c02d2004000a1000005140305040030894040c0e940300d01100150841400452070111441c1c00026211212080403d40000300e90240004000c0c0c01d541d400c08a00b2202003005541c00954104010140310340b0a4001d4503100d0030007031656190542d20700c0000c030030507026880380001d80c10501c00c10895214a12a0b0b04c11a2414100e075491490003807002080e4100d24003071a0b03103240f400300c0458200e44465000340704121069008540d101c0d01c545605030312400c21101c4100081d0f100240d40b41540c010301600c0c8145a102da4480005030030741c1c0c010340d43c0e5000038030143c95120804c100082c05031494800140100c2128000b0040d103401401030000700007074088024001c085c04018480d54a4040e0729045085815181c01d403500304219400900e810000c0400d18050701c00310b265624505910 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 44939177 1250 44937927 44937931
    0x2011101051f05060316180b1c200306130e0a0308060a080307050316150c0306180225030c0501050411040608010c0c03030e03040b120a110403120c03090518 69
    0x5441c440408581d43c2042084500c8120340d48000c854801c4d600c01d01d003601a8041b202d60f0102081641035441c0c81e4198030f156030308411400c4002d040b210070051119000c61003003c000e042e0b04041d41209080310200c5940c03d20018004c64041c0000480801c501030055204911085041c002da0b181050f16050080248000783e503400c0c4144503030310000461040c00802c440e600f40d480000b030740c18504551070001034004440c205443d0314003d02148480414188a80324102035036490000c2d07094140300d040b804031003201520100040c8108100c0c0c800d0b0003240409000019982e0303250f40c0d44007032032400320b070142c08290300100a0f41c240428441040900031800715050f0050701d040103000e035107104072404e803080c1d04034000c04100d0381c281004c00b00c1d2103500a00008038040003143d28060307a625000200e5407064510b11120181701e0240440740300940142c0c1d07020b90014140909060030342e210710403403290304920358051080f200e04400c105400754803244000e000c0181440c6245140c03002c0c0701082082 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 44940427 1250 44939177 44939221
    0x100207170313060203120f0408070605190e071d06060702190303020105060a03030e090402210106080c010f020706030b190608091c050a26180705030601060c0f0201110105 75
    0x207034007008522141300100380c44101d180c501c8400819218000681040341740944141c2c2c44c4c050421100c00440c165000e030a025010258400e01704006000c0c1c408102c401e4050b40d900030b50400c2c20100100c540500106800070103e0f8100001d5445d1140095214442c07060025000030b400300b2070b0000c000001d0800c2085078003075002030000d552201e0401c50751030800d01004000c22040000c1030600d040550f81c80c1d0b4403070310107080c041101c4c1406c01d403820039101e44810001560f4455030140800f500030b014505189000b0308180e4289244468041c0d00c4001c24003500e0201542c80314600c02030740e60b40c2d030705d005800c0e60441844142a00d6040040545000b1160040a031103030b00f280e146038650203090314503007003820b903a5641040f11480040b220782107640c940300301c0c00f07401c3c4c000d03020700c40c4140307803524050742010314041701ca8105000143c0c2080b46950185210750003030401000412303080420080307a6507000c03031610011940c070320040e1080581081208055840c150410810440b02d140c15580042 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 44941677 1250 44940427 44940457
    0xd0e0d020d0b101406030403120902030f0706020c0d03050909040c1211010810031101030b010203040305121c0e0709091406011806080109080910020f0d050a0e030c01020c1002071703 80
    0x2031074a204e0400040b42102880e0030140400019010911550214403c10540c05001c500078050350006841d0201c614500100c680000304e041102540401032440b40107415222419081942c5d2000f84c414090000e00501854000300000c04100088240310040c04080088082e540d02c0c9041c105181d100340c0354200d02007000c103030115091001003100a8112a4424080011a001d940c01100500014070615055100a01c808030020b4010301c10100040c00511150741c84805100c0030154000c40000350b0b6181a1138028204c042d85004a031002c26036101220101c0c0c40c218500e000314420b100c91140a20380c3c06040000303c2c40c0160400d00aa81524100061148a4641000794201c541c030307d400a0100e2010450810700f81001d500800f50b10750b0310300660360343e40c0d20758221504200f020005c0d1800640001092400c0715000f001070b86600c00190014180f0307112940010795104c880381081882201b401c00350050403442027102d0406050002040402e2104858046990360040010340801c41 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 44942927 1250 44941677 44941679
    0xb0c011b0c050607030f0603050303090606041103071403060607080a0801060f030209010e13091a06090a06080a0f0c0b04030f060f0c1b030509060318010b030c030d0e0d020d0b10 78
    0x24814981c266100380c200000e00303615213035114154010004a18004442d82e00c416001020860600c06544510bc0802c00742010745020000c100c00c9400d07040c4281c0406005100748004075600212107100c2800c207038480c56407515600000b440307600440100074086840064070f00001a0701220070f40c100c0e0800d03101e95440410f84582030301a4040c65106e1800030b842120b200965241509800343c1c40400c400e0b001500c0ea4154036485200182c80790700b403401c030100105029503410b0038060613510181440b81045080c2c2040c103036944503c41100e001e0500980c6c0404c4000b03200001441c2002819440744959455a81e0300e007007560040e2144065481d1441c1c02139507585200c080c0283c3c166008075548103400e0480c0449042e4400340c00007825030070040c090018102d5510303400c0040d40120310851004180c030064803405825a03401081c1c660084e0054010441e02c0e441c0043e030708440c44820308154035404552000b0a03500d2004580c00380d40400742100300406c1c8890711404501035000c409000c4281 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 44944177 1250 44942927 44942981
    0x2060703060b1206060d020304050a0b010518071d0418150203070905060a031803080103020405060406180b0f1017070c02030c060d0b040905060601021b090402090702070b0c01 77
    0x1680644100d6020700d01c10080400401d03001d40d40f0a90140d0010401c1c6e003855641c0150f00e003280c1084400315680e9010454580a0110656503a0300601c01101e1111950010b4668081410005450706081c840b101c070001103d0300d0106c3c2c0141501c1c0c000b602c03c1000701c0400d08241c800204440b01a1046503d01000b5448088a8000c6a100344100d80355110204d10b4402803005640c0714800c407034100747d56070058500f400310700e20500000b14002da941c030035154103600400084450280c00383e80b2035803500f941003001c0c08007030b0170350900001690700c00941c90740e008004c610309602c2c23110103a501002c0144055412a081410b03129598129140884981d41b451070076100c000079400080d501d64000c011044203480c0c0f5200030a41c00f10143d90124422100c0400b140c103481040604071225003003c01080903e590400c803020401c06420380c00342c0d00d9901e500200e200c40340c01404c00b90007510188001400ba17030080211000a0105082c1f03a69140300000b030741c50080c078101d4812007120380955050020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 44945427 1250 44944177 44944181
    0x5031909050c0135060d050609010218010c151104170a0507121e08090d060f0b010c080403120311030406060e010b0319050a06080a0507081e0604110409020a120302060703 75
    0xc6581c1001103100f40c4003c180052003149030080155900c0344510648100054023440181e01640f0200700260b03c0321503180503081810301800c903150400484140110115103068803403c50040700c160001000380140301290440d20484e002481c002010310540c0040e1880006c400315140e01a00507140b14075191400b03240800c140c203001400707800564241d8600c031000c900406200c14031400030b4900d000000c0c008105014444841504e100c0e98843d80c201c61420140500d405e00c030024a800c3c402010143d4401109004500010701804140c85c0340f8034000303010380c1c400d03c2181c508072601c03a201d1806140040280075180a4190000f11990000402e0700710305c03099900a4410b42d007034000d00700742612400e0003003200401a106981c0c171204c0003c3d5003e400e201d0300180e98001c03000f41981c5030400c0e10710782c40c1c203403000d002011308400b00f401c04a400001140e8150400c1e840003c000c0300b4240080064050000c0d198060742c41280f461000500e00003140801004511076000e45220760b4030b0b200c050b81 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 44946677 1250 44945427 44945477
    0x110a0501020304090216120215150109120602040b04030b041203060315020a020705090a0c0206090f0304050d0302010f020d020901030c0c02060301050f060d05010f0501020f011104050105031909050c01 88
    0x2025910a00040c00080c1c015009481100e0b042c105548009030a031721490701a800000d41c10002da04000c2c20082701c40c031807605c038035881503503400c142c4625841d0800003812020b15126801a050300c48000c03d0810030b19070100d40c0141358500e101501c59459041080c007035201524101d482d200400040c12415009006480c00c0329046a8120320904d03643d0030000103944030200c1c03c001c6000304a400300c0c86a44014a2501234414908001032605010001900d001c4020303001e448594007600c1d0341e40003844c0010481d070030740e01e0076220000050500c1c58141c0c0500100081590352600200700f26055048550103403880040c00d90302400ba14031040b00030348041c4480c000181d08400c00f08018480c0b070501c41903da42600c0c0c0038101c3c41c40c185001e209d80d000c68600307812088072203c04a00800103507030704200c00f4101d030460200801840a05840310409842a031183c1410b225000c00001d803210340e51561140607204103042800030740d455103041a104c18804000c240480c2070750003c0150511400c400003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 44947927 1250 44946677 44946679
    0x703020a15050702071d04030e04020d140a06080606211c03090218040309090e0c0603090106060212040605030103030806060408030c0609071706060405041e0308161403060d1502070b04110a05 84
    0x1b180301d071215181120f825055094007500320b80c08000a5100b10091f00c144140120740301a000d0032820030400c0c0b07a0546007a82d10051881d80280207102e45540c0e00c4400d2010342d040d007c0751008810b00031200d1802c1543c0d101040c00c85140000c400d04016805800c9514940d1088031105014940702c01c5095102c102650f01030300161159005000a040c43c1e84640307d1800c5450865482d02d69050009002e036200b2035410f00d15945540782040300b5074040044a807200741960485052608006004046000510001d01003290340e0000c00c04513100c0e00100c40103491854182c960b6030040b0304001c2e5541d00d003501d14091512403907400203008440044078070880c2d84e44001600207515200104400317494040e0059500382c010024403040407201c00c100148036842502c03500c03824600070015903241882050403801340900c4800200e2101000350480b0ba010f941110f11544541060034260110659070030700ea00007920008000301486240c10a45214600c218034005869500e0018400104042d104d96 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 44949177 1250 44947927 44947979
    0x80c040f1109010c03050c0a030e0a0501030501030209040f060603150218060c030912010b060c0a03030c020604080d151503061e050a0b1c020a050403020102061008120703020a1505070207 82
    0x206042d984031300600c1190030700a141c40c60810000e404180c0c1005507826040b0040307100c044400c0d4803400c0c4082240d0043c4800d0800300455855078010490800c2d00400040c100080a034101d8100081c81e070009001c0d54100d00e101c19180e0f01d810501001b0351210608001240480c1d0720f0f280d246c0f40020445800200346400745050100c1030003032002a40e40700d80000641e5482d001c200086d03403100005020629640802403d03480d03458200038045406401030b40085400c000104000b08114200319089010002800900c1d02e0b104401c1c4403a61059030041024403103104000380140354581c20003010754101203101c1442c0c2e0014003040700f0080c068807402e50040900e04040000064810282450000341e0303442182aa14002d07802c401c036880701000700045100801d0038015968108851540206079015120f02a4240b40ca010740d59185c90140c1d03401c4400c000740644c205803003484202c03c01680500d80d002c009460701e005c400540412500a0018030400c400025210301c00721000040007405034407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 44950427 1250 44949177 44949187
    0x30b0d02030d031109040c1e020309010816051b0106060e090105150901050f041d010902030609040b060105070503070606080f12030121080309060711010204050a1e0f080c040f11 78
    0x6070060244003500c2a400801441100c03206d4a8a00134109903600315654140ca001c040d80024610f40010f0b5950002c551043c0650401640c000c40707110713041000440115400c1c03403040740464407407040d13584d410741002221000400c01c0c0015004107040e125141c84070b8440e0310900c000d0100c101c07003d2150320741c400000b01c1d10011904403040200880a410316056191600343e080d4968203a010794401c454002100d04a5000c00403103106103405007854600552030b60a20200040100302d001e0300280c000004000450f902d85c0c024011591599803140640f6149c40c410b0900200501482c40b901005010790b6044284c403d1003c2040c48200c004e601c2800d0850342444282041070a082c940c50314840340034403a00005c2210b031401755109110800080125140800e0000c02005480340304103c141c0c0140010300550760307101041070584003240140c0348820400603283c401d0010580c80300514210b913041c0030030480004603000301100c00c00e540c00c8c40a02d400703d45e1b4104642c42400003901c1c1c1541445 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 44951677 1250 44950427 44950453
    0xe0306070201023112050f1203070c0311011503060608010e06100608040203030d02030405030c0d05090109030f0f08030412031b0c0212012007060608010203010803070803040f21030b0d0203 83
    0x111804c07421014400020b14a615484e40c0a908541504240c5050340441e6410040f000304000c10300d04000d1020f00309007507050250b03001d094020b1a120007014800786070b0800e01d01040075485001c00c10320030000c281c03019582c0c1c01c103400104030b0f60142101c00e509010980e524000000f43c1c050055406d2403c0c1d02aa610b0214101c841d0000904100d81c140020092040725606900145004a00070030103159079500401d502881c10003415012820b004090042c440280c3e004080341d4200c0c0e40081c403100ea41e02180ca07100304a400444001491694080140001e0009a0030100c501d03d102d40c5040060b01d40300d0b04280b500e4420141140d0005005005030001420803648440300f4948000000c81e200004a00c106940fa0b410006c8003490702c0d01140950910940c0c0c080e800041144100851541d414007402988034841c006c4090065030700003020a0030411211006040a90004a44d580341d1403908030274501c1800d007041d07440000f0f0a00304003000070324107012890301442e40180145800c018401c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 44952927 1250 44951677 44951737
    0x30105060d020415050901021e030d0e010b041109091e07050703030e0f0105060f04050c030601031d0601060518040c020d0311091903050d0503010b041e0302040c0e030607020102 78
    0x74500310320031502404002035210585041d500c0c00030054540302d4035000c1180009261140c55900c1020300710003440312906405000c0115203800710030038004911000174028003809040c4080132190080d14008960803013120380805441903860844000206890301d03149003520400c0d039080b81070130040d5400400c0050b4000c500403c00c5902c203040101d0011001c040c0c0905007001281c0ea42000e07516403007049168541031046000740141103d00300918140701c03d1041c12400010212070605603035885000c2200a040d0003414110a0b0364112072aa603107500008115402c8032081c1c452408405040d18001d1920b4041e02c1000c0c01160300030000c0c034881090880c01b400909030350000301c04003080702c04000d444d04507044407104400050000468070350724000d03151400050021082103414001070190f10000e604403400c48d0001d031480031442e4821120318014000c0c43d030009500034541580005400d41019183d50304150480640d010b039954500c0580c240c0c41040c540e0250188a515038101000c408 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 44954177 1250 44952927 44952937
    0x40302071509030605090a05060a09030207090b06090d0302030d180807020405060a08070603020c061806070c0203011e0b0f01051809090106050a0305030c060901060b0306060a02120406050c06090703030503010506 93
    0x1071800340242e5540344c40700e10807540c003561031240b2504011002414041d080100b56003210407003404002810f0143c80c025220300850081048103508c91000725940c0d9a010203581da0740800074070202c070a002070319000e5540d41c8184003d0140900b480f5103c05040b00045000c1d2402e500078085500e42801d5a080000418001700010380c049005c0710040f40c040001c10040c0007600789034400507901c4c20707880022840c0020041075020510102c14129094141c0404d05903000766960409c0070b00041ea40c40002e0240190146079004d0070816030214000c8609070b08080c1c036448040c0e500800c440d000d2001115140b24000e20078005503644494070002d41040120f29520083c40d01c00011020748a0000271504c0300f240d401a102940f0106c3c203030303000b0f0b101800601e42202c2001e001300b00861420070300481c0c6000051032188161404038520016600a000200c50a019070701d2195655880303c102510a41214001d00031510070480055081703240000c2c0403051780c1d096201c180c210381c84c001c01c100d60355020b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 44955427 1250 44954177 44954219
    0x15030506010201060b0f0a020105100f0b0d020909040f030f03050c09010c02030c04020a050a1d0f01050a260a060602061014130c030209040f0c1d0a03240605060304030207 75
    0x1c0c8520010352445401c2c00b90041c022a1206c003940c85222032402400c0d076201a0038840402c8190108012102180f20365000300c4480528894607071124994120085c000e10b40070a07002100c0c481000108210701c8035401d000c0d4400d031540224280d603040f0890485904981c250130400003041a4001580109006699640300400300c03401c0702c501ca00030505a0b04140b003014003141001c82c026403450303000941304400030044611040f0f40c844800018400c55503594615050140004400e030445109040403106801206501d0400d0003000c29043c500181c2268a614003919003440030501920200d500b0b40280000e440a140c0710f800e01400320380840c0c104581c99400090040d05054020503401001c1c1410b1013920010380f5410800103200035640021800c8459918010028400c903030004243c1c2c0b42c0110749501364400780301c220301080c942610fa41016042402c9109600c840310400503680300546602d078001d03c2042e50320410303c5a517010a0300c00601580240c44140070702200900c1c20041c43c94 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 44956677 1250 44955427 44955431
    0x90402120f010204080d0e150708030c0403080703020604060c02010207020f060d0207120c1509030203070303050903090a03080d0b1203070f0503040e0a020705060105030d2c2106060a15030506010201 87
    0x490400c5803c9a209a2020005800c00c03080031420a81200c004101080183e03080b00c1030800e01d0110700414824040d004000e20b00100100380d81102a9040e00c0c081c6a0151400da1395064a0a000e50b0710031040321300700d4405007821b140001c214818001e48011590281040203450301c00c500300089600504040c0001c56400d0000d0300204400c400403040c1102992030701a8444241c0c04d10001c401e02e10071000191a00300030503030002940c004102c420640e018500054070751115850581584910315600d0b130310100d803910210501c90740c01d0040a000d01c4101c003c00900c000c0780c050003190024400540041c1d0820f10000020650a1812001c001d20850a407440d00d40c403660345030805402518044011035001ca05207080040401c401409440114018400c24600350002413610712240005008240c074080181c3d410b0094154425052000070010340b500c03884010803810408060034030010520510010600d1820f003400003405449a01440d00d00380d80f000107054001e0000075084904540d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 44957927 1250 44956677 44956693
    0x6070201050706022215080f01050910030501060605041e0e011a070b0c09010807031b0e040608060f100608010b250b04030207140a0f1703040f141305040209040212 72
    0x2442a40b50b101851a51700001590b2a0910145803016254160183c09100b0800c05100d1305032988888641101c9088440010316038640e0300048800c0c0903940024029801e200000c50b2468014000d001542d00b8007880130941d06010b5216140c0344058032403c21200500001070001d614000d1803801411000200945000075558440709600d60486402208010110318441d182d84d000f2a540d80114081c0780074010a15190500180540300003a260305026804409000720f840d00d4010000818000095800f6031401d5a13504444813002c0f1640c10a21500300000b00d544c1c0e02690000d810703101c0c500c0c00d5508240c0c40850360059403070181504122019030f017609500084c98926103074407070ba2299003c0c000c1c06113042c0c005020640c8542c08a84521044141032019461718038035a001ca85071810b81e041d201d82240700b014218132a030f0300161905007100b04049440d401d407844c1d0b10035000d000c2d20307050815038010308520b00321f5000b91402503010010700046800740c80e0449d1143c002c0c4144070240c031030f54 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 44959177 1250 44957927 44957947
    0x206030f10080a0803060114030906011e0b0d020705010c050307020712170c0d032003060409060b060f0c070b0301210302010608010c230307020601090c020a060903030212150607020105070602 84
    0x100c1d201040c00c40d401000002001b20650380002180d28a5030440909421801c0131059141c49072014001d03104000c122000c500005010719070460020014182d415645807207220000010f9408560291040e45c208041090035920074402c403031050000360302500b410307405c14440f0041030455482c10b540310b20032106141100707031000c0c004104400b0034400404114100c8034000c3c0641d0705c041d900005860101200b071004003040411030750b002c3d00403500014002c906213041e10042201380e50b8203030082d0006c9020501c4182c500000c04089617070004540d01250b8880740c600e10f61200340a00a081c4000105a08965000d0f8071880c0c1c0c2540700e8000810115204d45095084549441e028000202c00d8030751200c054401c42d114800b40040704441c3c038514030340400d000c0d40c3c031641032142481c040c0e65280b624254030b01c20312500c03000a501007428050301c4110304004001c0d400500042c401c518081e804180001c06524414044190250010741480d5958005498a400c400e00a68045400b084401c2c49 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 44960427 1250 44959177 44959183
    0x2040e0c090108010b0405060405010c051c0203030a050a05060607060c03090206030703090606050a0e061c02060a0804050c0102070602100c1205040b012409030609080d0e060106110304030206030f1008 88
    0x30030051103480986a89200e40010034411044c1c1c030440c0040c50410003031109481c0d100440e01582c0081c24100da2024051419518000c0e102107140c02020090504888540e400300066018000c090030501040d141c09032014111507081c3ea40c290300c80c0d800c012440000d901a0022480e1000905001070684460740101c2c042d50b2080b1059030000390381e42881d0003085000c1c420034025007410380702000c0c0d031403c01c0041b001070340d00541194824108a03c0d00c01f011146600b8a031000355020700501d454020080c00500600c40c1540e08441c03034066401405c1d025440051480100c6240e0f80c0107045c0d5a00c106549002046408020300030099031958010350040203014480c015441540300c080690300d04400358420000d10304605c80d000c003c06102c5403a50394080c501740c00b0340303070007190014241a0928194606118a0b400d0b0815a070405c0d0b0a0501c400000c070f80281281c03496141e0345d15541c0141c484a4803441030f0700000b5408181400407901d1411940982c562004800704500c0c0007585400741d07586 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 44961677 1250 44960427 44960431
    0x4030e0607060f06090f021801080405030d2405030a051c0e030613020f090705030604051012050c0f010512010b03180708010c09090b03060a0b0f13090c050a03051203090102040e 78
    0x3030f41912240d040140d40414810007540788010001142040c8000c8404a084190f64460078100b22104000c18140706003882102c00001c1c0b139400c1040a0300314190a400e10284c040042940700c0607010703000440b82030200f005503119a208002d4591f031884000b503e070850b1714005081040003282120144162030400c8014081d0400c0d070100300c1e101c1598410400d01d08010a0b426018010b0501407103522500003066030b4010f40c04407804555540d8401c00d03c010b20403190b1052844a81d2007280740309100c004501a26404030540c0c4088802c07041d0343c0192241d100e42c0c0c0c01c001d851281000104202e4030510701030f540000c0a1051900c5030065507440e1403402c1c1e80e0740c02443d010b9540711501510703207030064406002801c12075818014446070320006600c13088010300340307050a6110f43c114a52903503080400e491052004208864429010b4081c0300142001c1350100c5012400200c040746034070344484500101c0703601c000200b045219804000301a50005000182199021b1201203419640313445198 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 44962927 1250 44961677 44961701
    0x20303040f0606051207080628090303021917090c0303160c0314100b030118030503070905060301090b01020606090408071202030903060103150506040b0f2e0512070f0804030e060706 80
    0x70070070b641416991f5080050203010904410001c90500d00c900404100c119086400090700149040003402c0a6000e8420019032150094040c0303000341445400c107821000f14100295005882e99a1120044e0388074449200e072070303160340f0030f2120b04443d00360000c0016940c0d120795001c0032256070725070707804000e203003540e8940c2019001440303007000018580c461482d040e03008030300907c1200c04140320880e03a0200190060b040001c00400a50014002e107951401400d00dd4030b019070f2580e482030170030020024040c6d098014050500031644500d040d141c594051504018500d03d0f080c015594220541c0d402500c0c10300b9401306012000c1c5e60783d030520045000794000c02980074040624081c0c5002c450700200003d00c10303454031031100b0168994441d00c203001031007981c800b031081c006450040c202000c0740b40311294164080303020440555001c1c02400e010803022216803955121004c00741c0e0031000300386a0800164140c400540803e02c580b0b0110806140034080a19144030f07030300c81c40181c4003441551 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 44964033 1106 44962927 44962933
    0x904020d06140106050c010e0a0b06220504030c021f0207090b010e0a03050705041104180c05160507060f090324020903070e040303150501020303040f06060512 70
    0x1410300604522002000b980c0d1351034005c1941d03102d207010403415400c1090074013000000048501c0c080e9405400c402290f52100103000c9060702144040415581240c0c40c0103d1001600c00d140c007460007990740c444a1030603401408007901107094494036030840b5a055112041d80810904181c40b06044040b81e061003000040f070b0005220b61600d90b11000d1201c000040010000302da0081b1802501c0c24050104000c05041c224011445000d10362185180d8111a240c6994000e07040d12645003450345c10a1800038040101c5050341c07008440c2c0c1c0d840150248101501325180c0d01d001406890b1070441e20f03055507500000d01c02c038008041035403404030f1011180d5a0782c68040d40c200c0080502182d4226641c3c20102e1302002060303406801003403516035a103c10b030140d0550502a00d006030002e52a50300c6540d0790102c42d41d821a0283c0d9020b83e00c0c04045804e5813405100d8a403983c00c5070007 = true := by decide +kernel

theorem cover : BRFrame.Cov 44784177 44964033 := by
  have h0 := BRFrame.cov_init 44784177
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44784177 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 44784177 ≤ n) (h2 : n < 44964033) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
