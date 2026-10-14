-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0817
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:58:02.583802+00:00
-- url     : https://prove2.me/submissions/7ee23ab9-77c4-43e2-a44c-42a2c179e180

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 146762589 ≤ n < 146942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 146763839 1250 146762589 146762599
    0x70e070824030a03030204050102011b05031501050409020a020f060703050f041106130b0a030c08150405090a0c0e040201030b040b030601090c1211180a030816110405040b01080d0c0203070b0306 85
    0x301001c0c0068582060604120000790f0041404c00055809000350311848280c21852799a129981c0d80040c014003005101200a446100c4c26502d581d0240c0c1c119400740c42d10250641d0b880d00c1c010800b030741e03c030044444d44a1314030400d00001c2c2064030034862a4001da00001c46881651901c0d19407144031070607440c42640c0b0100410511150b02c0d00c10804100521000c0800740d11240100070141c11103070042c05590600c03017081d0030800d02c1144400b5007291034104840c00101c0c0d0310385074045481d201d100c0e5402000580d0012020880081d00704400b440790703100740d034184180c01a40c01400103071100c40c003d00760164082001030041d0500781c0c100080c10300351031401041c40c0c0c485120407030507202030108070100c1003000180d00809150180f0722442081701075a91391001869540e03aa07603d80300322000781e5000b806000c00c06017041a130350f1400c41500c4001304140028145402c02c0d0049600a10a819041c070a00050108080c0184e282407081a00100600515494140500d00a91004110a0f440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 146765089 1250 146763839 146763901
    0x30309080d02030907030b090106140d06110a080406150308090d030527100203091e0301090b01030b06090901050c09010309020a03050715110601150c0512030117070e0708 75
    0x1040140b000e148240781c2d01c0028001d40f865400c01c02c1c085540a41310b81d1259040440500c40903510030b002926020041d500c4404c801020f00745040286040101400c195400046503614650b000c0d44c1c0c24080c0740103000c1000241015101e940c003450043c480241464010b100c4016035103041081509000d00038206145805107920410004174050390948074290f24840c180701480c206600d0016010045000075481d10074020f001070b400406c0d4294a50315091104001100c0392820340080c1d10555100e0700003621540c407803900a00300c40701280c101e030049000c000003e0030040305028207401441c00700502883e04450034011006070040c00b9090b80c01001a0200000058042094000030981c3c06224a41b43c0030b07000d8000c044588016403000e07294001d000500c80e0205080712070403150100e08104550741800d2074018100b4150320442503900304040700001d004044408200400d030344100a50b20398648581c1d41c3e101300c080a0f5600400512002c00295501c0c00010840284944000408040d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 146766339 1250 146765089 146765107
    0x1406060a090e090a110a030302190f1a1618060e030a0209010801020319090804260a0c0501030b0402070b13210504031a06030607031a0303040807030201230703030908 73
    0x2c90001980c004031164411030408040c00558000c4d2412850300322001d20131a851070300e000750354860088901850008414400017000010342441c20003e6010280c0030138030074140317140403203030b2021245803200c15410203582c1801e92080204c44052a28440b1081c071450420004680080c0f4000c54540c05208981003c00540d644210b4070740200345034000543c0e80e284ca260324400d081d49d0300f400c41c8049420492614000380c11b070400d81d01070b528440c00307842d41a5100080d8142e0080c25035044802c45c068401c4007004d01c525015900d050f107000380c806100180c422410300c0102e1099003805420250304001080040c460002c14004450007108504240e040d0011300800c43e642104096002c10b07000030302041081404000e180c4c0d003c80d6154412580d1600e1f41c0400d4941c01c005140c102050340c0c07000342001e40c42e501307007099414090140c212521281c03550700941c1c0c0e4265601040e0f01054040e04000e40312a800c03011008030350172030304001d42096216581038010b00b02d0801c00b1030704100b05005c1014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 146767589 1250 146766339 146766359
    0x1014120102070507051809070b0703120e0606090c120121021302040302040c05030106120504140a0506011404020901050d020d060504050405010504030807020f03120612010606050a11011406060a09 86
    0x42d040d4003507006012a20b1a22003088a20001080104c1480080301c00b00034400070301060110441d007100040d980d4410f003d05c1c040328001401c0134146030f91450081260305d00000003411511544091711910b0303194503100a0100039000d01001314000c6038000c0c00520120741302e1843e010711540e00b541e440b1001c05065000032940140d02c1e5003040740503401700301003041d03140c58000c41c2c681c81e001c3d09180b481c550508a00034900e240365080008190340312800720b0300308149040342c03000541d40d190075207880c80b11525006444140a00c19600c5c00c001e04a01070740f96107480d208451040e001612a50f00e8901c1da107401002a4212260302c003070281d0b80d00d0b0002030a40b540d0150900c42c51282e000029545007030b146c041d042000203441340c0d085611118001907040030020440c0c00103460a070074070072103503a9080000e0009111418103c825400c2080000f032298103e809008145030603100c415007110b024010034226001c200107100b100741680040350071030800038020404c038213840c941915120344a8060302 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 146768839 1250 146767589 146767597
    0x50f0d061d100f09030801052707030e010b09010f2616030203061506090d020a03060c0906110f0d0f1b0302070504061a04050906030f0607261014120102 67
    0xc0309504500210b0210300031a00c5402040c00740d50008001c003400c1510010005801405070300c4c0603d1004a900150700d008000b03500800c4030042c54100c2c01d00c1c0c1940000c014005140d0503007034541c2400241c1c901c41c41c01c1c0201506a0303045030f6146c99414980701c1409921000c22020301c6d223281585c01c2c21202d0b40828800329603e1386407480c0e1080c8882c0346205052500c10020014003e0910b44011007485544000441c1d8502d03800b140c03c8140e50806000042c4020f000b540300521844c944a0a0310001d03030881c1c0058112501e584800348150b40d5000d0090700c0d40940c000b21034441c2c000f00ea103c9081c07270041d4480c844268007440c01d05800c28190420024884082d0401c4c2c01607841024100402e14141c017030300004e020b640a628201010501450b030180c0078074003807144148040d00025215840030083ea0152030322410440b1854141580e000c1c0a03c5820300c40040041400340361582c0e00c003040c03403156000e8101075549072591440c08141c2d2001d0702c058090381394001d0708800d03c041000710900142c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 146770089 1250 146768839 146768891
    0x9130b060a050f1603021f180602090102070e040b100f0e0a05100b0a090e070f0203090d02010212040e040b010902070218070519020f0c010e03061303090302120f1006050f0d06 77
    0x50105130295540030b540001c0c01c02c41c021200741041c0392230510b02001c00340041c10340c0e8000e00158880040400503400c0c000740d45c00804c0c8110305001001700f4844001c80080c014602e000130f00c1d1495455080e108a0684140a618101c0d8804c4002c96220301d40c0d6800303281c1c0a0103c41c0b40800040d12007101071070710307400140340c40b0001d20a03841c1805000082c0d25031541019a030304180381421240e00c40070f07440c0e000b00c02d000d92180150b2300c510f000b07590090020700d42c8950400340309541c1f02e031140b21015403602d094a00391114030b004c400100700281d1f10300c22216816001804604121419044040521002003c0c02c040007014003034031100010703c0c104449107441c243c01900c250700b1222b024601c0d02400300b0380b1504109203400f0f1008662408a426a00940e0b040300300e021f80034960400703844187e8a6403001b0b41001e1b0300380342c2600512001c2102045542020305070342c01140c030a010740c416281701c1d0090541c06102070180e40418502460801603031841008042034290b480072159184250800c42 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 146771339 1250 146770089 146770093
    0x9060c050a0201051005030a03050f090a0314010b011704081804110406081003030503070f030b03120904050711121803151e07050a03050408160809130b060a050f160302 74
    0x501881c10350280525a130064003440454000c40ca46000681e4520000f03c003e002c2c840001030000a05982e0011110826400752003184034507541c0c034048a8403515042100195403802e003803880b0540c030800030031450b0039840004160343c0d220b90300c039440e4030392010040d6820080403507411261900d0314015001c0e40c0c900104880d440b145841009000400010000a0b09404206040c800281c0242c00c0e281c02001c1480d098010b04440e0b2025001400000081a0315118030300d5080d1b0f00c025210010712501e00c044c0da06111984910740e080c5c801c0311034003c16a0031900003803402c041038941a800b40c400b02c0d0081c0307400c0034982c20040200e41030481030380c01d4412018a500c03c1200c0180840103a1a940b210158404910301d03181307134000c0043c0504002502019143c1c00458103100b0224141c41d00b009803a011030b6914948ac0c0303014903141d8040018240101c041030800c8161100d5440781c40703103060024200342e2510324403040031282644400c102303c10036602400040000340134040d114100314480d0300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 146772589 1250 146771339 146771347
    0x30c0d18080c1608120a14030a1d01020723030418090c0506190f0e1e1912020405070306080d0c02090c041203080907150e040c020c15070609060c05 65
    0x4240c20002c41e1042d0045001010300f00708202e0500144803400c07500aa6945901c03003030102011030f41c0c0c81c00c0c22100012260048240700c0b80802c01d40c001014243c0302000003c0400e02d030780c1c58034241d000c2c1c0800070f40511003048414a032240d001070f29900344002d10056902c0d00351074080da03110880b6800d44050f245642c0d501070300100850307044000d026040403203042d4280b451504103550f024a18003030b0401006071a000c80805c00e030103101078440c5500d0007003080803400c42c1c0d9041c4d079038801c25440956100b6003070500403285000703510009105403800260b034003440b00d991b6028070000e403402422000030142d0340e04000402040078010070300c0c0560a1358070075086200500411512120281a003402c03a04108020020803c1c64800d0056065242c208030403541d035020800741c10410070740e00180004103d620815019540401202e8041c030301100c0421a5412425003241d450b6000740c61980c10a807800300e095a92101d10300504840c0e489150086088003041d80d541042d6104820b00340080340001c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 146773839 1250 146772589 146772607
    0x1a1009140307030803042405070f020c010809030409051b070c090606031103160c0206030702010c020f01140f09010b030706080a0f1109040c030b091612060803030c0d1808 75
    0x480c1119415044004110352030850b01c400180d444042d00041200211034054901c00f031020210354a209446001049585040b00b0042c2000340d801440c00c0040c003891900c10143d600404146008000c40c100070740c201401e202001c4020a00540b14006652540b405403042c002d941d00100121841400b004580c00e240192074001d0304d5098000350700341070800080580048000081da6841014141e81e00400c41ca5580c083e41c090260040194004000000300700b4216015009401440d1a81e03007120034022042c02680d0803504444070381000180c81d000030481c4190391070f41e0341d604525150700000790041c0c4000060314091940d400f840101e5181010421444013034070406403000c281890030300180d284050406040c5c451000c0c000d10440e501c1c414041e4440c460707440301c20903040203800c2c03880b142083d00c100321007003070720407180400141151144481c9020134098282140c003140d00a5085031a8942d0492803900004158070109031b4031064580c02c040c2070392203031800074061078070390380d94400e00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 146775089 1250 146773839 146773859
    0xc03030a0c1523041b03110a0e160c020307080102042306070b06061b0304090609240e0c07060f0e0c0118090e150106030203090105060901030206030a1a1009 69
    0x803604010141d854400b040f104000380060000c465400412115416550b41c90800408001e082d8115500e600c8407401108220b541140403410140468403219069592201120240421200720302c2c1042ca010301691440d0007448483c1da194401415194510388072040182260090b038401880c440e081d0003130036a501d11143d07050420180585030145840456100e980c25070300f02410711070090b007001518171041e51140e03069075030381000c501c1500c0c0c1d500e6490350270750090040c50041c001c1c003610b403c508030980e681b4a101e5000d08401d441e42c40c01440d10781000c80c0419800104001c00744a03040120600003a440c0c802c045604110a000081a243c0d00407d0b0780b0300103a0810300c0741408010100d020805020114940c125080400c000c0341c0303040d1021031541003001c80000628a4915a000803c1664041e000b451103480d040c0d00800c0b19650301c20401c90700030400c0c480039420117802c00c0418021200c5411040c0c9017002206a940030301e40400102e69541c0f00307032120703000007040c54000740084902 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 146776339 1250 146775089 146775113
    0x9040b06010311040e2a070b01080d0915050a020c060c06041502030709270c0206040323091003091403070b0109200d0b03010c030f050609270c03030a0c 67
    0x4412415130820381003140c03044400c4005003142d50051881c0e0050300008100c60b4005c00031625144619484504500d000d01201e002030080c06101e0180350350503414544a010020300b00c0d00b410880001003100440b059460f03a000c10011001c50160b0500107480362205802015a0001714004001500cad003400c0010322501400381300a40c0070700401c04c1c02000d0f41d000c40f415042d182c1140c1c2c81c010025003111000740c600c1d039400c41040e5580c188500d2000f0f058001c6105807040c4e01075124030801d01040030b11040300c044100748025030b5480601940001d41844003032040344803010305000075540001d031600030409810940d00b603503070b600026500701009440494280100311500c0d0501c4034807040c19411070030807509028540c645e103000c02c2921208131150002002180f015000b000310704180c1301c0040c0a000ca10a170391500b28240400b0806504120040c176104800440326050f00180c0044400c030789011b802a511094460b1310580501964140020b104401841c1c4502802c10054a050410407103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 146777589 1250 146776339 146776361
    0x9041b0206160206061e0a03050102030f070c0203030a080a09170309150f06060f2110051c0602160c08030903010c0c0c1e0e04030c0507080106050604090b0f09040b060103 75
    0x4880100310b07203190002040c94201d00122880b140452881d0403044c640c440950086a0000419000005000040d03000b1402100c1c15101c49503280d881c44420380d070401443c03070300942540c03040101110941c410b4000f69001210780d4030100b00c148280d211040100c02d182d0106100c0700c4000b003481175a40d01080b600303881e0750403103410503004d241c400320342d0144d02401441c0e1805074000244100d400103100045400f40b01c0307074240c43e116285540f0b48440b41c0740400c031002c5000c040486d80200c5ca0389401c10a1420703410b00346925102140e170300e5840001a4205405a034060782d4080080c40000d000d03070460b00c0c054a112001551a82c031510101405d50746080103443c00e10084000310408034201304410401d580041002c03044541078020700c404451080c0e489205451062014041015440300d00003070140d020348119280940c072502420b003240e40ea4851140d020408200070042998150070010030307400002c0070b1307500200084001ca007150100b1602100e8202d09441000030035070f014403448007645 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 146778839 1250 146777589 146777611
    0x20106060909060f0b0f12040f020a0e0f0601120605030307030804020414041e020a120503030402011806090614090a032d02130506040e07060504081002070804060503090309041b0206 80
    0x10b19041004094410394001c0440d42d010001311020f901009500325600c4040104002c403507031420323052a4098003000c0c1020bc1c0b00710100b644c0000d02440e1040098040c0390401401c10840d12a1030040d0303815064070510054003912030100040d15038050016084c13a5002e6250350b403861400b441000102d84090848504041c4040d0901c804100b4118620f050303502043c909490031300c141e00000b43c2c06005a80032a40013100354441300d0030080c0c08406940030314400e80741c80301c90001ca1882406c2090050140e4000135140c1701c010000300d441164440e1440c3c480e480402d1030320303201c0004100f40c240740d03400a850030b90600e60030450901004182e8416104042c8410800480580c000741c40207060200030443e06da00d440114a032070762254003850440c510003044850055446001505a0300320f881184194000c0d9482c3c126084564001c0300c660f25400482580707001d0501c00262081c2d040171703000301024030040c0030210390b41d00d8a1250303015100c841a03c01588aa044800030725014000306004499 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 146780089 1250 146778839 146778851
    0x801141003030e150f040306091109060906060d0e0f0307051203071403041505040b070f02281704090f06091a0f0102010207060207080d141603020f0403080a020106060909 75
    0x481e070b0218842c440c05000316401d8031900c40501281350745000b1900d41081c05140041d00004000c1d00b68020440e540c03040140b030780901c070794104108203110100d4030303240c000700200b00203036407072400000900c44140c04090010361108443c140a1801a040703801c849a40d0001a1407010320808100e601202c40b03060020a25520348031800404007004031511504030400413010070f00300b01c0f04108640001002100c100402d10307043c141189007000594800c800b00310114031000c4040c1c400720b41c610741100c104000003041100311030508007003810309106030380c114109d80034141200c1a50008000421200001082201c0c5d041f00703203808c91301c1030340c8402c10003480c2540a10003080207400c45842010120303034511281d0b1000006030b02a2043c403070020116440011300302e042009100c0030706089a09000100400401c60003e400d2810703007038802c1a480070032030b909a03d2292003034004005a401454020741401c0e0380c0d95540c44d141c2c0020b050000540d455140510100da48030f1100001406e1402044c810 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 146781339 1250 146780089 146780093
    0x50f040303112104170c12030403050403020d11040b0301020f07080705161e090e060a0b010203130609030507050301060b0f070f081c050a050709090515120d110610150e0603010801141003 82
    0x1b44252061280c0356051f80440014185801282690004d58019102d03400c001e00d6450541500500700d070712981306614064605509080c14825100c0100d807108540b423416000352540783c4c1c1600f20880031192849034017200210009454409402003118140b03680d014020700c5084c00100001e6000f00d0840380c5007203400310301c08400180303c5030441e03042c44002134800c43c440d0040b42144509404101071101c02000003806560000c001fa00705ca000384243c4105a48513810182a2f407500d00c1a950144070521002900e00c0b6001c004042c2c56204a164008808955440c9156a0007054201c101580e10300112500240c96000302036000c840a03508100c01d2410100c00f60508140e4081c40310700d20358420010701040e03100c119442c50b04000500070f1010072040820580d60341c0115400c080040c401000c1101e41c100c000400e0707030050040c05441400141040380843c5210b1040700018104002e140f800d290649600c0019070207405034400129560000000c400c1a0b0100541800101031180d141040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 146782589 1250 146781339 146781343
    0x103060b01080f0610141303060e0102090d08030a06051f08090d020706030f06050d080a020d0c0c03060c120504050705010f05160b0910020408010903080a050f040303112104170c 78
    0x2500c41030071200d40e88108070001007286d0b01c02003c14086504000000c145e1b00350028a516501228411a020f0284520103a00b07a0b0903801560442604a02d2030720b5910001b40080010315807100303849400290481d603a000050103d1107946541d2615440f840001622a92018600360301c0b04202d00204004000504d00035954181482110101960340004013040e1060350400e10003400001c205400903121400e0030140d03030740406000405031140401c03400d007a81c018503500c01c2464110f940300e40040c0c81e40d110318019003461308070103080290b6140c0304003030000c280c8204c074040c900680040000e113081c0400500074808020140050020500400d84980c0012038084100c50703120844103443d071a0000041e180c0f0445c001039040c041d0010401050080d4154080c0002c0c6000356102c26268981007001d401300c80040c3c1c0c48424030490b000018021030300a0f00300307101e506104182d42d403800c041100030b00c2030003140390180c0094180003400d101c2444014a2640c1c0f062803000300062400592990300ea03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 146783839 1250 146782589 146782591
    0x2010210151a13030206030601020c12030a021e0a080a0c080a1d030f03220503121801080118050903091e040f1503060b06091002011508120702040921080103060b01080f 74
    0xd06c180f034004001000ca92084c8850710204802802001c07140e403100b45e50948a8224100c0c0c01d00500c40c01c8201d80032520b0244800000000c2076024140c484415240c00e68181c0c00030011a00380700c001080200054480d20091210701095521851108202c2c0302c040780340e0301003904a500c2a4403091000c2c1c40d0020220072500c0c41240c1e40911440151001d10b100c00700641a030000d503140c02016544400083ca0200809018960a40036000f03844101e00544010314203020725581c100340e0021707100c00c1c02c4965200c0b13038007c0c0394502201c1c00d01c0e540c0c1001802c8204501c11540000411955140441c100381c018084101d45040d410302c0b065202c01564049403800d84005040c15490350900083c0d62150301c02c0781e080c081e0142c05001801c406d940041d02a040c0b11075500700b54107944034002401900410401c07207846400400c1c1c1d140212a40800c005003402610a43e025002c8400c0b500030030742d03001c0c52408542119207800c0150343c55404c0400495140e00ea6a5050102c42020458088055404a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 146785089 1250 146783839 146783843
    0xa0204200d0b030705030f0319021b01050a17130209090d08061504030b0406020903061b0a0f0228030807030b060403030309110a0306200f030a0902010210151a1303 72
    0x80d14880e40b0b00291412495070700c515090b00a40300184100000031000301070303c44080005804c1310140c2c0f2000c80e554a00c501c3c10b44c0380225100c224040d039603c02d90051990f411140b4010701c40030320006200e4124981610444e40314419607017480210b0a0100e0301e540d003c160403005d410251000382018240361001091148580340c6c90f031158480d07000d03510950b000b550f04100410003900d45460420001c0d8007041c0128880e100d00c40c001500040c2110051044450209100342032290210081c1e581961801000042d40100800480d00003030210440080821000320721480e90110306005c2c00321100500750004160801881c407205880307000c00c03101125898940000d043c0d43c036090802c040c2d60b03c4891641d20980c002c07000802e00203690130550b01900d1307501084615042050311008548520442480c2e841c0086c400642a00c3d400ea1005040700c0c010b00585041040901c2c00904854200c1200d213000d884401c0148a01552040c00c92524000800d00c0d916005c0f00c0c400640301e8031424800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 146786339 1250 146785089 146785091
    0xc0405040b010c0611040320030c0f0a03020d0f110105040f030809150304050d0801060c050705040e07050d0c150f0c0f06110711040c09030209040f06021b0a0204200d 73
    0xd110716691103480c00840c51500303c0300400c10303e0b003803508641c080c2c1d005120656511481c58a203d154140d84500b86064510040c000c0149500780001c0c004a040800031250380283c00075030020268403070106024050741302d40301c40700002e04c143c500941e20001c1c104130b0a0400c1010300080c806401c1a40d1a40152900240010b0b126050320300028520003412815440005020062008001c800030764030445d00460384600503a44e8a07507904070b6062105003005000d03640244020019400d2544c8030594031040b51007921301c0c80d5114804144400040e6100700ca6545098000b000303a03104191341c1c10f0f4645c095140042c1040004c141c020314143d150200034000304110019441040841d1717000100302c1d51294495a00c4140d2800c100b02840300d802c1c07100f8000e6040001c0c000502d4801c4d0782a005176a4014137608654803030f9100c00c110000c080700100c0703040340e003000f034054401d1b00e0701000048400a0001804403030954814401916907032159401083c040c0c0142002e205c11031400c2c0c41d25140d04000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 146787589 1250 146786339 146786351
    0xe0103020d140715050c0106061b0f0501060801090b220201080a020310090606030905011802090129041205210d0e01020f03010306060617070507021003020904050c030106030f02030c040504 83
    0x2c10142000a15032190080405110b80307034805503004006080d0503410140200325182d9070f03260a0320700f00b4030702d42043e01c0c0c80811030344400061043c840e1009958012000041d07080d44030221103003125080281030300c1c0e01049d00c08004400d101d4141841c020401d580068244404a6001901002c006841c14400030b030044009006080116507000003008114414000b0039aa00c00240040c5030301d4100b51203950921740c400400d00c5203ca198240c00d40c3c060805051a03103000703201ea10507070400c804803030f400d02001d0f20464035000150141010384003041c50240d00c06441d10300036203402d0311070111010f4215424440c6203060801d4055800c102c8443c10081802a1400030b103a0081c071074208a01580400403001200340081580005c0c00d5a865888400c800448403941000d005000c458001c001001042180014140b80383e4607040b09400e42405030030f041c010381c001400e445040301c02c0c51610001000402001d0380c1800351003440300304850f0442c0365040022800516100b039014030740c00b50342c0b695 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 146788839 1250 146787589 146787623
    0x130203070e0d080a09050301020414010c1b080601181814070914070212120103030509220507030b061215190e3319090c020a0203070e0103020d 63
    0x40204404050062100c180c80440d4030740080b0f59008032400c0c00c000f90802d400840c0c5424144226019201000041c40441c0340c00e00c0111140c2e40518070448021810300c13485001d1180d5014140c0240107849c0260030030358142038821200400e80641c0c801a1414940d4a01d815021540d80aa0f5607070008408c012510314042014a4031000b940b20f081140d1800d00102011081150030368005c840035030903145101d110b0340b05000d4034058800c1309031103400024010800a406040140005807020380302886103403c0d40000003031021170041e40502d4a4a4504204507a58180b159044256086910702d0601c4190021410b000c000141040c54022203407508816541d207545013000b05410810000c2e000030784900007101854401d07180c481d40ca021403800c1728900c0e0981c080c0c0714400080250b0810001070450304110180c801c00046540305001300e8404103404071980181c0342c085410381c000300000c00c2c3c0384c814117240803010392050522190440c018001603031220030201000c0d400046807a40c0840d41 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 146790089 1250 146788839 146788847
    0x1503020913031110020c011a0603010603050a06050607031710120204020c0f010204060c0309270506010c1203060f09140f0c13120203210901200303130209100513020307 74
    0x51215044c440c400b81d0300c20700c01c510303002002200000d5000b4404600444030750308000e004250044e6109400340010700c8814480c0e401319078008141000420003e0f501e50106406038803041e015400030301d00d0a0403030042010003001d00c0e0000e841c0060302a05038170340030300d10003044d00302c0380000c0c41650000703941c14002c40108260301c030315844100215a5103503140d0000c3c4c82d604103914114045070301c503440001e5210340c2290140303000c401d5044010010440301c601d40014030005254505102905464202141d4881d40c6c14000000c035840c005031035803d00c1031181d1281c107542e128042e03041c01c0000c1c02c0b9180340385110703ca03002410300c04801100c0c3c17225622071410340204c0500071108592400c000810604d00034801480034025001c3c1c0754110012154804100d00d405001801160100b000800301d500c145004800075000e09041e1641d582d4046c00c05055a1040d10b5888100d5880300c1001d040d440c003503040c50f070408002d51030110160320301008680140c00c85030400400340d50100019800c2d9000b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 146791339 1250 146790089 146790107
    0x1020a020a170a171c020901020d0f110d030518030705070620030712030f0209090408090103020408030409050105010306060203070b0a0f0b030a03080f090109030e120118060c03150302091303 84
    0x10000604d1500b5074001d60700d4400c4d4004418100c3c012520800c540201400391007154148a0107078054030124051820540d044d0100401c50030800400100151520b00c0034407a61000304055a401310b624200a60101040008461060700507081000001c0c006000002c0290840e02e0030700780070f44080c44000b96058000c0c0c550746001c20b1800005503030000c02c007009103880120481c0d900c2c02c10640d51001c003c041203000f02041d0541007000880402c002c206503101038040000145000342c80c0c03d0f2900c170590f0544d0869408400495120750050125682501401001e003500d480290704200c00c5441c0c40110801c05041000701d590b6440070b20240000607048115100300c040d080360b104220300d01c1e0040280504840304c40e00340404902142041e50180940d4240740e07003603a100103250044204110000d0011581c0d002c244d982e44802c080ca020003403a4040d102c60003407200180d02d100025026040d03c804c43c07003501014031220003e000603607650a01e190049201503803c102e4005901e400d80312401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 146792589 1250 146791339 146791343
    0x7030b0312091c0f020f1c0c03290106050703090308040602060f060613050405180106060809120a05041205100f0605031b0d03050d110301030b0403020c01020a020a170a 74
    0x24a00caa4200c0180460007070600042c26140d0048034000d612403103440c0344180e50020300f02400c00c0301130009071030858048000107000034011520124480340c8010000713503060086542100d603100800620802c0c0d9014070784014013004201d200043d0702da80c0d84a111341405494244403012840c2404d0501c1341c00040301456000c4002d5986a8440350003965909044a440b00210400b200055880c1089000d0380c009614a01549202c1820602007001400b4010512800d50700c0070360810140310b1003401014010881d40d190b8681c103060251000381840303401850b04013030300401c11448215a900104440842c2d021220034007100540c3c0c5401c034240a48600300884142c03e00d8140200d031400340c0e10410849104508407210a01440ca80103075040166401c01d500c0078411503844c0100380614000d101c0018103603c0001d20f042c1c11071819040d60800c0c0c02c2034442844000410080640410020041b058240002c1240703140701da002039030101243c011045031090b03008040340078490401c848010741d9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 146793839 1250 146792589 146792593
    0x14040201301a0f1507061103012d03030c020f060d05090303060a0501020714012003030103060b0901080c0a090e121b0601051e060f070b0406090b07090b070b07030b03 73
    0xc1d00003940d00003610181c2c014a00e44401e426200c0c05928115840400058000c1e2456140034001400b0203c2c40e004010150313400c0d903d03024403000501d44440154040d0100a1140340070314840020301900c401102d0558615400500013440400d40040740000d0075075044641900b42e10314080815a40d00600c02c0c0d01d6110b81c20403051146212011018600c80d1000f40c4040c090755075250012030751640e0074815038041c41e13600e05446d04254455660001690500e601800f920600c025910703295038001d0344140e4115550742031004052800c0074410340100781410060960128a00024014841c0345c814200020ba90b22001b0202d942e061008040c40301c00356460a40f60001920f2009114081c401e40c2c401e035000d19000428285400300d000c6200940b641c068a88101040086c814540d010348140b1a00440c14001d400010f5640380c5a284a030f80310b1503020510a0702498000e45890006d0401400d2203003000052268810f03200564088035048002102140c80d056005e600424099207899014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 146795089 1250 146793839 146793917
    0x111b0d0b0406060e2a07020307030510020306091803090f010e1203040503070b0c03180d060606050d05011703070b100302150403050c010c02010e0105030403030b040e0d020106080114040201 83
    0x441942d900840031036083d03903a2907040e95515040c107412418000951100c0d04054103015005c4001035016180d414806030449210070340f0b17a16024909200ea12041120382d80010070410389003480c4d00459001071070740e80102c03503240100013407a032a400b80080b82070043e2051510400268419440c544080c44042c14400d1500d803600e0200d501d82e8840d0180c54002d11501c2000921040c00000301c42800d84550069401e000c81d200342d50000317592020040c2d61042002181e000415020301c6074000401b442d07111160b950340c00408507019154161f014601c00e00c4840d8400741000d00c003104480c1c24907403200c826926985d83c03444c103107600c814581020390024080703000160b540c040b1a0042003a01e0003102241d9101a0340b50044400720150200240002e0740290202c02d594081c2d400766401511070304000c00e58600031004207085400d51085900558000e03840b850842c0e8084c824030000e00741c400028031014414504104013500d0140000b070400903180c856922460f14182c1440c0d00d03400e400c07810120 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 146796339 1250 146795089 146795093
    0x3080604140a2315010c0305040e1602250513150b131a090402030411121c0513140a120b040b0618011703041d0106020607111b0d0b04 59
    0x40450f40940c03041900c40452a151080228a040b4840c500c058142109983c1c0007004481c0b804644d03c0071418000b050101299101fa0303941007a01c140282140d0780344803425440001d1034109261046526004061919001391200020003800c1c0d82080d56001c006807401e0007140c0c01806e95000e03d4100355042c80380070440d855690020702e500f4000c0405000c603240c0700d54400740c11021840319516091410131060340c05051030307009140c0c014024422402c0100c0d06a0208602641107405a101c41d0442252000c0c0f401e0f0791200c041400b0041d25241c5e050602000280c0289403850007000188032180c6000303601980c0350308840340076140840c100300320349060303250041c2d1088090b03c0840360710385190000340c100d04140c081d14022407400780340590b569103003103411940c40b0741c44030001e59540030401012030300c07290841d290601d298040c0384041d05589807000007400c04201a20704400c1059080541c00a242d0000b00700b08440b0000c800702c0030713489610001948e8200d10380310092140c0700c50310801003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 146797589 1250 146796339 146796341
    0xa200c03030f070c050909060609060409020306090604060c110705040905070b04060908070506070f140c100c050c03070302150f0d05130c090e03070b060609060301081b030102070f03080604140a 85
    0xf840d904c6824803040f00f58490f010003100c00030803100c502c081d500070b0000030303207602e401c1c8842504940c0180c030024079580075801180c2400000c50309130b0200e0703204c1c04c2800b080000c01e1080b01e410254500c0d00c0035401c0981c158079a110382680c4221449541c61350101000d0017024404a4014900b22a0040e5a0b40d40e03001c0281044540e840707441c0050091100c000343c10b041400031104425407181c50003450b0f40043c1d80b00c840d107101c0400da100e09031003181001a030035103a402c2c0801d29000e0f141c440c040081c0c0b003407900301d25020082c01818080d4001400400041e22910382030486540c00c40280342d1140b0f0020315901c05801211424035200382410b0620001d01c0341101044440c500640f20360050759100c00c40342090701c9180305209441d90007000203a02044c1401100ea40080e0000c04c1a0f00e0080c0031400111541c000ba08a4030054000801d8074180110510000c01980d40650007541051005e8440340c81280320103001034107001c8480d00241c0707540d0f40c41d0b009184810b095400e0900c00e09250042d40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 146798839 1250 146797589 146797597
    0x801060210020405010801051908010e0c030c03010e0d08070e060301030c05180103030909151205010b0a1217161202060a14040c0b160f05010506010909020a200c03030f 74
    0x9405030244104092855009000700c0301500c0041e12043d0b010392801d410b001d440c200340c40c607692003074180350030210f0710440a0144614405805005007a1418044101810a150050401d100e80c0c5004074000b40408045020200d420907070600b0304150351500016500243c2c1c0592160780000b00000101c00c01c4400f103030030030548005443c0007268400039100c3e503001000030700003e00072840641c4100301d00316582e08140c44000146000401c5503940383e495103212004020100e6150751290242c1000342019441e00e002800c481d941c41c0c145601c41c2c4c8810f03100107142e011141040100103141f080c503008410940b503186602101803000b4620120000f51640c100340c400c40ca400b130401c4249a5a424169455030103690805036800718580786c005c0c241d02562041e8101c0c0d1507548080564030100c0d0071110366900c100d028030004141854070000040501031030b500110480352040c42055101d40d8804d401b0711405000c034030201f0646507208402071415001000c05d41d03051000140c6a002c211340c0801034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 146800089 1250 146798839 146798849
    0x3090f0c1e080309010c02060d060308030103080301082b03090c0b19020c010c1505040f0f1b12080d1109060d0e010e01021c0c0507020a03060207030e030102090109031b0b03070801 79
    0x180350700b502c50307801c961240b04000300940040c40380d45000000d80b800c200207001240968400141c0903559581d958240d402c2644152241000400104a00c072000d0051904400441907a08164032600c12080c62004112000d00d081590b0340e46840c040080001c000405400d00148030741d00d43c46d0b00f0000280c1c03001ca9442000c014000c01405503102e500a03819103d8142e40040c10546840c040000c0a00810000300103071184814044d144e0f001c40c94480403281698058400b41001c2c01c200350b074800c46001954485030f040c0b20300450043c081400c0c001500c40020f050003000c1100e0f1000c1220302454081e01892550000f400224107603844910752110200c08c02c5040203000441520008508074003641e003849007000c3e06242d07500318001c066800780b01c07a000c00e410300d1420181d198011075500740c9580c01c2202c03041d900182180605400c448c440311710580480095140c17200e0000000c101207441e210050806100c102607107100c85a048403807014001a03850103480385031092006159800038821 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 146801339 1250 146800089 146800139
    0x30310060e0612041a0112060b06070b0f09070305010e03090a0f0510050d06090204060302030f060910060e040207050a050c100503040c1403012912010203010f0603090f0c 75
    0x3410900807400000d100c44014806418050503214103034030b50600400855261409503641c07a01650401003140c0070303010110701805220754526007001240c0c2d00341c00c2c81d44103040038400c6034009a00304140301d600c416101050b12082d02c89100d11842c258403500700030001e5013080c00c1100c2c12030002010380004941141c1507140345035940e520015544003070040c503400c042d070302541c0082c281c001d0000b0a80d00000b510300150084e40c44101d90107d800541100000030303000030a05c184001c0302c04040740c009004458000660604032200a0030150a100f031009000003509104266551503064610b66038100080e00c100b048603141031900e8a90820300584aa4156100c03d282103103c0c101340c91040c0e901005091802e0b0414214040d00c102d06603403c0c1e4150340700c5848150710881001410b4110280d10004504200b000e02000b826461200e1600c030284c0c4180010400d1202004440301282d0ba5400c000460350f02c1800c00500e58416404e002c0c02c0807180d07120000c1c80302c5480c07500da4000720380026 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 146802589 1250 146801339 146801371
    0x2031f020315150306061e0408010c030c02011803030c0201020409241706060f061c0b04060504090c05060307090b04030803010e0c0306010804150f0f020d0c030c020a0f0f02040e0303 80
    0x100f04401c0151076480400070820601c001800ca04084000344410700014044098003803010390210220380c40360304002030710303511b62400341200c54046c05071a4440180f40000d01103941c24204c0000c0104200d6005810581c03140602100d86000f94100c1b80a445152030034404540c0950b00307000c941d603844000010400c100040024591200f9420391074400404005e0305880d1901402c010b19214501216640311030104140005080b500e03c00900c0440d03d840d020428021017000c000803030300035a2001d8082c904001c101e4000400e42c2c100c80081c0e0b00708455460700e03074a0f90394049a615400b9003009030141d0002030701200340700100c00503504031030420405072103951701e508442c03407140026149a40490351280204000981c5404c501f030140e25401400552035a01c3e40d6034800b9502e5056030401202e50016442c01502d4260242d0501e0301030b20b050512840d100d1001c007c0d5501d82c2c1c404064040c684000d00c1008200c0d02415031107500c3c0c1c00030710900a41e444000346070b440e03078400e941030310300781c42542 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 146803839 1250 146802589 146802631
    0x3080a080703020c030a1e0e09190b060a030b01020c061306080a1b12060504180b0a110406180b0c0d05030c0712030501090b030607081f0306090308040308010b190c02031f0203 77
    0x1c102e2181d0784400b80c90b100ca40d40301e01cac6410548443c4e12070011405a1110f04161050700c601c1d0140006140e680d40106821240344000f900707080046650502415042040580c0c4065501003142113401d98648044140e80d1801c40e40c001f010308100c4480e441e0300318009222484c0d441705505003004c0b054078082202c241d03920200300444a0401c01c1084030350c41c0b0031542011404001829620600d465004944800d9190120316503a00c1601f040e004294640c940f0a5801840e4003100081c0c4152004d003441c1514001541e50784014409140c007c0040000004030301c103500e1019180412b501507100000920f611a02401070329090060050b018a850200c1034507250000302140100120784402c4003e07128440c1c0b4000d490009048403800000c107220020010b00d840c070a0601490003540d40d04110300302841c0050001c2c0c01030f03000d0800250144580c0d91810001d106610341361240d414403a18858861020908085545c603031001100891042c8030041c00543c4c000710703c203c07100324099136807020300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 146805089 1250 146803839 146803847
    0x305180303010515030c07061506110c090f271c0507030c03050f0702030604150b03060709140d080c0706030c0302071505100314010e07050a03080a080703020c030a1e 73
    0x24401d0b02e0307002e00d030302c0003249000800c0c4c00215080f9503580b008a1070071489466040554800e072100807103d6100140820005a20200c41202050721501421341c03075500000144800030090200c0c0030f004c0400000ca0302030029070303003509110107198100e400b654001c07046468030743c885090b494030140d119090f403600c054410b004543c0c4080d40358890410900c12030701c048440e904189500c45da0100104000c1001d139500300308281c45144900f240d060f400d0b507000e00e408281c441e88100f042c041d0f0700201c14003030788541000458040d58000d409580c407840c11030000070021100c1d85000b4200700400240001c884101090100c2922581d0f00c05011070404160110202e100d901006840000307980600c084242d200e03001503801654508101500701d03102d4545414806021010040e071303030365400e003042002c00e090106030014903085655091240c559142ca01a44c4180c0c5284020040507200041c40c642c0281e040d0b44c0c8000401c41281c0c0c5a040300d1502800010f9070049650004031201024501c403841 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 146806339 1250 146805089 146805091
    0x103170408190302122106062a010c03151208070b04030e010f1d040f060f0e1e010506030105040f09050d0e09010b0a1e020102070f030e09090a020625020d030305180303 74
    0x50b0065090010102c4042c941014009403005c8e07808501048500500d440c40d4111002040a00c00180301d80901c41903840e0841d454031041005050400d03e00e4948401c850a20008407082e200d03150800d01c0c60ba18102c1c1d110310403900c0c010440e020400074001450345c80f050407501c4d005c3c282ca4940d04916244001d49003140c0c035a1895800c00602c45c80d21031036040641180914107200000861001e0300d902801e400e000482d0800350407580c0302c40801c81510751443d00f944416107200c85c10701d0b00d5414080491520b20050003400d00407500e5041c40e000408480d40031008990b04402950040a040c044c000e11a807109085244503184d52030002c640034200b00e08039400c44503903403503041088100302c48000880720485089000d40d5424800c420224a2060102140920a035100580205402c0411003100409041c2c6079041d4405410381005843d00d400300c88806000543c0c0e000d12000c0d00c003620340c0034000c07440d009400a48010000080540640000c0d0056014041480c8509451103041d039403804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 146807589 1250 146806339 146806357
    0x613090803060f030f01060602030927040b150a080f1e070302090402060d0507030f1406030703201c0507170604081b370308010317040819030212 64
    0x6410804601c9518043c000940450300140540320f110348208425421074005501c0203016030030001e4174200501d00700c0901c40c1e45907103429a4559910041402c554502c600500081048400b500801c5805180d000c0385030000100804090b100750716040e0207a10340004032004a0544101c1c1c1184c0c02c074100d82c1079250940c5040070000c020491640d02006071181000e001641c011504208007800300d00940205032150041c0c0e140443c151085503040c03011602c6c40041000d0241c00300041c0040e956012030210301f1682c00500210341200c40710b41180c2070302e038008050743e0301692140c80740b040340800c204120b0040f4024010f41d40380070b1b07070744d50440000b440f4001414865080100003c0018412a014285c0305403200f081c005a0560307401100e2410710742c0394075014442e96103c85004402e00c69210040c3d0300381e00c920b141c1d015842c10b07640601000701c180402440e44030343c001400c51070408501601d000f042c6503070840c0e004014102d690000c451007400c0a8006024001c0c001c20400300482c129607140c9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 146808839 1250 146807589 146807603
    0x72118030b040f0609140a0c0504050f0610110304030506060a0e2502011d0606090919081b190c080a020907030c090506030c04061806020703021909050c03061309 71
    0x982c4a80c0d45100b001d4041504a90072a81d03400020003140f00000542d001c60080c60081141c034119061004d035020056028500c034074202010000300003005030201c0d81011054071100104441d2040540b40e007103000d52402004d1001007030000a2040015405024440c01e4800d103007926212401c881300361a04840301c94402003410001070f40c051041841d0058482c5610000640e01640c50340c0c41d42c01c0f10041d00341c084a038464800c0c48403d28007017002c07030f4110340704c04010090010790003109000c0f115a00c41c041c04003440803406852079900d06110140c1c5040ac00141d030b0702c045420400c1704904202c100c081e81d1010501340007065040000810707400b0680c0003882c1030a195120324044000c1c00091102e10108038440c04002440d485800c040c2d802100d500410350303140c504101d40140016214006a606800d40c50003c000998021070300805482c2c05947d000004035403032140240c1184c00d07900500b01e0350710f400108070f501a14940038601441e01142c50322241f000b00c210b03a6082c1c5031034040c007034881 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 146810089 1250 146808839 146808841
    0xa14040e0c03041509140105070c030816020715031e150e09010b0907050c010b01030605060712110d03060f05090415020a0224010509011a0a03020f072118030b 70
    0x280c081d10002d103521030310802c4120001070070300c0103040c10740350f0000d02214100c040d03000c801200306080c0520f55001b4000c0c42c002d036204082d61030040000101501443c0d040e80c40202c90540b046c03007400b280e8050000c1e944484940a5001c00003001000d0f4214020706aa19920088039034004074010001168200c000d4001c074181013500b080b02c4024007900030401c3c3d40d45d40400c141135440b1414083d200704115101c0544840000c0041e078250b40c081c6844034105460401f003405950340fa04c003a581120b82240d41e80f49404851a8155100324210000c80d41c0c51060301c0c1d051081c954144c002c1c9090340d14450030780ca029560b42080c45510042030741c001b08520310800e0541c92080d0b6641c05014001c0c0c1da44120f441514025060301ca9440b8801070444205000b6030042c000c80c00c01c2c8800b0350040100c1c5403040b246481c450004559802902c4504007055000034540d9405c01c001c00035602c040741c024181c40e19103184400200e0038003d82404160102e006040558072403030321024000101c1e5040440c407402 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 146811339 1250 146810089 146810101
    0x6020318040c091206060e01080708150a060f030c0504060b0c0607030b030313060e040b0303070f03030c03060b0301090c02071415250803042d0f020d0b0c0a14040e 72
    0x1602c09a2280300801181d1540069076410341c0031000e00c1d080c0903240001e10b580c00c1c01c0303000e0000c2a050308880c0440d40600c804001101000400c4a02030b0200e414540e610b45030103103940003a000e035500118014884420101c2402465003c2030110303030301120200440fa94540401c3c0c0b042c05820014046500500c001888081c0280c100c90040e52000307090782d00d031070a01c10100403545401e401110000700c0c41b0141c10300c02d003094031858100310422001181040c0503a5168190b828040c1c40003401c03d81c98103510910140030740c000c04080c1c80f161041079121360311020403000a1028030400e8005100300e01000440e807032180e080405442c4054500c00c550740c462600380e010341d480b02061070f48501e51103560201c7c170145031900440301071040c00b01d10b90307a04041c1404920410801480003156142d116078102420407809541003c41e405084108024942c1c0005140000702071000307010403950800300004007400780c0061245848584450050f441075a080b80183c0c0114018034004400c450040b0305 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 146812589 1250 146811339 146811341
    0x152407060623100c1509060c091d01030c0b0d140a1407030b0913080d060902040f0605091c030e1009050406172508011109150c06040204020a050c01050f0f010602031804 74
    0x1022170400c049208000d07a600e0070126800303580c14500107038a81e8000d02c0b189040c101c51400000c00c8140e200c0e11541152543c0000c200c2da0309c0f818146800026802c2c1450540d50020707034003d000d010014040746001302d084400341030020390041c000516980050201802880b420030307015800350005a050350760104103885403188800680361100188401240c00c070b16070041402808043c2009600e4a1505100e6000d50885030055004e1003010700061b181d039140c00b01912421303200007074281d2941c00710b0704007a030340c40031105002e903005403108a224455a40020404085a400703a604110855a400300100a080703e100060b05c1c0350031100f05500c8410700343e1050400300600c85071080c4140d0380c0302d040300c0c2107031030306100c9114101010510300340360314024008400781c44000d10204e1a200c1748501c0c0341c2c0c0380c4000030700086c0324541c04500c84a0721482042503815202041d0001c00c25418110000000c01a08860102032000c2100000c54040d10200503151003502c20b00c3d0195100ca08182084 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 146813839 1250 146812589 146812613
    0xb0a08040308150d052104210204020705011a100311030a050411130c03050a0603030509010305090102041d0103020307081504030e060d0203011508152407060623100c 73
    0x2540342038081a60003042d80e600d01103c0e034100c0c46400100640d20508225604102494154088051003072008000d108c0c82000654404407441d00c00e400704c800380e071002800900a54501034103c0d0320f406000d00510400520350460340200f100c2c2c1ea41c482219940440944200d401c001c035400c070713040c0042071010040f50400c80c0c1003072060302c0481031100d603900031aa140070703050170b031301007003a164070007882c0e01501842510b42018840d081802501d05549010300103110f070141440c1015a0b581c0010241c2c4000e5041d10702401c4003260514001c107078903141ca4200c2c0428001a40700c0d01036500d000495080014544011101151030030080703903195103003034400300b05000721950041000c218070905800c040c802940a4028904203003d08c02c030424004001540040503041d4000900c3e50341c0c1e6240d030318200103044d01c03c8001948007080040601004a9004401c0300030092403e080300403441001c400e5129008030300c0c40b143c1d522038800d110204203851143d501c43e030300424008910040070941a180c51 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 146815089 1250 146813839 146813851
    0x90d03030b03070e0705070c050409030c0308090c060a03090b0a050f1303020c060712020f120d2a08071418010806011b061506110304050909150a020307090b0a08040308 74
    0x1480f07a860380c580d41c40b100c001c800ca4040c400108005190700c00c200c0c80303803041001341c54156810410568a690058404042ca0310081d01f400001000204208000c01c11345003e10000f42c80c480e150743d207041c00039020f41020b01040b40e8042074240080c00e980118426140b1410389078144401c2d589911404c40800c1c05418010703011170058001604941d11032800a021244c410260b1480c4801c5c0303417100906003210700c0030340c84482d0840540201d0903038449007950348458a440d00014090704400c3e4a06620300b030902c90781d84002c0a83c0810a005401640c0c0301e20030b13080c82d00c1d4000050040041c2060b9407041c1c0351702455032004483c2e84a01c035481030b558903030300c05410b0400400750301581c0340c45620607000b50b0040390300e641c030346294190450012214000401c01818801c0c80000040c010f02d4490042c5c0c006c1034012490070307001584419040240301c414840f10783c04240c20b401c0c150000c0700070703500444000002c541421400140d880140044540707415082d03644600a8480d42d6084550a1001d080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 146816339 1250 146815089 146815093
    0x18060a05042301230609101803020306010806011a070503161104020c010c110d0c021009030b0c04140d0201021504150e101a091501021014070e0402090d03030b03 71
    0x7903280140b001035006020384020031442d00d00003480074042d00c0c8202c18840c2507001c2c04081c00001c0c01500d902d545a095401c0c0c034244407400c0402c00a880c0c1e04052507a01c042e50510400d40002214900403e196050307502d60008500b510000510a210034400c2c084000c0c00b543c01040440410b03401c40031020450787c4600a030802c80d0900e2800103050380c0010a01e1030469668018004c507080d04295062006804a00680041102c081c809004100c090802078000d800a004001006228040b1034000c0c40e8418281249814003e43d14a415003090281e800040c01000c40c80d41180b40003e0a4611395505034000c250204000180d0058208003400459000200c0219408100c40500034020a408200010981c1c8601643e0803070076121240307001502090440b0b0107046944641504542c84035110790f03007c501461401c0100e1030070500e050760049a40c40c005040101d01c0100303d82c6402600d00b42d03180104286e490081000301d22403400c08a0b4014003030070308000004e001c0d420022402c3c2c40202 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 146817589 1250 146816339 146816381
    0x102090325050d0f0b0a11031e1501120b030c0405040f031b02060f16080d090302010506060c06011208070c0f06020d021c030b0301090f030807090f06080106050d1803090518060a0504 80
    0x447d102e07030000e5400d240c24903040c200030824480e040741e101c0d0340101c86030140f140e60482107001078100e000e00c40840786429100e56034401d0340c0d2000c0000b10b40d402c202030410080d038981070074404c1240f00004000c40019401e420f0400c5042c40480000c115660010b0250745440f0010507550402d0340078000741000081c1c0c146514003c10a010043e022589011001146034151807400a0850b4401091648244428002005c003031134001402e82c15940c400701ca00c10b2200050a12098501610740c3c01800706c000510041910507031056514201c803070130340031034010891301f040c1030384c4030070120101c0c129450403101c90303040551003500314400025000c1d0000807409425100e00b1032000306500c0c00c1d03010031401800e03c04a41e030b00ca01e1500060011340200c6100b2420442c000b400780b0f206104070030401401152a42007212582d001c03c11600840c80254890005482d000c2d141640602c110340c8200d40020001e05403e0300f4406441c8205402042001c001e8181002c02008014100c0300d50082d2450305 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 146818839 1250 146817589 146817611
    0x50918010e0718030c0b070305040e0a060f08030702030a17040305010f0b09010f080705060f040b0d060305010e010b03060c070f120e040b010c020f0904050102090325050d0f0b0a 78
    0x1061140c003802003004001800e14240c0e0b0007030500c1000c020705800c0c1c490801c8080000c0340e085c1c2d69103001c2d12a0307410b00540d501c0d16400c04544a00032500170a03c00040241448085210350b8051002c030340c61102010000c0355940400c5850b40180d807000794240e002200a00c0000d001440c000344814100095641003680743c0d281c0e2800c5680450200290130f5071420214032a1034400b40305070041904140000d40541082c0c4956101c058a129080c040c0340d01240c601015520030040d54007920070040c40540714442c03004810f024002c68072080c0c2d40c0703500c0d1a045604100040c02110001c0201900400031380e2100040c040d9960311000d4140d66040c02d544090000039908800348000c8000f9980f80388501d40d08104000442e014a604c0c5818051807040d075500588886074002800746040b1203080d4196246c2c180140a482685111036050040540c00195806086c00e440104244000b84007030302a01e0700c090240b801c89010001d440c1980001a0300c000030061501ca592020500f280482c01090344 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 146820089 1250 146818839 146818879
    0x1005011e120c0302040305071202030709020c010b1309110103020c032d0c150115090b03061801081b0303090913060f0615020f01060501090b1b030304030c0519120509 73
    0x50b0780c050000903000181001404420030081014000082c8044c800c52407039400030f035641200c1e225501800b5000b280035103002e842948500c4071104043e154071010b52002c04a40001c0c155004100c900030140c00c10030429522074802d070340345080f0680041d031a0070741881c400350700840300403c5074123000b400700081e0150580c514060404180820002d20745c0c00d1800000c2c2c2c86401058000003043c00b84031141e500c1d00c5078444a00d5049880d070015031944c075204c640100c2c56a8900101c40b8819120303030030000807840400035403202145600380040c041046404201501d0707104070100680e1014496000c6a401c801042c1440503d80c844d61000405000308001e00703041e03651591042000c040380c04610301030380c2d030184003c403581540c11000f0040d0310b00306800605840780c0c90203101d1721180d02240b6444199000301041491044030001c03651a032170180340c000c100540090084495004004840c1ca102021021704504941d105442c0c00190741d907901c0884941d000510713481e5000d051248010500040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 146821339 1250 146820089 146820101
    0xc010f0e062718093304080307020d020309030714010c050d020601060e0904030f080a021c0605030d0507031b021818060601090303051b03090a0602010603020102061005011e12 77
    0x10502207090002d03100001c00060b040460300c54070540f11590300b000307503220300860810001030440010b0010390341c4080341000181c0b000040d280001d0001020b220a108a0001561050f0000d0b821907580030f1503104100c0c0c8a018208000b0b405901882045c009101c1d0910030b81c44504047c903200e000710b00f00780c85207850010849609000360304044011320040340e0150402c0304041c0306542c0c080c0c140c10255030041500c11a81244400c20540310082408400c0540440e0315241144070340105400d60f620ba803a00900a6104040c8248500e10621000703902032001e0300c41c06a0561100c141da1000c46040242180340103500300d07400101d4210030400781c200960181d000c0c061a0003030403002c4800740a090318244d400307000c3e40d06001400d80e08100099000c0b08030341c200f107040b80d0103940024038042e6152650180f140c100d5403204400070082910303507055100c64201ca000f60308851664540d100116480d21690090900060b858002070000000c4008141001c0c50f0501c1c1c40700c80305020b44070b61022141 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 146822589 1250 146821339 146821387
    0x7150203210105010e0d0210030f0b30070f140d0b0a0c0305061906030e0304080a030225050d02040c0c0203030a0c020f060c0d0804060e0a060606030e0c010f0e06 71
    0x42040060026592204d17142640f5081640c8400300c0b5907190b0001042e0004c200c100404054031107070074089402c003e400c03103480a84080d1a1480d0351540c0c0c00e10b100005030482c240805c078049280743d21301340c8100140c84030845800509100c010303824040300a01e40e9640000d1079030403020149013000001c111601007441000010000140790000e403500405840010b0440c920800104100880c0f103480031480ca01241c40500f0000345070501d4a09050450045510a0209004842140044c15000f00c0c0c82c180340132482c40c414030034400301c6501070003000050140f950400c045814520042c10250300521000c112420b100081c0d40c0e0355030000b441c40d0700c1421004005041f1040820440c02d000c83c01e4030b5141c404451140c00c1056600301c4558444c664104001007080c900301040c1030101c40d80c48140500c1ca83d5043d5000b84900d03080075400381040748200000213203090a001900000858994007041050b0f507100499110782d40e0498410107100e80041d1700c144100301203e40c440001c08495202c0e2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 146823839 1250 146822589 146822647
    0x40303051501140901230304060209091003050601120f170c0c010c020d0b040804090207082a071502010e0604061d12040e070e0301020703020c0a12030207150203 71
    0x4508440e107003582961012007141032040d02d541e40d107080c2000500341c40301c901d000c0c80d00b00e800d001c114010f100d0f152415034502d04401c0b8000140001d2003811340042603202d500352034200b0719842e4003034183c0d10152540720140c966003100005005101c02c0c181c4a6801c4d0313000d0324003c0c0444402e502c4010140c00880d02c0010030441c00581f60888041c14800380076020b82c2400e010b804620590040340050780f034807100814524181002608010701942990050150346c0c90464450200785840412a40035040010791101424076021382c0e1b0070100e05c1882044c46d008041c02100c5c0c0b8140c03140741c0041c07140c0c058000f55502c0c0d64404d507c02c10100b0919101c0c0c3d0042c9808929090a8402103450000348200c01300682c002c85400e202200c142001c403400c44408183d034444030b82c0ca59030219000104000610340c10f500001c1c0f03c80038181c0c001a58a000d103412143d02507a1641ca8024020101e4940030040160300450001c1084074004101301021901ca40140c0740703040701c2609030a10688440c441c0c0030700b007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 146825089 1250 146823839 146823841
    0x1109090a0504031b05030301140102010212070905010e0405010b070204270804150207080604031b020402070303050f010e0112031b21030b010305130b1e09010f05160801061103040e04030305 83
    0x1041c3d00200b0359080340000d00001320448407940b110ba4407803205008030610b04032840182680ca074407d604494546000f002001c01504140100501c034810320302c0351a0002d000d00e80d02510900d8640700d094103c0b0310808980c0d01e040e9090342031101400e42215443c0c8280216400151071034155210400450303c200f0483c2e50382ea04101010b00011a2494180c00b1944880030612210000262441c0c20903018141083d2070b844a0484054030491441300035000750001c00c06004050b00342c0c00c1a800303002134030035103031040e83c071160042c072070b09402d00c50032124034044c3c055500800d01444103840c8070090710002c0311882d94141c40d02981c0000182c81e03140000c64500c00c03404400da040c0f0402450b0182443c0501c04c07401c1c00002c0341441000c052000d4081c603030100128101084013400e180c0304055000300e00199140c0001101c1c0249480c0f828103201e141400d00080e48040751450500c1500f07500d80350000140d003032000440314030f49540c1900c0d50303030310041001052514080b0261485640320342d40c00702d21 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 146826339 1250 146825089 146825093
    0x406120201030e03030907061101110f030603010c0e2407020925140a11011b210b130e0f100204090c020303100e060f0a0f0501032301091109090a0504 66
    0x880d050000500b4050b002441031006c1c10303401203481411101c00d40b9004003181c0c2c0b10f440150040088812244040000052442c5411982c4002d1446040110020400f070400140199023035410340007450f51220500c100c0980d070040c07005100250b1000045582c2c2403100942c00f10b411600c1c140d07001d140c446180c01d12050f0009540303081c3d007520705040c1341c02041d40030328010701241401101044800c3c410b184010464040c400d510148010710103018180700340d054a540a800459102410010040f0007800030407403e041c0c0c01200c0100c10040c042404000603609000c00800481008007081d02072513881004200c400c020201c0d03110021400181c0c2c69107042000320855a2041d85041076400900c100450740c11104521401c40d09061500b0310255140f40c001801c001803400700a80c0201c1003280420a4910552248203440c020380701042001e4054070b101241280c109586540140b06400510070f0039090780141071304406c5856254149481074000808074101101c0d445902c41d83e400070042 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 146827589 1250 146826339 146826341
    0xa09030b0a02070b1003470103140c01021f240509010608010e06190510050c06010905010326070609080c01060b0901020703021210020a1706010203090f040f0b040612020103 76
    0x3170821455589032040510703581e80d1703515a0012480b4484072111003000403e140001d08000740704102082207490407100c0e50303070358581c0d0220700303000994100403070301d01d11b1244c00340005c0d5003042484160010030882140c0202d00d5890844d4074500c050711358480112030380c0903080300011103106141e94440741c0031381d08050074000c0c0060305900040400002c0d600401410400d440e241ea0080e400395013400101c0050310200c061490301350304c030917004040b14042500065004001d002a90740050035106941d0761b0344500e0040d210203000107400780c400100c01928161404100b43e1115003c1c0c0210303828101c41d49c440b0002c89843c140184c0314800c00082003e483c15003846080080c1048486003400c180003200000d50740c0c40a404000c2c0a1000b10010503000081003200080300402c9403020340d564110301200130002103c01140a002e1034804000c65010360000c4169003241d00007502d4401511000030800002c7c00706142100c820302d5403129043e41944650113014042d020040c510410300981d480010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 146828839 1250 146827589 146827591
    0x30516050607060923011a1807180e10080c0a1a0a05040801020c0106080d020303131101030e011d070e040f1106270109050402130b0a09030b0a02070b 66
    0x849059666805025554510007030352521078000f000015600b45918041211038614540e2507503d01c1d039403045000c0403030150800c900070000030005444000700d80c024051101000208198010a0b600005210610845490f8061001200c0200369660707100c0419451140c00d031041c0143c500005014003426204120f4802408802e54031248500d00c0d000136003814155002088154010005986070094031500990b0068210302000310741c5d03042c0d030301c01c41d50003002c082c1314400141c00380600281d030407400801034a205100340300010048003ca42e032a284428810b00e00d1a040c1b5550308003403941c1000c2403160104074100204e8001ea80c102e180c650781d203007030344c00e510259216400340b04000019000d803403800746040d4400c410080405c4040000340c0300b030246030164044047c0c03000d00c08a50310030b4041c5140c00e02c8400c1e03c03041015921101444260722541c09180320820b06480c04010040e00d0340020410000c0714070707082c1c240319142e6580355484442540c41204464001c900e1070240701d8162905 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 146830089 1250 146828839 146828863
    0x809040e0c01092d0e1b040308030c131203090608061210020708120a1a0409020306180f030408152d0705091005030a0b03010204050a0b030a02220305 66
    0x10000480240e0008000c100c442c00342c1d07060b2818600c20a071041601401c004c056070781c140810440d00b80c0301c0b075040d480040112400b8400710215940507600041030340841e420b59400000e010f241d48d48042c12407032581d110000721103442000540016810748040701e141600c44c4aa0b48607a03042d80382c0030000f401c4120152280d4031424011252140001c0300103840c201407440b070305002d61101418140081e00380914010b030841161410f0400000e140c19500c031900c500308110703440c96403021250034001115000140203400d5441240891350721081000c203100d04412440844ac001c80d1400700c1541582c20a91203206c89500102c002254000c401710019406100d01c9014508009003514480090303502c28203c4248074490f00109104070f100d28211180901c0203409404100d5240b10010645e0f44110b5841341420b107001004c403003d01c5c040c02110b003219001881083c0c1c003424800816160781c0042c0101c05502d070b0801000060380910070700d41c1260240500300c1042ea0346141402030030f0951003549 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 146831339 1250 146830089 146830093
    0x71205061918240e0f0f010204031509060902060a030c09081207032a0803091b2d0d050f060c0703020d14120108010b13020f030112031206030809040e 66
    0x340d0000e42620301c82692260360010b5810142081d008144101c0e0340304101000045130400c10084050000051a480d10744200b6084800008030444c04d00d08134095400020141c02110920124100b0141c2024803040d0040400140c090b14075070020f81158060b070407507000700303448000940b56503030420840c600500c01c0002410b000308824280c0d18051046100c018148400c2c0703401010781382c24500d0101e041121f06429a1a548d1403810111050340048030004028402c10310040a82240e000c80e294035414068280c00700c100c412502a50300d1903a0814041081a00c000d2162541c0c1d5400c002b51000b5004030040d1010481006103a820804014031011f5000410040100000e5001a011940740854544040c1281d080c140312034580c46810f81d8641c04090000002c981d915065004007401031084819401960b98078004406030b02441e160180c2c10740c0c040c80100310070282401d1b24a106403082c40c203417404244801d034005c1180d02540043e24180c0e40072441002905162080103020940400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 146832589 1250 146831339 146831351
    0x5011e050a0c053108120d0b06090109090b1c060e120a020705040b06160b090607020a03021b060c03030c0c0d0801271d030d060911030403110712050619 67
    0x40412008000c505100318048060800f044600500740301c904c0c0980410825500c00c01a070502c41101500600c2a58a041d8a82910320744030f840c1540480700d02070030684995400e02c0c80c240106004002200161780c01088030038101041da80b20300781000b041d0f84a40340c0040d548118500152500359070703419012048d001000881c071219000a0294220341048601040c10381e00040410100d00a000c900c5584009075910b0204001e900514144103800c68000ca503a66070f40c000c0226a2aa011040500940c100890002c800040340b8582e2820b4007010740454685401402811320b10ba1048401c00040e000c007080e400e60071b900c180b004d40c9250240f480c00201950402900041003141c0c0f803000c00a51122003907080080e407a5420a8841c80e11140c40405e89d1408150403d840350300c0340300080012450b2038400b2509522512650342c000020480c0c0c0da08665895400781e031403016981701c4010398803d01000040b00360507401540d560500c11000341c03400d8104810081041e641208484118a040c41 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 146833839 1250 146832589 146832607
    0x80a03051e03060612040215030f04050d0503071202030606090604030305070302010f02040b03160c0c060207060e0607111002030909100e0a05160c03030204031a040c060e091305011e050a0c05 84
    0x4c07081d40c02006a40315400110b4445200040c411841c102d0034541c481008010401a60072040c400380c8198051020784203006100d20302190607200459a8401291181c544041a00c20503400b0395030003200608054031301000c1800041d541d03041a030007180020b200003044420140e083c003442011501c011825810941000c4c1c5c0341c150380c00002e18030402d4015000000145c0340c803860b0501c90003034000d84201c41050300c6031802910348025000e4100400c0940c0803d0311203091a108584460b0b8204079501a1503401000b0800421100043d9408501c0203101e21140c0e6910316004601403c091580c020180d4548480c0050a1200070100346400d46000c041200d040038456006000480307c0c075013006804882c0c40c0540090086802c0589007200122055481d4105094005d005d035020313990305404290341d00c404441102c202044242c12540110110710045211400b0140c0c0a11410001c12284650003803019080283c1404c10041501ca10178081c10f407413030b03201d02c0c843d034201c9240c09480c181d580c0c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 146835089 1250 146833839 146833849
    0x90f16030201082a03070e2d120601060201140a0c08060f060d0e07090516020c060904060315090210030908091c050a150c0e01020d110106080a03051e0306 68
    0x14030001e41442510000a00c007020f1000c2500004264200d000211259070240c0c543c458004454000c0401c101c4e1841202d1480d11441c02801950019020b4415034414200e8582e4280103100f81038100345c081e1210760a00f030781400f805000c1c0c0b1132039000194400da100f03507614282d031025000c22000b514018000080d90340c0309140c581e001e6001c0c0e070f0480a1300592808110a4401d05002d05032503840c005825684010100340f520844022031818052a00c42c00c102c50001400104074a003d070b40038a0840f40c240c1000301c042c1041d40c50061001502583d0790f2500300e0000d400600c2c40294603a510001c90441c13505000d41c445d050264034080054001c1541c4512151250b038400c180300b48011041c202c07554146000c0c00700b040358444150741030401c2c10301d84907132061401c003541c0c00a28204444180854403ca034400c111260503801000300e130021040c140d4941c80030103c00719540d501c2d501c002c10480303001c002158006129956140d620030307621141034650908100e4034602010100f00784642d0b82d8503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 146836339 1250 146835089 146835133
    0x1110a0b09031903051b030606040e09031b010c0809121e0c0d020a03030b031b04050402010e150901030f020a02070314030408060103080d0c020c091302030f1203090f 73
    0x22044510320a6120218280e265003e11100d010841c03440014064086605400160040240345032401320911803501d403040f070b800704944503500840d00380b108021003541945466040003848040d0b901c2c082c2c418030007004139401060810001d0791107860f500610355100e00b00541c040c2103140640304141c2c0d004610401485a160064440080c0707550300070a243d0103000f1280021121400c5648880f594103010392181454074013540460305d4000c40302014140841d425420b40344440804044400040c1040001e103c0903100b603040024807808407606458422800d4400905444095107400c42c00000400703850080d6503050010f070051003241c0d03859400140390402d50703034030180b091015400d12042c02e00d140100d03400210340b48541000002404904001000c00200d420340a004a8100d00d0050380e03a003001c80701c0aa005070804d00000c0c41a102400340110f482c2c030007000d40303600503c1404141d150150201d03210008010001c14000c421100700501d503400340d00f14002d0402c00660341c2810005500d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 146837589 1250 146836339 146836343
    0x20303060d021903050c03160501210b0405241c0b04080712120b010201090b06040e0a2f01020f03071716060b01031817090a17010509070501110a 64
    0x74580c80034011540c800c1440c6107140205203440304003c1c0d59040041c5d81c1e020220806010340500c40c4440d000010300a414820340c6c03010384900b400c0c0700c85644051001c198074030487e03000c0ca0341c802c0d20380c0496565004050203825160503192084040445000d500e403a50310003d88203003540141c3d090024162052015410380140580b0311680c2e8500b842e980d54402c0c178100808d8910000310100c02540c00c54003105514000705010807040349040c00590803100148009420301c0030390f40006110746025003005801206140c29121800d50680d10044130341d1031b040b40810030bc500711116066020001800d00a4603900344014581c034044104c000380c8a11802d10060840e4601401e41c003005440304045030315a0f4400400c3d4150108a4208800140220700c030b071500080c07c0008442c2c448802c6050402c1050700406d0080103c5d01142001c00303035500035402e040e0045156580000d15014184a40c0c0da141e002c1800403540d0f01c0d080030302600b001501e0300301605011844c11a2070710a5400642850216 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 146838839 1250 146837589 146837599
    0x4080a0f03140405030613030e03150709090501061e11030403030815040c090902130509010308070b0705030108030409020717040b030a05100303140306041512050610060c17070204090c05090601030c02030306 91
    0x360023030400700e1303030801005811a01480f45214a4200301d4021124610030401a0340301d00f641d584614028050b10345c20700c96070000540e99281080482075001109180030b000c0d040c4006101051410f240c1107030020b9209401082d8010300300858205038000900038098100c07002c00c40689444c101420340f882e01c1c020820b440380c1c0455101c448000c0304c05000040c02008024510365a90f903d06a101e0341e000d14401c55219038807001240d83c0b6070133441564162847c850240d030a00d070800c40024000d401c0b103102950000d25600100d0a4a14500010000741c010091060354a2808000c400155000503000c0c0500b402801420408a40e000c007920300e00e060340c2411141c1d030382c81c3d000010f000fa0021160384000310803525070016000700a540307101196440b45054032802c2e80c60a4195501011512810300801e5082c0200d000141984c0b4080645107001401d113030800c011a0081012a4180c17441110f031402c108505010030b00c2d01c00c100c5944003000740380c1489003003150b00b4025280d0001409481c020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 146840089 1250 146838839 146838871
    0x10605070f0516091401060e12101416050c120d140c0910031404031404080d0c020f030a150e0a06020d0b1219080d0204080a0f031404050306 62
    0x10035011003a80845401004840070b0f0102c0006020405126100f0444034a180510384c0115242030029903040300e00e9612483e00d8840d42d24188180b0b400c00c40c0d140145400794405440c2200210b1040b245802116005050030b8903004071044141e5043e080c034041071120a01034400038480c002a00403160142d0403040e51181d266050303481c05885003a00f40c041200d462410007003044103c0000d088501e0007106c105442e40768004042d41100c05a0171304601d0540c40364001f4001c01e02500d89030500a91a1a16030329190b40c6400075418a003800d442c80c800a90301181c180d0951034021000005280f0840242403d03007000d80e212003625100c5c078500004d880c0c8600d400304140f001840740320012908842d0543d03894044480460003000d0b501d8449218840c4001160007000000555480c0c034148860130748481e00c00c61b107500c0d4035038106247c1c5002c81c42e003c01001c20b241c00c0900a00f40c1c0c0314480c18031501d40000c0c034a405805503040514446d40344801b44001c0203ea6000628141c0000345550100c00c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 146841339 1250 146840089 146840093
    0x30f0c040b040f0e1f110d150807060206240f101806051306030501031a060a05060c030a030b0328060b06030c0301090507050f07030f0905121005100e01060507 70
    0x500f0f12281c40800c00e5180c00407440c0c142c2d40109038885c80181c2d8201030f960030403c024041084940e421070588400100b802000d04d6110640d00182d03800f4000d07150411a40c0e80c82c86954948022900008010780210090101900c2885a541c403a4030b014800c0c03c860300d01103804078a103e2041e117911485188100c1c45000c072140120742075002e42480d00c00c40807985441d46006811580035860092044008030300000fa02da2192165034142ca90043c00b11808030781051a890707190001408240c2d01c11013514000440780d8500f070003000b290700b4000245440703800c140c0c001b0301202d4034030081d035010381c128100c11508054101c2c003245600000000e24522401c190803e030f00100a081112130b0000d400205200c4020120b00c0903504858480c503051005944041003244caa010300c808511600c90300344040b1000038001c07400c80138824450701d40001141c1d0f80c0c600082e60f00300d00c40c10b0841e054200d400448844a21030044550111103541c00d20100b524042540e0840b05052091030100013021a035001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 146842589 1250 146841339 146841341
    0x20d110a0e0109020c070b090a0b0304060b030601031103010e060f06060f0d060b120a02130911091003020a0215060a0603150b04030305120612061503010212010906030201020c030f0c040b04 83
    0x10141c40500c84a010941c1c41d070704860000c1d80055003009040c8540c54001607013610040c100e070800c0401410305c440f52444c20709554000d420140c0211500e58807680201d600340c41c200b0540b8000d500a000d201c0f0342515280c103060031168207106d41409604841c08003c0c00b40b01501245400c49800d40b513982d55400d900c10303060224003900d4001c0640c0f03801c0010000b80c1e1210b81020b000c18160340302038184503840740114034049104d5800c500e8070300039010354208145c45142d4805001d00181010003841c00c040000001e6040001d1030101020030740c04110b8000b200d42c10040c00c003428a4008d111402070801000003409d103082842090101519560800c020b03800210301031005000d141c08294841c0d490380340180887c1c200c1e0000000498810000031000c1c6400710001c0f0b0142107110140285c1e0b01ca13620703598a4041c040d03c0716601590200702e41007001c4400c4c001940201410301000500b5400d42c17000900740245080450b11903404000c606c80c0d0300d030000c10010340582c3d048400083c0c2d00b0191010030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 146843839 1250 146842589 146842609
    0x10021203090a170a0f09060c030c030c02190305011521020117131e021309080f040305031206090f010905090a12031b0203130b031b04030c030519020d11 67
    0x8201c03c202c45940d10351900d218000d0108036000d51100360485025031002c4480101e50b00c107946c0081e611468480c0401d0248040a46250080c5050651413a480c0c000c1220b000c5561510401c80c4203d01d07040040c81b0081c801c0c07080000c0521200702481d841c0c151980040c42c240250303200c280d0b1001f00c000c0e00b1a8014030900c0c0d59100b110080032000e103020744a4148003540d400040d681d0399038040e00c19180701c50b410021401c859000f0031155405003c0503022006140300141154a52010002c501d0011068005003000710711460040d55204640503a00c0d00f0180d01030601401810130794180b08038098021102030550b41da2803000142135440250803403420325075070409812150420090804540d050300004202112221404152034214004907500d1141e0b030200590329003c250305100344420100115080701802c1394149051090648071a0b040e8407a500445001100d0031040041100034404a4080c500c40c0b040c4060540c1150080740d030400c0c2501005000c505032024041007076075001605 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 146845089 1250 146843839 146843843
    0x90918031b0506090303070f0806090403031508030408030418050417070501060b0721020d2705030102040905100b0304020312030c13091d0a0809090903040306050c0d0b10021203090a 80
    0xf00c41c94182100465146d91065031745000041201132492546030107026040d000315005010000c03581c1d12503d003100201548100d100c1d0502e15514001407410041018202401a0801a50b030712072501181c003400e0b0807145040186d0a051104100126042d5004680211800c3c20140e90340c404e280b900500520940d0407501030f026002c02d503101480b100c281c50b200303980c8203841d212804059489003a41c0e15100d00200800090500030a51800300500103c043d030000e6032020740494545410009003a6001034114010741940c031410070090703e01204540c4004c00c04c560502d80756003002d8004c40d803203860154040c1c030801c20000c00b0840300d12091003200c4200704c490303074031900c540d455201010142040c030203000707141c0781c005580da509103001085a5407000d80c09098580781c0b110ba40b09004d00400c00a210101a000900c0000701062440c0900d52054034150202c5541c1c079048001007007160703880d40c0031a0007580e10400100301c8a0b00022000986060101c96079266a0b4035042c080c9030148110300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 146846339 1250 146845089 146845093
    0x8071403030f0a05070305040f0201030213050904050d0806010f1b1505040f0303051b090f0a0b0a031401120302060a051f12050c01020303090601140415080d090918031b05 75
    0x200400c0e40d10902080c3d005010542041c0701c1070711070080442c26034100340c030090401d0704800411001507000354000d100601442403102911a581c0001501c80d071012141528507400c2660481d0400ba40304806c41d030300c070509081042c240d1404000003030100503a4000c001c5000044181c1c01c060004508407102040006202840646024580401c40c8585ca150803004a4201000b241c140c8044142245151011500301810201d06500700310f0400110039039160050000440480c402d110000144404034540e20081010764140007440b00786078050340454080554000d2580000b0750108200b904401040740101c0c06480c1c642912811061182440d5180c00c18454000340b0300c00c401140065a41c00f4106465015a00000690b1244011550000242c0007040188090f403c0703684600070901d800b410004407a4440c02901c0d200103240d403c0b084140e48070141903000160300549481c040c20f4029030501c034008101c1d65041502e07480760001005c0c06401715003c0090180e080d0030201c0e141d00101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 146847589 1250 146846339 146846341
    0xe01060b03070e0306010506090f0d020414090601060e0f010909021315020d030605040504020d0f05010209030303040f0b060102070b1602030c03060112030908010c0801090905030903070806010609060e09040807140303 95
    0x10043d00c0382d20000f081500134050f07007000181e64900391003603906500024054031440003040c0100071020807542c0f01203902940d24031a40625800b501d209074071a00440000b8200d95042c003030040c1c4103c1c030788483d007407158203560011501660300100c400c0460303280817005030b00d4000d070000c007100e000c0305c603003001800c2072031001070b90b002c1640000c2d0802080e0490301c0400001d502c0d5028082a12000c6602940014004411900040c9280d07407048445024200041c14000898006401e6034402d039400d079415061844a0f40620115115054200301c0034002040481e252041b00203903401020b40780224880c0b40d42c4000159181480680caa00c0c030020305494213507842e182280c0c05c0070030300001980082c0428001003600c04052007003409200244d00d51002682c41c0503064005040c8a1500300d600340803e008110f0980c030701f0440d06020f000a60060406581009801840c0380034540c042001c0203c80c0b00690140d48404201c07940240e0462851660f50000d07081c14650070810015503825484000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 146848839 1250 146847589 146847601
    0xa0209070315060201090f02060a0504030b010e06010f030e070618080102070c08010605010f0c08090a03080a030506130b0f0909070e0c0c0d0f021b1c03080a0e0d0207090e01060b03 79
    0xd4400000b045140341c04118842d01e400040382201e06000d0014441c000003a240c0002d0700d80440586001c407035500e00107141507160b503100400c0840a034082d50103680f103071007031290640e000103100215039034501d0708110b0496110161903650b00d19100740b03018011711401009844c90190030103000303001c0c664001e558412082c500403a440c0060f02c200202e075403a12002251540c465031240e82d00014542d29840100720940300c8040c00d620204000750710002020300000018100c0025040c04805618002018036244052151080d40044001d07606407070801301011503980c46100d500d01c0e40301556400746540c0c0d40d51000d4070303240e1250468410200d00a003003094520f045402000303000350072825600130b4100858140c074401e80900141016070040b440c0f2000c181c070180c42d80d1240171001003c0510380f8440002541080005800c00c0d800141d14000300101b0300751070700038946a642e2000c0103280c411058070000b0b4036500e10f4044c6485039900c96000d0b072170001c425002174010b4000030040c0b030381d2400c04d2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 146850089 1250 146848839 146848841
    0x3231005030f100b01050703020601090203070320090108010918060b13050103140705060403030905300d1701030f030c050102072001030c1809020a05071e050f01090210110a02090703 80
    0x10711141c44040e05142c0c04c08155440f80087c0c480d21645a0000c20003a401c145a64000e03401c002c0c403401c03c0503619400d2040c07807082d0b0582c1c56041521501d510741d803003100c000010b107045016005000c1550510f10120030030f500c0e4400740040240c21000c000f464175000f000051410480309041d4022900300310020081c82120400c070540c0e80e1340304040703e40c496a100184007a9006602c000742c04a241400c00b0041410704800e013001d00c41015911a811104240c00e08505800c0302c002d40c13507168444e080911406070810702d41d4000707110300d03400d00c0c525600d107036504801140810310040c01c004c208010b140402000f5010380e800c0c2c581c400e10341c251441c0c83c2c040d0102da001d144851240080d060051100742240180505061610058040c0003180e0900700000c2c042c1d4000c21002d01044010070001d4045403030200d0b10030780401e1246a1041030351460070424900341c010640c00c081a450b01c44500300503500d140080300c81900354109010040c40d00a19075051076407541c4041c0d08900f4103003c001e0b4180d41 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 146851339 1250 146850089 146850103
    0x5150706090b01081c050904180f0b0115020102040e04030f0516120f08070206160203070510020a020c0306070503070c020a080d080a0e12070204050a1d030c0d03231005030f 76
    0x80d0400c9801e900294002c80c03140c1700214940c3d0340424820000102941010703000721021a41454043d81b1819003aa1386040355000b100050300c1c400c90b00c0e8014014820044450560b1411505c02941803078201150300c1c07000714024100a050014403004406002e010f031054034010b12240a04072102e10346810241030340c4031841180c41c001003841640ba05280d000700c0040303003d10a55030060210340d40d0803c2070702c0c0f20b40342c0701c000d082544414422803000039400c0000d102d0300c3d02140c0340035031540704c480e2029141a04404149100740c000100700030083d50f01505507503016059140c40c0198030414008104055007a40014115000f40018803101541103440103014202c07000c1c0c2040791301902d410454a5030340c041001045054100040000f51501e5040907800c0b030344c807410008094000c031075200c001c840000c0c00a200d40d000032030070380c0301180140501e210071907650806016140003243c00102010306046624500d05601011941d442d004805038005410041d04441112410011080d66201d0f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 146852589 1250 146851339 146851349
    0xa0801090303140f06121f060f12030210020313080c06040b2202011206171c0e0105031603090c0902042301140a020f060c0309100b01050405150706090b01 68
    0x3051107080110244001e6009101d400851513607106030303d901d010403108508110f005411031180310b090040c1e18142c04108101030410010005803546000440d80e180021503120703e0307014044020040c00300e40c001c6900092020050030043c5d03241e0755020f050051840d82e10340278095030310100c0e29030f40c12070002409500490290900d52803596078803200e0711075000f203101c0648400303441c3c01c22080194064694400c10810b51729001c80c0040e15110706540c0b100406503e40e030303143e20880300da04401d500c3e4005201c1c0c003100b81c0b030080c02244612002811130701c000703040040400000c1d00f0030900540300e80d211040603030f0f000510b2405195140b009602941160140407460808040b485040e46480341c000302ba01041a110a1302c0d20500707002100090b003045072408191302030307002c40c070a0541c0e052103103038800c601d8083c2c1c040c1c0b00d0501c41c011625020b00784201351015403400d043c10910b031b030300001644d00301c0304102e840340380e0341010042c100c1f06801800402032019080c08800001c11090482c0c00e41610707 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 146853839 1250 146852589 146852591
    0x9150e010210110d090204090f060501061101050f1b1c0605030c030303060a170f0f010525020705040f020c031602191d1315060608070c052503020a0801090303 70
    0xc1ca100c00d10104031041083d10142c070003800c0041080c1c8840f02d411400c80c0600082c0f0014000201d52101202414401000c035110b580e1a801407240300d411451540880022030020011450725024044c986030b0050614001703d001107002052182d10782d001c45001030920307510b04503800c150708828800780c9a00d00070740c0d00c00d01824401c4030380b50600205591068000509481c207051a202c08100803012007000c200d41806035901d4040d554108002d0780d5040340500d400004d0300e144c888001041d02c0315060755209000101000007030015030010b2610152141107600003101e542c440c4040f4028460301c462040c4a0101065100f0180003040020194a001792445032a12020b1030b207801291080d4014800304a40d18100c400740000c608400d0381d40460458a5503d0500f440e481da0308205490030794000b206502c60f42e0038000140d100002c00d4209009080400a44006965480d10f40b81e801342820100300d0948415112040201054001581c0103000c503005d080c1c4805510703000e0140010180d000c6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 146855089 1250 146853839 146853853
    0x2070602010903080a090c030203151902030103020918071d042d1b0f0b07020a06050a0e04150e0c0a0807091203030c0c0213060608010503010e070e0709150e0102 71
    0x1890040c050a41802d91680d01d9100b950f50780300c05800100b802c1d441c06e46440030700c84d2011006171010401c10142158640c00d540051038041c4120b10b0082c1e686824160300f6006100400050b110190120b412036a10407840001c840d1929005107001c1c4107601c102410f40482800380e440b00c00490f04540564080c90000308400b1010410048002140180101820850303070510046103081401c8641d06961001c1c91031b256550312000c031042a1541c1006030b10841c00580081145420048440100807030304200d410300c50340350006000c90000c2d0f16420300884e2a0403640030081125030340b140c00741c50120100040750070f040c4c4010090b078100e14078101c0454072140101d600c103402480b252003120031503000840c0120850350110081e0445c02c0c800c0d41446461800a4016070b110f05a03110a8075400c400003c0702c0d4508000200703484e006038000c44c040d03491301142c0c0b64400c0004c00c141041e00d1585442c0d419075102c1070012034041c00c155202c0c01d64050391040c0010802d51040c40c012111809a080b200740f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 146856339 1250 146855089 146855099
    0x20405030c030f0c01110a121d0d050d0c020402090402071202060717040201030c11060411031b0d020405061206070509091f0303080c07050f0d0305010b130506031b0c010c0207 77
    0x9140210003000000303a00c08204141550b10036000c2d1031101000c40251f602d19a03081c2c3c2c2e00c082000480c0c0b028000300751a481a81c059070482c403080000900100c50842540e045030321140d0301c0320080e0070041e08114000c3c481c3d40543d00ca9404a40341d100025008556854845c102652500740e001c1c45900107000345004a0a81ea1203441c031085c8484032807080d2003203500c40c2d40c015801032207001c4440e804d0000c5141855030075842070200e6480f6074000d02c100491501282c04040c01c2803079000b040b4003400b41c40e00e045002070301c23814406403c055055600084507140d000004456141c0202e1a0503144100420000c0040d4064090640d184007581d501d40c850300d4015000c140140d600ca00b12012400c00c40080000c00d21403900a50069102036501d0318004158481604017032005900110a0780300880c40803071a689803140ca401000c11208413828820545c0150658014038030072148102004030105020358401c002645c02c00c202042d0007652061180000da002e011420b40301c0002d80030305080054 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 146857589 1250 146856339 146856343
    0x5100506190b18040603020301180b0a060b0304060b010311040f0504050c07020303070b07140a081006050f0a0f03110409090b0105030f1e0c06120108060603070e0402100c060f020405030c03 83
    0x340c0c1e600b0b111490900090114100030399544440059005803201e81c0000540c800388500c911401e04c2c4c01e10308407901c2c00340c10040a408000780c03414102c42e18110040140302e4045003a20340265101401191034104200120090300c90404511107201000030000760b00c0b4001c9076104d044a0058034284001e40e5504a1240a801006d80194140d01304204920008080f1240d590340a03015060010081810456092103a000760024101150036a02401401e24503045030000920003840c1c40c62511180414400140c01004000810300003240200886c050180d0488003440000c4419241c41e0b542c0c0709183c1014011030380050740d00002010000c144e038180880d02444801c4010010302580307035015400190402003411811050180004c9020140c0d640401080d490b034091040c2a07095041440090412802a05603403080d400360381d04002d071402a04c0260341c0150111000558000b210340140c03a8a005a80300801007440c290000442d1051a80a44144c0f5019400c03a000040c19105043d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 146858839 1250 146857589 146857639
    0xa0f0807080a050a180605040e04050a060509010b03060f060d1209051e010f0206070801120807021f021207020d080f070212010f0c0e03100c0c140a0b070201022701050705100506 78
    0x6c1c0001c0d07040100f844a19403110445410034411400c407042d2041a4603000f08894081d1199007041c0d458202c01c20321403a0800000e42c001845504c05406428000000f601003105007400902c41910745101e0b01c0c00ca40155210350041c1005424800e0904109001e07035400014001c0310390224070030b02400d1845c40c1c40014090302c603c0840c0c036001500d03424409500c601440410040310350380010001a0010b80340c6c2d804100c100450001d6021380458200006810400d603c41c0411042406106000140e650b5200d1404a140c021100030344c0c0e80070000c0da0608070b103d0114003a4101042d02c00e1103010b400154400401001211410000024a544115440c02c07144207040c6d03240c3d1040350300249101c4281c2c27100d030f0300308014105445901641c1d0b440005401c40c07251503400da500803040300d800344001c5448040d03001e0103501c0210714100038800046e010704010307018421907104032144034107980d00071000c480129421100301c0e602e62184205840140c101141e005000ba03c0e07142c5c8800595004400c91 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 146860089 1250 146858839 146858849
    0xa03021f1e150b07060f05010b030405030306040b12060906161b060e1e010203010504201206010203040b1209100b06030f040305070c08100515030a0f0807080a050a18 73
    0xc580108080701c400050100014002044020020006581c0d08030800030020079105203404944186900109004ca030016400b0466414041003004001580801140d5000101321000186c158000380840c0f03246500c010101c0c2a4805c1c0814062003030800a2140d200b2412001d08400b1145901d41c12651080840703842d801d2848480e81d000c001801c0f42d08607030346064400d812a51240c2ca540007002840703259800903d480d9500000610003410180148140c103070070302c00c08211a410f10444159031b4030071807069000044003803020452981c800d00c204c84c0100028609151210341c42e40081f00b40f00010351300308000740701c1c82142d014040d8042c0194162074100400c658115901c0c04820440c1c510010411406c00c44204003d000050984103100c000d081414000c280d1466089803072011201d001d004000d040c4826103032012256000101e96000951140c502500c80c016486c2a001c10300034440e004000500100c4d5505005074010f01509050006981e18481402d0b00b90804042610718011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 146861339 1250 146860089 146860121
    0x5071d0a050a050405090f1914070e01090207050f0d090503010e06010b0703050a032307080a05160c03030209040203150306010902040602030a0f0e0406080c0a081b010806120a03021f 80
    0xf0800e620303143e030046522104e10000e0f81d28111101e04da490606200b4205040011510314020042c1324010740f0915221003058000c08040e8107004051410000510030807410f00d03000a200c0080000912036101440d07072140c200c5040d640000c01c003502181c003c0c0030342c500a610b003179800c150000c4005000c0d8100c2d4041103482d0b160408a44086445601c407070034000c14584c603203034580301000060302c030b20403000b600c10002c2d0803170f0920000052060310068441d46100e4141000d000c81d00c030340d403501e0044030065810110001641890250040d003c3c07424000da04c140b0100401144148000c9552460031048007580c82aa0700c0e280120124011070140340c005a205209007d207003401000e00c266403540c503051613810140f402c0c000509403a05a00811451b41000e020b4004074240111241c000e0920000a4001e24680100114440c040e45001e5410443d081700030460365155181c0b881c00c12965a41900e920701d605003806540c500c00700c0d51420300e0241e44403041daa50101441400a0316100703581d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 146862589 1250 146861339 146861359
    0x6030f0a270305030115390c0902030603010e16030f030c1407050109050102030901021002030a09230606011704020108040212030c010915050103051e070905071d0a05 73
    0x20440d00911401e8038030041010041e507208528405403002826641c42656501e58a41c1030400f00d100b04003451183e5014004014218404840140f44114038401d6159503403800e138803220f900e20755404c1d00c840060074007410030310b003c00c08100980046104001c1640240041440001030b282e5550001c0d48040116180304014400640e0301a0032901c114001c0c5807094096007151501106c107500c00030304002e05d500c88633042040e941c0240b03801c4010072090002c0c1d810061500c0c0041d40b9441d096a403844000d83c0000000c480201d140e0100e00d2194220f220038003031a2000d0707550034803565811100c103241d20600d00000c0040d031160420070321004240442d6044c80d15998015a040400a0b00403640032110111425659504201409044550f00d00104840b1028284000000d454840460a0328180001440852000500d840b03d605d01086001c00321003002c202e45060840179001505201c1c140301c103110074150710406007a283c00c44848c1203a500c0e0045401c00038047c01c90301c902034011301041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 146863839 1250 146862589 146862601
    0x60203090d0809010e04020a02010203061f0903061d0d050c1006031208040f1b030212030f0f071b09050609090d02060601031e1506110712060b0f090a061406030f 71
    0x340544900c0c10706060103441c188070040050b0981e00001d2360140144e602004005c45c034681781d030000a850780304403000c2203031100d0440018a15000760001402d4140c50b11030500d1299040802013840c61070843c1515070a00a482008110f0351146010140b0791090402a0704606098480c41c0f04983c0c0c060a1903c041c104c0c0c01013910901402401500c0002420b061040401c08075420000c183e401050510002030441c8100a8020440c0b001500c4540c01800040420413404040790500202408003e071207400742e00c1c141d0000d00152030b42c901a090300b1140094000020342206020360011a00070f2415601c40e514079a441c0d014aa035200181d002002150055009601c060741c2c00c880200d00014941d280c0720031070700f680c114041d82d88000585120030040658800030101e8011a400041d000c072174904503641965a0940344d020b051503079604c68545260380da1100d1500c62800c06014182c0515160b60010b009110070b2240c200c240100700300070f42d0b4038503080048a00c99150140b1b48111600c901c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 146865089 1250 146863839 146863853
    0xa14010515130914030301090606020604050c04090f0813050103050a29010c06050108070306110309070e070302042106060b07020d0b13022d0a060f0809100606030f06060203090d 78
    0x124101102c6580d9a07007940c4082800780e40c94000d42d08507200250760702d51501008104840b513540c084011074100d8005e0200041d004180018045404c84021601c0c0505081c03250701005d072102c009100402c0001c18545000243c0d2a100440d802601e0400c00c55481e1040182a40d00390400a11100c4011910356840d049805c0c00c600c0ba404185061004850140d59100803a075081e0026a401c0d4816401082008105d01440e28424902c1c542c0038103604103629000d0b0390b0781e0a40aa5021800c3d4000041c0e000f610a40c1030310b0007081e94003c0c880e525a80840c01046402000c041600c4190074108007282042c403182c1150700c07003035014103194030000980e00e0b003c00c0340c0406002d804c4001018007406001d40d803103081d41242d40202c51190f02c00b542032000c0c80c146220303c014805014400c0ccc00420490241c101040d11020100ca00b442da90301d650380300410b802c2c080f00343c80d485a66450008007007a5194142d00c2a22020310181041101c0d42d110340041c1c0c0d61b40902c21005500c1464510343c100007400e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 146866339 1250 146865089 146865109
    0x6100c0312060f060806030111070c060e1518030d03060803040b07020a03050a080a0e04110301230a0803071416050105130807230108010320010215090a14010515 71
    0x1200c1d4000412545a40d00c1409440ca04c0e84483c0000b0a407000b0b0110919082c03080b800c001d9086424503290540380d94032540c4090a920400040c0b18428000000303d484403503500150b00300724a034041c4e490702426040c01c10500180902d074003a108030752100b11100d002e0300c61f03807083c0c82d4800c00039424103251406020303465004942c204c1e0040003034040000017030700400035901124800d03401a51031307030b040d410010400c1076129400c1e4412414600c1d1b50403039850a204903410342e6109418005404154448418074940c981c203281d8204510700f070002031111011001e007202e80c0c845e160000c641000f14034210380d03800e40c00380e03002046001404108169070080d07000700340000406990788085640c42544c02e040c010300358040701003801d80c0c2d00b5052614003107035600350101c0800d0030108ac1650543c2c481244d44900842c0c40411003240c01034205043c1c1c0200f00f045901c3c03040c2c8200f8242032604028168503940100d608807490780401c1c000b101c1030300040c05002e108440d4040f10810001c81c0c0d908102c21003403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 146867589 1250 146866339 146866367
    0x601020717100903080105010f0f080412031407022103010509060616060f05010f0e10060e0d02040504060e0607020703080a0315090c03060f0b0406050d0b12030307030b030606100c03 80
    0x2c101100080310460900070244200d010741c444822642c580f400152031031012555900402c603d1110f019a016000720101d60041d070403181c1e14404514030f000a40081182d81440300d08038496a0422004950005020701041000e440d294030040000e014603245000a0003480d504c002c880c1e0002d20f0a040040c050907915840301e803508420b030a20740722803044800d0100c1c00401261214010b125000b0600391500007001e400c01401c0c001d20344a081c3c0002046680100006c02c00514541c00a6603070300aa80c80310590000e00802c200d08003441c282005080341c60f4a42c840d8028440003074181400400c03584110f9411082c0c2600d042020241140102a010301c0151180074821000c501650303107202e9081032907140e4030002489401c003100140c00154070b82c00f1810900c02004180880e55111054078404d01c039000000c116502c1190028034142000741d107601452001004110446505400015040b103080d026101151511001d100c602103220b00c0520204841c480b140740060b2050303540d507100c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 146868839 1250 146867589 146867593
    0x31b0b0a090317010e150109060206061203090a06090f0b0301061d0303070b180601080c030714060c0d0c060c020114190912030608072306031e0c0403050f060601020717 74
    0x2991682680700c4443c070070b81007003548055103010006a43d4007000e860580b400f003420203002040c500314000703540350b500a0840d170245400590300f003045038080050329043d2800170031440318a91603401c0100a100b0504c6034000030b00d040c440000344410500b00f142d068541c40d82da00010004846404100c998400038183e415100c10803502000c03a991001141c010740d4001030741440224002201842d020040c1c000c0c0c29590800c1c1e80c0d240301d13030b50006244001c030383d60283c01c0c2500c0030180c0005041401482d04d264081d014440403040941c0e80a2000001c00d4805c0c102088100c013015130890032070b0b5003d02688591441e00010030300031410300300e141c114008000700100c0d0728240c640d100c82403041300c072a00001190b120076050200b41e000303000140c0038044584400404a80d0120a0394845108840280c000c1100101140c203601c40c00541c032042d8681401c40d6061804c0c60302508025500c81d20088e140d50103485e40001018001040c92405a00c05900500b20603090030818484c1080283ca850524 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 146870089 1250 146868839 146868857
    0x507060f0b0907030b10120e010e0a05100209090105010e03010e0a030201020316030b150705070b0c030702100f1205060f0415030204110301030305030703021b03070f031b0b0a0903 79
    0x1801600410301110810440810420703100c1051080c405030240050040c142006000841c540781ca001d000c2c1c4c0d000701d0b4605070391410004042c88000f850703208401007107942446420311740302800251a080d000d102e08129001e0400104010040b0300075003407211303400f1400200401c441e6100b210704800000000b000001c080011500c80c9207852100c10080b40542d40100c10403041c0c5004800ba840e84440318201400036202c01d80008002e64070501020060301e1011a0a0303045c410204040409070080b02c40311540d80d0303d0140c41a03640d400608080b44038003504c0700101d6035640b00c0c0b400a144404281c41e00d40103641a10000000f50070014001d0780c01520031800b003070141e5164062042c03441800042e0868650460050005a0b0680018020300c200104010000298400c0c00c0766840030403490010384071440504a006060a2000900254480400c0b01003d0140c42c22078040b429100b9103881071038032014140700144041007040601b614141030b0010300409025086003044910030b142c40d840d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 146871339 1250 146870089 146870093
    0x81509040303020c150a0b04020a1b140d08061f1e03020c07030b01080f0d0c060c02072d080613030c081303140606010e06040501180504020a020d120603030f0f0507 72
    0xd05040801d0150b401505c25051000c82d6106214011136504140e07419850400c076003401624001030300c80740c201c90344011101c144c140501e151038086102c205400782e0f1401000398000400e028000e403605071144030090191102c090000c2c098032000c0311241c0711411041039100b0101d8402400605480034181c0030851918505018071208010f584540381c03c00c1c09504001c0c01c10300d03020764141841807503844501c044000c190041655050150b200b04080b4004407218001ca041c0100d581c00655035440740045542e0301c9040c041030610040c07044070700494241e5901e00c09642c40b4015140d0003081120025050b010911442e103041c46035028440c1103260000080820b00c0c810075950040c0c03104603140c3c04c071800100090107074a820074403d1030301511a0841c07600283e124461442400c1c103000000c415000310b09030036186240200002041191107641e1860069200c00c84400c0d4000001c004246041e1410058428070007aaa0142e039030303012450031450181c504040c00b100003010300c141840b00b000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 146872589 1250 146871339 146871343
    0x819020301061d0d0b040803180304090912090b1e0c240708040812040224030106030c020f100c020f01060b04090b0603091c0e1c050607081509040303020c 68
    0x2000340b030303640d0302d00305a03c8485100111240c802d00c9614411844084184c002c1010f03070030100d4200750050b001036946d40714504600d1392082c0400303611a15003c085170001c0c68141c141c4c8001e400d1806071024692040c6802030480d900b240b2130191070101d0798280080c4e0001054005004103030071b2010b2080b4a00b102e41c141640c6003620040c22007800d0b840c0000c65415801260410710f03001109410044c5d020304040c0c1e545c200fa0300524854819500201c000a019035239101d98901c281c0034505140356a00001c6008403000d07602c24003840340440d00b00840540280d100150010b02d41800c2009403884c42c1003c45500054107920004da02184102d07038a2152198081c801c0030000c3c020000000d42c1c4502e0603038030205072004807d10300d1042c4018005c10042c21004500060302902e1000024003c04e0001d0054600c090107000301600b100c1e00c01070ba2110840300c40005050f16000304112b81080c1d031210400ca4541c101240c050946124544540306c40b0f05010351495040b61080c18054103007214008028 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 146873839 1250 146872589 146872591
    0x30f05090a0e0c0c07080d12110d09031130130e0a060305120403080a0804051e01061706091e15070e01080105060408030717190c1103060f0708190203 66
    0x3e0b40f0500009400340660002c2042200602d80d002c080c1144014928000d00030f405600060000d050701d0300c850001141e000800c640e20000c103507104119042c20f1f400c00805c04100e22071044024412040c2004140074842c800840a240038401d81240b400c0c800048001500200c9400b82c0100b501000400d45501083d0124884d41040c1c0f0f0005060380784d42401c5180c204c4600c1700d06040c041c10041800807813840c100b100c903030b0465070510386000d0b01c40385401d0303203411f0070074076140c45c0126480c0c0749170754404042d04030341c003203480c03001d51401c19003c6490229247d6205480c5000154010607060314840c03602c640c0c1341c01c61895042540d465001c000d40c81c00d0b0390030044407441d0014648124000c025030700034001c0d0f0701502d41600c4107802d046c00e002c0620b51f00c0c03040000107800c0d94002201040030500c10000c50b45025001d02d032040502038015000740c20340c103044104859001c201d03112610f039410001205449514145402900c40d103c00d04141c465610240a0707650421410789440304500d00744c0011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 146875089 1250 146873839 146873851
    0x1061a040314011d061e160f02070504050a0c0207050901062010020a08060319050709020c01110409050405070e0c040b03040807060c0e0315010b030106030b0d060e01020a1b030f05090a0e 82
    0x85d000620f0308011604249503200e0300809001c02a2085c45810081c02c908a010301c04982400360501120920076440e1540fa5800b895105080c0010480942c4058120000551031a001c5501c05510345d02002000c1100b4004c41002440c2c00a000d144400004400b0f0821030481d803c0d100030f000038403027182c00c2ea401005000f011802070003c0c803400c0c0c00c04005c03103503040841010704004001c040e622241c4034511807140c540740640115580910074801e50119091210031170840c0c0e502c0755210001c5018103000c4600707844600511400240d051030202031a403090078040e0142d4035207800c01d841c10300590409802910100f009000041c0040c42c9442054240c0d01140c942c0604c00c8001b2042615148040c09451807460416004000e404043d90540341034480908010520b00c04643c00300e940d508442201821032070a10040966684040d4010122207045564036400d4000c540d2900400c001e00794030040000700404000504544200d000d0098503e00401c0c081550b665100e07541903210302500c01c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 146876339 1250 146875089 146875093
    0x8070606230102010e0c01080a0e030c06090d09120210030603060e060a0509030703020a060c1403070503070207090b010816141b01050f01030f0305030a1104060509010201061a040314011d 82
    0x80200c0704540d00c0c0ea181c040709001d00c000d00c42031030090111901c58400d00e03112818400c8850224020001c04d0b0001d0715004070103000c07aa21015900c2102b40d43d1041521180074a000e400c3c17101000d24410f481c0c420036035150b001d89035810f280c0380e424841c01c050344043c18000c140e503a81d0044002981801460044242400140001e003032100c2c043c0c01303c034009000304441e03a00c10080e03100081c0e0041096203441da0042d2000600701c0b12010107a400c455103803410000b102d400000c21040c5600000a140141002d44c01c035040c19450703800481c119180c002d1060b021501c80310009240049c03c0b0660408400240750010084c43e905015040940100c6902030644030011498001084240b04255119071203c0e07440c0175551541d1190290306000e04d00160400030008002170509140c0e800447c6111040c104c15a6113039071714103006100d9046504a98019402c2078000162100d11050441542e615900c0300c5142a18594880c4200308820b06415001e540b54501014450034203841108030f5854540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 146877589 1250 146876339 146876369
    0x30909090c01020d020606010e09090106170d0305150105030f090109061104050112090809131e05010e0a1a060d06051203030618090606060304050a02040504140d03061a0708070606 79
    0x1c0064140000700c82620110b40c800001c0003513903a80940001407001c0195808061500c48500160140281d5000f1113421061002e1380114110006044031b10000300743d40c20881c5448115092103c942c0d582003a0340003a4007030021a240e0000501030300e0308003a091000080c0d0710403d0780c0c3c0c0400da8440f0384080c40c1c00d51021070b0030042943c1255081051282c0d0500c1040300e0304456440c0b030428001c20200c070303000c3c07030301d040c0100009034040d07000c82040e14040c20040c03001615060704402402c02401107a61044030b5401042c040e0030300c0d028459804040141c40b9005510403828005180c000d2440044030a40b134400021346a280c800e500f1241d002c208000d5a0380e480c1c03103c18805201403030600c00452408410420640041c0424550340000044941a40d2601e4504000303140035140078020790305c58644400e00003044000f13102d9000c4103a0340f01c1603c980d000c001c50241d048441070b204210301e07402e0740146000c001903c90010004144a01041418118a6140e550850b80c850300410b58889a01d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 146878839 1250 146877589 146877613
    0x13060f0501020f0a060902030a0c080c12011506030b0a181b1b0611040b030a06031202070303080402100507050609060103020a0b1903111c02030f060102010606091703090909 76
    0x4204003810082c0020f00c00000302d60101c41e035074501228098001d0307503a84a1001195010f00000b00b80c0c9820036075440200d03484000d00b5131074610300c1c10a0340c4180450b4940c18840c24042c05114846400d409000c401603141680503006050344903150f41e40001c949901148950640c03002d03540c070341d07140100000e50000250100240c629400645000e00c0700d2084400702e22608288599005540400701260681001c3c52032901c50140c1e07040115011400700400c091801194060350840b802a8682003145a001c001031b80c80c1e100300c1c04050b000801c444002409030600b0400608092440d103081458100140c41c1c49043c101d041d2081807454100c100104103601c0c0011114010b0000e54048070314141c0b8246000085d038a034041c0c5401455140d4111070142c0c0119019034014603240341c00000311f00d140c24038250080d40304881e9807001c81d200034089081075105204d01820788640d0707240c04500e9418040307800e081c440640d448503854881004482050b84443c4101401100c007200104803003000750f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 146880089 1250 146878839 146878859
    0x60909102c090307201c060504200a06050715020a0914010503071d0a17010b040f060302030d140c0d090e07111f0605190f0603091208151306 62
    0xc0e21401e0250300521404010030300704840c0c500d104800320300385005e210300d220114495040741c0c441d5070b1603900b5164100b424899241c01c0144241c0c030910000b548080c00c148c10a042c400b402e014140c020541d8001480710354001c0307000700135460090848156182e03100e61104180d900400a640c0018407540040145008510000314113400c00d003062421460410b10081c14080c100d80310850010440d070a070f01c1140c840d00c40030400b03481d003800039030004141c2c41d0000e03001e0304c5a580001d0069150081000d21550a88103a20580303600178060b0400003419502200c1c0d1400c060f030340c0c0540407410044644d03009000c201d811407804a54613107403503061422030506040100140b0aa061041c5039070044200500810b051040e000c4460210901003010850100106a142c00580c0c006c0c0000366401201044c0007140c1c07080307484a140d4200385644404044003960300d1200c00610100030a00e0a401140c0580000350348200e1002982c140001c0c03140000e020040340c4521f603110583d0b2940280304e0040a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 146881339 1250 146880089 146880091
    0xb06131e0602030f0306041e0f0b10020102120f100b1602041119050c0f01060902030103110a081005042405041b03050316060213030c0509010e06060909102c 69
    0x1070740051400c0c00d02040c0e5600c02e80c40001c1c20a442507955450850f8505070382d081c41007030902c01540800032003042c0c80c2d0510081048072000740c826140c440135400f0885c414021548040c0744096a04d50507140c000040815600140c2041c0e42e28107001c0010034544074000c00346c0035000d01e84800400c1808180180001c998004e03480280c040703420040c40c2e2210000c1c0c3e9600c680d201c12403510300c1e40c0c2c445c0744110a0508204010100c0c0550070300354001a50303c0e458000d12f0580b405886040444c8104008000c80c949251040c01c52607084001c2e101c549241641c08544d0041c051071034440c4460a264003078103424001749804603550381da50180818440304c1490b542040e608d640000103458110b8407880d1341c034018040340d903841e040c201d0209002c00800da010fa43c00f0341c0004004401041d00c81c5450b074081841030050501405800000045410701401c940340220006040c192802290005015035607000400b68054141d02c20f000040f1811f45074800481c084d034040e24510b1001903240c10b6204488 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 146882589 1250 146881339 146881349
    0xa080703140103021e01020c1201090b010501021f0506150406020d170903120606040306060f0e09120d0e010e061f05030a03140d09170301030b0a060f090b06131e 71
    0x7040800500040e154607162200441c4c501a00d00e01c2c6103003e40040746480d4140c903250382c000d04120b5102e140217030150001d580380d9200d0781900301182c3e2034a0049a5079201c4200e400314000b00090b01c820a1100350340038641154000e03181c1c040b40d15601e0300c4030300543d10035800b00740181d1083c4100252954841b00c1410001614105036000e420031a003480e503203025030342d05100d205080201050803595080c0846000356401801440260754403a407600b50b200c00f134441c950b00440c2c4440022141540418410103007035400e042c550a02c0c0401008100030261203a212400c1c2d982c2c1d07441c411800e241080168440c0e00781074030b846480c00c1c00d4191001d00c1111035100d54000c0d441001c01030000707904440d510043c020000003440d100e002c0e1900040192000e068094502c0c0e814607810005040c0b4140150705890103800341c45801e40b03610740c0e0202224580e108041485505030307028400805650404522500001e02d110704008030418400c400c81410b50003e03c000306c0118450000c40b10384007085005007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 146883839 1250 146882589 146882621
    0x7030503071803030203180109050306010602031b07240323011409060f04110403081206011715040507050c010204091b1706130204030b16030e0d021506060f0a080703 73
    0x80c0f465401030b42e64010421580000c40302d5400a00559206010702d80040400504640131940d40e2440070351642d0044c3c0220104114040111901e2700000801d442101c122041600750130401400c0540c100c600614500200340e00d1700c4865480f420112802c80702120240d400c00155454411105081450002c2d00e07402450044200041542c900030700401c07040040ea0040f034100e441c807040455511407030304010080c2e1004101280b440c0203018005118000a0701c440c040400e43e115241082c00080783c500c155540b1075031014000e420260021a080185410803508100e49106028207a80060700040e140b20395902101550b01e002c1031480d203c124003400c00300000b5680b45003a01e2110703001040b4501810000c00144202d0b403041d07045400071500024450858100300030050b08900324807100d180024241291058001030200d8205040c40041d0000c101000b5028100340c20f054004250540c003020030322000c00040d074920004c281d4a101c8be41e600d4214075100300c025003201c40581c4c9001c140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 146885089 1250 146883839 146883887
    0x190c03150816090203071e020307170c0a03030b03160b0309011a0d0305090a0f0308030a05012102210a0320010507050711030a151406100c03110c03030703050307 71
    0x3010b034284056041d110820b0001d40d49542c4c02109a600c8041b403076541c2107113040714450611080c0c0c048050806a03100d0003100c0c503d6224003180d4460381c05148001c0f0b81a07000103482c0b0000031700a0348080c0074003d000e020f50304080c04100f07655840d07682543c070155154600008000c01c1250a1240684025034800c071044840302d0000424168031110307200409210001900310042e6407440c40c1c0710000c0005040700600c03683c4070726055805030001e0b20400c2e2440e080200104200303e5882910741d8030301202ca440d00c2d001d000c64080107003145452214a100a00042c25603041c4031007406600a07240c020b03202d1070315000c3c1e4103500782748807071005480003040d034500000c1c0400309501004590704281c20030460110500b00390002401d110f0060001400c80a154404000312041d64020041000c000c0c042150303140c1d03a00707060000f40b9640c65403040014865803c0d00300002d020b00b9440880d040d020341101c03000074885d00401d14662184a041e0003007000031040014150340b02124822122200c9420608 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 146886339 1250 146885089 146885113
    0x40f0f0510030308060907171008010f06050102010e0a0503031f030b1302091008060a09140a05010b01090515030c0c03041206021905070507030b09010e070311010906050301140108190c031508 84
    0x710230b4505052404000c03d1804111040e4811182d030000c0d00d2204000c01c14904484105070003400c0c184a998003550030902d030001c0c3d90300042071030100c054202c4003440c6159103509402c552074044280c815458402e204020003c100c0c1c0205251040780b00a1728460030003020b004011130510018185441c5c0c2c803218806100e40140820555041000900003084000319446d0504264801d40d0f143c04641c400c0c3ca01900620905401031030b8000c6083c1c0320480b0341074549061104001c1e0010200701e003802d0400210702e403d81c2d02c0e4010a01040c0d0b0700144d90906032501e036500c8248562820035030f1083e4010070106402408903e42d641800e0705030034035510744207441da903403620342515100c082c0104141c0c00028490000c00e4008035815019107050b80d140e19207070310f44001d08928810902d800103d42001c01720342c950182d42182d069540c4074074410440740b9190011203518400074401030b0110080e07101c2c1d6000715040c0c000c0c07248140803500d0200d00040c9001180880350340c40da00100c0203034840c800c1254 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 146887589 1250 146886339 146886347
    0x30301091401080a03031d0a030221040e060607050a1e050d0306050d11010905060c1c05040812070c050915030f01181704030203120d06081605040f0f0510030308060907 74
    0x131581820007044d04450604003030001120f036244010580520341030101010303070204501c40b00700001c500520400d4040c0c9504001801140107040041034640041084e510740725020b4061144603404441c08411075507190940d60891b50388944000e07068143c01420000c085c0300154910f04603150810042d49844000346008070b5945003c0d020004030801142c4d540d10640740a009000060512603541914401c0030360b803030640020f04542c4001410810008520030380856088403011001861400800900c0b000c4650001c502156440890341c4002200d480d1030700868464060703158222441c103040e0f070a00d0700340a020440e4403216450103d010640b0240c241e0100c03041900542d50340411840e001c418040c41c4181d400180d0306100700404066040341800041c03508554004041c8800d55450880756526140c614036841da00d030280f8001d22842c14140d10071800b02030120008140c0d45980c0e250b24044803001d561f1049400b1007040113205042e000b00c26550001010343d5110149d141c0600010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 146888839 1250 146887589 146887603
    0x1915020303040507240302030a090b01080309010909090201142b090b060108010b03010b0c030c010908040302031903050711030c0d1110050708030105010f12020307020a0c05030a0c1a04030602040803030109140108 93
    0x342411f40c084081103a2101c164495860298400041c211713550f152003040b95240c102c0c0c408140082e5030700801140c80041e0780510300000d80d040c4c50b1100107103110104a885c0750003034030320803003e44041004d0500185d11880e500c60100e81007140051000c40d14107254600307000080c102814000101c1c0100030000303030482200d045860b014181900c2d4800004000d00714840e502403507185609051020003444a40720003401202d100318100e030480c03a50380140c0081c96651300d2024021901c00d2140c0d001090901c81d000751207180040039075081c04001c0d0b00003500c11600b42400d96440b5543c110945d00740c10440c03e405003170681341c140700d401c001c840d5a40814030700c0140181410071038007100312164140a80411140210304050664036840c0c1745900a5a5003004101034500403174001000401e82004a2000130032038110500443c9181003104080100d810a5810750a2070030030071001011130f50a101030070142c111507010356030329490000d28209490115100000c03509544004203d105000600b034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 146890089 1250 146888839 146888909
    0x7090b04090501061719032a02030a05060403120b0a0302131409031309143616140901090b0609060f030402120c010e1915020303040507 60
    0x2064414481021801030300504030300500c1d41d8205040441e560b80300c40e180203c2e00c0040fa08a410000c0096840030000245074005004181c51700f001040b5680740c0032100040c0e242407041107031000e0703207035010925000d1440e000fa90a0340102e0140410542d1008544c400040111400d1000000326000681c00c0701c02880021b21821000908060b261900d4100704181e503207601425502c0d151154060780c0381d521050303064121034002400460860050b21450907010600d1064140507524420403800c61048000682032680441252a000c039214413a020031085224000d01103918000301000e8a004d49070300144038140c0d4000d4043c00340d03150340c2e203140d04483c0110000309458a421001c680c90744a41c0c0119500000c001500d460255007800c001c50140d03201b5207800e65004032507546107441d181502c1c0d446e0300044803141d013030105180c0b0300c50f005106000401c110f080c1513618a0128944403078020040050381000c010813085c490306020740b03001050a084002d810021405504804600021803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 146891339 1250 146890089 146890091
    0x1005030a0f0603030c06180807060c110d12061d07080a150e15010c02061806160302011e02040305060601110309030a0308062407081b060c040e09030901020709 70
    0x24060312650340040740010241d6504000054403030030300420f0461803100c284c07850350401380e2401c8104100c005185e8103d0300a4900d9051000f00e955a00262095800c05002c12807060382c0f01456131300600403941e50b44229113410300c41307400e40e104010550745180c0c41101c2c054816a458400443e038030f081280d2048091409805c5561122410801003d8443c0540020100b010b80031403000c40740024a400f0790764207203007200d09003040300045034900201c140082d003040080c015039032000c0703030f940604d00314490040080e82005948142e009226103c1307141900141e45503003444501c00342c8905807084000502400b54079280c15034941980da0b0344058101c50400c400403150f211b2504090059444544000b030036100c658480f0300303004040800c02c0c0c80e0f81c0e2023000041e000b03ca24801d42c1100803114080400c1050070b04006494542882c2c01400480400d0b0341d0141e008108500188071b900d200c5c00310030315299180d82c2030180281c14003e0003803201029500400c9088100da030001f840d08115003411038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 146892589 1250 146891339 146891341
    0x5010b0a03020a0212130911031302010e01230702090c0a0e0108060604090f0f110c06040f030507050a0501050108010c0e030a0b04080f0f190201020a143402180105100503 75
    0x1285000800070090486900210700d480c0c002025040d0303481140c1007e882401081006100408644801d4600b003901c0d041e82030002c0c0040d402100701081401c01414900449032200050f509200e803484074009203088001030050443c40c040c005150030134603601941e810710344208405000d52892580050511918ac800903441d0394400c82220060403030080d0038407400c680e50113100054080880c40c038000c00d05126040741c260346844107599103940100005e0134191200e8880e407000350910f00040d4200481004114040390040100d01c045901c9032000059543c98030703004900b1200c0715210394040200440510348181e4002850740d920541142d4000b140b0746641c5807441e500d00c10a031002402d10408038008030994840e03805050440d010314001090002da14004030b00f01e201d10120200452182c0d44072110310000700020300a81500c4405804441c412500c42c41040c5201c0840d0618889010b120341302142404c45d02c1c1007114561a010a0340c1e94100320008540c80d0f90303e001d800400c00084 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 146893839 1250 146892589 146892607
    0x50f0c0703140a142a040608120c0d03110901030e0a14010b0906061201210503030408070212070f0b0a0c020d03090510080c0d0207020112110310060305010b0a0302 72
    0x200800e0001c50340308059003a50300b40840465111400d51030180e40c105115421600c0d5880085210030100c2410381070303c1c09003c0003180c403135194800c45807111707000703940e078800414031460410026001c2105807070203e44030030050040525000c44180301108050030a4040e1034105115402d442900800342800715850008104603440c0504600010702080c003030348182c1d80862410340c050b8103001001e64603085141d907010203000e5944a1150741d601e42000d00f10040040c0100610781a5560104000c0e0410504031a1911031560300242c0e41aa400394001582c034086103051078028141403a80d070060303c501498620390f0071030501e070352161507880b01c800107a039000d542c40f822030b6000d225801003030f810f03002d482030a00406815540c001d4600550b0802040c11401340581c08907407041c0300c503069113444c0c40c110794040406508034207001c83c1804140c07030242c902d011042c011501c214103070160702612450301d581c0442400b00d99034880014545000300600056204903300c0c3c04103d070742e0502503030310f500d04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 146895089 1250 146893839 146893843
    0x904020c01150e071101051303180e1e150d0605150a031505090304140120010e06041101050a120b0604050a061115090d08090c0a0f0302100c03050f0c 66
    0x16002c00c072801d080b0002142c406681d0707036820300548850792a0110066070200140c01c98009a4101121411181000c80007034890302c43c00d00c403022116803210402d80d55440a0300102030a17a103142000551a09030b420f10701d1a0b0300f015501c45a00c2019413030f5400f072440428500300040d40302a026a88440016403d00e80ea44c01e09001e907840a000300c19520354900f450b550341031441c1c11161032a41000c0101e8100b000c000251816101c0c00b82541c1780340c1018500668001744180e0059251500201c1070705041c020078030840c440d0246000103800c6514141c035000403101c03040c079043d40c18000240700c1e54180780d6000310040c015048102c0c0005680540c04009849801075510481d030108c0051004282660f00c401c0002c0c801c0c04050807520060080003c2440308101110710b00c0d1164012100c0307500a40c8258251500000c000040c0c588000e60036020550a040a03006840041d90303d400400031420301100c402c04007507603880c03e4090105180c0d0014030314070515140c010590750116280c03080d0541 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 146896339 1250 146895089 146895101
    0x317040b1f080d09050f0402040506040b0a0e09010e0601080702032d070b0420030616030b0103060f0b090a0b030f0126060a0501090510060e060c0a0f0503030115020a03050904020c01 80
    0xb030100b16007502d4161007000b882c0300c500c0d00030180902e02c103214943c0e080c2080d000384d41c15100000c2c0302070704090820502c0c800c0e50300403107035003810802e40102550081c0c40308080d8902030848280040c0c0c40e490428005046110080c001c50110761081014542c0308045000e5150403500801540110510a00c601500350040f90350140400b100e01060104110196000c03096208a140c011001d20452200301605c61008a48140142030903001031201c06120303500684000d641410700250355900d032140b807082481c081e000307900c6007400052044054a40422000014080941c10901c0c1d4505446c041031a00340c18842d191b41081843c2c4c0c3c2c0b00c0300e42d03821410342045203060800c9801a10b4a19000310185c2000e10410141e40d140c6804500000c03403200c22802500c006443d82c1020040c00020b1000c1940072680b0a00345000751031030400083d2800c01400c404500800080d6100c1d4180303200f00103d5114881100c043d94007138a61a800603070044285c51410074100d40058848c615008203030701501c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 146897589 1250 146896339 146896349
    0xd0f05032403070f0f0609140d08120108030d0e070302101b080307080406060605030403090513061211011b0c030204050c0903011e0501050301060b0304080a140a0801030317040b1f 79
    0x2412030f0200d030440c00d0400784003c0710301d4000f2145140d07541e050280c81b0000140a0008009150a000c0c403da0402d0001100100c3c8100101450480440c0c0081942c250130f8000c403520350000121061081da0702d025940042c240d01e406000c441d132466000800c10510300c618002404000e0302c0884881c800303844031071520340d082032100d556413518010041148002f150201d807240d01d010380108070148a082640d00c00c60b8152104a00181800104000004022110403240381c03500c41c0860402001030f441032314103125030840c1c0c204d000900e001600c0c0e9906814810040000d4616045c0415044c1c8080300c02c0ba50155400101c0341c0302c1d281001e290740300e420002c1c0d8056080030011070010030b2a0902209044041908112998a600406098030135610502004c6e045c144003040100c0d11500041000c1c1c1c0c0241810015083d00e1180e010b40e6411442828000c903c1b075500410a16812802c204600f884144102c1640e103400d1b59004030800b4040c054000031030f000c01c1e140307003201000004000a00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 146898839 1250 146897589 146897593
    0x5040203030f04060903020a0603060b0d0b06160c030209060d0c180b09070c210c0201140409050711060c0f1801030e030409020c010e0102070206090607030306030b1302030d0f05032403 81
    0x80d04c0311405098400c10b4801240607042400300091030750321901c030f000d0903039140111182c6048881601c20001d00001024554448c0e0108a2818035020840f000d0400e1b03031241c0c5444c2659031843c01080390306c08000b0902c0340a540381d20f11700d40c0010f07166010349042d54a90940040755252810144000346001030880d900300c1c05143c288034010b074100d2072000e01c00d0310800c0104980d038403280b04000e8684041c00280080345039460380100560117403c0003500b1808102c669810960303585400025600141c4020005c01c0000941040a51050085662120f10080b5040c0740c200820f2100700c0c0c0784a00c0c02c162803104030914007210541c2c4203400441d200c821075811203454a480300501c00003940282c401c0751032586000540e00c1ca1700818003c0d00c134455002007801e81445041000d0003000d9020300c0302181095038480001c0001600e264641d40261090300703140580340c0c4248103040c501503030301042034203104845140c0e5040303d602400300c03548004e105031500a0307c9881c040c220304a52102c00341d1036041c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 146900089 1250 146898839 146898847
    0xf03170910030501080f0a020906010f030e01060f060f090b09060309010b04050412020f15040602030405120c0309010e0402090d060c0903060915050c030108100209060408010903090801150e0a05040203030f 90
    0x140e064100324117072081d44081e1120f2103500300400b0785d20480c3d01d0000b50010300140020340590700510309000b025650303040c0499426102c510980c2120460341080d1020103044205000480d80200c42030001443d904280c5051400e00c25548000d000b0030500c14070503100000010640402900324401b6150050000c1c030407401d2614000340440d0641d000c000051040310b83c04049024001800210384000c42003000e00b5445a0701c1e40030107984000d000b507809202d00500611740300004401002c1d0400c0b414099070721540d020000408940134411220700c5640103015640a582e01c2951a00ca02d41c0d10810000f84050803010584030038074958005001d81d41790511a17001c0c0113a40042007140401c10904020640c0e4036102c221003808203001daa90140e000e455500c070b1721555030b1300401150390010022420140d880c1c0300b090940741058000c400080022000308020242406030b54511101420700d4180c440c1030422141d035502006040c034403540d486101050139510280200e8905030f010050040d59 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 146901339 1250 146900089 146900119
    0x1002030c1c06031403090604090e030c06041b170606040e0c1c0b0604050906040303240801020d050114060d151a0703020c010215040b04050c0402030a0b090901060f031709 75
    0x620340342c03005448000c0720041310b40c0c4074032011049404403080280140c0c1801e003090900c20082c100c04440c00030350b02c82003040382c0d040601086070f9882140310340060900d41c048001c110100789a5540300000300e034070508140341d908901065a41e484441943d001680342c084008552809a405001540080740c0101a030003d1029161180ca03850003400a155a622250188411250116a680301d2a04140c000c1400a0301c250408103e00d11030380c040e5200c0281410041a106c411684554844d80d800605640e4a50741030044d58010032200302050344c03116518020030b08500c15040c81c1d04030f4654401c82510003100c0c1110580242041c3c4c03010b280c94000d0011b180b041a400407805030701520079480341094940c80001d85180010754255401180d4032650b44040740c0303c1000c0c1c006c07611342c0180350410217291540c1c400b85108000001c004940781d0801000e0241000b000f800124460341051411701501c204010140e04599000c1510384400b52401142b880c01e0240c5021a80d00c21145140600 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 146902589 1250 146901339 146901341
    0xe0c161203021e03150d0501060b0f0307030b180c0f13080a0312060f14040207050f06101e060f0203130e070306140918010e070909120504081002030c1c 67
    0x880d01c1402c00410403003500005458143e4002140c13604502407440d186211582803429008015034890300002c1000c035201d500d0202d994008460600c00b9407000b0040100c4103506000340302d030b034131425280e07034030189181c4032450743c0c01074003c040c0085080c0020352002d21041d03490880e03840c091510391000d201900c07210b0b0319440785003600c1c043d400140307411890700481130284242c40461340004000c3d9011454240f0022105050039801c0d580030340c1c288490380120758140142602c3c00c580e40064041841d00500c00340c0e110200f50030000c00c1c0d202c20048a1202d000360407000040c3e40302410014070302d0320a648100e01e18807400c80304019440031071800007a030303a507040c00c0d69000c0c071410f0314144071258480000303806020700f1050050780b01801102060242d480c010401628164100012a080714200320b02c0385051a02c0d480719a4042c1d444203c40280288095a07400c81882442c01900d0980b422a599503580141c13454090400e5000021072205205c107801c4400c0703400c840300d61400310500c07503007080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 146903839 1250 146902589 146902597
    0xa0804030c06020706020703031407050d080621030906090f0d030906090b0c250f0810050f401203050916091a040212011503060e0c16120302 62
    0x21041820070101149142c00410301100355040c0342e001389003541c0385031002c9840c00c1143d0003280041008001100200340d0034001c400052410743c440300d00c941481c41c18003180f203682004e5040890412814440078200100031130718140c2c000c80c6d400d91030b41043d10006c3e41100001182c15841080c2042080c101500b1003550011508903895101100b81c0c0c510201605114503020a500c4d80c02861200e140d41d4900100a40b08412400348400e0f000d4441e8044500c0c107105810045882c0d0250603107602c851624000c1c564490320703041c2907030703071a0078900c4600d2482c5a1070703c04810780140c0f18808842411a070344c2000d28084d241241401e0003816420502200e01d40b050980c0f000904210016400c07440004100718840c2c0512052206140307064802002480c1100c04030380822002d2000c105140d1740d90015103040030b80c0340080b140651610402c690400d03d585000350900d0b090900c204110f000007280182d00050003c4510360b00d00031048190701800d03a0103c0101a0401260840d800680c568060 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 146905089 1250 146903839 146903843
    0xf03010608060f01090501030305070b07030b0307060e1509150307030e0607050910020a03050a110304030c030605010f0f030b0c0901030207060501080f0c060403050714010903060c1d062701050c0a080403 89
    0xf100f11641c803001060103446007400068045a000c00500c4001380d003201c03e030743c1d1060182c44d00148189a1100082c108030990b40000d00207404840c800cc500d03e0007841c120f881007403040100f450104a030000c0703140c0103500b441c05200104044002800030b400b070340100a240f02c0100c01d4503001d11300050040d0058100e0341c9014010508041004040c034000500da440c12505600d51504042c46c4e01d42c100c1e044540350322200298001844008001810f400481000d944564000f18480d0305000c4603d04505196100c130b000d0600e1100100042255558020380250310304000c0d99a4655250050700a1f21801d20024034552500340005105000031454980301c806100941d884007141408000a60040d40005440c60300070780c008000c010000d4070900300c41141070404007880c694030b0b00d40380222040e03861071070045604d5002c103041c03811090205844140c0d00300c4896061101c4500f86003440270514000300341428505c01e155813982c1c058415503940d00034800032903e902d0014075080e40650098401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 146906339 1250 146905089 146905111
    0x305040b0708090c1c0506130317040c35010b090c0f030109050601110f16050109060e0118120606050f040516050304020a0b0d0b030706090609030b04020f0301060806 73
    0x49801c46105500b080d0150080f4001840c0d140702107401c220f50414020045c03110300500c00c400c4d800280040c040d042c07003408500000002041c043c1406000354a08842607030b49124180104000100100c180e8010340d04902110321111504951280a40c0002000d205c0000c000d81c1c230b11a403860781508404404038041d25040d109480c2c072840c11195010307145480310074010074130060062240795440140d100405250259480d4500300800c0e0501201e03007a40c0f01944c000b0054150304100c60401c0900034007003031812070703001c0e498030740020002104028040e0421505801d801821000300342c000f005002c6481084060304424605034005001606c51107001c2c90b8117049100e41c61034284544c0341f140902d13100040c1021400c4100f01c5559000801c105c0e0322040c6d10101080700360546015002c100360100f000920101107104042c50203625900000422205600c117015803548480d80008580d840510359056480700e10001d641e9005900105d50190701c2d1000025188400184e418041c240c0c0000d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 146907589 1250 146906339 146906341
    0x50a0f1a0406020705070524071707030c0302011b0c060c020a0503041502120702030a17070c0e0105011b12050a050910030603140f061602031b0601052706040908190305040b 76
    0x8140000e0740c4562210407080000782300700940f0354801400900740ca91007482c03075514821030f41000c0c06254100650540024a851400d8000c240e024130900c40249c450108581e038080503850014041d075140b400082005480380030401d00301d8000c1100b081c000d6840300c1900c0d10b40c3e40f80c0c110140100c10200341000184901880321211450240450309017030b4000d030141810b03110546800380080b0000c0c0c1303001041d400c1000000302203998401c450002e0a580540390390994500b2000402e000003140d4080100e106045402c0000391344082404110710315810a40e403140d03404507080d1003e00032a59041d07000301c40130080441607580341e4480030549104100c00000c0e690a0342a040e514550940c080f9800c2d400203010814404008071950140e1003284100c174503114440c0300d810981c01408120704a55480171006001c0380c41d01e5902c44003c2003401c0e91002d280b4035181d0340105d501703e014003501d000e1682ca00e04d0200780400c860840d03031443c0081003001403940d08048020020401154181c4c0c0301c4540c04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 146908839 1250 146907589 146907599
    0x27050c21071a0a0c17030c09010905090915071403010305010c0320040e18030705070e07020f1203100b040f090c03050114040e030415120506030703050a0f1a040602070507 75
    0x26880520050304a020b8604086000c10281c8056401e154181d886100c043c00c40c58500140400851240422680d0a40c81d645504009044e940d60f5421462103880500200304c040c100c00039101115013040364071150380c2d4a8000c0265003054030f2410401d00b1200001c004401d0201c15007101c00c125161f50b50400a10310703461445e0525131132940e100306100b0740c10401045486081d050083d04000954264003172560700443d46491940100c0c01101d0b55001100d081110510040e1302c5584058140041d004204441e000a500c030040c4010291000b41c010010032017058403078441101400d1016910343d5240e446455240583c0124880c2a81040c01d042c1c944401511900649048600c0003000c6403240c00c0c500200800380042100c80c401c03a120a1000288801108110460000d0262182002c0150400c80e40b41510b900400f114000d6212040400001e440041c4400c1e110f84c2006440300f100f4424034018020103403411a0400146000e4140418000298020304542e48070314100d8801d15510 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 146910089 1250 146908839 146908859
    0xf351314090406050c090d05010c090f0b042d03031d0a0e0f04050115060c0209060301154202060a05010e1602010b0d0b0f0a27050c2107 60
    0x103000490308489000301040000b01d1070b42240e6040703c1514442818812003401082c8030050070507066565079140c01003901c295400c16101d80151640d02d605607449410f08000c40c1051003203125201e541d650003100cd0105081c0e4190000c0c000c15076800d060305450340c90030000c0c030b521070340400e5200490845d20b000700c503440e210b1084401c44610130207021644d5500b00d40c14032603000081c001e8840d9500c1c0d9102e4210101c1013000030028040584410414100c2e03401800900c000c02040b8034042d070714100030006100c01c1400c41500319101e9030901d1000007480c0020804048998400a0100001d40d00070140c1d020040d25400c0005019401c98480340e942324400b0041d0307a0f084c460340c0e000070700c01c801007040c1c00b01010300d92542d0401400040303020b07010030020404e22200440c00ba074542c50000148820189400313203044d04581002c000b881075a0300c03071800280d004252b05042000d1004524201e00b0810244800b04031420001c2100075071151841100f49108142040d0b40b580d8042c1580100b401921 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 146911339 1250 146910089 146910119
    0xc080f1005010305091c0207150309050604020d0311030d06090c05030f0712020f030a06080f030c0304120f0501050708040201020f010c09030210140a0302070201030b0603040f3513 79
    0x404200318000d524000041d0002c00f0003501e034181e280200040e02c1086074044020500c14007a03940101112803a0500a90140c003040787c04804260628600201040700040c03403982151b01103544035a5482e0903c0d09503410070b89a810070341207002c007182410401c8440d41c046c0701100d0703a0001c00d000784a0341c00702c1214984021070708100d5204110022407207a0f441420001d07460b400803040140740c2a4411078001c400e4208a9020740c101e41c807070324103212058050180c0711000b80200c0c021801e00d100c1d00b54294690256000e04403401c903081114505000d4120507103210190000c00800660421540081180400321003d03800b5110710b204402d00d81c281441980400615940c44200709801d541c00c21041e40202d001c00d500b040040000343d021401100700821307210b44280c40059480450384005800da80404030300328850b40c8140200800704050340480340310b2030740c13080c6000402c950740000c1ca500362003010100084040f20100c042c828104840c010580b0541b6403c840c86035a507101909100f00c86 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 146912589 1250 146911339 146911351
    0x50a060320040216050f0f0601060503010e040201020106030f0303020909010e0c0d0f02210702010f020306010509041515050714030403031407060603022d090105010f05090f130c080f 80
    0x460140341d021544601d01046400100920161030115a041610050f4071850070a55894114000f805140b540c1000385a03030304007110f40604069850100b019006010500c1054a50420480002c04581c400e611070070145a004062010040f51800c006009401c0100341a0159640e0000884e9141031030b45c446100d02d440d01400391070a0309002060000e0301003148910a201c0d000d0052340c45c601411013070700184800c1464802098a40920000c0c299000c4401d450481031041040c03144903603105084a00100c4181c03408030715440e90b2181c08890600540c0411080380c3c00d6150f0f1170000303070300c08000c11005000341071015000f0f414800d02078072481030344001804a15106112a107a150f020003401c88a405000c00060039913481d00414002c40003125442d0620b42c01c0c007a400e10044140000b0303100c1c0d65055512466642c1032000180c450704841000005110f4081044031017036440b481da10703035154400b9151b113081142d410b0b03504c03000e00013122498000c540c4140000b00001542c50f6540d110352 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 146913839 1250 146912589 146912603
    0x70e0307090209011b050c060f0d0c020c0312030f07050702061b010213050102370b09030702130e0a1416030804050109060f05070605130b100f05030c060403060506010203040314030706050a0603 85
    0x1c0747c9400700001030340210003000c9556020f1140d1080590036110b52841d4250030b4020303204a031109410103050144020360007866040510a00c6015070128a02e140c0c0202d1600b802c1e55110050300004a080c00745041a9094001180d5104201c82040d0042d14030040030703001c4030b0455070300c42005903120006105080b040c022413607100c0c0d20410611000d61401407448000c0380044585032203030030f40f0310021100000701d98800640e0f44210b00306400584403030310007182c080112022241480b5190003403540082d1140c1c0000b802e00f43d500300c0500240122280c0311003a40c1c50b055503450150243e4009105050208401800010f0500d001e69030101c50000300341c6c0d40a10304135050780e645008040117000c41c001d0503244124800000c0d000c0403114003c034020401c080c0120300c0e0002c100350071441a00f06038000d8104a0704000346880703c506603000c2e00d52144011130356580e1840101c0c07941c021640040c2421094120241101102000400f1940d02544040c0a269500401a07040d40c3c11031100034020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 146915089 1250 146913839 146913853
    0x915060103020408250b0409050f0c0a08040b0c0904150e090601050616030212040306150503460c09051605040303030b040f051603270308070e0307090209011b05 71
    0xc43c0803400c040001c0089401c40085130344440c00c500c6c040d00107030081c00c07000381d8400a01c080d03892080242940042222406440c000d40110010036174900030300018541f100300408180d070840760300207a40ca000d0f005001000000c01d103003029041d1340b02c540300e041c20f1681d8800100304a000040368050503600003614107840c05000c064054401d0480b0541a01140514040d50781c440030003400902c010b50040074085444580c000000ca060140d9904c1180710f40e202d020404a02510501224a480016001c03441300c110403080611505200c5015034074400e030318000740d0003004200140c142c02e81d48480400c1040e5643c11803a5271003d900209410003040042c042000064230a030172001d60000d010340b0108042d84c81543c0c400656000351409644034141c080200b41d40b640c1481091840880c900c4031020f9010a0b00e61140302c0d109242c009410011100009911207000c1c0c03410f80a000409811941702c10703995070240d8025080400c42c51300203400307030b45500a600480141140c085401001030021 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 146916339 1250 146915089 146915113
    0xa06031a04060603050313051c020a050f0414091c030504051c031e0c020c01080f010509040201050f0c0102090f060309070b0c0f010216050105060a120308060402070b0915060103020408 81
    0x8121001001290320b103441d4079001c40001c03401e1010740443d81404c0c0c0a50b004504180420545417548008050380114900340880540e80706010030301250b0041d41c09071044002e80c00410050208016031a4100c0c811400307100c20001c00041100d8140c403010014200c2c4020044220306544043d54090103940c02001e801e030481520707141c640d48412680c10b0008001081210070380c0c140080c0849141590365800000b8081c07a0140000718685800740380104091512003e86015024180502c502078201c21001408690243c4200c500c3c05d082402010740703c920b0403c200c1d020b544003065460213100c0c80340d00c00c8101d0809505490003010850007030b040b1a410700001118580148007080510300c81e0b04403201c00700300d0a20080048211030140122405400d08165080da076020b0701d0107000350300c41d15040041c0c6581d400c80404050741407070308400342d85a42c400074000c0d005074100945110005014003000a40008040609540f140c11101c03071941d800340190101c0c0030f94401c200c0c240d001400c03026a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 146917589 1250 146916339 146916383
    0x90203070306080a1112030408070315021e0c010609020a05030406050417040f0e0105030307050a030f02031c0b01030b0319170d05100906050d0f0b2e0e0a0603 70
    0x54010254680080d0441d43d0342055407500c1c2c04035109460b580e0380140700506909051765025408010040214601461f109456a60f050b07644001703003415074170281500c10076115404940c0655000b60280da00c40c100075144000307542c040ca035605907a42c038091001480d02d5884c02a200c64880e1341d1511f074119595030300c0e030b02701420006004543c3d110b410150005c8079140400030b08068a0b142c200d880055081540c1110b000406800144c420740c02440700c0d42c001030700021320801d4158036141018421052103016403030350045e5030f444142e4546580340e4680094066101401c406826a824031500e1000c005054889042c40c0422446c0c1d1102880c1e000401c4560050031424a02d182a13240352007019040a81190401da48610640800c203008212400e100d00801000d040d040b01c060a013030b1910351300c5410690780408010158100c0d0400201458030300801103498540b04885070702380603510141c0c41111240e0780180200b031245140030840259081c81500705982c4d018480656a000d4216000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 146918839 1250 146917589 146917591
    0x904020f21011803080a05061c0302030405060f070506060d0305031f0b030403030501030b010626190603080c0d05030609041416030b040b010501030905060604110403061802040b0316090203 83
    0x1900007101ca401c0141012400d2255610280d42040c0300780c8545001c0c0380043c414000609400c11060920050201942d1203100c1003141d01c01c40380e000e486540d030310715082c0c0c150301a0f0340c0511750000c404143e0b03d20a00845005101d41445080ad40e001641c072401040003550141c40c001e80020000e0000414029410b00f069800f00540d84945801581c0c81748007d0065000b181c2c110700003900c0f10010000c00000103001405811341c0d0034188414016201030310702c01e00681c074030087c07584590000310740b10803100261440c01e501c804006010350b41d1079090150003907100c0e8090081c144128200264075510031001e0b40e001d50402804c0320010340f52501d50007884032071040200340340d01803401015400c156103821907008500c100c003a0a5145003a007450210b0b040140c3c0f0940c141424000e0000004c3d1001ca036881e03201e10101d60004401c212000500c00e14042c58100404040c0342800000c0101e55140b0351640356407085a040c00024141424140c4590007030303101c81c1917100c00c603e0038003252801e03401031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 146920089 1250 146918839 146918869
    0xa15030809030111030a140912090d02153601120b040b0a080705100503060d20040c02030c010b0613090c120207030e03010f0506032107060608030a09050904020f 71
    0xf08041d44010004c1c503181d803003030b11340041ca6039441150783d0010600340382080c0e0141b800c4020f00301d280252440000c052040c41d5006124a031030702005011940c2d140c141c0440fa000884d2856101d0300e04036402400c507001940d14031640c1ca4402e0400c02c11044440c04024121410b039580d0840c03410205c03d120103080341ca818142d10a40b1b030300b00700c20b254546951075002060f070480140205850070042c8450a0107040307803c0704000301041002269142c800408c1c174081e42c800c010201140007072601d0f04100303100c051804d030f10506007001900c0369580000a0240c0000715002007252280042c01c0008510400e00c0d800180084004100a1003c40340d20110440c01e10f418214a1310198060003000c990240310704501050320040c2c1c000c4c0701d00b8244140107070b41100040402c10360810100207544c1e110607070090200010100090000d9031442d80607140d500758850b1090041c543c861401a0300c81d04803101c0c0e03400199000780000380501c0c005c901c25010341d40203000740010008010501c160030001c0140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 146921339 1250 146920089 146920091
    0x100c0909020d0f02160b07021218030f0f0a1103160b0a05091003020301080c09010e0a09020111010c0908060703110a08070c020a030b07140c0c19091109090a150308090301 75
    0x80310070b04513000500d032100b03207031140c201c0c080000d20349801e00c040003402d01d404550003451900013084903001111202c59000b19043e0020740c0c030000082c80c00c0d44144050106008010503040c8810f000140e14034000c0c030030002040a5500d84041c140e8079044032080c44d46403014a0030400c04608000010720501d0300d02e180c242d2810711190041010390911400f03040010351b000004116600c406d0049042d01d07002260b01d4685e039450014070103260356001d040c03030398515030307518802085a008890f81e86000312144000c2c4041c10306281c0280401c80c0702e214041c2c283c007403a0001451503104e88200000300b050b840465017400c8046000300c1d0507010040c052800e00c40480007110240c1e40c0c45142000075407281030007544600d03008030002c0c03030f5842d6580c42d010305600c14404100d511601156030210228107030b41d8804d00464058250425038802c1e8814101680b6001c454407011310070400800509800b0b40e0080070a8450410f11400c840031100650194402c114083c4001401c0030028001d40c0c00081c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 146922589 1250 146921339 146921351
    0x20303030c071b080706080115020d0302091c08090f03030a02071215151503110301030f030905090a090506070e03211905090f0105040524040b040314100c0909020d 72
    0x41c0d4500b1602c2284c02000031a80b12003820884e050780042c049014104040c10000070307011031040a5950800313103540106240c0c022403c12540d44403a100306441f224032240c0091805198200101c050380f051003131a02825070315500e01c0c098103000007100c51000072a801859041d02d4a441291149005c041c03c65030b03915034030313602800102980603000444500181718a001d0b490f06070b040b040e610418002d0010316050494400e0101c581a095074112604540c1100041a142c9402c4503801c1050700041d5000c0c605409001c3c04c0309840d8000c0c03d00c580300c0c81c00c07035030140c94480c41612800002c05030150b165100e0030440c842c032400c480e94400c00b5428442e507181480c20310300c0482d41c1801000420700000d40e01003002c3c0e130a0714080d0f54422078500213090a0313290034144030100c0c61014122080103920000d20a00d000106518001c8500a00d501060300d9296a2646000030000440030400341c082c1c42600d0030f2143d40d251502c140744140406898071603010341381c1003094029410400e10b43c42d0035a5501d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 146923839 1250 146922589 146922623
    0x10908070302010e0601140102070902030a06030602121e1027241203050406050c030f03010605120906250e0a06020d09080f07050402091f05040f08030304020303030c07 74
    0x2024040051080e0000b182605102525525001059110900d0041d10100c440d009903004107005040d40e580d11009030380e03951007400110140c0f19980c002045240300040381c080700c40b206d2085501a0000001843c3c02c0d01c0a0000341c040c2013000c1e282407003100d41042040107000203403480000241c448144e0703004140348c803040070002c8591f004440782218070303801e44035041e00641e020354001904d410a10340905500c5d41d00c00800c0350241d800307500c2c03c0c46030016691400718810002d84401034514a1503681d81d60310340c00e000b0156000194201c03ca014088d020441034000880c0ca584500c0303484500b0380500e8165503420b0802512291410705000e00c2d1452081c258030384901c0385001d85070a8005207640c82481e54001c004507278a601c0f2080310f07000f00450ae0601306010880c0402c98500302c901588030f014100000b4140c0b034110440341c3c84200072114806186030820003800448250441d8650b82a07030741c00c5d0340350301c034030003220000d5041e001040000c02074103c0202801c4094040c800c01da45080c464 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 146925089 1250 146923839 146923853
    0xd0e01031419060b030f010e1008060103060f0623060d020c01021206011e0804111302121503010903080402060d090203030d0207060c030c0c0201110c032a1009030605090109 76
    0x2d4032800c00c102c400011807499030109005500040800c204010b1071440e1108007040c070072006010341d004070303480700d004944140555076044c400360051506550b02543c1d00e103071074030003441e006e40745051140c01e24100007013070390340c24071418044043c00501c1c0c40c0307015100f800c010307103036200121070aa01d650030b100c08252101e007440601002010006042d0860904000140403460390300d1410b11071078604d0441070381641e84881c0a40c0c0140d8441108081000440006640c00c803107100f00000181c804503602030308040401c2410b000d81941803c04041d0860541894240d8003040c00240105020784041401030901e403005150758002a030000400940c030703a002a0540d4811b42c2040b007043d0300030806406105c61403080510f1011103040030080d007400f9030405003400c0703030622010f414082900210081c0d0401485000d0440c500101642d040012603c40d02c1d014201ca01c241703954a2510a50128960034001e028403c5583c0c19280c1400e4a803840e80c0355805031000400405a80d501c44440000003124 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 146926339 1250 146925089 146925091
    0x3260408030a030203010503070509040213050a090206070b070f0906020d0806120109050a031202090a05040b040608010e0307210801050d05010b0904060b0907021507110c0a03030908060c04080d0e010314 89
    0x50740d41c000d1391702d5141204051514210b600801d01c6608000288001030343d84400e152411280e40d170000c8ac00c0e42c1d80d83c1c01c2c100100201c40019400210000b056420008482c2c2c07030034410070403904c619580d1100300c401200e00d805c050080c0000740c2e00130881d00702464080c0b42001c6d0b001c007004210403030140700101140e0030754240201c100c440c1c0e0b0041c03195408050b0020350415400b280d0003421800d10a40c58005071a0007071a1054070b01865032182c520520384c4407a00a20007500c101c4000b4402e00f4400080302d503a0342d1180d0025140321032142d4441840a00f504141c5241c068540e4a61506900703000401c00f0000040108a54540d41c88400880c1c0d900d4003032040d80300318060440040c440804d032060141404000342118210b410102d608060f20346400c090b103800074411303e46621081f080301401850502c2015913150721001170f041c00010594002c019000b6140f0100650b0019110351304e1a091500403809000388070b0304001460314800384102c0440c0390407401490086281552003c0300525800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 146927589 1250 146926339 146926357
    0x12050703060f05011502030c0606090a090609080901020d0c0f02010e06040306050c07140c03070e100506070602031006080f0f0714190305101a1b06090a0b0609010326040803 76
    0x10f00d540040100880c1c901600b002d211890000c2e501d8056020080c94852000800180c4100c3c00d000c04221041d0a95000561a550001040181c50003030305280903a500300c400094010320038110740d81d1089104100e00d0051542c411065020440c85a0040d94000c81604425410604c01c1c800000866000c2c050075004016100c6001d65400b510304181c003817007250841800c45980032030a140c40035100010390304112003030039070404c0003074031040041c105a007990362040d94031460200e42d00060121581c01180102c1c01d41c40d404140b10782ea28030603200f410007290800c40c01124440028a56440d040c42d003540300d00d0350301e05002168043d031079081494000c20004024640048141d1800d15050720482e9000440c060b0380034030741841e1503002c0100c4010440d550702e50b07034000b184c040d101e499050038a480450410003a165039181003610156500303201030050790a103406030081b5100c0e050403201e9a051380c1c0c0020741030004c44540c912410b0443d1381929014408a002c1000040c070580600c06007010312 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 146928839 1250 146927589 146927591
    0x807052b030e0f01050c030d0b060c0d030b090a0908030f0403020106030b160909060b0405011103040515030a0c09050f040b121c0816050909040302070b07060906051b030112050703060f 81
    0x1000d90014041d000c030f03014801c1d5042c00303010819142c1c119000000c0c0e0300f80c500c20b8a40400c0d0f10040402096050140c145c002d00305105d0181044c0e603c1e501500a100b088005031030b0400d490350b030003210109440740080c0180800c80c003000810741000d04d410109500c940240004184a81e0341c3e9154084100308507100d80410014252403035081e0340c0803401e08014941c2c0320050003980d0914112120a00c590b05c01c240c188080c1e810309116400e400d10984004110040100351030b41400071024810703070300444403056014a08903003610f14501951081d010750350050014a408071420040c003000f40b10a9612591121060004025880c0d080004800c02402882000f5180c0820072014040c0c1da006010b106506800300900c91082c0c2c2d20806940261008407800c1000da00c660605070b04200c2c0d10703004400740000c00540703030041c00003039080000c05501c1500b04010599521482c2402940703a207100b042c40724010001005004d1300900400e6505000c0c0050f210752a0780c941e10b110884000000c07204040e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 146930089 1250 146928839 146928857
    0x925180503030a0f020115081902040e030408010b030f01060f060302070f0501090305091002070b0307140c03040909140312061203040905090106030308010509160f11030a12050a060807052b03 84
    0x107580d0a002d40c1d120a0b4011524012090404041d552074145841d0480f9109d000c0c1c40701d1105556807500000300c00244581a03e0f80e81d5118200580a000003502443c020311034041d0300074104d00c0500c182d9048403200d002c04100d050602100300c0103548611029541c00011a0704107012600c203101e101a018825200d01f82d4818a160911001d0030130b150390102550840c800c1000307030000220071640c3c030030841d04d000d1044070b90300d40d01d107441030140c0704114179070f40320106003c1450816035020700c41c80303806804d0340404d0402c008222a502d12419140240901199000c9141400c0c083c541e000c501d00046e082d21f00301502d070704501048550440710f00346030360b446000800c02d141e0020340303240c003400d0180d41d5442c003898a0b001d101c0c014956450b1010808c0300009810103594481e04e5980340c180c0c0e454050326600c0b01d4402004007401c01400b94500490318210214140340100d100300401c50b4441800b0b0000d9914240402c0f60110100d009089044032018455058505a04e9400c140fa482a100c98440d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 146931339 1250 146930089 146930117
    0x150207050126040f0206070c0312120c21020d09060203010e06060903280807060e0c03061e040c12050601030507090b09040204090c0807140925180503030a 68
    0x118a0310380d0a80702d400346140d49414070710702da10300c805a805904001031010004851001c10014881c0c40d10140119940c428040201324031214424582e00f8107135515903510783c03004401c00440341451100c2002c42d50241e00411402208508a103140101d00001030134401c04203000c00680c2d107190400c5642680c0000180079031410144144d8202c1b100341ca0b05414602da0901182e5200c1c80e15258042100241001c4042c12841c03152500b402503102020603284d20361460120003412884040903540c2c000c203202a0018240014150702c14030801c2c071b03042d803038000364010488411000741c4162401140c1076404500d01c1c0941401200380c07841280100200c0d07143d030920900f0701c8642c0c0c0207194072508001d0726080c0c581c0c5d0f50503c941c00940440e000101c2100d1032030034a01800c10b56100034021f000b120000505507691a8160044a50580d081000e035618620b503a40403198000d8502d05000704411164100c1e84a0509016030216691240c10f606845d80002071030b60f003018508000080340400341100c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 146932589 1250 146931339 146931347
    0x609010b03100603020627060703050705012301060f0905060403050a020a080a03050d05130609260304021005250b070e06090a0501030b01030f0e06040c0b03010e0a151502070501 78
    0x940c80c0c042040410466003903500261040c8101440095182200700b464003408101f001d042d81503040041c44a541c48a161501400c00d4000c00c005032510f52170240f42c6100c2000c100302240503201000d0440380ba41e070a00d50141c0d0b082940894a0081120044010580f900c503000200302441c0580020120700301140304104903d44560000b6460350015040d000009800c0340a686142c03250307081c0072559a40d111045000c0c00070903400074180f00e0078244c904060080c1e207030824142540084003070070600120105410203201c1901d00a4104041c030008415061141000d410518810b059129090100305c1402080100c080801e9034210720031400c2c048480d030800c800728038200c0f00381d0ba0741e070602c1c0c401c50001d8881c07441417184038141516481044e140d07038400d9000041c041c5403d0410000e8141c0d540210341c4c1d44000700c6084a100c6030301e103004103007006200d003541d0403102c4a900681c02070f942c0d032075008064500210100c4043d03507030701000305900185000000305140141c4c002c009591034500010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 146933839 1250 146932589 146932603
    0x2918032a060702030c121c05040b09011118060327010203190c02030d05100902131403030304051911090c0a0e0a060e2e020a0311070e0403200609010b03 67
    0x3040d548200400d154400e070101e4000084444056400e403209003689507c11a600c0301d0111004440ca004200030410807949603c5004e039507407900801400203030b5100400d8611808036015409601100214805e1034072000456001c50311203040c500400c4a0802c0c0490140c049628041c0d61350040b0030450100300300105502041d42009050040e185a0140039407a44907204416074040e0711400010700402c40c1c1700d814002003041400840d566030781c0c420001080c03e954050b00300521485a030303d0101e854000300b40c038003498100001d02144000000180d0300c0c0d00c1484402c4070460656000401c6a50760140c05511034000da001c1940d640d2542100208030300a1400030501c68580c0c1041800090317404041c940c0c034464242c6808004a40c4c40201c2e00307001000841d0076120b88800320241c114690b0100e81c40b44440d100e5158240c01e04400c00305581c0364200c50058118086410001070082071003140c0004004212400f501c2c9440d8220304242d041000c1254160200e031345441c00e000c054101000f010f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 146935089 1250 146933839 146933851
    0x50604050103020f0d030201060503100b0a0b0322030c050a060f0b0910140d0c0803090924040b01030e060403021608060c04060509011e0207032918032a06 68
    0x10031441d81560b0006035000d54280250380039030780701d05021081500035170183d409894010300f2588e203a800003100c1805014420762190140c00a2100000c00b00c0c1d0450a890040c101c0d140841041d0703400d11103503c410440740105400b005040840803000c101c0510100c952035010b0400800d03a081c06820700070a54950360105401080c07035000708114110340c4142d03101038601c1c2e0030709016028504400a6030ba085103100140189801d00f000040c2440b00000900120000351900074255a07160002c040c10040180b2a8902d150000c00c00c400c0c0349401e40c0321030340488050400007804050555072915158044a04801590189081ca80d01c1285a4410300c018010100107094905d44514000305600a500c00c02c03042c404041040322850f802801d201141d003503030013403540d84500801c2000350b49150500c001d945601d441034110b407521115008071945092542c2c040421500c5103502c1c420000340034655882c0340e0100f0b00440c041e03040c90700c1185039140000107050031041380d050344242c00c0c2680036110b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 146936339 1250 146935089 146935091
    0x60409020d02071202030313110f03060f01030501050f100306050601030f02070f03032415141c0605120c010e010e0a0e090114011203080403091502010c02120901020c04020702120a03050a0201050604 87
    0x100f04075262034000054190b039121807002c271000320844c0410300c0345102411140d4540035036400c00ca00d204a815849040f079010b100280f041c4d448021061905550590303003203030f41452045050002c036029811907074002c00706140011b03034607400b44d51600c01c9070072000d0101d03007000c0008943d000b850b605000b8035a4032004e1000e441a481031005543e0500350480c420f103003000c422040c000c894240a0785103003c050071084032242e07544020711002c503a0516280004405517240800c041124101a0350940100110740014403d8000702d130015070304074a65140303a6040054403e00c140241e150010381d00028050820700101311700f0b00020050940780c0298110600d1a5040010403051395040c41d025071854050400c1011521076043c2203238103190540141c40000c1d01d0350342800615605500c585212031550b400da86101001c2c43d241d411368800e400d03a1a005901410002c0701902e041e034020100c1900c0100418801941025040ccc14480919130903404102c0100b95511510b4081c0529913101d482101c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 146937589 1250 146936339 146936341
    0x307020405151804050703170309070e010b07080306030705030102160611090f100e0306040309061e081803190503010f0f05060a0c1103010501080c1002060105090a0b060409020d020712020303 84
    0x4086044907160b01d00d100f0003074040300c0204041c40400c2c417600c0043e641081d4031a10300c070513204040300300307078815143d02489201e58000002d180d010300351004d040c1c0d019100719138603192254640c400c854102030401c2c0d9240c05010f4000811303640074401011900801200700d0703d0580a030410000b241c003030040340c81e141c4c4020000c00c1c6c1c003540c0342c03e1046c0a01d1008c030760100e000600344a088803031270284200160503202e10414030042c1500300c1e002d01c0171900035644018501c60289800e01d0131910076103180f000300d030035440400d1918240d808150542200e013812a82880125081054962800c0f414000441d40010040c01030f02c0c1e81401d07240140414100c0310750040d2400020038420f1190100900401c11804240d90802a1112807102402c40041c024001075071110f60f110b44881c40c030841d0b14400d6031032004642d06903001040b400e04032000208501002c0c0d0303900d2106000341065a86441c3e1200007040301068400c40c1d4170151410a8110000603115100c41c0b900481d20092031020380300303640c000c4c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 146938839 1250 146937589 146937631
    0x5070216050d020103020f07061104030209060409030c060b01020c0a03060c020c031c1d091005010e010c0f080f1b0a03030f09051e03041206050411010c0302030d090c0909050307020405 81
    0xe0702d041000b50b080c600181d9424019032841d895014150000b00702c40c0c1410301d00350400714214040d1003568002c0703500040d540c0b2a1800c101c00c940502200502103242c2c003501d030300407449584c4000308002e4180165009401e09900044c420303a010340007100c90301d6551070360384070240d41007241081100064004003a03240910100320a01e81d0b008515608002c2e18030308813202c5141c11144420b007014054211101030500c01e0882a07840c2d00350240c1030000340000107104903984654182e25800380c10504000301894151a150210740c0044171080071000200160800590100d03880300c0707990f010344050440a04123250045c141c40311026040c480908140301080490004100000c29880072041074034070142209101d425805a0380c0601100c5410400d41810b00440d034008034412449000742c0e01001c1e00c09401903600704020100540140d00c24058903101071034591010325014096035040c081241e4404001d025200080c20496498002040000440c14079000f11030300507000b032905003010004c034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 146940089 1250 146938839 146938849
    0x801060c0809010207090f0e0d0e06040639050f070e01090b010306030204020d0b13020f12070c0209070e0907081603020f070c0b070212060405030904020309010e0a05010507021605 79
    0x31016108220000380108680e000b0042c203070092200c030b07070281f220f4044185044002d10701d04101d000240180c4030314000700342c0300d20303040810304400810b564103260070901c044803081c4840c5182c0210b201002c01c0c210040303206d00800f44a01040040401400c01c1c145032681c10420001818000d90b0b200c0074040c071180d10410080b9056401d168400078115070701400481c00f401c010351001c0d4210703100180f50800011544c0109030340c0b010599101c4c00441e000031107041248164003a000303c8280a0207010880c3e8075030603103d07802112a00d00b0060300841d035000100b6003002900c0744008282c05926120280c2400100542d01c681141448101450500105132582880b03610550805a0005030710350442c0e410000e039880c068211126034030042c1c8540401d450b990160000f80d12a560480503c0c40c003500010f281031143d0303401409141045442d0083c00083e42014001d00c100e07540b66401c240c1340d20420080103105500030ba00100b800d081c00c080182c103003007010820360308000e8145011300c00c1c0e82310 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 146941339 1250 146940089 146940107
    0x503060103050402060712020c100504080a03030518010c030f0509010c0c02091e0901050601030605060408071211182415030907050d030909060b070308130201020c12010912080106 79
    0xc1c01c020809682c0e80c0f000500034031600030300800c0d200c1c2c010881d42d00310f070f03001441540c2080180c6801d0010f071240101912030340254442c40b0040c2c1d011038407000000744a60821a003010070b01c034480c04007118610440d401d4270310040e01440081da9450b2102c001c42440d0040c0c3d82c2050b0030750000c011030745100c50020a0101502d50280c050b0303110001203081c03600f000d5100041301c02c000c10b0484076414403040450103001e0543d95680060700b40700020803180303404002ca40440b0380c190001e268061920494070001800301c441075500804a03a806015500c43c820101a0703483d0240542c681880d001003d80308000300981e442d1b4035042c400c5041c0304243c44400107401014006011203440b55212149940740c100a608190740140d01d0714841001c0540120800c815100340c2c020034041d0310348500120b1664002c1c1c0e8005400201c006001ca030070b0f040071640000b15030340181305648800c4080f4010800032200700c0c0822110f695036610100034000c1a00c00c1400c0c0d0b403000d151141040d40740c080b0040c80001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 146942446 1107 146941339 146941351
    0xc01090b010e16091208092808190204021803150f0f0705030103020607021216030209360c09040b09010b0307060f050c0102130806010501021902010503 67
    0x8000880c000903c8402d9640d081003600d40b282890b48400742c00e005540d01c410801c4071301d80b640c841d104131290350150441c0740700403601ca512040411030151340c0104080d401166064188505105210302c100750100c038050b803030310468810b0b40605901003a4455140c81000d2940d0b030140c001c083d8051180b0504820a150743d500d01841c6581181c1c2203c1c80c2c40020001c00c0140014508440038142190001e130002d01900e4008400c94540000b200030300c00c508100000400840c901650480c1c0d0000030f400346900019401c03c0d14280d210315080180002034000010300c2d92039035041024407035040d0001d14000311410b250400c0341c085d40b01592101965401c00c03401a0081c1070000b8480d048074111384d0b232030a01414002c1d04681c182c011020a0215540800c208000c1e0741100352080301400241c00646241c1d49000b0002e8641082c68070000d10340d412a0b0105c0700541e1304441035981c001 = true := by decide +kernel

theorem cover : BRFrame.Cov 146762589 146942446 := by
  have h0 := BRFrame.cov_init 146762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 146762589 ≤ n) (h2 : n < 146942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
