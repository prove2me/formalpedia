-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2871
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:59:20.546474+00:00
-- url     : https://prove2.me/submissions/9e3fe724-3272-4461-8155-3a51b320eca1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 516187050 ≤ n < 516366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 516188300 1250 516187050 516187081
    0x7170c070302090117010e150a0e121605100b0319020d0f060606020d030203010b0d05280b010f0206090c090705070c0b03010504180c0e06060702030d0f18030b 70
    0x11004226000c460356034020464081007a0031a600c103882c02503150034210310902035000c44103800e80040101610324482d682c82002d021f0800e130505ca071140c0948000c520300304101d0a11109105c030303c030b94501038585903a05450354807204850600074a904111124018441d2022081011700034084504d88a059011146c11142089a100305403d0403440841d4040c4101309009206000000345030303003000b0029207885400d80c40c2400701401040148810b51200341600c209451020b00480c83d500d50803598800300704400000840a0328402403246081c1e8190404066050207881d904d0340c0b105448822a1a04030031104003603560b00c1901504480e04108030440d0703110396a0315000d4140340711941d4100c8102c610790b004a940d03039400b10040c030842c60b142c454010060f410000c840071501e040d0780c50500314021445422070325442c0100141082d100d03002114403440d030080c15120207035101d1501405070103032070528034001101d41c0300078014078460703516540c00d41e9002050441c403950340884071104c221 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 516189550 1250 516188300 516188317
    0xb0c071206060902120f0603011a091b0319110a0813050f0d0e03060606030112080a05041a0d0c03021602130b040e0d1b0804170705090a090201030609020717 69
    0x2d540e0800020036400314806080704102c03828041c90581000c1503e16035514010341401d2107a41741403e01c001300ca002c1d03502c039410360301309491100c00b40d80e50000c61501301c0d1000160a040304400000c1080c1504103800c080c1d11041140d0b020040600b10000644a502a03000182e02081c06d5402040110307605030000000544208121802003030742011140c144110503c05102040055240c02202e2800340b00681d440341003500c8503411503140c500320020380501107002a0003058001214002c80384128126000b819010003424080001002664030b04c0e8000702e07152008074901140075941c10701ca40201c90f000c11002d04030700b55220b10381d02000301321320511205a0b581540c0d10094002511140203001340400f8130006002005899400900300140d8010b520741c6190880254000003480401503c040c0c07182514220603400100003544d15180b0550000c41c0c1c4408042d040100c82111a04000680c90bc01e80c5c0c2404600d0340c0f81c2a50003039004803400180b4075050340e484904901c080703102410721030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 516190800 1250 516189550 516189563
    0x9060c0a0204060609030b010e0c090126010e180607090603020919080f0601060f020a0b19060b04060f1d040b0d120504050f0f010e06090d0c0803030601090b0c0712 72
    0xa000da8001011903000c0d0b408200810b4003c10100140030f12424200d0040010001c801064500a50901300e030f4031031420f005041c000320b8101c010044076502c0c201c4c85044036402038409e9039610f0701c603010b1407001c04550300d040e404110203288003e0132010918501074100c3d511840030560900c1c1059010390003100903943c020380f58841d180c5070080714250940040c06010054084800c1c0140f081d402c110058000c8028050242295003085a0004034188c41540080c071568550700c80811820890103950070f407480640c11f01c3c0300803a60300c0e0103000810403a40d0079180c0e0640800c5281c402d039031138149102c0030018040e2641c2c2400c05414103401c0002a620000c0c1305540c0c4240350343e56003c1c0103a219140310000303600400d0521090400d80240d0041c5a4201d640809046400c00020403a58004e0b42d902c4c090640851040000d4030f070120020006d65000a110400c2e54403552605d039241c10843d0910f0000c0e013104000541c0386240310071103510003840ba01401071641401e15841d801d01c00148120b030b18 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 516192050 1250 516190800 516190813
    0x1606030e0c0306150108070c0807020613030615050103050105010207080a0b07020f0a03080106090b120a0908310906030812040203030f0f0307110619050c071b0e010b030c09060c 78
    0x1d03590510203140305015844022090318801320005203c500f0040c80c0c034003072210000f0301e04081000d000c25510301e540d0464034582c0e5140a600c00e01400300740b541c00101100d05002c06074810031a012a403209441c800e0b0b80822950780e0750801242e46845c14458183c079504415005030202e000d61a0496000c45207004031810640d00c03a07081858001091410380c00150400d0041c880f042d070015000000700b0801680034140900c0c40003080c41c08101400c028200323944c480301c0d00d041240300c2c020b40b00781c620200355104400034404071440801d400b400c500407045051500220300c002d154444c890580740c010ba80c8506007070045d5003000010030701400c182d0b030612081c0040980c10740c8820050030304101c1007803900d4903824811005404102203007550301061300080c0c10841f02c0345607540122044003818001042d40e403a403c5207800d00c1e1103043c030b01500e910500c1d0490103400042e1f43d030080407140326080c441e0389030382d03526a41e5045002c10303a82305040a4040100f500149405000f030081d219503081034814 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 516193300 1250 516192050 516192073
    0xd1401140103120809012711060309010b01110a0b1b0d050a0c02010b1005030601050f0d09030801030201140405091b120f07120b10051c0c0315081606030e 68
    0x9040e0400d920480d404080001c880c0c0c0041c2d4002c81c450341054600c0c0090000c4d42150f541c01d45034030040c0c1a03200302d05035550840d03800d00900140c038881e11003020340007e41e282002c402090103031520384016404204003e42d5400140c074001174030040160061208136840e12409516500f44040b000c441072000d505110802e0b10007880d10940f8001e0484010000d54a0b01c008400790a540e080008544508012112000c03026040300803030354002024605a955110046403113120703409032045c0007859902d0b080c003503000c15800402d8181641c2c000d0300d0f20000200d1000144c600b602c0346020301038103c010750340800e03c0e1803156481c1d0340901d0740d403400d0343d400c0c20b140785802020031360b082b14421100c4201e1302c20312103036a0300b090641e9001d030782c00350043c8265225203001c1401c01c442c0d00c9002041020010300d0200520016100340030000014000b4046049007000080141a1904242145902c10480080c0d001c000040c90240211600c904100b818507209040d401000407c0148205000b002c07440303503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 516194550 1250 516193300 516193331
    0x1b0f090606051e0a0c05391003020f040f0e07030b06040b0403030804020f030a060501031b061d031507030605190501200106080109050a150b03100c121406040506010e0d1401 76
    0x82c0411f011210301100a602c151101103600d54210315000158088240d21040b515968103280380000d43d82005070f03584800141d2440307a4890340c0d00842d03034004024404101100c0300a0224010410303076600340820000c0c401004181d01c6070b88a5a8000c000030030040001034011005254002d00040ca00041c20b94080042410840e404504a03141c9a5450043c4104502c07034622225860030300c00d01e8501075007071a0000d4a0260441c8103490698400900c400203a03408000540042c0590f109110042c100782102902600380380c0070720b0b481914800c04000c981c0440d147d08030207c0c1c4050791340c2c545107041da00a507044000c1d03860740700800c0c1d5201d42d00419100000d02503043d8151060000f00b076241302c141011f003001240414403010407424480484a0350754001130400c000c4462280018000f03403400d106403202c030a21000580c050b400c25100c3d5121000c900d03042031050350281c5050005039642c00044880b840d1040b0441d81c4000d9070703d181404503900c110700c0004003500d00000645d480890390300301c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 516195800 1250 516194550 516194563
    0x303230108010e011b02031803030c010e0303010611030f04050105070606360528061e0501030c030b10110304050a090207050f010917071b0f090606051e0a0c05 70
    0x50560b440381c0500081220900c03420710170700c0c00c4000a003041c0201380e40c025205d10401101003110500000055050307641441110b801e4410390b0002c01c802071070100303919202c1d0024810718011500a8030310701d604140c0801201d120917804d51a803407a0500708401500c1c0c64010315000e45050b95203c401141d01c2d4540211005481002004088a03807100c250b01c07142503402850184000741440e080c405136200c0d2164035a24400341032140b400404256258000034005540405c0d0700c50040d80200035a1302542d1503942c10f88a00703a0703007030018810300c400503030030366680c80740b0356070072602d4441240706d40c612540074110141058020760749483e41d1180081c04400380381c1c0044861540c006842c608100b01080244104404e40300203100c60341c40d81c2c541c2100c0280c0301501c0daa41910000d0708001708000c04020403064000c00c2001013000d42c58840c100c82d40e0140f40900c0c040140707480c40120700b140c002d00507135441b0390801c40e10f544812108038941c1c0380e60f0070034410078003882035282c0c1c5400001d400780181c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 516197050 1250 516195800 516195809
    0x7020f011a0a050402090a090c1101150e0708090705010e0109090609050f0f070507060513021e01090614030a241706010b0f12060a0f030501091406010503030703032301 74
    0x8025204001070100300c0d0107800d903400f081c81184100031614581d01c421002c0b4044070b0710050005000d02440c1c000340c44031014001c4140d181d5280040200075071146010407003c0c0c1d43c01d40c0041d0707444c0d640ca00c0300341e542107002c3d50036440c15800420708000030740c8a40c001c5d1032803801c10301d4242140307956210b07000151101c0344c000c84090303034544041081e5442811180b561240000841d03005034149850040c0840c80366250107060140c64030005113003040c07103022550341d050340039014101c1000154128091040039428280c00207078603850015429108503001941102c0e07496445180d500c13003411140087c04100650080e00366000c108001030070012580384010f142c02c520102c0d03c000440c550b1030408005070409420514240f25a07140c00b00620107030751031155020020340058460307100090b0580e443d9480b070002c404450750007008010064000c86021441210074900c5401c40030690390305d60009026040d050b0b40107201680110381319030084103a62262600c000b010380010400808804001d801 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 516198300 1250 516197050 516197081
    0x720090c07171e1e07020a030312110c0f1002310312020609010605060a05220f17060912121b0f28080c090406080a060504050d020a0209010e07020f01 66
    0x10b040031264a851040802d03003420828003881c05c0803e6000904119060001508000d040c1c884180380455a42c0f00421000207800c0240c0c4607609411041d503581488079540409000304407040500d0b0140b4000d0760410580c40036100c1518181008034542e142c0e017510401d521518600b80000881c0d0b0074601030740805c40d40c0d4050f004604d095141503082d2151175120300c1c09024204804101d5580c0603054400d005260740300000703140642403160701c0103405a0011210302c180c0010000b2110f90070700503120100304a1041e5002540c8507001151103100e0b41c0141801940200032102c003401060255641c418032100303c41400415910035410720341c01090711040c0010001075100d040c2c0c00f41d1003558010392000c49000103901d4420400800c52903014090040030600412504102d503120f420070806080e90320708031905201141030000c0031384000d4800782d5650240701458010684046048805035402030700c22189646403007650400c0300340041580046000d001202c894605082c042d0701d2000300d2003130 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 516199550 1250 516198300 516198307
    0x9041806020721020d020d03020a030902030f01060617090c040e031b0c0108091c030c02010204090f0605090105030613030f0c0b0403031506030c021c0e060720090c07171e 75
    0x901c01c0e55000d40220542c15035000c5d403442940c0d194002521a880c01c4a46405038658204100070b502030b009001c002945406840c0e035852072450305500c44402c55015035502c00400030602d14008007041c1c00e992010098008a1200d05a414240c01015581c0c0070b4804a9141a81c0796110f114243d5070030700101c1c1d6030b4000004242c003c3d030740811055080401007010340135043c0a134001e401c002c0002c0007801c00741500d910794099054002e506490040030f03501c4081c0000b0100030403c07001455103004080c800d0302450004142ca007800220b0511401c4061064901c0e090142c60a0380d45a580030810010400700c4405031001840ea064a28001d520a440100328a02d45031440802d03486140c2040c0c0c00c16141c9008070b524a903000810302d82c4082040c484030540c0380350550840341903920040198010340005084820042000405181d18444061010340c0c50019001c004880d02c058440b1000f11205005420228101c00203c2c1058003030007003c10b2501517401c070020310400103950038194011012 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 516200800 1250 516199550 516199583
    0x6150412060c02060717040f08040b040909060c0c0b0f0c07020a0801020a0801080c1503040c08060c072a090f0e0610050a1a040608090309040908070510050408090418060207 76
    0x400132a50819401c3c103201e011030541c02220640710f58000c1001d0101041290000f051009507011107020709032170100300b42d480b80c546400d50050b040704402140c01600e0640e0344007226100b02d1075440500da102880c140b20380c031168044080c8440144c04030303551601c200300d4036005a940c045000e0041408800258861000d1000500200016800300a07160407001e6104001c3d550f07110383d5903075100c4400510391031ba161818812031a0020750092041403150405101040c12000e01420312a8031801d42044040c1c80e0081c40300c0324034600340d440c0b1101002d907402405074001c40c1d0059880128050000100d03130303020080d1280b0b42002620f01011902d40d84c2804e000c241402c045020140c0a1f4942c00340181c003001501894038480c070300c584c10801210b040819240b00c4103004a070304000c0003c01c10300080940b030814240c0780c0c0c8442000c4907a84200d00340c800d01c02d80c01c0c0c0141031156407c00c000354146110310091001070107140c0c0d420958155000901c1002981d5071000c3c100d07007070241d1000040502c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 516202050 1250 516200800 516200803
    0x20c040c210605030705012d0203031017071206200c07050a05330706061716030201110a0b010306050f0c070c035102040e06150412060c02 61
    0xa14007000100b400c00e4424002da4500054400450f2001c1c6000402c41812030a2842c19882840b01c240f440c1001e004031a00c0c00f17600101542c01040c2c0030f81910706865890b070410040b4441c0c05040c08850308040c03000c200c0960042c107040b0342c0502403403011440545941c3e42c0034121144940300c001c0f007540442d140c181210f04020080103002c050b6000c203d01410300000810505024100791050300310160050000c5095003581c250000d0a0b4201c01c1d11500030340381c5000582042d0103003407160303003282c4800c103500a4001a040c109004062080381c0d403a06540044400b01e61609040f0210b1003212071810004c0d04200229000b540110f10004840c01d1515802544a0019144c0311b44440705008030004105c940310030724101c0303900c001200f242e850f20440e80707900c002c90349200c2484c2080c40380d04038a100d0460091000030000d020300e10700c000200c042884040b4042c3d401400e840d20b0000001038a1401d000004480080c44c0c080c0850070035585540c04180b050b20600121140c0d03456a102c6000c0980 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 516203300 1250 516202050 516202097
    0x414061003061a130f020c07090906180f020111011e060e0f40030309050607050f040308030a06080102040f181e0f09120207060206090a030806010f020c040c 69
    0x7090f444403034005060700c001800f4410702d112034500d25541d522441041c2d0b10a03412a514080f600d010b66035065690303d200c100500c008170041e81e00505010152180120b85802d81610315404a003607140c100480d001110a054003543c0c22070559a549803004040075441880ca00b210345005000c50071a04000080080c108084c2c42500b440d0056000c3c400805401103c01c0300d020103540b0303444078500031010b224800110304a10044031400362446038061542c140c002410301030281080b911240c0f600d500c1100d05210b04504101c0c025010300043c40050b0b50100190341041e001c01020810325100c001749422603111764411007541004e0a0104140c0861000c4814450203508041101c1c400d441d8500c0010b009a500b181c3d081c940c0e440ca9000790703407101e510001ca183e401081c0745c08055100b4001941d03821140c0140c00152144100107451020300250301755000e9410350f03c5130100e8a5400041d5070344c42c0c00760340d9142036019041800c00941c8840c401d846c0740d031005585403540038886090400000310f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 516204550 1250 516203300 516203321
    0x170703020a0b1801121e020c0c0a0509070f0306080f0319050405010c0204020309010f0615270e040f0b0a0b09060303120f06040e06040503071211060708041406100306 73
    0x401070148941e25100c1044502c030b00070f400c0c01c221100300c070b150001900400740e21311040805000e0145485120429078080c00d5030590010448845140b82010081003000c184103517584907040c1400101614828590725810154a0130086030342500c0d10102d50800445085800c0980c0c00071900d0346006c90f200b05030000d172500701c0c209245401e0411000a02c030701e81d2807030042d0007250004045424180258403102c0040c00200c800c01056440d0300300c076813400d40c089040d0000140b03000c00000c4489000d500c42a0384001a0881d400000d00d4400c46104495001340182c4100b40c040d000c000115816510702481007542c0e0350b0024004119000300030180070090301c01030203940300740030f10009102100051030b0422615a911328540d41c4100c0083c0103070403e5200b040307080c0500002d00003041000409403c10a20130890f03840441c0050004558025404845a03ca5407001e4041600a07001d51141070f00107015001c50911148400284e80c42d040c0140d0344030180c859040803c00c01d114040c8914442d50 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 516205800 1250 516204550 516204569
    0x201021b16140a12300210090c0803070c03020f03070b1602060408030f0d11040320060d0212010f0e0417090f0a12020906060a090515090409050312060f01140d06170703020a 76
    0x40804017002503070351508a000061030707992487c1712414429480c07c80030040c034280301102d580740c0c1d070351500842c141800d1000328091155402ca0540d0340c500410b22000f91109810358505292400003151024040e6440580e0407000800010640c02c82c10700042c1500007070000c0240d660042040e5840880e28508400700c21643d0a1000b0700000f544c8456440c0540d1110364030f40c12003442d00c0c0014085d03104a00414511500c0000e412136005101a0a6070490704900152409a0b5440507405400901281e0042000c0842c24206c800d011300341c8040c4c442000c02905003c00f84200c0c0c0c0c086900c181c04c0740c210f44481212841c120003145818150076038011400e032000b45c10aa00000e02404109082c0580c0703219686007051944805410029501c0c81d0000500c10711010500303040c103039241d0384420100b036001c514540000d5103c0c104000c2c004c2e01060180c5d11f00075554118504000f1075081910700705c0c2c100c0d8071050300203a13401185002020310b40c1c84802030007025145d03204200d08041594403000300e4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 516207050 1250 516205800 516205883
    0x2040c111902061207021e0a05010609020a0c0201140405040f0902040e0109050c1002030d0c091a0418090807060c1d0a050d12050d05070201021b16140a12 68
    0x41e140d407801c0d611344401c0e0031aa0425502d600a0a07420b03c9201103440c0030010040e11041c3e6021400103200c0d22090054008001c496213448501c41039101d502102e201280510b041000103503c240b201324940c00c03440c4102d600b00f9031a8000101034481704068a40142e03203510104040d40740a2117210404160b42008100512140e80c905440c4e1107040c030f20038400d0014120112000d03009004444602d0469107040040701c40400c6c000d03040d88480c5c0240034182c00ca03684011500600b0000f240e095800d0000b421911256038030b4100c025000f6044221404035040c001c0400061440c015821074a10b542c0703824003d8041662603400605905142510a00c2940010041c0380c4410012100207074020b568451000c4030380100307403001d100300b42e41c0a4446141404020b0142d9048d400b0b064900ba13020440c2044c0035040c016940e03160080400324606480000c002c00000c1e05044107101052400380c800c050031652074410044050801c24180c901c0300d002c0c2900c0102000c3c01d80c82c07203414074100550081 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 516208300 1250 516207050 516207053
    0x207122d12110a0228030204110d06211502040b120f1005090a02030402031204030c0f0609060e0f030f0a0302032101061704050109020907170a1107020f040902040c1119 74
    0x52441581c08119520345507031070185d0b152000c82560006160003400600110604104400741a03100700c20000f501071a04201003015001d4074450012028200c111700c00751811922040e496000080240b24510390030000002d501c840301c000f43c4a0043c800008001c640b60900d01e000c1900002098412040030740002030196546d01502d9903041742c3d500900584942e11407010030314000d090344d070300035400001050020421010340510416980081683c0c0401550745000b0f450381c041794010500400d54000045440c0c0c00c020f800c80e0f030700c20700c0141100c008102c2d4603003150415000300c00c00d50041e00005a4241c4d02c1840303a040c1c18000c1900305100301d00d1340c54840b0081895a500411002c010340717050115061080940100a45903002008103106041c0a81e019190030314202c90000d222424800003030310354801b880b4031920360f40c400c91000e14002140c1c2c2001705418000c14001c3c1d229588003001400742e1036034442d581807a410b645800100c110003541451500d91603048801403101014071030740 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 516209550 1250 516208300 516208309
    0x203010501090b0702042307030606030504020904060c0905041a030f120412030e04020409020711030601080613060e1e150705040302091510020102190207122d12110a02 74
    0x1c480683c1c407402d44442641c80058003401480c0005a944420514984c42c0c0ca201c0c10782e21030286107140c03020816955160400c0d415a002150003070f50102140c000500885c030540c01504800100e4503007500301c90385441c00a0111901c141e10004006d00d11051680c40781810400f07100207114500041c412518541c0c40e010b014401c60240351070000e8041c01034404c05005480d2066500c80082c8155155074407411140000d40081105441c0d050b9401390300582030401160450507102448050040c607900c11010014860341007074200d51a90392194018901d1400303020b12000d00c003008401510a03204008074a240c0b452900084000d808084240000150800100c2d421240d05507000391141d51200f41d4448881000b0380103c1d00000344442440310150b042d401041810201e01b11848500b0300d12404913036076903650007010711400c0b030358581501103440c01400040c410803690891408180002d40310b154980c004200f2600e0305c0804104456031900b20301d0483c2c58003180001003005006c541c0008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 516210800 1250 516209550 516209567
    0x20d0501051608100317190210060b031005040e031201120302120f090f04020d0f06030c0f03081b03190203041a030708070f030605030a030804050705010c0803150307030c031211010203010501 84
    0x418004d01b0401d10342201c1041b4040d9580040b04400344092400585c10181d00d800503a801e40a0540c07900f000420400c00010949000d1680b580b0303070b40ca80394242000e210041c00810f01041007840103100750f4003a881c43c18143d90103030942c1034080c6405005854084c1ca01010b8124011400314244208060b042c246810303595004000c852617a186101322010030020f04c034004400750440c0c1010111841a803151300400200e82c440c07461020401e507079003c520a0b800d00c60000a20320b0300304004298295920984002c4440c46000540b803070301030381030b418515640400c02041c1c09600040b4041202c1d800005113071920900700c1f03135410b15500d01004020095407004010f001404000306640041510990003400070705000750440300c14013524107007e0300700e420803201200e6500c60480d01003500e51141840c103000940c0030f0b03940ca0640c1c64403240200359400010105030140319440000010410585510000350301540c2240b0300e000305840c00410307003130000c829011160300400040002d660f002d00b0701e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 516212050 1250 516210800 516210803
    0xc0105070f050d05130f03020309030f030903030405091009151404090b010302090a140c34151103070c1e05060c0703020c06030711070801050705030c090d020d05010516081003 77
    0xc06a45401c846420820b03401c50141a0301c6c240c0380c1c05002c240e000002000101030840494070045015144180d4a1298103051074268200b84020440e81c2004610b1381c4d00504071055601d03c041e1501e03200821141d0580c0c4210b600000f200003041a060300c40005030014505550920070003e554841489000b0706210007800f40403180d00060244845900c5100b0f025440f203590826810481c40701c03d030940006030b088003150714131440481c8110b800782860b00c4021101c0514181b11344039131241a00850324605580c84103465500b210381c603202c8030004611400e660b0326101c9480b2500d043c10044020b03000c0e074081782024000080b1000c9030001403440d500142c07849440e55a150740b89400c0b03042c0310103211440e82140c2c0101c144a0b0580e001480c0c61492b100040484403219a0745070036034265102941d03c0c101040080010499a07890f8000400800302e0203420301078406166804134401c2a0354400a071407a0755101d007401b0005201003601c50000196140c05102070800c103c8071403001089100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 516213300 1250 516212050 516212077
    0x815100e010203070204051f240f050f130608060306060d080901031401120308070513090903090e040308180706120209010c0c031410060303120c1b05030c0105070f05 73
    0x40c04180d60b2080080314407650b4003600038469400d18840d06070120102d070341c03004071204c0c01c04030100e03070980449000c12400340101d10160401030000002c4d41d020214543d00300c00c10408105c20003c0c4690100180308120015440c22034041c0b92050041107440081c244511a80004007803000342c0d41c0700c0350000010743c3c01ca900140c2ea02c0e140401a001001c124002201050064000088480d140070300241c0742c5000703444045c1d2641da514012603036407003415254081207000040601c8030441c1d035032001945500c02c0c20f00c0035040352140360304072140001b110100c0010300b00b00c0c2042071103a104507124801e501c0100040050505103a07000d08401104010216040e42c0801d800d24030b80c1c429040225540d17004a00c0d56045a1a0b0070304051250303203c08150128860541d003881a00010b01c200801ca9415aa4610f0f1554180389110090a10011468200400001134040390032644221403043c84c42030000f560748400e810300440c2560001801c0106004407998814051a0040c04540d900ea4081c01d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 516214550 1250 516213300 516213317
    0x207030f080405090c030f0703020c1c1814040b0d0c0e06010512010e1006020705060a0c0c03020607120e180c030403020f01020c010c1404030804030f050319050d0b3309041b081510 79
    0x380894184504001c642c40b0a80319550004402d0841c1c14ed8480030b0006440900c41c4c02111010b000100590781d1000344044a05c19040095000d0707003e150741c0002052418514114150b44240c03e1070100f038000800b0082000203210050151012500c0145090b0003c0d02c030b120b1414000486502442c1c00110522009498410802400c1020f41000c0c0d5401010309441e510142414880e092140c14082d01003101d0003452001031a1030034800b00080344c0c1e110028500d907a00149000305400290044040d841210b001a4400201780050446400c08100002d020382940c2002443c0e02074110009000480412052021810400888064980054503168041068505030b461031084459404455803070400340d46403254014020840c1d00d854a13401c0c4510400901001110020403003a1031101071018100c0b421a0082000700d00d01890020240d41011350600104080d10201c00b181c40208440030780c095200380e0480001900005051202c1541400c44000308400e07a110041d10010b120035071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 516215800 1250 516214550 516214603
    0x516061d0a0b24060d0c080c070f020f031006080d0f09050d08071707030c021005180111070305030c0102042103020c0405100b0705210a0207030f080405090c030f0703020c 75
    0x30503d40c000301401402084e681c1500c111100700400c0390b0044800010481000305000c0d20340b00082d101001d400280080780310f0308582c01c125900800c0c03114141c01d8011020303000581d525a100300340081012030b0242c660f501e06200020000011044c43d10180414a94103005907240d41c0b1003403a58903481000c3c541d5030041424064004058031705808a80b40000480400b0582c0c09a9a0045c440c42641e080d9a0313124824016101405500b02400c1000b074145010019503220302d02400140410206560100342c80751541070969200d8246a1750f640e400042c01c2141c5d10035803003002e46500e42030b1100e501e4100290740c025129224040468070861300e030390206843c2450038882100400821180c02c1c1d0394a8103140c12600da064900e26085140c44071815580d03c034003503074104c0c2c115044680c06040360340e045a6502c4440c4d0340d24181601d04c288280400b084c42c0e100c01c20710a0241c40031400300f94030703071034240507003003503480c0c01801c0784c0805006100c1c602400308002440f84103400d04035180482300510 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 516217050 1250 516215800 516215851
    0xa0e0d2304170703051b03100f0b0d030e1809251205101a011713020402030408040e060109030812071206290301030c050d030516061d0a0b 61
    0x15074100e6a4100e03600ca95a2542c50700c00034210b8212071251050341c80b010001c0c13680003030390381d000040140c054000c0c4421032a01440f9034006001203061501c001002c96145010540d150b0359090210041103001c0201c210610303116015035000e01c6c40e641e10204503d0700c04500350b140d903102e8081c00e4450f591074078030a010f1801c504c1040048c01102c083c0d40000c07031690078900d94409a29084401c4589014103091000d0001131140b0700303040043c0c40c1c245420802d04100d42c0b084a00501d094031000507071420500690365400214040c034014407170181c40b0f03130404001e5914500c000d800035051000084040000800f03007001c0d50070500d81c805803070040f541d50220a07502082c00c1c2407884c0b42189040c40c04159140b01e02d51030040759500c49110260080c6424000040f0710003800094200400c50808000c1840c1c4004241e409034070074034141e41854100b02610b03020071009d034411034030700c0d44448020301c980f10955819801d0400c14001008840760741e0302d03601d11010b00500b000c803401400f102d1420700b2070300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 516218300 1250 516217050 516217057
    0xa0312020106090533010807050d0902030303010303050702030d02060114040207031709010501060215060f06071a090303041106070f110a03020604030b010603050709060f0f1101050a050a0e0d23 85
    0x6000034180454642020f545d403580c00c210318018072a081e006440300f0f4840c080c503a28103402d101030b1917100c91911075660980342a0049041d10180c1515001c00e0401a03d0620143d0700035271003500d400780c44016038410103041003400310400d0215031042c4010803003441020310300781280d002940c005030340d0740481c18212041e140160355261034070000400c2c080c88000541c01207040700c0c3c3c80d031b00740c4601006c007050f40b2400080a0302d00030ba21080d000022070261920600800e502c6100e0b0401019402001c1c0640302e000500702e4401d600360b00301004010501050084640402034101c94541c17508125681e980c481041d4201c1c003425125034008c3c0306240f5202c004030607029540080205403229034916214008030024020301000a00340b0f00490348803070003030031a502660758035155285003c44106045030320420910aa004201d00d0b88904103000c002840343ca40689124440840e80d85840301e207042c1910300c04107520030140d00c020070030120240d015840e80200324000c4401c00f046004210000307810300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 516219550 1250 516218300 516218309
    0xd060b03061e09010b01091a190e01090905190e2103090c0a060210020310030f050c040605121e030c01020301080f0c031204060513030804090605090c0403020a0312020106 75
    0x104403414032081e024141c40c40300e00e240040c800740d02e007582d40480c0030b0f00361511035242a0100d811080e06012400c100c02d054410300840e0202c0c2820310080c003d10314500d44481c1106000308009070f00e50601d03564804100030284c848000b090105080c000c40c01005101d00a203402040d42d580c40c1d02000b054810b000c4c40341132520b1300c144210740d40500c846104240d801554151641d1041213803000460402c41031410481e45d5980242031003001c042d901c08040c1d0300c02030031615240b80b004008000661211850a5001d002c0c1008011141d900c03401d2100319102d9811051090958054603850040b000840f18590201c6404001c0d00c8d40c00540c409285000307021013035040e5400440089a010300000f0540c2070b800080b03040355154800c94060685841a252828001900401040c414540500024400380e0194a65030512607683e846420750ba07002034100c108640d03281e8604009501c0c181c0001030300b200e654601c0e2840c080ca164006070900307801e484018407140e41c0c8280003078000c0c001e62180b0b0003030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 516220800 1250 516219550 516219553
    0xc0201111213080d170403030b06210f060f01030b031009081c14012615310308040f0b010b03010509090d020d050306032803030b01020307110d060b03 66
    0xc1403801d1140d096810282e040c048203500c0c8040000e008400142400b142c4030682ca4070030248440420f50000003500600070703000e15468800706041911198010020703129000000c0000000c0c001c0d0131500c80c1c401503c2e0a000c1c4000606001c00c955650300c1010201d0404d0800040041c001e901090814844401c4c00301010315043c5101c06010303010004240015507802c10141ca85900c0f0400720843d25000280446106640014041d00204c251001c0c1481e0000d0810800310841c91a040d19101c1328003000c03440310885a003030104e403e542d0765102c0c07047c0078006c01c0d8a18135144500c025446400240b406400c00000001160500402200480400d034000d08482619a1209849a43c650003881804c2c012036110300000c032040d002041100c9030000960250448030b403905012a060f810182007070b50315002d00c200d4a855100c0c0c50f8600c0490945d1491203181142d541d08014044032074011030b040c1950000c1159000245021400000000c2c08441c070740382036540d5040c8800100300004003150103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 516222050 1250 516220800 516220813
    0x23060a050a060503010609021e040e15010c0605040c0e01060c0f320a0b0a05040807020f12010204030501050603070803040609090203040501060b2101151d0609090112060623010c020111 81
    0xc54060740080075090003a105000050109c3d254421943c46188114610394140d0f40104508041c00c101c1d08070f81c0c040514161819104a448202c102c90b401d031001c4a40000c06e5400308511030a100c0203030300500150524107440701e01c54483c40710301e40039404020406030700d802c550500c80050303055012007040320751803004105a08421440c1e80b20220482991071035503140014203451041d000e00c0d0301c91580240704500380b0724a9401d22080326040c441e00c5900c0405000c280d41800024806080150301420000ca01810704000345410300b0411340004a0b55041004148095500081d904d0200e4480c4032b0010703500d603200e0800c50300506280e08000034100c0006070040c610201d0b0400c600340d034000e0740c903000140c0e41c0e03d111404016101205410119407030400c0c44500c000c0c03901800e10103d10150400340382c01c812030300043c02d0380c1098010a02009921205009000180c0700c0c1002826071500a00503008009022a61595451840b503040292a040404c11a44203800304100441800c0c102c0c0da8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 516223300 1250 516222050 516222059
    0x405070b1606060503190201030903030f020c07030c140d02010804031e08071209030806220609061703040302150c15180d0203040302061213080409020723060a050a0605030106 77
    0x340101c402000c0d0341640c14504041000d20780400d00c10a94503100d01e07940700424403030340150302030600e08100f40c0c140359a69a044460608a000a15040c01f82d10082c1032003d09601c3c0018041c6400d4014141c03440927407138180503680340c560001c0d034050b4090800000c55a620f20b0220348100c502d4640001d00d65192003070b00c1c1c2003608401c907240605616210700f00e04800162010045440b4500003500090100b4082140e0f41461882c85a1604030f1550b481c0403110b8210000d010348400d58002400103a46020401040c0846458101b0640800000d1441c0c54034540018242075060703001c03004903070400140000c1114040041d22008031502c0000034036031500c2c000c419140e07083c4050000f014002c200c5000700b450302c044221400d981c1c0c001d002d81d0900e42410b5101070b5402000740240b8040941000b0031000c5003451001c2c0c0000d2114440c05070f0b68400b42c1c9446081c481c211003240b601e15910342a800456000032500a43c05025030000080c165603040d41480500402d500071034055280620104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 516224550 1250 516223300 516223327
    0xb041b1a030a050c090108010b09210f120c0601140609100309110d080d05040609020607061e060b0a08060303190c200109120503190309060c03050615030405070b 71
    0x5108941d02481000250b503118840b031110b01c20741031702900080e4900014003074500c8000142200240160520070707003105107080e243c0303007441060590007a5032081c400f11621690404c81c1440c03420702c005da001e0410b800681940c0d0f40301018042c00d0841c088600c5105000e44402d420303a0300d00c0400504410f490b07044000c0143c002d1000010039074007000c000c019080f8600740911480c41c0d0b943d004001c6031800c442071402c40d0041034094000c40d1550f444601c8080580c0d1507001030150345024090008001c1185160802c00d07451484003911200d0030801e00f02b00b2041c8020507100001e00138144640c4aa80b034030b000038110b102e007901c028440444c5a8aa02ca81c03540a03045500701449002c0754582d03124803000080349440b02400050008072a0079041c82500415018001d50900c0f4008680c2842c00c101e1242030590756a010b44d80000340d80e803410310103000c0b40b400303030481c100382c14102000f82d0309180000c203401e840c450195041520001022400700b102c10050000101101013000f9141c0a2010040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 516225800 1250 516224550 516224557
    0x418020927161d0913050a0302060906100302090f0613020a0f020f0102040503250b03010e061306050616020604030803070203090a14010206131a0c04170a0b041b1a 72
    0x4500100400c20301d02c0c501c900520008103180071000d04140045050f5040051201000b8000c614455042d01004000f500820001900c5480780d00900064a000d049007898030400818440e00603108001c01c1025071140341c0e1007a000409040301d61100d80d039210100d200d542030b0214a4002c2880001c0750040c5940c0010300035041c2c0c1280d400c2c1e40301d00c806904664241d005e180903855250700b0018180301c60190803042d00b024104107003001074420b40da03100d00d003140d07030001da02c40006140c0c450b003007244c5490000d100135022080d12000b041028100404124607010300c480d600c6d80b03880d1a070240000e5680d460151001140e102c0384080d03980c503042e04020740301c0d048581000d001c1c0f104020041000301010851811090042e401003120b9039072030703040c030745035050060060320040c4890803002540040c07900041d12030704c03494040b680d44034900060305480150010f0102200d81040d0111400102c0012074240c005030021289405d51059800c4035081c000300354007900f18541143c89441a85000070041d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 516227050 1250 516225800 516225811
    0x6071e0e0607151a090103080d0b190e15010c05060c0d0b040203040c050406081f181a01080d051206270103030305091209010f11120a0302031603020418020927 70
    0x504ea400c41e00c2c0c1c05200b4034403000e0100426070710090140d000a1841d40d84114041c003002031a00b84269500310000c03841039000d40084107e52082803c00042240c41050032130440d00c01e183c01c07034505c0b0464903a82c1c3c03110405400000e0305103001901c080061841d400000e80504010411952401d09242409024110384100c43c0202d003482c40004a04d40c02091208102003500005150801d034100203200421000e040b0307107031109000946c00d010600e140313160704403100303804010482035041112803071902002c050420704101080001c07443c2c0c0e5003003e42c45074000000350f4106801384c0c0e0b0b03040c100ea00c00703080f0308002d102c5446050001051580c503812560081c540d20040d01c01c000c020040500d8144560075039540450b00c600d4170750210512555400c402c50401005481d00c0901036400901c80303601c00c80d950000690080144901d221a40c0c00151740c0e1411810110b1034246007413440f489034000340510300700e160360200c2d840b20a51100d0505100c007070906140d103045076102d0b207a484410402500c5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 516228300 1250 516227050 516227081
    0x301050901060b0d0b0109030f05030304140303070c02010e03030705011529031f09110d0501050301053303070b071208074b0206071e0e060715 63
    0x8a03500c81818411035098800f6103600a150060100101000c0c142c45000b00341005042ca000101152090f2203d840443c8200083c1d07640c0c1c103241c2403050b1148284401443c03980c0003082031082c207541024112080c27a0782802c1450101c00d40c103000a095011b1054094481d5003041e0b281d0002e40b0b0407003a55020b40e004061100400704400075004041448aa05c0c0034180400300041461a041d240c003914071a80e820240003501910703a44004142d034052300308800001c4002c581205160824051a400340c0000d80003002549401030402450110705001c01104800c480c4035080e0700a04541c1c14088080003a04589a140c1e491725020103943c010a400c1d140c0060082c104220903214141e42805850f1551b5840050441c800f943c4d00e4840702060001544083c103c0c01c0f4412a440490030703006008103082c0c51001c4440e083d00a802c0c000c004101c1c20401041c1d070484407103420300f1041015202c100749401440c5da1405004030b003a40c0305032074015242280011951041a440f83c2119103003020059 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 516229550 1250 516228300 516228311
    0x13060206040212030a0905060d020d0e07060905030615120a0c031104050a021e09030c0d08040801060b041211040b120a030f02030a02030906090402040b39060a090c091a0301 76
    0x1060f071512805600c224030006013050a00300804c1c90100080e05c3d0050382c40c2c038018540703040740030140c8c00c0b56007004225415170403c5004000483c1c00c10300400041000350040d041910b851117400c0d5403e45084910380c403030b00b000000c41043d41c1c000c1014442d1244d02142d2152056141e0429007612a0720361940b40c483c40c10240058140081402a2815402050101000a42c2c8030010071556081344003400e0701845214045012692643d040c4004540103e070342c55038941c20401c0060170340700f00d5082004403500c2008100443c500d90700c49102074070340201100031144003110003d0050315498025580c0f2280c205694520750201086290460740701303440c7d0b200e0600d540507050361680034134218180560000d021480950a00c03000401001c280104018501511051356151541145625100c0c0008243c41c5008800700c0380c00c1c0c20804c603050010000c002130301d48512550303614020503504506031603480c0041009aa10041c0000e4500043c003800030682d145070a4440802c0c80955074442c0d800e01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 516230800 1250 516229550 516229579
    0x60b0c0f060a0c2f030d06140108040f0624060e1f0e09150307062c150a0201060801020a2d0c080c0705100504050103050609220206130602060402 64
    0x14464203440c0e010f16200c1043e406118500700e0703d0b090f00e814149081c80b0744000c0e030443d5200140700816000b03602d0803000450909111018409100340b100366814800030800740030100d1180c9d01000d6001d41c1c00100411031034445604044680c04444c44804c400000100101e002500040281c024110a84404500c1003038100400c2f0f000c8007400040c0301050200e064150f031401c00e207500c1580b200301760584544421492000c280703429880d900c00000507191b0300364031050010102034505c010216588081440400400103140340c186100d5508841500094103170344c1d58000c1d0060f400802c010300c0215142c00c980640039041c2140c1a0004500b00b0b00030300e0707580c0340c05040d0501c0400003c4a5490240b0800d1540e81c8415507030080d80c1c150154802e4a82c00030391581c0e151218814800b041e510079880e40d1a060000d03040d80c5000e401c41c3e1203412804100203507802c800f250742c26440140c02e404c0303c103190b080c004240c0070312440751016501c40c505040410341c240c00007150380c003462090b01e8001c2d680302c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 516232050 1250 516230800 516230821
    0x6030507230306040221040b040212150a02210a061406030108062a0f041403030304050c130603020d050105071103160209060a08030d0b1906050715060b0c0f06 70
    0xc08012a1070a030520124809052070780c003030800003039544040710b41d0350000420b0000806080368104e801019140401c421400c0500d03480f00001c90100051441d004001040900d000c030042440703010a501040140c680c000980584038201849036071003925091003050700010342002c1c020203600320303070040306800103040c050201c034121600701c0c0151107a5100d50038906103ca140702d50440341882c1d4025409070070340e211170040122589860846540300d2601710502070700e05c054a0032a1081d0030900030807012410100b2a60f2503488102d6810104100c80207810001f4005078001039000580c10010030200141540014000d001e03541b01c28440301c82d07065500c0e03564800c10144601040e030043e1ba801c010f007803880d1120f400c480001c100720100364540c005a891a0851500c0300e11580d19980f400c1054104003008883d07004141044105090a0000151980c410000010061101c20b962071200c0d600f40d9001e4000b03031803006484e81d5651034140d80c050740c1e080c6d038a400d01d003070740030b0341e0085036000c80d5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 516233300 1250 516232050 516232097
    0x30405030604080304060b18041b03080304060e1606020114010504090305070f150507020102090a06140703140403140715030902090c0d0b060c0a110a0e010b07030909050106030507 79
    0x8010010034540c0d440f41d03203540e11034001a004075021911000819000e54859054113000c140d034000c41c000502e0203082410020030300395a8000c0400801400740302251101d0201e0f5070040e0001350101d40d103100b1901061a0840c0e0b66190400107508a0340421050741c1034024172200d9644000010b003903626407082100725554041c000300801e03410442c450000341c540c030858612a008009422000c42d10001c0c071416034108440000c0147d5000403500f207035142208a070000707400c4c03603d860819020348900407071243c4111180901032102c0e180d2800045050f001c01c58000c0c6501040d07808111061004082d0303034215074010f049400030350b8900300d44118400e00c41e000401d50002c2102040b501d5480e6541410380c40400c1c881c41c26511541c00d014070740c0b84c8100500c024000080148400380e058200220f00100916a17070f4031542c00580308002d8000c00c028030a066410500106030364400c18501640d21030aa50701901810341007600020305503405500c101c0c4211100d44954541c03100f1601d89207060038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 516234550 1250 516233300 516233309
    0x9080706052205100f03021309060e1501050a120b151b0a110d0204150b03010602011a030d0f02150403030209010305060d023304140102120a02120721110c030304 71
    0x281444d0b41507400d442204240c000a18034100141341802c4111442c9080002d40c0050b48401e0f290f850030440310725842111a8021100c90300195641901c000080c19031281031040420011010b8000380c0c1400950702281d0002401001841d05442120403500c00d5005140b0880c0c0e02c420907035003a260400c3c049071031145543d20180501b003c0c02c3c00307400c101020200340d000740d8200350340e000c00315040115118050060540241c400383c03207614020000342580d0407412380480241035030b032603002691000242c0d50710310762440c01c040c0100c2c042540f00300d1501900b003000c40c0c41d502103042170000b03050b095401841c848200381c1c1c007072085aa45000303108030307040e0440b402034101541c02c810440e40200c44140041c0300d05000c2d00344040d00c04811441c1d58035001500961003d5a00e06c4c0340244668042003440c000a00204620b4142048100c0103912201300c40d52020f02c5c1c04000540904000c06120300c41e00284680d41c0314508a402205e0050603a0a800300000c1244100c0404944601d40002600c0444 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 516235800 1250 516234550 516234559
    0x7030b2707050d0804080a050c040f020a091809050604120806060702010f12150315150e1303020102090619231803030d02030403020a030324050f0109080706052205 72
    0x1e49000d040c44050701d40440300340d0300b41100f80030100f0462018041c0d10011405180244000203440042004483d000200412400e01c10480c035012240c200441f0b80840c3c2d80f0607580e00c0c0d070b0f500036a1a034002e400b50080007091400784000300030130420206801000b2605565540c8000d640e10014020303284075803840070b408240c641050544640c4100c90a1183c003c1462020803040e01c108802c0500d4030440c6c00480d2030f10341030030200c840c41016106031030f1b140c4802012403511034a00518060406005020018000c6407004044207041c000d4045400e20580900341c1d81c0c0e07510314040c20b90542c0003030040000000300c0450001c000741d0700904451568080f0402940e01e000f40e1545039941d1203103060031158150005001040d0b08101910243d0302c1240250041d01c0c09180500d4010121400d5182c081e000025103c034040c494011510031100392102912203204a070f00e4100180c841600d644c0c0004081d00c5510408a01039070302102800504800c40c0760081a4031001c40b950f214946103000f1140c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 516237050 1250 516235800 516235813
    0x308191107061a0a090e0c0f061b16090e010b0d0206031513020408151b04060e040e071403010b0402090f0907110106061806030b090105190807030b27 66
    0x21454a81c85001c3c00c40c81c611112543c82400408280c42458035031001500030385e903155803112003e09100c07200064a080700d80c4289006140001242c5004400c40c0c0c5151500d59100300302c84407410404280c00c00024032002c1c54482c1e40c1c05501000d001c031340315028032550070b0081181e4141429a05100080e900070507890441da282c40704c1c003c80141800086900100b0420400280c0c1d03000c4c4010400b400b500310290200360100705031090400c10103040d284030400e03886014044440103d0a49007a51020324041c03d56039038a9000501400d06250300d4102c40c020050001030b8080d920702c05841c03106045e80244400200c030004c1004038000c1340b9203243c2080c00109102004d18003e1011382e401007417800c228142c1d42c0412551030840350580c1002c0007083d004010004d542d03501a0071180141040d245c140451000480494140c001c10b100d01405550000f00c4440d80303440009a000290009004036841d065403402c04146144003528503400747d44020503d1070301c2d2900b9a00f13669050192600500d003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 516238300 1250 516237050 516237053
    0x1b0b0406110706020d0c110708061f08031204020406090e03040b070204110a0804020f0405011412071205071703030402150f0702040c020c030f03090d030c140304030308191107 77
    0x24058440000003000c80400c00c40000880c51310103403a6002e0061000100c440100380041c0c889128482e40100c16840381d2810098664005141c99110b41488030b0107422406e00809004034040715040030b51103001c0401c0200d0603c001d000106e1059000b00c8080c400c0950300c02c5800200c62404030300c08038507001000180300e02c1c04510000c1600742d201030320001d5510540d01e0054156040040d410000444010600040d480d2402840350460000c50f41000a940743c4105040e8507000007482e24095104040305c17540642081c407680b0014034800060b51103401e95840d04070380b204501e00540b41c0c50080320340c420100841c00010350303128503400751861100c03e240759030780344582d00045950080488100a100c0040e1113601030a00b50780020703002084030442080403d8100101070701180300991040c0001d136103d5031125681c2000c2905410a0505050581071407074240c030ba103500d044905c0c800024004101a481040c040c858203440000c80328031100400490162000048010007070f08007482000b0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 516239550 1250 516238300 516238313
    0x1517060d030c1505090607030e03090603040b07140a120612050c090c0d060b0405040b01230d0908041203140307090302150c1219030b0310050727061b0b04 68
    0x1140d040c020340c3c0c03074000f001d096151002951403c0300c2c81d403c01d4103d0030a00a2803500341c041c46802e00b400e070000d1402c1c410958082005400000c1c409000e142845001c928150f025454484220203c01205542d420000001030045182030a185030510724200c000a08941b08944c81c140803503100000d001d9540c414807c11603001005001180041403c11940740d41603100c0c441c030002440c107100070f070b5240c502d080100b00c111600d0b02c525a0600903241d81500710544082c110f0044885040040c5441c1c40d0a0809040140f9030417200404100c1300040209000c4c05070300e07600384c2c018480d540305200c1c11204541e941090005480d81d10214481c01004d0006260141c0c100010b18a043c00e10307400c110020640a1800d004a0940b0628400000c0e85600c0d580c81095041d6034804242424000e41c014030000c66926200c640c00c5204071a40e4501241c0340724400c041104c510b9400c40070120320400041010032168103944900310110341d80290940082d030b90300c005510300903002500b0710f49903038443d100c0300c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 516240800 1250 516239550 516239567
    0x309120304080d240f05040605120a08030c070f1406070f0801051e060d0b0915060906030c040e010305030c0d08060f1e040603140601060905030d030f060f1517060d03 73
    0x100401e191000001c13803621103042d01680103100050005804e02d252009200480306a0b40180f4020903100c0c0018413094400644007079125072108460307617660307544101190789009010000b17007001e00301003000003841503240142300e00341c40c01e1043d10f400351140c40c82594019111400307c800319411740010041841c2c140e446801c00001100c0110406019100180c0c40d60301c1100d9000e0b02a94030a010714027810143e6246500150111840c28401281e1000905600510300901c3c49004000005440c0f01404002d90300108a20b040d99160b82d6140d02e00507450303070803c1c0d40c000c0b400d1180d41000c0700700a10480d07185001e0203000c1c0c0f60720f07001c01c502c0e410b0003444d00100240687c802d400c11120861600c41e1700c03400008501901c0c494101c403a5560303003c0e0501030181d00c201c0030418501d406100b9030703501094404560b9031300c2c200081c0f0b4040025122001c4d081a41c45407250700403c4c0ca001030300300c0c400f810307484c28242a5030fa91851564011149960030209a0742c00790820406002032001034054041d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 516242050 1250 516240800 516240821
    0x706030e0a080f1e0c032208030304080415090501211d0a030e030a08160606180b010206090a170a030b06070c210f060c0e0409080309120304080d 64
    0x3503a0701070744140c039078030b1007035200c4012440c0d28800010014a440c01a4421000f40342640012900e03100145d0b179600c1e568050501c614074002110507903140300e0705410392003074000e00100301965140d29060400b07040b590018480c50a0b1010b9451044800b40c2c414580c00066841c140c40352801d403180c0183c4581400f101c4840c85c50016510301898511b2084c00f01025114031055000f400705980c140390041025100d07035040d9002c0e0b40802401e00001d201d01c130917180c40041e455440c0c80304c1c416a0130f0101c00341c03400d07611404d149050081c07039070301003210703504034030803400080c2c08407089915400030440e5184040440903145c1030b810401c0c2c0c0070b031060b24001000c400510703142c04034000d214580092401d074840c00c070884511216842c20080402c283d41c0924228020104000d41c1d40030640713503d6012001c001000b4440c0340d6a2425108403401898151f43c0b8401c05442044009040c1c41c203407415078000e03130354007a0500c140320f0700020b000000d0303088078411070740110010b0805000740e06010240c80c10559 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 516243300 1250 516242050 516242053
    0xa05012a030501051c1b140112150b07050703060c0201090b2415040e3c13030504091a0306060609061c06080a05060103061523040b1504030b06010c0201020706030e 72
    0x107000d082c0e2890500f44101030800b0941030034204d05087c00141510140d040c1c9030000704c0c03c0841c07040c4201d481d0151501124000b03504942c3d111a5480d1050611519420060149281c00b40295546e541517010741d4a46105180c2c111040c1c07140e0200600c4640c48081d178a034140082d610001c501d041c81c40d88072003002070340d0400b2400d050301c0b6a054000300500310b541c00f005280030110011400f0103000804901c5825a046040e2041c03240e00448034500b00405240f01a420511280b00f0988148115801004540300c00c0110080c1001e05000ba0240003143c2841ba101d0b0b1310101e8024600300040340c400d031400070b110501c0c22000e064036294002c0b0301c08681000544e52580090100b030144420802e140c800d0024003c60360541c5400c00485600001c1e090704101d6a2400f40007200002c58103603038283c3c0700880c10f0007c1402900041c082d0590380e0301c5031341000d0f0841c403a150301100d00d0301900c2581e114020102c1560744401c01186c900f1410320020740141e000c80c0003041100d0190f0f101e03a00200301c510 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 516244550 1250 516243300 516243323
    0x10203011a2d0c0703061e0605011b030504180b030705101b050a120c03030f06060906030207300905040902090118060909030903110111030307110a05012a030501051c 73
    0x2511810882e485d48241e500d9600c03102c030308032030000440c8031030719042c00c0c1c02d81004030302d0030b040c0000e2144035030344a91950040007082d0b8405042c060005c1d100107202c0341d4261221a0803080380c0c1030260604206080c001d100b20000441d00d8904583e00d800d54105c1755444084c11002c51014011041c00380d58180c0c0c07140524003080012644101890400100a45400303060f916145402011114041031842055190040c1070000c164001b85e0442124910700d405a00c1d03e4007410400d000b01d007514640680100d4114109007a030500b102440042d03901520b44031a6a0390700c0051005445400d00300035401203000006100900b07141c0300313900014090440005129884191450413626106810f50120700c13010b800b081041824a01c1e181c0c1c600d42071a00d045035040c0403120325903034080035200704140f06841d44200c00b0031008008240c003003038102c402031040030f80300c0c0d060303200311000d21248030390161010218201240c0240202e40c100c032000b503c9804206041c120b005222201c02ca000c64030f084840 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 516245800 1250 516244550 516244567
    0x220201090512030304150b03030304060b13050906090d0212030103080a091203051206011b030e01180e0901050919060209060921010e0a030c0f03020c1002010203011a2d 74
    0x4030761040b11002108019a030320309050920500249981c1400440242040c624050a072004000c0e650450390200c80828820303948000104001d0031001c00107100c6180c0000c0145003c2c000031100e008103044000d90f80483c210701812030701d9512110802100c11003c000400000300d030407008101d00640381c90060034444e2640c141e0714144c145280160001880410140f0440c0a11010642c0007882400e128014900d1a03105015501d0152405401d0007007203046a000d03a400754100c55408545040c1010180791140341e0594220380998010040390320340030024030148400145041e5007802c00394088080700b640c0da9000b0103940b012403041c1d04460288220007144e15054142031245074030102c0320001c41030080300c05085a000040151081d4844000706e804281c0005074660307402d820000c0030201500c43e0600743e180510f101c4066401c0790050990310318065041d8040c41c16140440d54041c1d40381000401218180107400910740c02142d08910031104661083c0e0340d0b0300d030354400e0f15901d0402048 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 516247050 1250 516245800 516245809
    0x80318070612060e010305100b030102040b0a08090d020a0807080a021504030e0f0f010e090a0902100c050c03030316080711120d0501120503091210090c0312082202010905 75
    0x81c0e2001010031480c4450064140550050402501000388440c044d50b1540e2900c542d11710284030b2840080340c2c2c0e0420b000c0192000c0d011a0041d00244284680c3c030400c444001f06400e1040784c4401c250701400341c8069465101052039a01c1c15000385510f03003404200c0d1a904e0203503202c0711914055124443c0c0c1401562500310640344180c0c081c1d15000300317669040c024007521071100111548283c001c9101040359070380140203440c8281090f01e0044007035a40038600c600600001c000654040c2005208510b800d1388900000c0c2e005104400f514500c0c440c80e07040c0b6540c2d0106548a110a50902565140151003a6103450f0300190528018404000b00326201d802c001d400307078410804080000e00e0f442e1202190240e1801841e000018070080c0720541c484d251240600307207005104000001d82c094801e401049440c0f49001d81d4041009452003e142c05044240c0701d200c100c41c05400c01c180006041c0c041d110842c0f280308141000201d400b0700c12155118085908001c81c1404401d04010803076854 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 516248300 1250 516247050 516247063
    0x3040806100303020640050a111201020a051213020a080f072c06220f0b0d020306061c0602031501081807030305161b030210030e0703080318 62
    0x35541d031020781c00c0d056040003800c100d0002c1001c198541c2c00851b803604111405070488188054030000048201244844002071035000c0c400380061040000810074070103c01003510076944100d4034a4513024071007107001e00344d014265501c4003056040c002c68104418030100c042e480075030f94110150040c01c40d0300040301d000d134903080340d00c030742e40250741944192200f049900c028114a002424081100c6848843c200f003a00758003800240c40ba0b0013103201038941c1500c14042d240c030000c030a9030104500d8042d600409149117080700381d60500900f400103042c512003a910031600500908800d0f9218000e020800744c1d900020380c0c48540b0100d002c8040f0344988081c42c003440d225001c0c2c0d280c0c2d491240c001086104040c0025050000980c4511801c0304001013160031280d1505003a501e5a100050400c3c9200a034a409849000b849945040f594102c601d0308003903038800c4440001043e41c000c1c044086448940e00301c1d03020342c0680d9040c40425040d1018690101e181e07420000b0240e0300030600c41c103105 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 516249550 1250 516248300 516248311
    0xf0a0e06130b1e0a091b0801021c020a320706060503010608061014130204290306031f1104060801140301110409050a0902030601121401150b0c03040806 67
    0x211140844000c00000b400e0340750300a00c140004400d901c4030440d02d035406070f1010708000001940c543c0c1078010810500b0140d1b02007030b00400320b603800c1692600c00c030b0701070350008a04010b00711500c02d540d58a61035610030380700e5020700c5558201c485003030110701200d5a9408903085400e610281c1c40407401c080100010030806201e0880490804d1800c820b0600355102a04105030316040442003011058900110104035142080000c88200342d8901247c0314055601c0c50f10700040c000200410b1071080e9924808698410303c4583c00d641d16404400946804280e80c5240d2540180d01900300e5404044007131917010940c001c000510b82101c001c0f9114035803099001c0e001180d0480010844034420040003100709000382d000f404410401d0b459880903100e0381c0185a50f040d51200818602e102c1c0768894843c06038050300721021540c480312011004034000804682c0a06030a42c0c00240722018014210515210480a80590705044864030715801121121485200c1800001540402000700302d0189 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 516250800 1250 516249550 516249571
    0x1617071a090112140a0b0a05030601082805030f1c0e1f11071a070804081204050c030d030e010606051c0b0607050105010905041101050a020601060503070306030b09070f1d0f0a0e06 79
    0x405c001340507803c021f40d4046446600048010008044041413401c00205500c041a09195885444031034901110714042d00e1f40c80042450b00e010080b00c0c00520b4000c210001b90204108201081400e40f0458021560240c0002d2000c0c5005085022220b111003080200490304101c40f41102c0400e405c0003030180c070803400324481605201d290000c90f44d007200c00e07031814491030300d440e03280c0c1d62540c490001340440e590038450009040c1300c0c0038400f081c00f40c44003c06550580e02001d41c0200a016640c5800d9072b19440c2010014809008400301c802030f4000030035502202c40c201074500c00801c00117000c16000a420406500020002e1081d03d002e4140900300059605040c280a00723502060880ca505000d030130040d5100c6203400040361411105075144c825929560b5980c1103001e81a1075000034404245001400300580011901c041030b141c08441c003800c000d64600c0729461105480070381d190100c13076030300104580001c0038100950000801d2808a2a0400c00384c2070b61400d2000c60f85150075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 516252050 1250 516250800 516250811
    0x21070621180606060504061d0f040c0f02070b0901080408090f060703022413020906060c010903031b17070f05040e0a0c0e1906111617071a090112140a 66
    0x104102c0d84101005080c00b458458101420000041d009400c50164500071404000403900d050791030b03a061080c600e001074400e10003150341c5100035141c4510320a40b03d015004480010446098003c00e0300d80c1d4a40507590180140c840b07840f000660340c0002441074001c00c40c6050b0005540715013009040c0350b8426030040c090915140500c0c44411500000b0580084c9000144a10044019450700c140c5404491244070fa498220000e90180305030740e041c3c1820750800c0c001c1410701d9050f9020b43d80c4820200d2481c1c03141807a05408642040201c25100358480d0214042a0b00c0c51040d4418000580c0b20b0500524058840030b0000c00c1400841c0c00b11a00e60f00d440240a5803503000e1604015a202943c80d0841d481c20504c0440c08060140550020050500c002c80d0064404101e008585c00300c4803003c0c0c80140c0c4035550710380c44460481c441c1c4040d2141710702c00107940ca10300c90a4000003485451107410200e403400110f03174810740110741c80e0703260b03444080000010100c3d400c60390090301e000400059 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 516253300 1250 516252050 516252053
    0x306010e040207050c061909090c0e040e160914010902030603061b040504020301090c18051f03020d110a1d0f1003020c010e0d0f020c0618060403050312062107062118 73
    0xe940c450f41c2081450a04004a2b000f2003038000c040c10707030f4170041110b01248141500e01402e141500940b0280000c040c190000200316885d54801015003030340d0105040103a8817050310f10103921065541c140c15a01000010f45030302071913451031a40008000b8442d1500c1d039140001000c2c0e030401c0c0c1110540950b100c284c00b04054005800e00590104030040c1c4200514181c002000888400041d140f0640100444d02000e8400da045410745840c0b0103007041901011561050b0940200400d000441c8060148040205001d40100d20a43c0028544501034000c10103000c00e4041c200c042c6402d042d004d102003000d0110a02030540c915400300c004220240e85108001d0451640c260f2100079034012820515007034540d041102c21890000c09414044c00c0380c0404600d00c1d00c83c40d840a406404046003688d8000030310307042c103405400c08680d680219050203440d9120100c0009201c0c1f0386070700c40c0c0401c000030b90007100c3d05e09200030401485407601c0380a102c0380c01075900c0402401b08071503c6042140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 516254550 1250 516253300 516253307
    0x50901050f16090e060103180b010e07080c040605090105070510090b241c0c060806040f05010501020c100207080f03030402180921071a0a110306010e040207050c0619 73
    0xa0b071190302d9038805102200695006014000c0600801361360803012400241346034082c1c1c00281b08028640009828a804d82c24045a42802030041e41c200e038040602189c0303400d105c0c0003010b014040c108032a500d0f007880c0000c01d0318194445010141404400d22240c0007148041c0503144240940b00b40102c0d400d422843c1c0303000f071400700030100e030007022440c6901c0042840c5800c0c204903108003a1031801072440400919001e05007111402400c1e800039442c003281c2180c0c000c6620380200c409440c14002e615600000f04140e500074000da50051b80320000044080c502030041c000d8a910500540f00406d0b00c9288040c00d01c05040e803405015800041400f0441c1480c00500c1e01c0440c02c0036114455090400e0516110f40c103070301c4c06c103c4038080307070306022150316409040b14032490b0b00001c1c0c08403440110700c1020f108031084401f0008030340741540704081c040505040740e204800c169200c043c10a210800c02001b50072000c010740e520700c80d07022111803d80310030009100102c840c4150740364009152030300a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 516255800 1250 516254550 516254581
    0x203060703020c0d03090f0807080c010b03010c0f030c032009090907030c060c0321050603100912031e0f0902091b030a0c1b0602042c01030b06030304030605090105 72
    0xc10401d441085551140c60010442252110003443d0100f041e5001d8101985611036911000d091008000348003003c00c03001100600d0380060101c002c0c41901000b00806088a403a0110f0b4004611900c000c1c1d40242c0c46580003001403081c90400080d408a40f000340903010041e524240400d120004000a945c41c164a640368030041000c01400b103a070659885901603659842040c050151001c0ca4004050061559a150380c002c1007030300f10680010030400d005400e059070a80d009024440a80c626000940202c6013030b1500408429040280010110000c0a5401c0d0407691502104038080300d04003680103402101100d580b02103800d0a00313004000368460040c0541c0f80c640c081c0441c041c081c21001d0242d036031108440300d000840ea15100000c2d10072654040800103984035000610080250a6004e0320540e5a031100c2d540510750070805200c02400c890403050b041c6003292004200152010503034940c0640c0c050b003541d0401c0c2d0380741d40d150142c8100b0782e9a00c01a94603102006003103045035110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 516257050 1250 516255800 516255811
    0xe0a0f1a01021b0a06050f0c01150608060402030f0705090103140f0a06080307031202130e070f02010f0b060306150c1002031603090209150406170a060b101e140c0a020306 75
    0xb900c0380c1c00100d00041844445105003406e0040100f13030000d4803817010041e140d40200c268020311070340d55031b00c0c3e001c803840c510b90064801142040c0003103400e03402c1a1098910030300322406c0c044a181c4445000307442a0300003009a40c10107898080302d56254a1480b8031600500840d840035401d41041e0103010706541c03860300022925401402040007203a407044500401185030500140d541c0012041683ca039803840d04043e0030101e024080c0f000c030591007490721a0070390540c0c1c000c07c020315801900300b0030f841c10b200c40c0551100c814404507009107449c044c181d40849081160ba440e20307601c1000642480c1900342245050342d0b0100811208100088102c2001d140a02d42080542c0b0389a000a20300d010240c0b191183c00300c9a11550800d480d10b5001300b0180c680d000c0d144041103480303000959202140c1d035045422504140d00004da5040c800c2c00c0100301c0000b03485e8001c0300f0580e4240088a0180609a2010040148200d204c148444002012082c030f051018086900380b03401403506d4020b02030003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 516258300 1250 516257050 516257083
    0x140f0702030f042903130506150f060c0703051504050d02010501050603040308040203010f0e0109020f0a0f0b0a0311210906041e0507090c050c070e010806010e0a0f1a0102 75
    0x2c1100000700c5508560035658104a440100c038804815901d4020320916030b0807589100005104101c409900d6006050348034100300c91181c1e881141c070f20200c4200c180c40a0300035003219800e50701403406a005d8100040c0010488856030f50f00d031281882c2020490f02c17409802810010300092040c2440300300c201c800359000902c620752416001c16514800203201604100c4c041000c40e0440d2340a401c884411905081c042c0201203422210a00a20842e14100c0c42000c07545e080e500c20341800300012084514400c0011780d41ea00d04002034110364041ea07020010159941203010f04100514041e1002002002d00120410408058559a50000f4000f110950700840c10800002c035200c6600e241020780d4100c804c041001e601d042481c2640d950403005001d8101403d9890300c0c1d60110152091148400440e02d562755201020500d0150078090201144c114100601000300c20003140c80d084510040001000816445884200d410102194024081c6450701844070740c0d04010078451807000d40f9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 516259550 1250 516258300 516258307
    0x3090a0f03140106061b1109071d09060a05010309210801031202160501201002030a050708040b06010c021c051005060604061e500d1e140f070203 64
    0x7000038203c511121b110180d0345665803200c1042100c16448181a12000740a01c2564240a54040c01301b007014038000c403685228906030f07141c0d880d22078200c41c054031000d06109419400c2000440141c0540a0155034010604a40711a40c1400000c0441b05008942d500c1c0c00035411403500107094403c0c103440c1003c5510800600056920b948804411101c0900b0055100c0e00c0d802c8240034081d42822128032203005000100c11006400e40041d417080b03039600d0080029540703111058a15403810740d00034000400001c0003801d50350140c001094000d00050440410003540120b0020f1040316a801712001c1c1c008140303100d1000d003503001c0e07150040021a856800c1508100004003805040f40170b54296003052458018502c0c000c40d031020203003603201d001001c1100301c05d090070512915824100c400048180300c2280d40340301e03500718800300449581420724049042c0d0060015080405c1017010000d0818885c19000c0c1982c850404100d80d1032406800364544800300500390a00203041400395003041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 516260800 1250 516259550 516259559
    0x22103150d02150a020303091c0512040f020d080a030608061302040218090c070b1005060f0706140901090308090601060801060807020f16180b060406050c03090a0f03140106 76
    0x442403a103440040e5032204880a01c0c0c000160008481115036081c00070014800103030550100c0111700c2040c00c10b04846204a00c00c260412034040c4002c41d800040341401013113040f41e0300110203500180107001070b0201c40420340000b04040e0324808200c80900d40002e4000b8000e4150007884010304442c0d0241c569450503036640c180341c82803074600910491780040c0c3c8800c21100700d251056800c40140a07640c2618140030080541da201003016200e0618000000f20000118001841960000381c0998146211050f440f402e940201c4000c50301241c50f1816039110f0380d50f1141c12481110800c00100c3d08504504010f4030f85000a00708800d250059001800500d40002c2190b04440e07031450000310568599800320b00309545c0000c0c40328140140100902c50050744038520059031605583e0008418094900004544010301251b81100e810300c020854a8002d4014182c3d07002c000094a1401075240b0010306081010303004508005c0c40b0310740600620490f01c11140c80c0c0c002c07560003001a1801d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 516262050 1250 516260800 516260821
    0x906050609090c0d02010504030f03050a1101020f0d18120921120e120601030305131202030705041104030807081e03070c020d0305040b0a030606080703090308010b1e0703022103 78
    0x43e07644403800780c1e4010400f2411640300b40200c0e0003e507000010001050039502c2c000301a0b900c43e0003681c0000728000b10070a81c4400c103100f11070b0286182c0301d80519100200a200014200c00d62120200e90804400d000c041400e540340030700d424855a403811030040c180541d94030b00180410807107040302d00080700c80c0c0000300010000c401240860510800109444c4001401d1503500c41c59190309000780000001010f400002400e01e211040040003503258958280d44012581200041e50540c000700c001c0119041503070011300784005180100349440c4c0c40c2d442d4410150f000c1c10302229103510020b1403048009020601c0950b5221003000c0d5442c50030f0100c401003102d164080080d102d07450302c0c000034041502440840d0f0003446d245101940f90400d0010180c0102418404c04001c56c2a410028503601e20910594016903030584079045140d08103c1c1207603c540085094451007003840000c0807108002c1e8025040c00d81c803035401400f4800218024030b00c1c0480d280002c24030102c0034002d00100c20705 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 516263300 1250 516262050 516262063
    0xb040e15010b2b1b1b150e1603020307320604090504060b040e0d090308090303040b0403140c0f0a06030c02150703060503160608060910090f090605060909 68
    0x15070300c0c030503122002c404030398001e50030403c55080e1503880150444801c0d529604421403180340410354403190854003200395480e280000c01c0c044c54000300802d4800044010491a01c0c070040d01c0f4000941744000788105140102000c078074422044032581c100114a070401c04100507007040007480f41804400b407100088615071aa598401c50403071007400303013140c40b41c2c401d03940140010704083c8a241000d00341100104044440030b801181801d419807941300000034010342c2c80b10740c2d5440c06c000900c0c40d110000681c0240900c25410700080200140c6c061106000c0c2001e9809095645c50722480030188a240c0340681c0c014a000d40c40c04d04c1070021590f20309120340101c641600300441d041884510407820541c40c4601c5540010b219428403080650507400030301a54000d40c119120b80300741c8440c2028030311882c403d0308002000c1c4000250380f42441c3e10015080411621190132640d03c0c0c45d00001aaa051940c100583e650703050274000f130020a01078150800015181d0410500744141c0302610b560 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 516264550 1250 516263300 516263309
    0x602300306010f0c060501121e0222111308100608030a05070305070c030803060f0d020907180e0903190c0b0103060b214606020712030b040e1501 64
    0x41801d10070f0300d85000300a0310700e8207548030800304a90341c0c50b84208010306c2380a60003500e0f12414013100301104414038040016045c1c000300001501041001c0d50034030510b0444004000a0f04e40c100256500500c0010740959982421448102401d041000c0e140c074040d0707284130309850f09100e820080c48502000b2109664003501e0090303038501c0d0b181002c0e149440303a5807004208940e13130071000080c440700c1d501075030003408120340c2c9080d01d40c090001c0200941c20404003950241d81e44000c286401d001b9104542c00c2000724030000c01d00c507510600f00c100d100d405c40301d00005400020f4804010f450b07200c01551004100c1c1420050084a0344948145900c14000106200d9580c03020100d180e807681c242851000824001c0c0c2418201141da103621030b0703a9030703a0715041d41d00005451007034030110680c1c4402e01d0655140d1000c1c200510b000c0d4000700c0700030160680304107a080020310040b490400041102c010580c030042070700c81c591402d0004031101089440310304d070420700b042018550031200c00350440b03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 516265800 1250 516264550 516264557
    0xc1e01030207320c0618060304032003070302120705060f0a0b0604171009020d150207080406080411011e1404080a03080f0604020a0804030324060230030601 69
    0x940c1140f0707004150411490403011500c00b01c940500001c0b4401d1541c1e04249001400c0c0c41a401c0300d00140601c501655403201c40500c0c08240a50740e6040004c040d66005009140c40c9804080d00d01089400c01d080c003083d90b0076504005159030070700da01000049400c040e07079000145040d19545801d9243c51000c0c1000000d00d07448404602000615006545990320007009070390707100d42e02e1021140f40070404035001514050840d0f602c2c0f40440d2403060285454004d0010b900d40c0d02242d4881035144890904002100d80c203001500200741d000000d80050070181d140c409103800c10741000c0c04440a4040c400741001600001c511b00000c44000c00c1d8450000b5080c4098000441d25a0b0f544070b00503270704200c0c06481a0900d803024160700142d42405028040d9001d140f51712241c2c144030607403140c4104040450001c502080000703109a206004906a41c2000c400d1b040325012140f50a44040d480b0b1030040e0700001c180a034052078142411901c402000f03401460342c840d082a413401d800001d1055051 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 516267050 1250 516265800 516265807
    0x708160606080f031b010605060901110114010b040501020f0d092c07020105060909160303120b1305010504110c07050f03030c060109090c0e100506030a020f0f0c0c1e010302 76
    0x4101a030303008000907024041c00e4410803001d40360080c4e5260085140303918201001e800c2210707900010710a11090f1034001e04918070341402c003001514400c6121402c3c02c41c0350341c1c0e81e0f180d80501c0080c18509029003c441d07200c8d82d0743c03850b11000901e08803801c1034210281d0400e810324400c0c103400c901030310304440c1e981d02e91441031030040e40300710052142c02c2070241030301091304104030b61254107601880c03040c802102c4d04045500c0e035020a9a460170020a6164010032070f038802d0002c00e001c1c0c2660103c1c90654040440c90101301000710b511150180f0201039480d40b1000140300b83c1c03803d03000708218280c0d840181030500e064242001e44d155402c0c850f0310300035040c0e807400b441c00ba01e050003154009020380b400c680055030f460250070010a20b080d001c0e100c4d500d82c9040410720040720320510380503041a010f0858401d00b001e0402c401d80d8000352040d44910b07420801e28110480c1040075003071610b000440b2640b6202c00c0c12111742081e009038031440c40790060402c40c0b09806155500040300500a20700140c9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 516268300 1250 516267050 516267053
    0x5040f0506130527070509090f070b03060409120c02030106050103230717100501090f181d1f0b0604032607020d0f020406080f070506070807021008041106070816 71
    0x3c002094135010100d05002ea00d40044551000031403e0880320143d418079415545c407050030382c0301e15495100c580e140d08290030030801c40c03040c0c0c4003039600298001d00c005021209580c40080114016a40b0004510060704020640c9400e1282d00000d107000c3c01c05020819244104010b003200c1c3c5003401003010252408203095921400c00b1300c0062403d4003114005040c410419900e83e0842d00c2010f0003c1c00c8041c0100d480e80944d1107a00031240e0700c00b041d040c0061220320400107052524010790010000980604191008000c07540e114102c4920344011644400e078201c09941c500c105550150301c0401c000c00000c0c41002c3ca24220b0f000300403103850450400c0ca1561054840d80c50042d6010160111482c240105080611440352003101c5c1000344aa95a80c080c0d1100c5040401e19601d40201600f08440d0510f44020929148a0f1002d24509112540082c00360310140c3d0500000500280810040105100f26514a010101d4880c2d0a200050342d0b200d41e14420881200c800542c0c2551040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 516269550 1250 516268300 516268321
    0x2d0a0303021e030c070b0a110304120c051f0e0304080a02091003020301091a0a0504030801120f0c06090623040b0d18030228020310050403120905030405040f05061305 73
    0x10b2010040840c5598070700b08951444000d40040805440d103480c8640820b1020781c1d0f070710894a0311903500011074211307900c0351a14500c6024400b44017090007140007014001600c1840401c6241c4110848041c041c0300110281c0c0031256003540c01000c540c0108010303c40007030300281c444102d80e07048521300c01c41d954141c68241403002a500c020742544c00d001100d000c0005180c0c2915807507188901d04180395440540d110140d44042c0d0740640450700717800061100100c0c085c1c006e100f06004a00031108040d00d41c0c0c894503190500da00600000342500414000d150f841441c6904c040c003248003400c0317040c0007120800d8461003203110701c8080b0140081c464541c62201e420410b2500b1601e00c441004411504000e901e421044013055260201e070400d06009100425482030244c0e0041c1c024904080000035000080034042d20540600601c0c150700302102d40d150040c008454820390155880f01e14000078041500c103200c4031243c0c40750410040000c1d80e210300c042060320005c00382010405454400414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 516270800 1250 516269550 516269587
    0x1413110303040308040b0a14132309040501091424060f040c0906110f0303010e040302070807033807030b0418060b030d020309010c0f0606172d0a030302 67
    0x1050010007117000a0103503408005441c541d1000c0c1c459003056030b182c59440c1054841c00045000038050f142d01130100c3ea80b204400750305441050145e403100501d20303002402c0c0100c200d9045585030b4542c5004400c1124540003c403a5601c4080100900c079209404408001c070100c00d410446030080000a00300d40e201e03840901d0908001e041044200111380c00100303051014040c64004c135460f4203510504560000d421401901e13080c1c007a50560742800d40000320300340c000d4400d82c114890300c10080341024003480303144001e40c0f080707280224241c40003000c507942c4040750200d1a02080d0f520b5006d521030807249000395110303a56140c000703840901c102c0024001c005140c0421001111a083c00c001c11840c1d501000c50680110125200c624206004980e40e2003030382d00550000392181e1403100020051083c5c01c1225210700c10102d140350300c5803520702000c805110084469400580180d80419019882c4a914011160500c0029104404c016600c1e418094001e0030950300080f00709180711200c190303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 516272050 1250 516270800 516270803
    0x40305091206060405061c02011202040510051b0d080708040f1e020307090b030a1502070b0c190c2a0f03050d08072604060e01050903040914131103030403 68
    0x3a0074041c41c1c4510060b41c0b0300045908a000b02c0c50400030401902e4040412021030364032581e092581c10300340d0300441d1002075400d21407103401e409010100d41c03595842c4103a4800300d010341c0c070740d0b449607009007549500321f006540d01085900541c07065610903510203402139001003941400311075074881c0c4c54466070076600e01c803028040904904041b29091300604c1c0e10740c01070303008404a4403190340300c1c5c0f6004116a0100080c032303070642c461b800c4903000920130064814100e080c181c0040c03c0212544400000d81d108481b070001b50a030014540da865890080481c01490a514065003018502e6952079030f212980c0c51890f180c0f0400526100b81100403656460180400f400d014849980d60314140343c3e2040c2041a80380400c0507000010a030300c1c4a1081010b190008040c038421041803070100627940c4c0000303403081d82c0d010746440d060420204240569400740004400966403145429403a2080340c00108844560070503060030f000b104100c02c0d01180c902d5400c040524240c1203a100000d02e03511440e0710 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 516273300 1250 516272050 516272059
    0x80f1b01060906051203032205120409020307120c0818071e0501140c0304060e13150806060409020105030a050a06030b010b1207110a03231206030d02150f04030509 72
    0x1c0810001240e4200104072082680c1d2280d00c0140200125200d000880320082c5035101500e1190f86181d1094507185458040d806071000c0c061141150785c51507000b6000080c0468001003882655540312422007481c00d00c0c3c220822010021040051602c14090030500702c407904504050314611042c400c00004006000c00e16000c040d9040ba842801e5a6921515000c59100001d2100301d1b6441c0d400ca804149203203010303500e007500b0090182d8a2403c001c0140e500140108140e0030307031045620a805510614000c00f804803490020120300e00b003001010717180150b003404c1e141e6005076000001e5070382008100b4404210f03a65030316205001081d560340050050303403444000080b8161001c00500da021101d04544a051780e5800059034203103840100c0204c10707800071049030301092082801541404d0740001098044c002803541e03da454000961030300c550705184080c000540340402c1494a04185030001e032481c07019000f500e03220700707000410105103804503100103010540b0420440d00b02c00700040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 516274550 1250 516273300 516273311
    0xd02011b110f01080601020a080c0102040344070b06030a0204050f040b07020625021213050a14060418060305030a0327080d1512030f0206010f03080f1b01 68
    0x91020180e03084041550107841000c401a905510904c0f02620070351040e001083e02c114240e8601c0100d038000402c4200e655800c0c40013000050202d10104400540444030040444401c1583c40390841440c880804117884030b000403404d220b2400994801e59040ba42d1070300540e6038000400e013415415140251b100b8501301c10081d090f05c08500b410f0160340110380c2d44455a031940f0050f40e94101c1074610045146a14281e543c0c0e010980340c480c2203204035441940e0320180e04411803c040e03080903081c82e1502c0c8046505010900781200c1040c0101244511805074840603000f00701c0d948240c0c010407000d0348c81000a2681c420f1903400c0300c2c00a56120046076590034425074010014085014407002c00444101c02d0f100140c5111050540c05030003100c01883c15003800d55100040c02d5100d41e510801d842107100080000c40410400c03003580c06902c995405031699035009080ca04141c001d035000301021034051010405000075100c2042400304840c3d41d604000413000311009001e2100c64040d030902c3d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 516275800 1250 516274550 516274553
    0x131101051b0102030a0522030210050406090501061410050906040512030c1b09070c0b0c0a03061208070501050702071202091e13110d0201120903140304140c1e0d02011b 74
    0x10f80c80148920303440300600c887d20000e140c0243c1c0c00f0701d4819001e00143d1044031515050300040c2e000750781081c412070000a04901c40ea030755600b907500981c402096034031014210b000740d00f05803090522084e031601e482860b18030024006030050150703001e42c078003d5a003c111118540d10800485090202d43c50844010800c0006841c40040800110a0150380e41d2000300302c6042c059150004c15590045828901d0360703c0b00380d2003900e60000680c6508040e00d42500007640d0044240c030883c00d600501c2c1c2c155503056542802800d444019080a00f10750000504024070042c07142030103a081c3c0d0480d00c50159031a0103494001c0301d14515072501c40e52050b4814000441d0206403607180e281c0c860080ca0001242c000c0402c0620b07a16244040d020401c0b0381c80410a11005a01c0340071018440c0c10f1012010b0780260718440c50340c004031012106030601440ca07030b000d0281004440b064503012544001600c9200b04503180040d80040034901030020500c40000310b80c00b58001d088044503c481c0c901192185 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 516277050 1250 516275800 516275821
    0x50a0e341802030a0f060b340501021b06072010020c0313151d1f0503040303180c03030302031008011107030e0612010608090a0b0103060b0108131101051b010203 71
    0x3513440c0540c45207401c952122081c120f028003800c4400d603015903400c0c028052040002c0c420f8030540c021105c6810182c0b00c031044d060b0814109803501400c00140c031140b842004d103204004014014000360b02000c04c00050540c043e804034082c8041000301201004a4082c80c1e04c1c1c01e07040c503040000c203400441e1001080000001801010200e0280c0d20021035482200466603540c044040000030404c1d002003800ca020380c42c1401e10712501074a2015041442041c00c0b034004040c420090001c0c00001c28041815418010200c85281d0980e4259004e115030741c4405e103947c83d500c0010240b58000c400295041076207c800ca0080034000000e118545c1c24503c0141c603584081802c0300480d2102c4412040f134200002030722001d03c521100e0a50690802100740c0f001c1c40d008003803020b42c3c0304108050b0002024104c5442c02940304002c0450f4219543d030024144400040c40c006014440d0004003010501c40d040084500c10207082040d0307241e400c2c08070556801214210702c48590300000501c00071049 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 516278300 1250 516277050 516277057
    0x312080402190503190c1a03010e0c03060619030e070e0a06060306260721030e0108100501030c12113f070306031401050a0e341802 58
    0x10031034003400c006410b41105501800c1a0003096016401045028040c800000c0d20010440c0200180094159103042803d05e16003100c01c2000e40080200040000e51427403202ea03600103d00c010024114039190000c16801e010b0b007000e20040b9441c0c00f07842000c560080d402105a8010441034039503054a4000f151402c6030103542001d14a0328040001886c00e200b0b100e04016282c1d0001c07000c20104100b04001601c401000c1d2410341801400300010311442040e0707160b100d002545101c0c0032200981c1c00c0c040c041c001c103486080c0c1800711500c00c00c40c00018004850054074400d00380046c0407985013000f1107098a0080c1041d000c40e00d00a568030444180d14040d00442c00e07141000c140c41c0740042c016100880142c0030010000060f801d00b0240e000c07041d81100d1f030101803854001803607590b81d00d07210003a890031a081d91950b5529400e01c101420240500002012607000602401d000607d07030202022442441014503582848044401c102d00155003004144800d02103000013a00c100d00c000a51 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 516279550 1250 516278300 516278303
    0x3080304022e0309030e01031505040507050c03070c0303090501030902061b0f16090b010908070e13170c1e031b0a080301061d1503060d0606030b0928020a0b0f0403120804 75
    0x20310b9010208600c7d0310a008450042810171100440b9914090512028101c0900a08140030082c0b00e1501560000c1002e0840613000b01b415160603469820301078480113064014504050812030903401580b03502007180c13980d086906004641115800440c2e040c50354400707036030309180a94041c482080c400e0740c1c405002d0350f024076000c200550541c001520440d0301449003035001d81101208005c000d1460300441c0e4002010510b10403442c1d00ca60320f41078000c800c44d880414030b02000c182d401c0140000c000c40c000304480581d82c1480071000654030f50f03480c00f809400308038005140100c216000005d0044034003480d804030f115a213a503100c00b006842d104070280c6c00100c400481603041d0a0346461079031640e44010904101c3d00d0764880d2000e000208107640030540c5c80c992503c00010003c1d951180b101d110720882d0010309600e0251000744151440e407501a0f03d91400b1540c9090050790341c06407841e08172a8003560041c0e031361a002040300c00d503004039070000d44005507075000104860741203021544110b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 516280800 1250 516279550 516279557
    0xa1404060e0a0803030403081303020f0a0c260304050402130504060801060501110d080103030c1118090f03180d0f052406040911060a021005090d0e01050403080304022e030903 77
    0x2d4542c40a00e80e0b0707005c02c8a0140000b101c440215428003200b042e0045101c1c040c4c4141c982d850a030040c0c41c3d2404010002c1100c1400704404100840850480a000c00c41d4a01c0020091041d002180c540d89000c3ca0203114030803603002407056000312440090500a14000e401444140ea4580425001302036a00c940c902099460400701420b044c045000c0e000401c080d00c2e01c5240b030b4250f403022914072441c800704440a6124a4040c103240d41c41d5500c40c41c0044d84088001950314020002d14100002d411036103e1680c801c6c4005c9100000d00301225001d40030070380d02d03408130751000d08045071281e083c0c09008e0004c1c0541c0701509400400d200142403420000304e00301095441c3c0b0300920003110402e800103442c3c01c00724241c0c0100c030300c0e111004000c0c0c25840d1040b20807001a0700308c890205e420036a01c0e08101e500003202c0804070b50b0170082e03981c0d240f00e0900740304c6c2c00d02b481c54485081c0c510000740020322a9114200001820070020180c0200040ea00700c6441c0b0071400340c2c0090000c10300b021043c0d010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 516282050 1250 516280800 516280819
    0x310050a12060b092a070803180d0f120e1f021e07080d1e062702030405100903350a020310030809040209040504240209060f0a1404060e 60
    0x2900703050b4861401010145d180032461030311719180d03d00d8000110840400c1075001c016000210f12408040c600401d9141300d65820201c101d010313146000790111480082c4841c41d407040400781e030040c5001200209040b07000c00c00c0340c1e1682e5403c2c10401503010f42c80d4200000c0c0465415080c10740d001c1d1082c5030403051905000190742140d00e400380100c141c0107040d140104040c00d106d42c15604004500002c1c0d0b0b41d580b04150005211506503206a0010b00c4001c56040e0096403030201880d4140c0c0702c48101c0021403030350070241c4445071103914802c0070302c008544544904040521030b07401136034002e03005030401e40c50586030301c00342000350362549854410003a0740c4082400900c2030702c01c90380548002c1607130001d0b2601c0c540da2601260040d07091244c0c026802d21400c455a192401006d02c21881150480300851910200c103a102c1180304800803810710500a139001c41c0c4039441191244000c4074500307900c840540904549808140c240d96503030b031b040170800181568104118500080003103411f000b6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 516283300 1250 516282050 516282071
    0x41103010504020d03111204090209011b081902100213050f0a060806100905060409020702090c0a09030b0901020d060e1009020f2b06031a06010c02010c0204020310050a1206 76
    0xe840040d50044e40c0102e035104a48002030040c00c0c0520390700510410b50340355507010318107020142c10541c40101299000280c141c02c940e4484090b409000c606200b8440da040641c8451441d40140030b90f00701031728600315818032003138005c11032403080c6003065074199500c0418500101a2480610516000da400c103503000c0b02e68a4085c2c1d22a003551001d5507004071950b40c01041140c0244c00091250a1084040c4003048940301c180040c00500888039003d0b13510080b40c4140a4401001080e110200206101040f003003540245807500301c03a00102100d41d0354880488442c02849403400100456150810001d22000004101d038803942c20812410b2000d90740d4482e0009900c0750f4401000c2c1c6405c2080b041908001d13140c003d02e0520480d8021480142403401044122210358205550210144003100030b50041d424402d54042c4080c80d01c0e000c0244258006000c04180d803100921a68011000075001003007a0b1600009000060405c40040d5a2300319a0003404c160300c4042d10a0b6007003d04142 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 516284550 1250 516283300 516283303
    0x40f060c1e030b1503090d05031302030f01060510170a020307050c0a11130c020316030e090108100b0d02010c030c0821010e010905060a12020301020d020403031706040c0c14160806041103 82
    0x7407003000e120b0047c20a00c92440c0080300c09500c01000e411414909501d00805600d0400400d070550001e40000a061801c203000c00001d0f401c4800c01004200a200c01c8a0842c0b030101d900301d40002c235261000da203903200c40c5425a840e0060031100c51b1540b0402c00c0d06400c0c4140b500711480d803440b050303030300c400c0380003901c0801342c02c9c2c8400f07800c4000942c0c0104440784460710703403049003c0520f000c0d2915268103122980011729114003a4000c04040c0e1000c1c1d0542c1480e0107a12695680c45400c0350f0060f1841c0c00d6500107090008814000b074240a8908200350500005c58200c43d0710507040e020912114175041c082032030600e030078001ea030201c804d01030020500184901c21107004680041c18103480c14504941c10740c440e144040201d07095502030101540b801060300290002d1440b139191034400c0030f50100d90b10840180100300d2886181407402550089811804041c441500b0902c40100c10a04110031b82c41c0582180055815000c0c8031030000d0b442d030002c1040c41c041d40c86540702c0e0002011000415 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 516285800 1250 516284550 516284557
    0x120201120f02070632130f0b1609050f010f0c0507060c050105060a081908070c0e07030c080106200708060a2702060a0f022a030f06040f060c1e030b15 66
    0x4850030f0041c05d2403280d1020041e400c1c07540c484400d804180503c0d00603901c03c40d051080c902c04543c1d182c41300082c442460345400700020200482c0c039103504010302d03120005014103006c02c1d1507410f06c1600100901d84a02c155104170fa800e41040480d030041c0e0b42c552001302610304120301070b01d0725440d00b4089242850400c0105086905010051915000d055903103180b20307060b41c07011038900104200050019518202c407600400c2c00c10520380030391030480406070554030403a445104101c1c140005000700380e003001400c484040c080302d07205001e11600a0851030001203801c1100f09108540420115030b0042e04240c4081c4a074400150808000c8415442e050940a00095101c20207121007820b09119050b51900d1203a01d2044424070703144042e4032540700c2c40c0c0c01030b203800d2000c10080f1081d0a040810040410718100c0005101e980707000d48031a10220103401000717140136101e40c6900e910510503100410841c101c090051500741c4040c0c1c0203402810003501040c040e4000341c1c4044d40490040d0180d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 516287050 1250 516285800 516285851
    0x1030c0605090d060e010605010809012d0906020c01060302012003040608070c0605070801050a38040e010e06030d080402030c0d0c0f0303080a0e03070c120201120f020706 75
    0x284825604102081d00c482c2c00c07419005030811a503c00b01d02c040b4100b401808000c03070051000196103810b0100041030210f00510801440e0304100c0320503e0b80442d000c0644184000d240c501d1740c0700600341d410002502000342c000d07000714004600c10072851410760104040300c2c800d803603503405030948a81501d079080c040b5070515280c0e04140b00400c8041d01520803035078010100c0c41d154100c01300030341c2c0d071004885051320070000140340c031001800035040c00c2200c0000b07030030b000030008010350812410351108000342c60907075000022290107114808804013902c0c084d00c00c0301414122907031a030f4031159110500b114003610a02c40d40003031024071801190000d00940e0050050050010500d050000300c004500e0202c8881c42403440006143d01144d80c504050361107940d406800d420311100410903100030418440d140e4004110344070003e01c034050000d0032030b45101c0004128074401d00060b19410101604440031504040b022540c0c002c26070300030440c00b4452041040f480341801040c88902900320320 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 516288300 1250 516287050 516287063
    0x10c0203030f2508040c030c14030c030c100507060905061f09020a08061c150e0c0a050109030311120406090303110610090f091e1e0b0406020a0e121b090103 69
    0x8260805a100b004000d91041c01001806c0350655a40c1d114940c4120351b900010500311107004990031440c003807004034800f001c100d00401000c0040c2c3c0000c5c41c5a0b0384007000c441030000004151040284d643c105400c5036810800b955442d2800400c4100040741d44408015501145500401c80720524400c2d10381c01c0346996201c03249641c60009000802007084102000b82c1840314000c8000b0b6a07038a18181948114100450074114801e400c0d03140521080b4082c0c030546404030140f00b180d80c484407550403a600741c60a80c020745004084142440c0c0382c00700404030101c0000d008075a85030400803402c201c7c0e04c00d54405d4910300c070f07039019640c54940030340c1e070008002c203034000c00c005413000c0380c20803103401c03424200010304105156198030700f6800300740d061040c46c107141030004140442d5001d0400d001e600e004000d064054103564903040000010030041129501045111003103208560360020000050f10220110110800301c9035901640080c4013800c00107017409407100d0404d0410703d4100d0b5400744 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 516289550 1250 516288300 516288361
    0xf0405030405060a02190825050319110d1808150a0e0708010501120c2913030b09010609290f040b0a0f0312031407140903010c0203030f 60
    0x104006450340010380d000114401d185000302c42002d07010008541b03511400c240760303444252051400401d52242050510412030803d40740c0850b10100440b00700844d40300c0301c2e071620507504000b52401c1c0720501c0350704058454140d1507460980c10031510304803180a49502429142d44641484e0b680305004401e0454800d4100480e8202403990080200340449406a03038919442e40e00d940c1c00c51324242c1c003100c1c1d076032010212802071000380c0b42500c0140020013101c41d0291084024400744001c90b0803504520040003e440710f1200d1024100b001865118042d103044e402c000842e140609602d011b01d1031920f1070034441e00e04082c0e0fa0a10b0250025100c030146040101c0c210401207145400c0035001c0d00f140e190001100240e40e44407407100a4429854400c4015046080600d010042e041d1400103062401c22103119805180550942c440b4151422140b02c0c00844500e81e0b484c003d420806816600300301c91100455000b0002d544103010740c0000040b1940c460000c10340d0020145080390403d400328 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 516290800 1250 516289550 516289559
    0x6030b0f0618093405150f090a090c050702040c02060603120d0b040204170c0301110d0b030a1b170d0804031b0f0c140f0901091d0a0303140f04050304 66
    0x9074000010804d8515800c2581400c0c0c1e490782c1e20a558001e8507415200d0b0340d0b0400540501040503010540b81d000d40000f0412200100b8410f85409000d24000410756031f24a0f51022441000f4002400c402c0c03012050701c040107460390300031500c1288030714102100d800c1131078800900d103840b034000280105036980a03000605501d41c4011030803060203458904250081d15240009c0004100501041079a4119410320030305050031030b8515486641004180b03d0780071505402d80300640304c0c2140c006801844040020f280210120000f008003416004180001000b10201001c80f003040d4034407201101c000003c00d40b10410050144042000030010031b0100c1d01c28248010b201c601e0940b491801450760b243c0c600036540d480b00840b02401e0202007170040c03010600391503d8003042030358280d0080d0b80c880300013070800105028112007281c0d80e00030300120300100b0305110342e6560003100707581c400e001c2828010040c06030600b07442c00007041e240c00b01e1407d0420410035803003282c000020354281401c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 516292050 1250 516290800 516290839
    0x911030f101e0507110d020c09062b1407061403040b131b3b0a021204060203060906030d0f031a130507020115031a06010507080c0106030b0f06 63
    0x350491140d00d50030808a440b101c0902d403260300e020302401d413100f4620842c00221280740c814000300c150304640100c100750001d502c40041803900050100c0320b540310582503580c1c02c40da8400521840121407500070785041406245102e0b103400741d9009040d1141c01347c84150aa50f00682034901d840720b09010400500401d04481056400200000b80c000700301e141d549514090705d440e048240030b2103403006401c101128032500c64070714002016208074000c80340585141c000035104402ca4221070304100014400c1180c95045aa407000c880f00c20032072904050820030003d42045402030f0081e5610404205103107400500c002c1d803840701d60b0703400c9005074003030404030003800303085030302c10b8001c007500d40384846903a942c601c3c02e6a00100b14800180524140400900790355480c100200c2040700321000780003103896007640001c0d03e50418041d0820ba00c0b281c0040701da6103e100f901030141200030400030030602042d081102200d0045c0824203c80c0c40e12501c1d217841e80e505441244d40504041c5900340c05084 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 516293300 1250 516292050 516292061
    0x204110c0606150714010c080a05070c0f11060417010b010c020603011a07020904050109170301060527030312070e1c020d030c08030108010b13060f0501121104090911030f10 76
    0x10300c0c513040205a5840e002c8410a5540d10303840750b51141501140740e64090145035221358091001c1c0401e007400b006c06402100095809031034200d9110540c0103100d41d400d1041c0b49810b0140500c0e684613a5048070230070710140c00038584080d50a02a000c8003542c4a00160300c01203800801ca01e18691074610702d05501100d030070004109800a004023405a9124010300340708034009e41c000304040c20a0305d0b12034200305ea80d6040c84d181900038001071200b10740c40010b680380f1810100c0c0c2c03541d28004030100e103004a8403101c20160305120004591080040c40001d550080e090390310b0340d4480809075000c00140956600080642030044080b080c05403800c2a0f10300002c50090034400945030b01901c48202d6036000b600040303002e0707440302c00140c0141400810910f002c100c1c0142000681e082031036040d0510210301c5502c0c10069810510312180440f68454848107038441645aa82c542d00e80c006000b0305801d82050300c00d00c8008008411174240455440d01d03095000000d05030082c1001285800ae14 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 516294550 1250 516293300 516293329
    0x302090103150f030b090615010f1b0b04260a0f0e06070606170f0d0e061c02032a030414102c2131050f0d0506010e04021215040204110c0606 62
    0xca03000c00b01000000c03c5880e009001e016110400682c37425040c1000008180b032184400701c40e01020310644046490b09a8940d820300385001c416500410b0000c803060300010610f103520180c001034a07c00c0160f2940004201d0b411150546040c40c00c080714035031900342400384102e150b080b1040d81040a44190040224038100070b0010341007520707140cd42641054503414003001c0303507400000d00c45e060003404040030200c003861031014000e00010203983c00301e00010b0802403400e0f0281e0007529070060240710380c03144d101103400104050180d041c1202c2182c1d0004559481195089804142c80304001c900200760b507880042c070114400d6801e00c0c40301070390f1140d0031007040441041c2d0310040c645103c551030001c0000741e02e0062412820001040030140965503a1440380c0b03800f000110020b200483c01604682e00190b0385c8809031f41c1c60010942c02020400e2445090144032a81d00c4a50f8584c802c0364001c40c0251000c014100c1e40b10481040b502c40d9410760182c07944030800040b050f10717110105110b000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 516295800 1250 516294550 516294557
    0x1140d111b01090c080a0309140301090f030c02040c0c1211031905090406090516030c0201090c06110f03030c1806091c1e030c030302090103150f030b090615010f 71
    0x1480e08240c10060001c90001051a945441d2041d052104498043d00500752240143c8000301107958041d11140d042d2190100980c400404a0343c566420740c0442c08903a04040100607041462a00400303440700103070700300c8c451842c080d02595114840d0584484150744020003071800e220400b4142c69441c0d00344699020f030310081210ba082c0d1301d41d944010040304100c1e00c0d8151038001c044204070a0300c600350804201c4600d09030400400502114040046883d541400101c9402e1944203e02400d0000390142c03c0208001c40020119803281d050780c0016070440c10390316481d0102e8100d603164403007131f0350912000130248081550100c89007c4e0b00a6440c0061005213403290344408140410099020207070f08401000490007030103144000c10800280c900c41390b503482e2181c3c1d41c1c040c0900da00e010014080690220341c0d0b40040e4041d910213517100000190000e095503460085440702201360008584000180012401c62940054110300401c0d0162204a8502916004682403a408440f44040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 516297050 1250 516295800 516295807
    0x5070302030d0504081509030a0807050403020603161d030d0e030f010501090c02101e090201030f050a0b01021005041e05100e0a0c0b0703080a0e030706050906100501140d11 76
    0x103903410040d400780c0c40b4083d01c80c0c40d162850b1501c1765040c0406a1401405240c000301000840e84002c411200026284e0408044540b1120411201c1d400303140c0001f50040707000402c1c4030008020200d005108030450740d80001c02800100450044c20b001710804d5019071141301b480c81024000e5604400d00000501222010442916002d00350f484c00e03406041c92a0761036002c2e900300c6905004c80c1c41c1a004000051200c200384080b40c0c40381d101503406000859640744407030002c683c4a41c00006049004180031b00040c02c02c0c00d0b052000b0504960780381d015100348100e05406510a00405120302c1d04042051780e450b04d06ca41b25800c01001d640c0c221003d014007401c2c61028040c0e03200795029042e000d0003c01c034050319440d280b09450540d130000c400300b040900c005e8000a03031100c00c8a61000c64a1004242c0806844e001d515501420341e00030300d0306081c08108003407800d00085091085100030050b005480d81e54005494003450044030079140c46040018071280d0394245c00403201030b8202c4c46014034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 516298300 1250 516297050 516297053
    0x80d0e0109060b01030e030307020d031d10050a1811040b060c1c090e091b030f010c052104150b06040f030b10080d1d0a15110f0d140304050703 63
    0xc4074803100701200e20301d6032a29103103d15603040c822000000c0c0b1050040d8a5810451000b80da101c6105a03124201030301d0b4042c0800c4010940c208680a400c900b0403521417581c19100600501001c03641d41c2d000340d14114041c1d100000382218000c1d215080384a040171008207409100c05031000c100c0c0540c1000d02001039140018082100710b000504181000c81e003600b21480060041080b030380003500c0303080c022080c8003240e000840c240c10302c0c400d404500c03031401b0012004282040c4602d140000954640310410b81d01c0d640080040100c00213041034801000f442d41042d00d0942e1013500d01a2440c11501b80f440f0a02502d5401068070780001844c079810f240d92401e882d030140c00103070000ca9640d92560305200d40c0d0411120904082c1c940100900382e0303486401e038010107240340140452000707000745044098648548040001a082000807c4100040403030040e003075103030117240003c15100b0441080b59178000416401d820508547d85c0301c45400b0100c940008130b40000d0419140760258440000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 516299550 1250 516298300 516298303
    0x310030f081201080105060603060d0f020a0906180608031207140f0418060e1501030921020d210e0c0901060f02010605030a050c010f020304090606050d0e0c0d080d0e 73
    0xe00c0984100465990368508811000c920241a07001c101d141e814041030080300d0b6580c2060b03030f5000d1020b44107400c0c00d8a079410404401d0303044600c00b079000340d1510310110f403981c1c482d084075003138540094003000301c0c040c1d41800e00122001840b44081d143c00902480e40c1c55040701d0302440c4c002c2458940f80c110425003802c04071070f550044800c0e25000d80002401c020300f00b050501d650740c00742c038110100901803510002c01007640004042030150f072115007403401c0aa001c1e612001c1c81d00d030000c0745407204441142c01800d480c50000400d00261042c1998030415038420110280c80d00c0004001c0703000141420810006060500d00304c00b091b000d004000070094403070900290091109607610282c1c0000782002a08441103604800d0190308240e8401000c10000903800035042c0302032a00d01304078051410100e0641c000c6800c8055540e00b030030400070780c041d4404090704080c8001c01c070803c01c2c01d040307901d6944e80710000308040c0d400801e40045c907804586914007902d00164104c4020608030911503105 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 516300800 1250 516299550 516299573
    0x60e19080705130e0c010302090102010f020c161502030d0b04060e0f0a15031703070315030b0f34050c0d080415050106050f03270a0b0903030c0d02031003 68
    0x5868035400322808000070f241040d80ca2214030788030002048001c3c003c210342c0e07484d00640c012007030604da000901c90646034400d500a2900e501c0a4a0454407480c842d008240c49104080c04207803e100412408140d00381184800000c4441e40e40065160032101c94400b400360400c41c011950050382c50800042041e0000c0e542d91240c07225130000b459502c0d00030041e03400c4461a8403069100d59400109000081000c0c2c4618500613504074241e850b5503031010704030090040480d90035000c0d604520000304001c40c0020b01c070b008803001010b00809070313149060110a0000034220a510b4450805e26500302141f00e0040d8030a0000361601c1490178460507000d610302a0383e8512308000030010800c001c24080c1c040031100150741c0c3c271042440741c1c5d403502c2e40040884c0511141c5041c100400004100645404e4071481042403810080b642c0310001c03100101c0d1102505c0030f0950711054008000342500002100300d0703108829400e9494101310749402c09000942004050b2988164030b08408000310782c0e0a00d05 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 516302050 1250 516300800 516300809
    0x9060c050c060a0f201203041401090b010311010e0108040b06011707090305010f09110112060306090308040204050a11160302070807030809180106081914040c0f0609080304060e19 79
    0x119100440c20007130061444048050310f200c44a081203c07054203000105419100c0800315401940344e4940b030804421414840d52450241d6192030914410031030604451030480340207420318074030740715580019101003140b2681c0030700060710300002400080001350340503041311042c900a05214500c2001894100050f5a414007150000f40304108101c0c003405203003600e04041c1003c0c0031002c0683c4d91100a0440604414144584083c4413032104030203602850045801910500c651300741070501415005054400b40d000754100b0700008d240b414540504075084001c03800851800c07021059032645004030590450440c000da1500203a04002000110051030081030216651181b0b103040104d111200c007030340c50100c0c440300300400260b908541c00503840b81035031a0307019000c145424442d0080c4000080540740c180c075441844203100e044070f401b1003035607259100c000029440f07020981d023819142c4240d40c0960f01c1040244211407146c482c18011130005002082034880803210122246001e401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 516303300 1250 516302050 516302057
    0x322060504030816020304080d0302030403170c0909010e0603060414011508032a0309012303190b0a0e19060302030604080705060106050a0c03111204080703050d0f09060c050c060a 79
    0x1441090804190040f44800c540d000a607e003600e00a02c4945850200503007006140e40440020103040c040e21040b1340440e0b036120580d8030f0385802000500503400c0b0a41c10b038003868030722001241041105d2001e074080c070001401020380b6139071b0307030344c0e10009005191500042c3d54072946850b100b4503040c0d0180c809040200082e5440c2c200301c00e0f00446600811803100d0100c40381d99666540b404001c001c4174101c400030300e8001d2008500005a03881c10002c0b1a500c030305554000704202c1403001c101c0c0c0101c8040d0340c0000a00c85c3c030b01c1c6142005001e07a050300a50840b01184c4002c0b0b032014021540c01c00981c0324035800800d1503030342d940000e801c4c03007400c5070700703546841c400240300d020400140005030140601c0c0c00c14501b000c0d01104001c003401945c040050034480b04140e05011100e0402c00342d0001150022100d9545455401c1c3c103840d2106071004544612130078184010140c001c0e0907411000c175103907456003032a504d00241214108800441926a800b4840d078040300d0362543c80c0200014055501d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 516304550 1250 516303300 516303317
    0x30b042a030506010e070309020a0e0c1306030c090602010b01020c010503090a020604080f010b0a0b0406050a11011a031501050d0f0c05150c0607020d02030f09120706030c02120c03032206050403 85
    0x425505c01d0000420100815117031003208001a40c40c0411042600d00c60280c3d010955280c0e03841d10005c1c030805044c00e6034001f10210024100e40e058010054543c00340c1c0e9240f80480c0e60300000d070f003610382d40891180943c124800380101d039489030028581c0841c0d030604490b004481600130412907401a00005125044007200c902900424000c0640c10030096608040f50703440c09000703010b140541d0042d00c2c10000f00083d240800c0d4801c0c09150b1550208200801201500d540602034844000c90b403240a0301500c9070050954a115040c54101e60380a09650b50b40f500f16545e045111a9a98044401611044000c2070584031100d9802d420003901402c2551031424401d4140f5000008240401b154054a440300586501000352402000f0a0b8100d540322501707000006d95025040e6820b15040c481c040d0000b800c5945604240e5900d081d0307400762640360312001c4291040348900351703446240340d204101040ca505420755800006100540c10b00342d0401440d40e441c0d0550385c094406900180005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 516305800 1250 516304550 516304559
    0x90a020a0b03060a140d2003012703030c05040e15040b10021c0e060d0606080903070c12020a090f0501080c06120a0506032b0315030b042a03050601 65
    0x4084503406400901000e41c114036042c000100760000303a000d80402c1a50450180c0d00b15210150b40d00b0316aa0b22820303803800c403801c00400481405a80c24040c0c031035800d00b11040861940c40703500780100c0c0041098501912003a40301a006001000341d88005c00c6410800002e9502c041c0710440e000d81d00b800c800e0410014880100b0083d1012100d50b544142e52000d8041101600000c4141190155042004010700340c881c1c1510380840d00d4409c0c50300131100003210303c800009079103c0001d48850703845502d4ad0741c40314007a0a03682e02540030010003000c0340031070900440101000e07180c407081c402010f1540c80c544410300b550640c0c1e0850b4030001025103801c01840882c8040c0400303203031980150f80c50b0341072051488255a030450084c01200006a60324082070041d00d082c404d400f4071000900101c541da1030808102d1800c5400702c0c110400180c50324006d0b254100345050307008200c0e070b007220f62740c003c649507922490304800742828004014650030144005424842d8603010040d0701982c090649036240 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 516307050 1250 516305800 516305809
    0x503040905060a06090522020408030406170703050402031519020c03090406080102030c04050f120102130906050a032a03061d060a0608070b030a0b0a15181802070812090a02 76
    0x43c1c3d0880300501c00707100428006a101e1828040c0d07051010034500c002c81d00003c58420091050f45c00104517400002000700302550031a41664001041880c43d07803031603440074030881c1250402e660080d03164000d00d902d096996500c1c0042d58208071514103500c4d0150300b0341c2d0140103d9110402458ae10f41002c134156201d80f41900c568001056400002d5145150444030040203100b44e0259a110f1010a50194055101c0c0380d040080c0101202c021541c2d10652244151050010307c21410081e041c600c02080ca4148030100401722544683c0303420084600103103000442d108103060b50381f110311400001010501c0e80c081e28010283c2c0690460304940001d01e442d0602000900c298449400c0110030885484001800c0b801c491070384000540702d403641601e4002030000500c010340e102012100100c0c1d4540ba810b204d0b400200c094403100c160b002e4142c4d400e0070094103446402440d0300010140c0c00c05980c203070010300407240300c0e8100e03c3c03400a000c030702101ca0520540d5200007035802500882c045081 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 516308300 1250 516307050 516307069
    0x1060507080d061404051509061507080313020a0902090f040e01090c030318120f02090903041716060806030d081b0f0901020105010828030c05030a0e010e06070f0f030c050304090506 80
    0x21f08a01c000c1d2107501140070100003400040c003c4ca840d00032550741c42c01c04415115041e6100030510f6403400d100010400c1498100000e900c82d6038009030000c0c4e42c00440c402c072001814050640f42000c154002048014a8000d950b03030440d5486003640c20000e0080d01c50340b40954840e490b2101c0480032446240b81c2c075511034002c900000350b0301483c1c502213030420f11b0706219141e044884500a81e41e040a41e4194012607000c11016020ba510f0140c2c880d0001c40e40003100c16401079640e00059031000b081f10094015142e550301134101c10f0603002c50a10491030035074003d48003884503021968030460043c00741d0010090b102c01c4000499240001d6a083c0955401820341c1c000401544203584014044412119228005801ca244940081500851401084d0b5410800b1381e5250309510340007070002c50030000c2540c0003c40c0705081c04000c2c83c0a80c29600031580141c48130b068000a5694240303006040d050550500556450780000030350200300620103013100f0100841d1504100e01404113007034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 516309550 1250 516308300 516308311
    0x13140124060c06020703140307020705010e0423070332011202031e070506070b040314041805060310050907060905041407030b040f060909030e040c0801060507080d06140405 76
    0x80c0210402249a020701e1003660590040c0c0d005a64807428070b03069581510a616000c41702e5008820800965008110801150000e80781c40e02c08001180802c8200c41c041c40059030580380300035142220591052000d40e2101d05800c000980c40310107101068400c10f111000c40c82000d03a085c040410a0070407010034010001519a6001e0481035800039403a1000030603140070507418155102c0200c0810000f4400074800546441e50b40c1ca0035082070219010112819401305400b010b880d444009014106c400310390740c80c040c02d06440074030709502c0050000507124951600c20403402c0010381e07140340303d6240180d800c00010600c0b0b51a04501400104090b0712691146140c602c54501c00312445207181e920103110b01c0e001a144d001c0d0000075000b0308810f191801554038080000c41c094605610001c1c9090080e11641000c1d0340c50310410041e01c0742e601c007510010b40040010082240100080c0051600c1580c009090402151102c402c4641c6030b4040401ea00000b203e490142c00d0078802c1d550001c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 516310800 1250 516309550 516309611
    0x180203010f0c020a020d0c181a01080c16030c06020c060f07030207120e030f152a040b0a1205090615090906041101090810060906080610050405131401 66
    0xa0000d001c1c4d112200c3d910f029004004070a4004200552840540003401032172100040400035104a60020601c210726003600400d0014170071217030360140070441d128500c605080c40c40c000b5a50b05a0424000f403660440521000d41e4400c80003030f54500107850200c06001c000c022500d040c030b0780483c0c4448050300d4078044c9441000f070400407411800c4400e4030b40603542080411640490f0210f8504427074005580386030b025006a804020b1040600d00b03011340b5007452454410783d04c010350210709130100c0d11501c1085030100302c10855810a40045c091804942c18820a403050001c100d001381c034401c441103203064001d1020803070302400b922030003820300c00c09507149402898500015a510907010344003401e94600301d60182c0c03160784103018100143c007895041e42c149903800041a000303007203540200900303d400e0500111300c039080064075138840c0c44901c601014040c640820b0100401000c1c06121a50724907484d102c011945a10900340310041c01c400008540c950140c02d65018040040042d81301d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 516312050 1250 516310800 516310811
    0x8010b0a0f031502070311010f1b050f0301180204120501090302190203030306010e04021603032c21090612060901050909030409020d0b030f06090106090b0901060e0a0801180203010f 80
    0x1c1040f45038001038040da5040010380e03c04d01820290303840c1a404005004543c2001b00d1106492010780040e040020035010f803444001d00500c0940d0315018034450301c02c3d140014070042260780d48844d062101040840001403900381c89818100762080d1a00058540b40c4d141e082e1001090350401030340b400000c007107004592600283d0f0010342c8034407000d020141000420b0121462940c0c8907412070301700c4e03c0c50041244940c0b00f14600a0082c265554a6a0602118140300c160f140c440080302640d011030714020302005000482d6546080781c482e500c030844100107110300d0b40d09841e240000c013103101c6488648102c1d481d014041110002e4141c10480c0030740c1c0448180503400c2c00000555007910050308002d61101401c030090801400e238002900c1d4503214010010000c1000450701d41d02a401c900c0c002d0100e0f58031240c141054a005201180d0804000d40041002034860b0343d00c00700e4040010138a080319555410747c182598120000003200030f1109800c2802c500d024400c0303c4c0c01103180d8000303020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 516313300 1250 516312050 516312053
    0x9060a0213050d0606241d090106110708100b120c0114070201110d03020406110a030e120f1f0605030c090a051308030406140a2a0306050a08010b0a0f03 67
    0x15280c0740e1190070f00a509a0070341908012150304041c0151000c00e01c0d05000d610340d0784405403001000c000407000710f602c002c490341002c2000880380c1ca01d11409041c1c01036170703440c114046601a2120200950078040c2c20030101e0300840520030107503644d1202c4004030b40390110904000c00c1c07031880e608103885540100c0a1501e50798003e2842d01c203d07514190401d0300ca031824001a103251690001d1104a802201c2400003681d4140d40a0415110a6a1740344912191903001c00d59070442d9903000780201d144c0c0700120080349840b0700c0185980c414441519008058001110301d40b2011142d1416807050003115020002c03000d01c50000109000c0300101030701e118210200c0d10401020b082580c0b13251301d420014902d440d81401c6000c015910002445d50b0386440e0820034001c00d10140d038880030800b1000462410905801200820900176804d0051056010310152a200d0f440880700c05041c3c86440000e182c0e601c059813540180707010000480c034600000b081040e82e60846d00420b9901041000c18030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 516314550 1250 516313300 516313327
    0x602031201060f03061205011a0d0c090b040912020c0312070305030a050a0212010803030f1005010206060f01110a050c040615020a0f02010c24050f060d0320030a020609060a02 77
    0x6044035075034100b10f02c01c5000e9040807000b030042500051a005181242682046070540c03241c0d503100070400d031198040200038100300307400030602c5001d003004003032030030510000c0070315409640c0d41c18006000080c01d443d01d0362003890480005200c40050303000345808070b26900303050001d0300c640d80341c1031512880c0076425a000341030b502025182510881e07440c0001411009258100c82090700d0152148881c0c1da560b1220796500d6004031030022031082c481000c074442c00c561916100c140d403c160040d250310342e90300e0248071500050340350450400203500b00b02002e0071000d1000c8031003280988094200020304809010036030314a90f03c5071050600000c3c82204066000c1602d44d881644000007800081c0c0600040f61401c14545010f0102032075640108000800240c89141d4107403288014005a610b00817101d80c030b00c60480b1240d070002500041040004d20644800c04421106490124022040b803046440d50300064100c0c009640302900b848440d00d02007003090351000c6101029440c10481000c0c98 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 516315800 1250 516314550 516314587
    0x4050103080c120f180d06060b0a0f050406050a0c0f0b090307060b1917160e01031b06050a032c1f11040b2b020d0b09010308120c040b031f060203 64
    0x410608143c17800c4654561348404080201070782180741440200c1d03c0d0030b94034419611064825002c107070020810b0a207607025400b640c01304c41490301c54604180030501c0540d011034002c0c801b242d5284401d11000c00040c5101411405083c103500110b032540c00c07902c0c02c542103c085454a62103a1412285444080d071003035000819155941751750341d40f1390000000d152500c00140d21401c4e00e40850880481c140d5140214a4100d034003d1070389014015448880b065204682c0c0600400240c0401459040b02c0c00781e001041c01c0b180384c02c00d14008808080b20710341c0e40c50749462411619000360700301e407020034036407414620105000101002062400c3c180c0c03009901c13440c4500906008003043c0c0907a080c0310780c1680c00e4a0001c415519083d694290304100083d032000d4000030710b1030b1510700c0252641c00c00e0140d01c4d041e00d500501c994030744541c1d0484520645402050070900c000100404107502081202850080e03a5921203039004a110001c100d4007000d0300d0b004802154400e02143c100c0842d5901740 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 516317050 1250 516315800 516315817
    0x2121201060c08070f03170c070b15010c080304120e0312030a090326010f08030f0304080f04081e0714010c0209040303180b15032103060f04050103080c120f 69
    0x80040408145007051060090341c2c00a80020800c107a801d040c550407202d241034245190303000c47c3da03556403015511313864011140d02510703c40307904e400102502d00803170304506896014107100030745108903070740d000aa9008550480303a000443d11a1a20a0740000300b49406890840141c5052510400241a0383c00004c0c039000440d03480e181000300f490b000786c4010a1400c0c80e0380860300c181000d401d00408100082c842c1c2d102d1807110540001d104500401600d06851548200d0352035034a0b0b54503042e180d43c026a4024403d00000c000019803588200511721004100120300d0302420040d1540c64205007642c1e10010b01d002a06076003521903a80202410000c560403284e0803078545030360030304030700510b5002040704090841200365018449035800d0184103440181d000c1c00f000000b5800e154544410810807503844517000310310082820081c01559004c2000341c484a0840b425500007026224282e000360b50500c00020948000001401601c411300300300b8141610b0081c24032000030345445044079 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 516318300 1250 516317050 516317057
    0x20d0612030c0b07050904050a05061807020c01050c151317041d040f0209070e1e01050a080403110d050a0201420e0f1f05090a0b031c020d0212120106 66
    0x6004d060045083d1110100060010081490314512407002841c06641a5102da0b40c0c0c004044040441943e01d503118003c10360140c8041601d40005403000c0c1c1041200490600804103041c803034200001d9100d1149458203007059540805040860f080300c2c04030070010406900300700901039448003054030402002c044030f82200b10340e12400c24401907111508000c0d17105403e0818072240e02e5100044281c0c0310f10450307012401e0703800f40b040004602e500c3c0500c030380400c00c00c1c050100348601522200713900c035010b400c044401080000689042c40004814040403907000305951009075424410602110f41c002001c5d0039038442da00840503200034500402c200400c00700c03000c52844c005008a040288400c54618015050600c031108020a0880e02003a041124102200041846e900240d0803110003610080041d201c0d000d25030040c00d2099a020f41510070000e180c04400480c4103840305403034040e03003d003c00d4100741340e000341846104d000c10240c404046c4006813800104492283c115040d604 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 516319550 1250 516318300 516318323
    0x5070308060d08070b0108071a2104031101110a030c030c12020f0903060a0518070b07030318021f032d020c15010f05090105090f060907110a06020d0612030c 69
    0x1e0240c2c3c0901c16814010320000201e0000207030708800084100c25114110071100d02190308a070b001c13900740101800307074200c4185180316903600003540b46d200c0c0c0c0190003480d03e001400b200b01c1589003034130219060709111510029600f1005c65052041c003548176010b02e414810b2000d4040004c0480b15050f01b220300d03c036400600b00549200d070008507140c2e04030280644a952526100e220014030381211403030219080c456032002310041c0451884280d900032402d95082400d0742d10200e005003025042112900d030440d0f04407001d80d55680b003a00c40703aa003409804c00704046120005068404818441c0c441e0032100c100c5090284c10b4890141b030343c451070b0718016120300000c240946440281d04032000410842c00c00840d03c3c51012904d00281d03901074402d02841e9076514103208503100300716501462200903070041643e03840c0c6080c00b941c220445142420301d40204031001c03418007801201c11140700da030008005e050742103640581c100074071601f03405540807001c90318060070520507014000c00004105 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 516320800 1250 516319550 516319553
    0x190302032e06080a0c0b0a0903030c021311070210110703170f0c0f06010e0c0706020304050a02060310090509121c18032105010302060d0c030e0a0b0601090605070308060d 75
    0x16000346200c4051840601510b582d400240e0740740c00b50690182c918817113003100443e5921703000e0b080741c4a00354143d0303070032000500d035031402c0780c00b4105114100c1e4420301c0c80c0c6003211a40e10900428101c24540c050050340e51006104020709440c0100800081c420108050307490400d0201d119004c82c0d400c80310444014803c0c8106908d94802d050501940b00000700311348800d40c07000212680b000480300100e41050341c031056514800201140d1100d02c080003005170030700040c010b801035504a88648112100c0321040d500080454100315045264015900c50401800b0744074000c0076040203c00e005001c0c1d403201c203030381e01030148681407502d500e81d2030344030100c5181c46503503101e045000648200149105d02d80d10b00101203c2c414110424616401901080700320480d11645040ba60700070101858445c081c6441e5000d0090060310130f06040e5a14102c25603507000707011210b400d61054503007020f180390490015000c08030b550004002c1040901420001030303000640c00f030b08060101c82100c500c0180307 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 516322050 1250 516320800 516320863
    0x112020d060c050426031c0e01050f09011401080c210d020a06110c071a070605100510020a030912080c030c070504050a0207050a080f040806010f030219030203 70
    0xd400050400b460100403205003940030000d4416580700000031405410002c070a9000700e0062010342c04150004c00c281810034400c444c480d050318400310300206034541e2502110b400c5940444810311404c500a00700500c82c40c0c02c1c81101c5502c1c1d071300c2c1e5002c040355050018066652001c3c0c411140036000c208903201341a85034045c80840c0f40b4102c0200d6000d20003905000f5101d4050303483c1260b881d801c25041811a403054000e440c0b41d0617080004112603890035810130340030015036280510b001810040100410400d001e020f100d0400c003c1c1840d4003515050510064189030303011082150072401141000a60080044d021105050140301d0300614a003452100d9101c1c0b00c0080501748000100c016072100d02080010896104442c10442a5a440080c006910402c0e6004016800504030900080d8070703030014109800e15905100e040986600006e49042000e0300140b00e8070040b58010811442d04514001d64000c0a00c04071008615580c00301c0e94684402d509e080d90a508041d03074007441e848 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 516323300 1250 516322050 516322069
    0xb0310152a080d091a07020a030f0c02010e0405150a03050109110603061503090304210201030e07260a020d03050706150b070305030402040b04050a1a151207020109060c0e090f0708011202 82
    0x100001030541c0c0c00c01b884040c1d690100b210044000ca4184480210f1503802494a80c090b00d80603107450000350782900170040144801400031030340c03402840d02070a840d103851000307601961190000148402180c20b00540c10880d640e40c032486030804000704010354070340362544611b8410f81d19002c0d44a03100e05203050300390302403038201c440011500c2e024111030315061190207000310f00071b0b01c040111140003c2c02c4c0351142050701811241c003800700c040d600308403000618400c41c5d10280c0180d40684880e90b00040200c0c00c0c403501900041c20100f40b880a116242c4141c20400d4031059002000070314040c80201d442c0200f08001c1c00380500800020159122504030440c8030303a0013002002240303000d0030858003c00c610406804500f400d9400039095050100c42d00340310101d00c01d089414280c3d140440c450582d0000c10840c115501d81c0d50300c400041c1240541c19003400151900704110050b001400b035441c000404000460480c2814450720b941c02410700c0e0f055075410a4043c1d000e826a0011030708100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 516324550 1250 516323300 516323333
    0x509030306061c0b030123181f09051501170613020108070e090c040609050105071505071106040303020a0806010f080c0306040204170109021503040302070b0310152a080d09 76
    0x50070071a01d0040c80111a4010f00400c0e00e0000f126859180c8400e042179003800d4071000c82650344410780c01086141c3e070744280d0003400b004272030208100d80c0c039560340390034001810310a28441039841c0050050401041703241840001c0b400041c286407803e0088440781e0340c0c0c4448064184504032000c00c505a00c1407032018500740001e40808410700341000c0c45500741e48940b080a00040c004840070425600c03483c1160910750300000050101d12100003520020701002e002c8505100c0108056904940c062000d13520890003a10010717150801e00c0c10245c40364400800c41410040d0401c0c101070f41c5504104484e81000b02259055143d80e40d000c0410000d01c290b0b0494035545076248c1000e4140ba005402c400102442611105050843c090b400e0203d0700003514010056013140c0d00500129401a01455200214100702001c440d0b030303255280616510b52030075000190098000159030558501c05646901d000b201d500703c611056280d508041c0101200201c145440394840030034807c0c440103021009 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 516325800 1250 516324550 516324553
    0xf090b070f0510060509180106080f01020c070f03120818011103010801060b09031b031905010b090106020f0c040b06090a260109031707181502010509030306061c0b03 73
    0xd04290805200c002844507040320359100d60440c01400c0e41031030180c80b0807540b000c2c14100440d10b6491f0444800040529044070329076840c13200140c4075808001d840a0083c0c030a000595a0104413042420503d9179045001080034040781040040c003c24008500b1050a02e802d030300030b441c1c41c031044119803200580c44180350f0902c403040c0d041082d1900218102d4292074002c0118958480c00340c10740c4d0245031005071b1701d5000760070322142c40d0b03101d03181d10020068014180e41c2001031140f180f00c0070100d160002c2e14142c0d513407011030706d090a00031081400340006000605071b0a042c601201c1e07a440850fa0020300070303520307041180f110751510001c0d22800e9000411004203591110003001c0f5100b085400c141c02c0c1986864154011641840b640c03c40e00d07015540c901c4640c540b001500c1100ea00a0800420014190045c3d008140050220409070003140303070700004c4c40c1140c1300c02420740e0005041c440e05a0820001d02400f5600d40c021030328200b03e140104a100500800d080340104140200c1c280c15 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 516327050 1250 516325800 516325807
    0x15030303070f020105060d12080916090b182703090a0e090709021e090f0d0c05101121190309120806010c17090d121b0b04030f090b 58
    0x210394005200c82d28032505940200403582c0c803401046408400b8210250083c0c00c0d00c1c0e03541405910400300319500c5440c8204540c9844900c0b111910710a46952141005075925000181203183c00088080c042c08445500750184c00c120800b00180a80c2c0d5451505a00d0b1050320082d0050f01031094418164006120001507039541e21203081665048540000b503000e090b10125286080348240c80c03010292110300e010320445a9040e580650025106030341c4250b040410166681d41e01005012031485015014040d5191209000000d00300948210034001024240b84412800161091605102e80c0e041c08d84030f01c4100d4041164840c10030f585040070129034000300c40e141c250f01f281d10350a21591503440c1d8415601011580d0a01c26181d0600280ba00714a040105d03400350b4001d9000c0b4040700500c1c2c680200c42001502a05e1905800c0301c2900c800c003020b40615402213007903140200360380c880c102d14844681e038500035403000500040034000045e1007540341c10b101c0c48151028140c4d285c0195603 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 516328300 1250 516327050 516327061
    0x30605030307170a2303041a09061f1e0f1202031902120607031401150509150f0d2c03040902070f0204110c070906060c15020708030106120507140702060315030303 72
    0x3683e1b0320840c2c085c0c0d1030f040c00d401640b0f42c048001c02c070148690109009096103895035030245010b041030050518120f408210042488082d0060081340ca070000601058180e1800340d5907601082c2d03551000a10052441c0c0d40c002580f40130419511146c2c0c101d4103c68640460300c0020041080500c919040340f1812080204d0203802d5031101c26030710304054004001d40c1e0382c0c1c041c000c0b010307801d030045000047c1c0622040c03c050522941440c181403c050f0501d0a0003d4141c80444a0304180c00d0001070b0ba0300c1d903a01c240d10012980c0090890b01a18502040e21610002504d40d248124881e0702d10560780001c0340b80a20044154908030168014810700c5044032082c1c15554030303044205400040d000d0b10100040c1406d0501c255811942d0940b100c5070b8a4401d5203540300030300041060184066001c203d540001034503e001140a4001501c545064402c0b0303e45c28030843c0c1009103101c3c148044030030713102c2d61035641d401034070130b110f80c1242d03034075900d69403416502c032940c10304100e268152201105021 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 516329550 1250 516328300 516328367
    0x703081b07090209012a050133121b050a09050f0604090c0b0706021207030501080f06010302030703290702030d0e01090f0215040b0703020a03030605030307170a 71
    0xd0318414030030440c0c4005845030110422403051100060100d454181d10781a20905c1001900c0001e040004810f42035900c1d0301e0311750a45d441d25131084400240078000c4a03011001101d124020030700000781c0300146080039002c441c0d2910016010b804201d400c41c00015010200781084060103014101c10750055450081c507014060659200c0188070344800001c04030b082c80d104101c1c40d1a00301c801000c1143c5081c1d9210025400b228041c1c0d00c240d02000300c46444048138250300d004e041a698002820340c54203030342c2c5003040c00c900b14000b216081400108096138000405100341c1c0d4104030b284e007140e16030982840703a890f121140d10441462071010481565000b2018101c000d00105050003018070b0020300070308882e20104028180ca00422011025007003107600300c940950f0180d511440c19440f204251625000310404500681c40204084100741e4180201401844158010350038141d10b5590140010803480e0310254020000c94205031081c45001030304485c0e11504910f0381e4000b200400032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 516330800 1250 516329550 516329587
    0x80c070807090c0815130c171305060c040b120618130b06062a0f1905010f06180b0303090d140114070f0c21080703150810020309070308 60
    0x103c2c00300300040d000442d240040d03248000104ca004000540348102c8030000801000300201c20010014907a6180c64410f0008541d14060a58044900c1c04884180b0b00546080001800440505028041044281440404c1d18281109540c072078048e070340c6040125a030240c1420000d6081540e0301e00b400208400710141c540c0d05401864003c071103070360343c07000d1040f00c2c40344d14051460096541c00d090560a0b0810703100c50130601310701c00e845941e2100d0000c5031815241c46481039200049210341401c0000074451504000b410b034005001880c40c24001c10b15482c0d81d510881070498642e149a1440c0e41d041c17003182d01c4044018501c0c00c49046605212020300340f200344404440d80b03030462a40c10501c441c030215103d1303080c9aa5000d00d9600d0000100c4d56485200d04c2240d58a99050b1a040c0b68002d01801081d05800c684d1082100d180141c8000d040d00d070b425840f082c3c0d180311034805000e0000007040400c0382c00744070000940e50341c036184002454000395910160803608085840c000b20440340303408 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 516332050 1250 516330800 516330821
    0x2709150415060e150903060c0322020916200a020a05181f0e0c07031805010519020f0613170913050c160501020408010606020712080c07080709 63
    0x8110010856200d5040d81940b0b00490000c00e0354203480c1042c030314141d0f00c0ca40072002520b221a00740020300c008203190041c15160215106004010001e070940c8200c0c040705981032a140c00c3c1440c4003650049041200b0150545003045500c0c0303010700c0b00c607000b588501003107403120107038440c11003000720140e4079614000b000301d1103083e14800020b00707440d0442d5030044207260840c60315101d454070280c2402104541c00b078180340b1984164002005902d11031040c0c8200b403080c0400b6622400d03890010100c081c100b901c040b584800a009104590744501a9a0b043c1814203800e01d510004120980c075280150542c03007100d2050004109440c445080419610ba01c140c80120411280d00d0008001b0300a401510790095500304e01d19034400050f8000b40c2d00300034400304251500001181c020480e85216209840d1a1f40000e8108a0702d5400d02c1900020401d80c40641a22810007a0404007400c03e000007a006210106035040003030824005200145203a60489196607079815140000c0d0140302030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 516333300 1250 516332050 516332059
    0xc070b04030207061106010f14031219080a02070507140a1211010828020922090209130302190201090518070305160e090403090b0403080309060a0207030203270915 72
    0x24070500400009105061307905120420400380d083c0042d025282c603103800e27107590521411010740f1016042000600c1c1c0c0d44651901c510001988010240941202501070040d07540304101c1e4001180010880005548100103500011624040010000c04082d0440081e40f602e04031400100450346240c030708229003e0700c0d0312905985807101c02c180c806203030b405502c0e480c1100c01c0d4446c401480b03900804d11400001c04280b03900104107204803503548444003c581d0540e07240000d000f503103010086941e1001007190b801403032648542d0000d407500c08455200c020610203208100840e80100c200d9000b03003201811501d41c0c55100e0f2002140035801303684c6400443e20701400300e0b0007445501032503800020b540c3c0781c080c1e0030b2205100b0b00ca101a8020410740c20045021000305802d500c0500501c003e50261000301d45a0510f560b00d942014009410b41d40240d204000180000b034020003a603801c85c4a20210f0811911003140d040006a541110300e82d009003c030041215203905d00e41c07505c08015056a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 516334550 1250 516333300 516333317
    0xf0e01020c0c1c080702031e210c120906090402160b1302010e09100e011502010b0901050108040209091f051f060504090f1107050a030f080c120c070b0403020706 71
    0x410700c002c0881c25040f0703002c02c01800c0200b001080c00300009149030b41c4007400f16031f00c3c0d5418076180d480e407455481408445801800b004643c00c28980c4485820210030000c040c64142840d10150391250412400400040c0205000c640c56540e10305176601e45c030303000e0003d41d42d420140d000b0703a844955a61013110010030190108404500000c0c2e40740c80a603040e128914400171003c208007210340014404504c00c845080c000c544003d098616034024489214003002546100d88040c0c00c1d1540f06815602407000d040040010f681c4c00514140c0068040e2072100c1d43c0e8403002c034054104075640070760300c110400e031400401018003182c1c80140f280781506411001c14040c401686c00810041c41442e000034414031052210106a90090032403005080c0d0000381507966100035043e541003140290341030707000411414145901300e401c00508000501d440002490f0180140e0914010104d03021149020000041e480e12251011140c1c800d400c1061040703180b5081c03030000d50343d000c0d41c080d4500003000701d07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 516335800 1250 516334550 516334573
    0xc081513240801110d0b0d0f030527031002070f0b040c152d03140108060a0c02030403050a030507030504180f0c0c0b0105090903040b0a090906050a0308030a09060f0e01020c 76
    0x604c502141800340054403442c001c004104800904450404a58081d2410302c001c40042c1c030342c82440c110a0b109445a0751a2515400000810082501c1c105002682c0c03030800c100d55600850b0400704000f0000c401611807800d400e02c000a008581d8000b490804e4050500040c0409a90020119180c0210804c041e080c103510403290809454032908000400c0903100c4c082281c401c4004640340e11030318000580e140c01c60f041402080b000e0b40301000d2500044240010784090740580c01002c143c60000718646440e42d6a45030b59034080c10340260030003401003825020035110702d04840003001110410700102c04440701810080c0b003281d030348440717161030a4510301d14076014488070f58140e508069100040e078601424080c0d02e42c001062580240000c22002c115000344001030301e0400301541d9044101c500f040352400460b405604064824814046c0820014141d2401c0701c0d03104140100210301c1841d941b500b00301408034828403202c0d460606c0f010740e81130281540900246003441c001c45100c61103e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 516337050 1250 516335800 516335803
    0xc070915152c030717010b010903020109060315090204090b030c04060f030602090a0801050c030702060105030a0f030e1539030901050304050c04060f05130c0815132408 74
    0x8034281070118011030502940424503007244040301840d540054031044034080000d0600d00180c20100020f41e80d1002d070044070009101741403410a0a007000740100341182c002814411003071185000709500c0d0502c100d031807204070a40c1001030282c85000d644454598980348094914134201030300903c20458920308500e05409148111100e040c418004036065890b444060752000d900c10384c000400c914002103420092141b64890b00c0500801502c1c0d04008000909010040c0e20441c030030b40c05000c1c004041092100c1e4101a645d060524038588001c060200d41e503014200c81a410142002c5201c418510854226524265107074070481490241080c141690420440341c03081c10340e0080c0403100030343d400341d0010b5030001c1c003039000c070380c5818510f83c002019030b00b5940042241c41c810030410410350402074103031030889800c4003060101d803211020041c0050030081200c4030b800c88011074400c0c1a210802070b0b010807000c809051040c0b0001d41c106040310030741040081801c5420503000a00d8020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 516338300 1250 516337050 516337079
    0x105040807060f1e11070f140d05031b07031704030201050907050102030712030509160308270f01180e0903030106021e0c01080a020c1c03050c130b07080c070915 71
    0x520a04003184e00c03003c1c0c0360b10003400c00c801c442c1c148000802c88100801c0c8820440f60419108144000c00760340314010150810107a20780c0c41c000d000e001d10500405045101c014480300600111640c3c43d1049800c049031980c2004103481c88050000051000380741d41074108600c1544440219001107a51300300480e40c9205011003e401c5000f050121061148250811600300d200002100c4500f0100e68040110380c4642d80211444400003449200c4a501000b01a4001c881000010240703c01c00c0c0215451400c8804a24100032003280c82812650011900a010344550300c4186a60b150420181c4c4e92a4403e0081c1170151080c2007160309203491400f1058800b5208501505003191840b0040d00c62a8015005070034040d0240406092042c00304015442030a01d8155614100496000601100c1000d0302c58602c0d190100451499051306440d44001c6401e20301ca082d9441c040750500718458080d496480c5041d000b121000512142280c001245280500c03400c141016969011000c0d80007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 516339550 1250 516338300 516338321
    0x50f0702071d1801060f150306060807052d070503030406060b030403200307021f03052202120a0206040e1501020601060f030b0a030212070e0a020310051c02030105040807060f 77
    0xe11280000c08540f0550041c11105041100120702d4903180e404042500402d80c200c07440d034481540c0f00d62001541806090300510080c00c00046a0500241c000c12512549280b000540c0c1e05a41410040e032002a41034604090500c080d5143d0b5928a0290b44962055400b92800c0382044004542c4580d41c03022640902c0d45a1140c562310048a8040341801080d0011980c080c00140302e03400160302c54002545400c1445105c1f041d41141701390018080b11005004484500002a002504142001301da40a101e4040b0341d00c55480e42d00d0b5443c0380c0392084001000750070090115000484038240204140610340c02c1075110070700070000c1d00480e0303514024030654001030804040c030179403103000346d010040081b030103414007222035201d401184200c000e001d59180160f11000d0100300c402421090355800c04c00003901035155092140910b44000c0440c011280300d80746001c14442c030344c01c9e102d4003004540d0380540280100c2c60036080c4010143c0003642d00340c17100c41c208944000080c410303105600d0103a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 516340800 1250 516339550 516339599
    0xf0f060e1e15060708070b1b04050d0c18090201081302010203070308040f12051308030702060306060a05040911040323060115020304030b0f1b030705161104050f070207 74
    0xc507a104a003100d401002d805484107001c20104029240c58010041420a0286090720350f01c4540f0300d89566107403002091000028a100c1c070703400c8803c115030125001c4400c101c0d110202042c1500b011174216005a104031403c08181681b060032072119080342600c203000342c840d17600e00c1d5140d8651210746451a0320090058008010480c0080c2c0035500090b00503000300041001c0762000d40c2c411106525100c440750100c2d0b008240f00200180804405018000d0400a0b60800006a001c0307059030102900440c802c040216011984d64032034001c0d10028504110f041c400d84910f541b0034485540a4001075a40c00403404a658190348035881d4401d02003a50301c02055143c4ca0415a0142c580341a0701480c1107002c200000404901810003403070040f21804c207100064100812103401d10540c185503035044400510402113104d03040400e03070301d60820511240c4181c1c4030b503140401c507180401e041c0680c450311740310a101d4680440075904e8403c03405034088490707403901d80704e082c2500c090400d02a07100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 516342050 1250 516340800 516340831
    0x30403080f070509190807140a03060b04180c0807090204080a230d02160501080c040603020c01151413331203081608060901061b0203010f0f060e 64
    0x1c900c070300c1030019800101458800d04145110300043c8400c4d00001881c90342c1005642c040c8490102400034170000c1030f071100358600044260001c1194088244405060f190392014030b11081d850302e401401007c0b05455146840b010241b400c00f901c0c003414060403c10748260300d004945183d00d40b0845043da5401030013805010142d54070300408a5092440f03150b00030a4090300201e00e07204001e050b9040c032440c1c024000d907000c08955582a40301d90b60106041210882c240800c82c2001d1040b501500c1c01e62401580d07a44400c81d4680c05002800341c420030340d02d181e1100069a040089203041d0054080350780e15507000e88000680d0035a0400b26403254070312100a5071a0740700352101c100b241020640400500002c3d0340c0c8001801c1e149044400b5404540d8100801081c958030100c6c4c00214400f50400200d20b0400c1d002185000c901409100c040c4400d0403400030400c1c0311045e4040c8010f5006000780880d404404040010300a0b030003000c0300c03181c01d0000c003141c1c0c190030505143c890f540d208a013448 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 516343300 1250 516342050 516342061
    0xc0109180f0f0608070501080903070804120302070f09020a0e0109030b0c16051605031606080708040f170408010b030106080303070c08070c030501090b160c03030c1206082103040308 80
    0x40295038112000320750707540b80d400c2c002c445501a1400400100c00030b441d40c14a400009084600300610307100c69a042001944001248642510251004682e21000c1840b89180036407034246903411000e400a1025400544194150000d041d44149aa04c1c12601c2c0b00303070b01c01034030702c0780c05800024040400340c400a003810081c50040c112101116208074809001920384a05002d049480c101c43c1156000040c072440c1000c116101340c1ea1000030420311210720b000b000804410010b0406001c20603880c000c43d0902c859030311417142150b00100705d00303c0306003c809003a115601c9032007041059402c0030840742c1036141c184618012201040059855655209821a9240c0740d051f811148840244074181c08107510a03d1980a540300703400018104440e8204207007910350082080308a0b40340e081c50a41415400300391000040c0d03060601048111560328151021001103402400c540e103050342c0082c840300000ba160308541e4140b440d03250070300c2e40d9080c880858401114003402164032240032a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 516344550 1250 516343300 516343349
    0x10020d030b03030d060b12011a03040201030b0105091806030f030403080306101701030f0b10140f030712230c010c0311010f09110907030621021f02030c0c0109 70
    0x840c0c4070000c040c0c81c0b401d000e8404c84011610b81d50840f01c1500804102190010907460905015110011051444400181600d0010710004100034101a22424401182d90041050f5000d4040c000d080c0240b101d414800c0d100c00b2482160f07054488c2c828090114814900803049070217036900860814510b40d6080280034420b01400d11000420041c800c4210034178048000c1c040c0a10b00c00c2050300700641d114240075269041c0944028030711310440e50100503d00781e41c403544138010029144c04099007030000c002401c140013640001c040d020300c002c02000308044448255460603005045550301c040c901c0e102580c0f420001d020a020a50030805440400d002c4c00710065442e00040002c204000c001068005072405900201c0760740e8500c0103521032514141010692200243c5070801085103048544c403c00d24400c003d220f41140032854010a6440782c000e1119000e0421580324080030203610001e40c0c940c840420b014541c01403d0320301c0125031007003034a070044407000080c1d141d1200c2688002ca = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 516345800 1250 516344550 516344561
    0x904050d1e0210090f1209090e160e060103060503030a02070303140c060f09030d1a01030c0221090316030b0915070903080a030e060c0d0b01030501180507111b0a0510020d03 76
    0x1e0321800c5d40d0282d080000f0b003030014907280400496a4412030300d80340082420640381c040d03004000d03540121031400d000e401d6a04d5403a0072900c03200c115040c1a140c22005800600c6607402447d098003000400f1403041e9000180401102d200c1e50381c11007089041c1180d4010b9000f4074003850140d401c03250200c0d0039210500d51043d08800120181c1c0c1c9081324110b003071012204000140100e81c818940d05041d250303018464001124030500160800401c414200080754070312021402d240240490110820b417010003040502c9a007500e114000d49440742000700310100200c40042c80c274070900a14050700214a0049030062406445018205003103990b005107a4005054507002c0550754182084403480802140c1c0c0988045010707030f5554021503021078151004164001d040c141007400401813018410800c2d40503407800c1800007015120003000b1240303401e18001c030040341d00c13460349614041403000c10740741d144c480100c030800c61140d61403051011948030310f030215025811004000c20302c90300a8001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 516347050 1250 516345800 516345803
    0x414040b090c2803050103230601051011030c0c1c1a0703270c0807060e10050405060f090a050d081b1207030801180501050d1403090904050d1e021009 66
    0x300c1d81189561a00c00030484210f128080000c3d40390001001440340c180d0441072100e010342c5039000b94a00711000c240d5651010700c6002d0007848642e0150041c10b01c40e00707548044038220b5080d03d584404a282c215512183e08081307610608100d440c06100c84805188410601e500c00d0390311104a41140f04c40150000052848040c1920348045141c4850032001806040da18100f61032803010782803c003000740d9803154120204c1580300203003d01401d0742040c041411030208903510301480040c4803040300c140c0103a601040d0010300100f030601c850350b11080684840002601d8204030140d4942c104641c68445103070103880c2000402c03101445207621015951504580c03c1103510302504007842040340d500c0000250f001460500040c403c000b00c00d504044a960343d0681400b02d54108000110020f004041c0203154518403140440d0542c0d050040d1804a030004005418600c1c242c02e225844050244110001404107600403620941d00b07101103840c1c1400d6801044901210a02600100b40d603c4c2e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 516348300 1250 516347050 516347077
    0x102090a0e06010306120b1e130f1401021c0e0c010503010b0c07182415080915041118240d0210022b1d04090c0305030414040b090c 58
    0x2c001c946c00e59041d0080300707801d100309401e00b043d02e030070700464a0000c1051040c0c02e41220400c18071180201c1000100692604001c43c00c0c1c0400351443c00d42100c83c1c003202c1c031100c65400440c05108195aa843c000c403003100d00841440144001c0703020f16140c24041b682240862403e0006206140c02000505001344800d0201c44c1c40d6521144500c242100290844400e640c5030a00b20310000d030802d900385404514030400007189820710040041a11210303035648200484c1000141480c28100600040120b03072403407003021030405080c48070b45001102001801a880c90b05900614106000c40b02e104840c200e6810801071182e03075000004030f01c0d8159160340b02d8001c003411000341e600c0064034440c1e811903030010b007114002c0c00b00c455040400004912a2080380c0200380500b641c02905202c030802da2602c44881d011101c0700060020146841c02400c1c1d450120404020824000001d0050324900c0d040d16a10814000400c01a039100551041d00160700b60041820f0b122094041c0282058800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 516349550 1250 516348300 516348311
    0xf030c0a020f100203010617010312050c1e100606020f07050f01020c1302250f0b040f050d03060306050604020406050d020918160e060c0604020f03120f19020102090a0e060103 77
    0x288000d1905501a103e5030045600000410a868024440f40d4200c890006001010740c07551700c40307030700e05100700c5041c2041c0f1100181030003907114148042411070038104200504c051003d843c0710b58584018070542801840c0000208403180005482036022502c030005149035070a00c02480074180c00e241e41141540301d070a100f400d0740d03501c01d89407091510b000c801c01038680300e02991060744500d07403030300c0318603078440c40b03001c100c00301e1030b00604a62000d400543c0f1141c6500e880c50004020248404003820b6402503540111019905070050001c91b80a40400c2c4841d80b1000100030492050344643c2012403810032440f10050a0340d0003a00c0b000030000d000c518071160100d04081d9003001200c03107500b00042c1c50881e0698a40003400841305e45000e54103641802c2c447c684107503491601600282c03007180d9600000c8950750b81042440c2202102d40c2100762562284446080740380c005c100041c50400822091030102403051096441001000305480d800d10300d002864260100051300e060304040e1100d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 516350800 1250 516349550 516349573
    0x60111070b0c0c031504032304030803070305090105100f064d03070809130603060c030b011709031215031c1b0b07050c010b0315040201020d02030f030c0a02 69
    0x100141c088902ca250250496040310020542407034000703008000c581075000d050202096104008580c202c5100c4d80c1040301440e1642341384a18001c03580300400d002c20010410007040c3d410340043e0301801c0c6000080c00141c450700b172030080205550003844244550450100810761095a2000c10140c0c00e84032454442280c0e1809401c0030003241002c121100b821031051001e45a000e500001c1c03d900001031828015a9036440303203140303da200894400c1040c021054640d0105078400c400235940320310100000c022041018000e06100400306000c41c01409124023114070b90a8450b00c40d94103500510314002d01d15051030300750500a804140020051513800c507045c0c404102c01c4451080844d880302c1900c6041d14000c04101c00402c0c0d203244004031003a600001010722105a4000c0980e00701103481c1c00c0340c403401c50300500c1c10140301a03240c811030310307840c0520365090002c0e070080b4005e0703090b03c914540012003a47c1c2c81c820b43c40130307644900e000c10010f0100144000903188a02c01c1d44155503858800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 516352050 1250 516350800 516350819
    0xf0c02120f04080a0b01030215090f04020a0509030109141603020907030903140406170105030d0c240603060c0905030307080a080c071506060f020109020108041b2301030c0c050606011107 82
    0x16408215205c44810006000394507041c0c600c901c1c1c1c100b90300074042c60101ca59010400712100c10100c80c0c002c9070003007202c2000500400960320940300140c020801c5c10300c41c0c242940d5020004800c0000c5002d00740c50b040e03030310031585c001d0300a0b41e4010b002d5007540e0b2664502100107041c14507068007005036030860004501134040041c03008185030341c0d40c11611034200400c060014411f902c01c034880d520000c10243d0f401d40098070080c10301e4014072012002d07002c06e81c02c480e04409a0918880d40b502d40003012007000221b5219012001d030031360f44c851040e80c941081c980e49200380800903207090030901a05402602c10f04006a001030070000300350504071340350740310f10500f02d46042210303c0c5070312110705004640d400585810002810300c020301041c1c0742e80d00007030850034000d08083d141a20ba03800c00b1804000d182c26171002086099030306c5000c03032044900c104940480303801e050700190030200c1c008041c0344120b441d01420740e0428007824080d15204011b544081c01e604200c20103028840000407810780b0b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 516353300 1250 516352050 516352063
    0x1050a05013f0c150503090706110a020d0c08070b040f081504060b2e180b0d110f21060607120f023d1116030309050303011401030f0c02120f0408 64
    0x4c03900c0e0203841c0d0074020340183c2010070b01e0700000104000f105404d5840c5c070000034900c0d0aa901511003500845a504000803514016007000e9041d01c40c0c81c000090b007201d0744004004035140c50300c0100859854500f80e0340c4400905214020100d90040820089503003075005415202d4028a0840f025086004501000d40300030302080b1101d242034480e40e80d460b04440419031407a0121403a030708040c14078a4410f40340c05161b50f6001301d0760b0340360034020340c0d680c0c40c2003191020381e5815a8580c4a08640034005c3c0380c00703400311004043d0880080816600d0811101380ca5100d80e200403030000428200f001140d01580b040824011841003072b0429418000445211301e03144a90485500912007540003c40c03c00002065000160302e00911100d5441c090f005848595038480c01c027061009140c2800c501500310904044c165002c0040001140d15210803040d000300001e880a201070000007035000c1c1140d07954a8540b01503080482d00c80b100001c00801800910612008141440e4446038200d00e4500f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 516354550 1250 516353300 516353339
    0x40906020c1006080d0e0103060f03061d0604030509060315040e06060411160b0c040f0b1306171504090803190b0618090403030e01050a05013f0c 64
    0xa03030004035900792110601485490414601e424800b1a2409500f1541c64080003181e00800014008044460380b1035000000189040424042c200b83c8030b0800c00700601d6007151a0208101c00810040303061800300340c1500c101e805480700d41c14601c20a0a01c801d80d44000c0c09000008000c2402c0e050550391742c418174000c2c03036052000381912306d840e031f051000f1200d605195450405061204002c1c042803d07911281140d0b21640e4805c0688424007800518051600030511f440e400b0b100200d941094840600845d28911a501c44156074950013070380c0781d0b060884008103514185000a03010b0b070028400503a0100b0141000504d15000e440e00261500f003035602e000008044000ca49081800740941c0181c0c40701202c40e9441c14143c800e50880c00c18540004074050089040010b00341806039104440c0289040c2c000e10043c40c00348800e50007032009000740200d0203507965a41800071003201d20103220841c0c1280c10385081a1006009001030a030b201b04540c10fa03103a90f0301040026404c00c24103c280c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 516355800 1250 516354550 516354563
    0x2070c08100e210f0705070810020306150412030e0f0a03060b0405070516140c040c030902011103040b0a1202070c06020307140102030f060603060d0212030903100605060306060c010b0409 82
    0x120b408074001428010340f0a80d62502041d128145026001000103d0b000d03101130404084d610259407a000d03050041980c00607a0f070b80100b03a842c170003080c0290000d500c10139044038425020340404030310481502541c051010002032007045240028080d0002d10310000008080040052030780001440c64000c0c0d42003203440c0c545501d08031120f402e081c002c5980040503410000c2c20f0201000c4814203009840c00054070038001800043c001600506c0b908908503c06041888420401c1d072014000c1e04004104a0005070110180b518400000c41503d09070340c403207007030b4a01d0001081411211031000714507905146070b00304031040c0024240c5404c40c00401d9550042c54584109003000c0305405407401400c0c8140e4010820400e081d030002c0070499114070115022038417030721a100400c0840c16005802508154060388450580b03900001618603500100d00702d840c0700b000400110b05440641c85940d8000c0c80a0010031114030f042c8000e00b0341e403c41800001080d03e11040024140c50f918501a10380 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 516357050 1250 516355800 516355811
    0x3030c010c0e0405090d0f050d1b020d08093d0c080108010c050f2b050a0b03012f120a0c1202030f01090b04020f0d0e06072102070c0810 60
    0x2a50304014691020b500443c0c08100b18900309400b240c03940c81c162441000c2011507907110000c2c0d401201624410b80200d0070420911402e0065980500344941c9894098400c80694000e1207101d10f0201e0311840c1001c1c050280581056802c14550000c01c1b5503611008500007408030700681c2d02d25102c200f8480e00f501141c404900035001d01040b030306800c448500d0741014400d4000c5074000d41101da107500c0ca02c81d05659044020400d00442c0514072000a2044080d02841091502c81d00f01e54051400f10004020790140501014202e0303c8014110302c00c01031048030707101c0002c1209104810402b00c680c070316250007807078060070080b030000300d48500300583e40c0c000b40d42440b42e1003c0c01d0303545035100c0f00e4118654105102900740d41201441225542d6071034122010080d01c8a4055030010318000d0b000c1600c80701d01401c1000900b000c00070488072842540005076100784100c402100504001a0700841c0c9403000c14020003035800040241d51000d121100010740603006c1080d03508003440600c0000341c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 516358300 1250 516357050 516357071
    0x80c0a140307170c030a080c041e050108100f0512010e07030506040302060f240f030304030302101512031d1f090b04060905060714070e18010507120c090503030c01 72
    0x1c030030300000040d0040302e42401403075004100041161b440c1c8006040c004030f95611003041d41c03c80d10568010008298071001c4540218410750005010340e403003603c40e41c00329a02c00c00101e04981a0388070382404583d10301d0302001a41461450900b48026030800440d41c0401c0b5aa11444c01d2443d038012104ca602c45410042459410710030580c00420700ca42010850401203030401d11001941c2d80001c41c000000148032159035081c2c3c04100f8554040d007643d40b2182d517410003940300c1c103032020a041c01c5030404250000b58040b170030000c011348800301f110381000078840d14119403141071140b5042021000d8041f1500c56545c000e040c4c210300c02d554020000402c0341d46401449800140d016480d4202e0a000501107a80c120035002d00b0786a0545445407204601d041c0b400c1240c0351030f41250841d004180ac0401c2d141c00003045daa109c4d2003a00c0311548280e064181850032503400f2901c40340041d00c00b25175072608402b16040401007082d00e251041a1035107800009056900c03002c86003055a42d00d000f10324 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 516359550 1250 516358300 516358313
    0xc0f030408161a060f010c0308280b0307090b0303120711012c06010f050112060b03090d020f031201051215070206070e040b060307080702030d09060c111603080c0a140307 75
    0x158040005c2c0d03041c8060000b404000b030310b48001440c004041c060710a0004681a4600c0c1034132a88010700c220004098600d40282c100800c3c049440070300a006521002c95a44d0310340c0961015681c025004606e41602003503140b00101c000340514080011030305100c3c9a16009002e80745102018001e01044021103040c0c65242085040e050301c0c0c507804c0300004104000300c130782010048030700a090041d011036940d08038200030700043d00b040c0c60003103001c010f00080e02000200d0142213102d0782c08440410218036952135403030254500c825200c040b4000148114108290490005580e1404a42003d00050002440104111104001644064200b007007640d403001c001c008510007980d0420401d000c04c0089005d84c84000d0044052101d624042800d06108100300e4611462040007000740d00641d14108c0d01500549501c800028583d03880809503800100d0ba850f40c3c070f100901021380445c55590740b505c04c1e4200e05642001401039054190114864402102090803404003656488689203050b1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 516360800 1250 516359550 516359603
    0x20406170708040c0e0c0d020304050d021e0c150d1e2702040203040804050d0f0c0902030906130302100f0e060a14070305270102030a0e060c0f03040816 67
    0x107020010310340700780004034401c0c103007070400c2d01d17902e810003001035440510344c082c00c0c811199a420143c1c80041040309004000c82ca81203108202d0342500e10244104c0700407400007840170b58025070358000815412982ca4400c02034080300d24044401030401c0c1d147c4200388101c0300e5080c0e20300c0d0805d06581540c81d038010300340f0a00401c140000c414407410001401d0400c82c40c1034102c002402190300201040500150806441c0100b01c02080030a0450309450000c040b00101e01c0c080710003801c0c00b00041203005060091728442d200080c01080300e40d481c00d0080f12614161358086d4158050000c0003400c0140318007400c4e01284842c400490420080d080c02c514211006100400e11840c14800181104c240702c00230f80c114249240200d1251241008a01c0d80c9071020b02800100c5600b51f021650180190040c61141c80e180808100c182038400e445a01d601e02168515040765080000110702480003001d1904180258886802d102c11180315686c40107024000b961a1658070070000034002d0541ca08 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 516362050 1250 516360800 516360811
    0xf0102011802090c0405090115020105090c0928150f05030c0a0302062506050f1003020f012601060c020a0b13090c0c0609111207150f1202040617 64
    0x8000081015a0181c0380109500d0002d03c90072110000ca80004040010350f0003030a0020119001540c5d00d50860403d144031103000c1c00903508000c005100410301199405803128040c00c0700382a951b030641000012100824000002c0541c0c10100c050b800701c40c880c0390103000c1040c48540c1d005080600032808207280358400b0b8440d81c01131000701c2103900c0705886001120340c10703114561100c10032058849029610080e114030388058040740c40900c54a500418003e940d270b00c0c0542c009840e00b2908840d010305a00010b1b4000190050000f080e501c5415096650030800c94029801803610060846006080c3c0c003050000f02c40c0c41104c0c0951030889140310041a02ca071b440e510b0144000080b2105410358401d0012160341c5c0c0940c28029401107030241d0541e584010204030851040c80c0c1241c008125141450140b40d250000303040c444000210b01050740c6101000d440c03c050201811992107058001200401c8032100301140343d40028006040988195102c4885080c4503464000c03000c900240f1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 516363300 1250 516362050 516362053
    0xd030b1c080a0309021807030b04060902160b0c070b010837020f152106030106061e1403010306061a03270c06070b0604050901090804060827010b0f0102 67
    0x150000100d41d0021505149041d0402144400460001402e107907801c000100c8601100c1042250075589503000d003042c6101250b08001c0d00e41c64410380d108a000705c02108600e402554a40c0e40810410048180e200f4010b01c04240f0b000c3d0103a030341c0c1c4001c20082c1c2c400e001c1c41c3d104001901d00d21404200b8421800324a9070440052018a01415105500d5050107405074152850488003500c4411120104140300e214041c1c0c0c80a10150b07100034101c007001d003001c0003504000070801d24034045c02014101d4400360340c0c2c21103101d01542254030310200030241d4410311216502040d81c1100d08400307140218015100094002d20b44501003c0850303100d50b01e403441620400400500d102c0c070088100c4406002031400ba1030000301e001c411f00d4070580e0061070343d00c5a000301d2954100a0b003413a14900c9080301340c500340b0080c0c82c2c2d00043c50980717280700c0004080080034041403000c90b00c1400c106602100d0b4520200700051300c040e101c0e642c5065001c64070a56515400703512018180740b0740802c00000d0031720 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 516364550 1250 516363300 516363349
    0x306022503140a0311040e0601020709020c0a02040b0f180702010c030603021c030e040501121e1a04030318080703080609040b1b131d010f180905010e0d030b 69
    0x940091401c0b080040800251001240031090188654001c0d40c12403007607003070b156035151103082d051f14020088071028014800e5030000f0456190300d0096416001002004180c0b5940325400c00014001000000ba001880806010b0842c0d8400104101006141a05c0343d4076080a842c000c0c02e4508025929045c103080070b40410058550362100d1409507650b8080d01d2640e2014602100c1e0107020502c0c555210f42001c00128400078907203519190203201da0300c13a2020001c0074441c0c043c2254448000fa000f820058540c0031001101c071041c0b58040c5c42858005140140d0001030304200f2050b10b0192509000070401900305900300c81c1e00c40d00040100d23201034148c80c2c00d50b0380800c1c03048010001d0400e0b103100d5011313610781c0c2c00200644011038500d11145146685401500100ca082c05100b0b041500425000041101c01c003401d03a0240c420030715009407101800741020300500351310001180e0310341d030348d0075040c2440b40c040c00b00703040c3c81d54166000704e609408003080000310702c0038140c18400c4035803a6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 516365800 1250 516364550 516364553
    0x3140412020405060d0f050d11060c090609010207090c080a050a1e020c071710050612070510091205010e0c0f01082202060a0509040f090807030c1b03060225 69
    0x39110168140d040314041450f50f07590001c0740450003402c0c2c00405031000143c20074100080454003440c09801540c40e81c14061404484950302e4109460701074021004010074899414440000c0c010020180100d403211550344240038101c074921410000040d09000c280326178161503005181d000013a008092040071840c1c02801d100c54210b119800748158001200e000c00c2c00288010300051481717200c0d02c040c68003031502c2513031101c4e43d108035401e02500c0c0c1000203c0c1403500d25920242103c0c802c008210403400c00d424070001c644080114800c1c00048000000e07404416240003201178403d0f000407079141c0e44000d040d80b07400c8501d00000e10810b062808110f02e640c1c403413042e136030082c0e03030200f220240152981034140d0100c189002a41080001401d40310483d042002440349190955040040c0000300c4019011100040001040741108228600100e13201b021400b10380c9d8041c4c030703070005c0c0c9945419040f003142401c0c0d40100d40050f00490035518082840240315541800314101c0b803c2e20206 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 516366906 1106 516365800 516365819
    0x12010e0f150609011a0304031806020318010e0607080906040e07091410051207030e031b100501050607150f020a0e0324060112020d051003031404 64
    0x12200450480d007061225513049036018103211781c542c880a005d4038020391011740280d0403c0790300006a840d09001180c503400610030341e0001d50f80c402c2d100701004100403080070340506000800342100660340320038003110405e541c1702841c0c1e540c072080040002c0039405550803c800c0e5071600030070065401c2c1c1001019065550f0380c02c0200d8501414020092904a8802c8100c00220148090071001c0d6246c0c440f6038000d04541404542c6500d510621495600706504628070250742071000c50031803038107020340403413064120001c0c0519130501c400702c0e00920078000018404800003002c442034100550152041d20b081c04800e42da2440c9580c0002c040c5647c41e41c10070710900920989844045005c420b007040310200b800c0505084d55554010340b4242030004841c80c0b81c917000c204040480750180f1070076108442c160080c203d21400c50030b00070401d401008184084001c20081401840c81 = true := by decide +kernel

theorem cover : BRFrame.Cov 516187050 516366906 := by
  have h0 := BRFrame.cov_init 516187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 516187050 ≤ n) (h2 : n < 516366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
