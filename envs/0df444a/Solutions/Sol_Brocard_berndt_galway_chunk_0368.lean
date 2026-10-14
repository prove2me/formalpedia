-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0368
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:27:09.266886+00:00
-- url     : https://prove2.me/submissions/552519ec-2a06-4317-ab2c-d6c8bd085450

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 66007196 ≤ n < 66187053 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 66008446 1250 66007196 66007211
    0x605030a050a0605010e0f01090f0b0714031213060e0d050a0e030303011410050d05090102190203090f01030c1701090e06010803040e070305040614090d0e10170901060b0a080a 77
    0x543c454241a641c05031102e1202075181014002c16460840032241070080b080400302d40365400b4500c400042c0350441c4440d42d105801c1c0742c08591490085011100382d441817011180391101f00f5060f95220703548000c040c04140311401c2c40c42c0600b03120650f840c43d50103104064510503038004001d0100345082d07290b0400c0344600606166403403000744a5203901000b102540c403054a41402c1ca040e200300c0c17178a0b10504050440480384200c9805480c0e43d00f41c0da50014943d040d0002c5c40310320441821032400910700781803440d40814854546491024101543c80d44500c002e1070158003180c11070010940f203112150b85400344000203090307100300d84000b0311684000080c44500001110f0507140ca5034907107030b004c0d120128103402030301014008640b00c07501c8441c5100841803107032a60b0721447d02c20004100000010101500120314004551b000304d17204a11984260307000070b40121074100c2c0710211003103955032120803401400960000ea80c0c42c20f002a40000a40c0e0001d400350084025580800115 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 66009696 1250 66008446 66008461
    0x6032a05030a260c03040b0901020d030902180405070909030302040f0b131a090d080901030c080903090904020409050303010303081009021312020a030203063405120a060305070605030a05 82
    0x452001d10010300035054201164605400f507007440303540c042001d01c5103050480e0500d40900b0340e08150032100803200301003101d20036582e04100d006020b0540d810304100090541d004071304c81c1420b00c0030040c0c1150040000c10304001040050500900030403c04101150180c5002006035000748500b45111100440214250310100115a12009203c040d004404d1809040c6606055113030a0511204424414140c003522801c0c03941020768418410300359a201040005000c680c40c1c0001c901c2040304001c10800d0300302c030000c216521150100e41e410301617515803000601400301010020240d020103c000410560441c4000e401030b0030f000e462406554560940000b240200c903401c4081500c0f001c01008038103002c100800000707001900c0e9407144c0b43c490700401d01c1c040054030000004442c1e82e203844100c02c10f25423034102e039220301e00c370f44501595034000040c0301d80101e183c5032a003140040007040c0c1441c00c540c0940e00a69100c029900307841da480c5000f403c00d4004840080301d0a080100161a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 66010946 1250 66009696 66009703
    0x1809060b03060603030910090803070308010905090a020a090b060409090503040e01081c080411040c0207080c150702010305100305010c03050402041409070b09010903140a1209030b0c03040606032a0503 88
    0x1010054015800d0103030003420000544c120700052002d008c011000443e841d1814001000214029207070046154074046040044038001081120b10b6040700c810300d40144d03503071032714102201c0c401000804d49540f5040022054440ca0b88462485031618014408112022001c1d201301e07040310300c0e04081c0d80e80e5081250f88070729500d848104d40084959000c5013050240345410b81190080e6005103100c00c0d00c201003030403125a1008400981e004c61010014140c1c2045507084590050b40c1d03180c2e00004103c11000300e03018492000381030580b504009031803220703540e280074000d540000090080300441503001d001020182c3d0140c1c0a1800e0241e10909080e402010034003407005900284582451b088080c0d1068000001c0d86042000081001010650145c40186546a800080c02c80102549040c0d44291145a2802d00344203442400700045039121480d40d6210340c428081c03581d00c0e0344901d052002402c0c0da402c01080c070790109812541c0072049105006007038400e0400e4554590311402015034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 66012196 1250 66010946 66010951
    0x170412110a11091026062d15062d09060a0c05011b091d090318060409020c0c0420090d0609060608030a02010507080c03040f0c1809060b0306 62
    0x14403150080c100d25083c1208100e0303005409401d6508402e03210800704100c1c815600b0b56400781c8420001c0c1c0c81c59444188001e80d00705021101c112030f00c880d8685500403030910301c080131441a841100081603001404aa011907450040c0240d0b40c903550340100c542c20f41070302c03030395240b078120000d4640c031180d94020219804040c0082031641403c2c003200048411079407521003140c07555200c0c1282d8117a0340f601169804012080d86407422032030708102e080c1c212040c01c400302e051a41588014441c001c000802100d2280e89411a00003490074401e0206015200383d500509e041440000d06200d060800708103600c0075801100d040c0091001d4044e032004903602c600f070526881c0010403000084e443c0581d00c3c440038500c145008141e40009498060132a05207a10107611034000068034940d0341e90a101b41a40020181029915070074035031100526804004d100034079480c00b05101d04180000300000c038004000800905010301c2c00102180e0240c0301d1008125003042c10240c1c01603241c98003068891 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 66013446 1250 66012196 66012203
    0xd0803040b060103200306030a0b0a0c030e120910021f0209030d02011b0e12010e070810090507150c300201090b0606090a0e010305060f090a030903060c170412110a 72
    0x120301e180d002c0c00b4101710364400303060305515104400a0b480003408003094648502c054000002d540c0f072034014050181d5500d0141c60811b904080a443c100207080c4c010768201072803d440600d03519010903000c1c5d18000310304c80e002c2502c0f0b03510550960b40c400351390010a14138100b075081c1d031840d402c41601642601c3c00c10049101214400c0204d800302407040b4a00715900070300410031020345801a00c01400c40d04820060005030b0449002844511000c0020006804031924204602d1610713440300b83c1c46031414081e41c10544400000340c42658401c2390070958498224a2281d94100c10a10200c4504420a800c805c507240c0e4961006070710b80103109190119800c400c3c400c02c076540321810452641c1c000d02082e81e000c03401d0314001c5a407128a01609020358410740082906081c01c018000c2030300e40051601b01d07660300203c3d050002903880b601c420120f0b03034800380100c0ca1740e45604041d1903240f01078880c456118070300c0082105100c1ea08014415004558842d18a2540a140640e40310b040380000034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 66014696 1250 66013446 66013481
    0x6060632030c040b040306050403020d0c0b07030b0f031005010f0803130b03040203011103040506101401120c273809060412060e010f020a0e01030e0c0d0803040b060103 74
    0x3140300805840045600800300a040d928190300c50240c07001c26001508252141e42c2d03208108401c15030100030f462144000c90620464464069a900e0f2018074010054020142c9400128599860710400701e810400b0041c00c0d1800c000c032107541400200b07002d12416089a00c000b800183c41d10002c012903038101c0703851040d00009420444042230341c2d8070250003203030990750f43d002440c42c0d450850f01450285101320064040c90802800c0f1035005480e40d00040c080c040420200b003040d0f0b82005046007801003440010559004001080d503038460040c1c0c0383d000400d41d0b04856030740d138440c03040741000352500300486c2c14503a02034094038140344109040b000c032103040500307a5242081e03a8102411003030b40000c0c1820300c0d080e210040f0b042c9209003400d0450740d16440d51103500d0070031401c2c05010814540d0031000c505040c24104010705420000d0980c034181682c41103200c2c00500180f100e40c41c061070240000c4004006460061100e900c1107800b40c690405213008a6004c0d03109000e2a0052030050012 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 66015946 1250 66014696 66014777
    0x5060d170c0706020d030b061206130605060f07022106040213020403150501030317040201021e12030106051201150206040212150702010b0307050306060a0b0f0705010504060606 78
    0x109482040c111091621000003407000d81c440741020003140028183c140d0180200344004400902940d02e1455858481c04c82440840c044842c41c2c492990720050446046c0306402c02800340400410744c40e0084c5030804000140040903016100081402d54402d840301d4900800d1840c403801c000300c0070650b42c0b03203903041800030801503c0c101d52021800307100034000505c0c1503940e6840d006900700001640c0364aa403900010000d0542001c2507030130440c00c2201c05076961801d940001e403105034410090f888510086454201c0c03440c02c2194a2000c04c0115003a41d481d6107504000c0c0c41a0000304282642844d442c0c000301c2c200c070790b90803655030390707038444d0000c0038540c1b1141d0030468404904601400b031885420940003203609422a824060316079a00002042d580240500d0b0402c062078005d01e0203a03100d0707400c0c030925071260171402d0101d4840c0c072451030322601007103000030aa22817504050f00355820201807200380041e55210724102c40c4a80c40c0d40080090b1000d00d28491164400c1c42d0301c0e8884140003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 66017196 1250 66015946 66015953
    0xf070e0103081602180a140603010c021513060203040b060405010f080d03020a0323010509010602010b06030a0b03010905060403120c1d10020106120b1b0403020307060e150c0a020102010c0305060d 86
    0x80d100f040352000305181d0f100e0800b040304142041048070807110b82529982d00c82c0c01900404185030f00010294000d10001e003014601a5541403071035550100750a60310300103850018802c4c4050320300c07030740305400f59640c0c07e003800c100542480030f44496110b585000300002d0b000f00950028403ca81c1c440014241400b9410381c00d500035000319428106054543c0d517108140c0c015060180f2040e07016880c0b41c089541000f06000d06440160410800c0d68501240c041d600d075655400d480c0c0c0030305440c1000c103c4001c4800032a0241c0402c820080c00c82c4100401e2004040e08034007040d901c0700c4400820001019400b108580000c41801194100c80040f902a401c0e810400b0078002a1340c120f000208039140e075142050303144410384a092311800d0a50043c0007860b50708000c40322207107940700300050400d41541c0001740c40342481d210303c006020214841d042d083e1112250134034a4001c541545445000c101d2545445100031142207005501c0e00701200000c500a03c01d260207050050704000b00d17100c0300d94 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 66018446 1250 66017196 66017227
    0x2a11100203251d01030204050a033207090c08040206070b09070305070b07051b0a05060309071223060114060703021002030a390518030f0f070e010308 66
    0x70140310110100e0b81030150700201541d0342e8020544036550b403490a810410001c02080321007510a8100746c0100000c101d2559030303e811106407500200c40300c1e2210142c08802d41d0b8900000c124480700140304800700445000460030504940e140b440074040101d0800c02126070040c200e0b00298482014403503c40070803400c1340c0459222101c20110b8541d9500e9454251a240e1240e200c00706181000075010308004052100d0442d055400c28507100c40c0113031100180ca80c004034003c83e8024800880012150720302009000700800b1028a410b200d1002c6040c9142481c0141c046084450542c038103000ca044c2c00095003504071100d048400c40c130402d008040000b10703403080400b41d0852007000310703010a4a0292000f1030103018940c0c00028401500707051000e482c00c1c003d0403030b04441d00c0d6000001c0400e490034040145006580391039a03807004464180c02c0c1e6000d0040c4100e4041c41a0341c9040c100340b40001e5045508400d1000b12410103588000e8005402c0c02400b004007040014000001c05101c000b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 66019696 1250 66018446 66018451
    0xa050717010617070c0209010e0712020909010504050408040905010b071a06030c130f021201030c050a060507081e0304050105150a030302031903090b2d061f020f012a11100203 77
    0x41c6032412080c2d145d0303000074980300801e0304444004614241800321203a0001514224030420600540c00c04996100240d0b906005104030382c007503510b5900003020854824129006040d03440001c100c00d5844080011894000002c01c5618a038544d031080c80003001d1050140c4101c030010001e24180000358181f0858002081e90455110b4039030106034038004160003d841d5803030104d10024a103616604100d8000100c640c040350141485110500c04c1951010031980c2c801d8000da240c0f60340d05130502c4003614807511501c0030000d13040007205110802406400042c0100e60300e413060b8140203480b00801642108920000b40985d0080040e4805449400c83c1c45120100300d00f000900e0014948919011300300c101c3e40004a080342c1c4100d4031003400307425044c42030124541c4c08805d0a07d00f46010076040031404026641d01c8043c1003071400e0325407003080b000d070001411000030f009460090307451120b0800c6c21407036803861448004c81e1140440c842c441c6007244050400061803116062140d0360001e5001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 66020946 1250 66019696 66019711
    0x90d020d02040f06060203071502030408040e040507050d0b0f0603010e07090510050a150f0302040501050f090307030816140a0b01062102180913021012020d050a050717010617 77
    0x220380ca0315410041e03910130000101040d401844c0d0b626220729007902040035101008034480e10510603c0003140c4c204042e201135415004203400c540c0c980b401c146141c0030880e400f5030345c480c0c00ea001d17400402080c0c0120a00524180c50240115120349040500f07072a41b0070300100d80355104050801034841607421590308500c8000b02c00000321380b281d000c92030440ea13a4002e03a100402d480c2c80c0d4841141e0103140701c400e400580c6421800e103814000001c05e548554502021205004142c040315568184950030045501195a0360744194581c8034501d02480c041044c1d4400c3c1e0341b0702c00004100408070b44400e2240c0d000302070200390303800e2200907220315510010030f0200c0903030554100e0003034500c1d10007000303004940509043c0c0d5003083e100700145032078000c3c900e40410600001e4200103032103501c5c100460325040e090043c00b040003e0951402406003107091800710741414140b00940b0003d9011601518990b61507020583c124480d04074601d600784110070015107042041102200352000254000b100d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 66022196 1250 66020946 66020951
    0x7120b040e1f091a040c0b040b030601050f121911030105032508030703030f0e01020a0909050601020a0206040f030b0903030c0a080c0405100807030608071a07140a08030402030111090d020d0204 85
    0x1000d481305640c2c00d0400d40c151449480c0102480144541b0988480003800d049403401d1500c1d0500b40c20b5901da003c050b100078140480410011000303030807101510078a609865903030707115240509245140c03424152450b205d031450040f0601e600010002260f0503644040c004000074210609600110203140481c03a68510200303401048183c000d00081c10000c0c000d41d00490004100a8143e04aa0131554003084982c41045206001908520002c0448980d40000107203075541d400141d00300f007500c040080d4083e000140c041901c940d051b825409032801020503019680c0e0301850f0a0313a80c03005580010400009005171071025100701616580302030305441140c00d156440020a144817100d0003a140801c00702810007040301c0c1d05200b428000c000400003400303a140343c980c10b5094203901e10b205401c3c3c0751001541005100110160b081007948010841d52180d00030b0900300c0c09038000b03440032446035080000c036021111141042d1005440001c1c01c52440b91400c0d400c100003540308240403a006034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 66023446 1250 66022196 66022211
    0x803040f020306091c0c02030a12030609111b07060c0f030504050d060504020411040f0608090a020303040e07020625050304051f0c110a030509150405040507120b040e1f 74
    0x32414071406000e031098200170f185003111001c0007038207024074038001c5041200000181c005070750f00003065410281c000e0051142a2080b002c2180546070640225940d141848040720500003443c00600080742151141004400710088c05c949503190b0b40f081c6400035480707104400114901005c4041c08512070b0408514155454001c136184906207881a12000d03a40c50410007503090a004003070425a030513401e0f92405040001000001280e801100100a007140000e031a0789030030800407020a03001800c99840f981d44620000d02940b0031201203006008040c00b25410f14030040303045d0340a05840307a26590001307410a048900d1f800082c0140d17414032644000c0005003492406070400b07001401000300d00d40340440e8000d802e03200b1001c0c00c0141e81d4010504032011992000035203c440c1c00c102d0b8880e4114215080c0b44a540c011034115a90145c81c050900c4517050304501e000b001c0c105080e000740901c01c03800040204503032544c00700d4200790700800d07446c11144090308011741e80345140003400111310 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 66024696 1250 66023446 66023449
    0x5150706050f0103150b01050a0f02010b1f110d0e060702220203090d11030301050d020a0330050a020703020405071403040803010311100e091003080d091101090f030803040f02 77
    0x49400355140841181a000140f0a00208802a20420171a0380c0240412082400002c0461041403501800c002c4024600e645551007034226582c1400010100701c0400401984807403081c060000c01c002044915060030459400420b504900484d6901c401e00300075102820700206600001c01243c0c40000540d414280f015200c90300e80003808900c8c0010303181d2803c5050305203480c000079110310910008020404608900004507410b480c420380704220110411b00c045206c071f01c0c0e1030f00003c1802c50165070206048155141782010181404020080c034040f158007594184240f060601c0181c20500c0d050015041a4010a8001c5207900d4155000207140c482c2d60302e0303a002650102c0b40c0880000c0100140049404003102c0e8031011115440d55462011020b04625a840416400342502a0000388802030b46184800295003101c2455902c81d1442000c42c000c0c0500d0808844a540c62403201c001c42d4131615801060300c4064440ca6900c5003192503036038a40c5c200074070444046a001400c030006 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 66025946 1250 66024696 66024701
    0x60d06060b03070c030809070e0103020f030a020d08090108010b210601140403031814090106030c051b061e0c0a1101020f0a0c03030b040203280b0a1203081005090105150706 76
    0x24030703079944c0300e50100c01c403490700a01a04000d000250981c0c00807030148164141e0204041c11654102c83c0c9140e2034000c0400b007801e00314240303001395022502c400030b1004d2002440081200749000d07610780c0c2c900d0b82c9980c15024640500c4c9400c1058004480320b070164225142c800940003801410060090840103010410b642d000d50004c43c006100307004000c1c100719103902da41c0c0c0a4940100c501c07005040d0400882c04125051051504160310360300d044801500503022075140000c0700c8032680e00302660012440e41e580c0c042d11908030100c04103140c6402d07241d84401c60b5000348803400c4241c1c039149000000722069404450100095503003042030408891000c0014004401e4507107a010f1410240d041c080e0440c2c60040303060307025900400030041e24202c02252007608070103080e4130341c84a04400c610b020060694059a83c0c0001d038001c404201d00e030881d400300d24014880d5071a001c1a42d101843d20103042d5080c0300b001c2c1c01c2120b400050007180b6107664003900560088501900700340083d1070700b000313 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 66027196 1250 66025946 66025951
    0x1e0f0213090803071d040507020c0603070e150c06070807021c110607080906150f0607080c06010603060918050705150d020a0c02040f0c120b0406080a05061006080f060d06060b03 78
    0x418404100d0300c83c1c80061803081c0070705c1d4070111000c018914092101070744a413880c694162040da80080000d10795400f50920080c081009403009111180c03c8007148060760000310069483d02c1000c001801c480e00c15848284204403507406841e080080f60f03419014111240f0900341800060703801c1740c400c10010000b240c4280d649a80301009400c00e003070300d103003004409000d02420318904541c0d00f00a481d40c4141801409003503600c956201074a041113010b900403404808414000c40c1e0000403030540c50381100050303450104003000750000500180c10220021a4000c015405c482410400c40c40c2003040c02d00c2091441c03100318a0702c075021640c5412684a1207164003c143c980c1651025030400303204008010804003420021404007600240016403942c00c0c1145c0c50b40c031000001c0685c0c4603a0011001040e0450885912110394075040751945412111044a0806804005016407141000c2c84c080c007001704c04110b040c0c07200d01c184040d160000500ba1105525038500040d00303c1e40314001c52 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 66028446 1250 66027196 66027211
    0x6040b030a150c0206010e22060f060609140904080c0f0d0f020c04050408030f090c04060612050604020403020a03030309050c0d0305030f010602030c030406030b030a0b0106050301031e0f0213090803 87
    0x2d41c82c0032400c500e4001c8803000840c8801310352050006015810401c00583c0c0c1082c0000036480368880d001c0005034164094050081080d81801c0326812035640a4008006540c06501c440f60032985401a11a010034110f240756400560135000ca00400d83c448001d040e04090f031030a403001840242d0000c0c1c6000001104000007035007050078120242d0b0b050010b00c0d0300c80e90889080c45a800c03c1c0e200c08100e400060203418a84515002054003040100303c80021400050428016241c0e11039028010000b590180d4014604080000e1071900c0c4c1803007102d056a82c010813660440e41591400c9000b018909000c4402d441408240203041c1d640044041c0020b01c80e0383d0b11952440c0a00780e4110360030f01a480303001036500c00d11640c41403031030200c140c500740c40151030002043d42d03454001a20f04201542d0103054940c100001080302540500114141d0740034441070b00f0058042014450400c00416024050403e05611600180380c102c507100700c0c0c0780a0444c045014069a01c582c500d5900603284407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 66029696 1250 66028446 66028463
    0x16050702041113180606030507080414100615031a0a150e03100b030123060d210c031d01140f0702100e0a0e060d020d0510050a0c030f02130e06040b030a 67
    0x103000c4500802c170180a03a880d044c4114200040050030303070803000d4002045d843c1c56290900c0c0c0c00404020a4040741b481481c1170108569906088500c0d040001c04130780003d061044a070401282c502040110360360140241d401503140c281c80700b40301d803808100042040246504041e03666010002d100118002d4031700040d04809803000c041c2110078034440c0c881d04110740101c01c0000200d5040c4a544008107a03071403181703610240f4112203800c41001864000c0450805084c0c1d40551140c108001a031003a1181400300c10700441c0070400e480880c2000340000d040d294583c52031250300024014001654a5140c2441d000c6d03800510b4a1103418615000504000351610061920040c19402480701d08800d4a0750300703201c400304203808109000a8028494910040b04019003001030030060b800c445000c010354103102c200700d00540030036207120740003034181a03800b404038245100b10341740d04484407045441e0925003000c880300c0c040c008083e42d41c020340c0d4070030300c901a49060000d5404c492090654 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 66030946 1250 66029696 66029729
    0x14010c200f01080412050307020c0a0905010e0c0f0301090209040e0604031814030c060a0c0507030b040c060306120237050418031403041e03020f0616050702041113 72
    0x1d01429200c100c1c1c54034108541c0390140310100b0100c042c010301c001040d107082c0fa41c9030b40f4030405a241c000c80c44411a0400001540040c4405c80c0e64015030684840e0821003e85071507101003003089005103a02e05c4080e0b58108010454414154001d264050003d00049140130900c1e0b00941412800c940075000b040151000e141200603891603540501a054404620800064003080d035440500a1f03560140d900043c0d1828040d000e440841c0701d0940c00022205a13030389915200030007402c144e508807213010710400045401342c081d00450055400c1990070501d009419001c00c0781d08005485002034219802c0c48110b04050384c0807041e1504201d4044050350103140034148011182a40030002d0070724803284980e00080e9001030482500020400030703640341e031142d0a14000c8040c0080c8480383c800398400441041540210315070640103901c2c4250741d070036524207513682d0f601141621800c00080040003500014946076015007031800c85240340508003100741d0201d01c40403000f0b41051010140e018030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 66032196 1250 66030946 66030949
    0x306050f061002030706090c080607020703030e0a03030f0e040f020f0a1806080c1e04030b070f0c08041a0903060c04030209070905090f0604091b09060506040803030114010c20 77
    0xa240760405000c1d503101d07001210301c50000b9124080e40c0c000400098940030720034144040f94014038040c1c8881d40c1601d09908060a01944e9100703540700490100d81d0f00881c541a034030340410200c0c00c5035011b40b11500e0032101c83c9000c49090404240450b40300f80e035058090201c41c400d2006d08000044140480d60b140100d40028012400100c12400307040b5218006001c0543e00140031500441d241791540c1d00c64041d42c074107580c545000707a40d0441401003c980081802051405540072b806141c68801540110040840d100742e0301620244c00c9020402040000488100c044151045e07448105401c0808001c0020f0900e201a0755913080c2c0d00003c101401580742c0078214580011f141d041c4014035030300d8400483d850201c010080110780c0f20348800180d0540312034001d90091603105851402e1000c100d10480f903c8101405403140142c80c0010104103400c0c5401140e041d1031400000f1411686480c8180c03108202c5892614100076514503000b0008040c1c04d0300246284204184040d80d003400740 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 66033446 1250 66032196 66032221
    0x6050f18030f0d0203040510020d0902090f13080c03040509010b03070206090d020c01030b0604030503070b04050709060503120705070b070f0605060f0612040501062105060604020304020105040e040203070906030605 94
    0x3181101580c004010311040390550744100c946000250001588030b03541d41c00d0041c03c251212024902107400000e411000b1001984102d4030184202e030360034041d881c1e10200140c440000ca9010700c81820034030715003011800705005404c240c1c03480400c0340c2c07502d5141c50210f80f07801c001303a004040030720000c400c1c0080b8540520055a1103100a8020301800c560444020341e14400800ba0a040c5030b96501050400c4d100d90088801641e0820100c03580d5050b54030740099403180448050314280140c4802040e050658090b00d401c44d5030082c01462060382900b407810465000e40000c940601c1803202c00618089004090700c00a0301a11007801700340c1039410136000b502c1000700070a22400060400c01c0b207680d00e032400da6410000c0c54486030b0340e43d9a549801d07030041c8240d4102042000003036412402c800c40180480c0449403107101660803a0300d50600b44016804203444c0280420340c140001e0050001c0d215600303a0003400101212a505e90307030b1032401c046513043d42056513405d841d60200a04000082c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 66034696 1250 66033446 66033481
    0x1903110102010c09030318090c020604030f08010501090501052a03031e010f0303050a0210050c0c070b0a0e09040c2102030105060a0602060c09040608030409051e1605030c0706050f 79
    0x20700090006650143d0700804a00a50000505100400c0002c49140300090a980c0144c100e4850410020740210300283d50340c03404a07002c41c0050180300300c0544140c402c4103000e040721410b03100c01c803c05060000655968100240c0d01c030840c141c648209071064428101144100c030389001550790ba0500c900d9136580480000010500c0503040750040040c600c1000c3c0f410201c9405181c49078481e030704d03120b040b41800034a03030480300114201024011400d09800040c101028560110381ca9540d880d000d903241401100444400702d21044c40b4504281010380e40145e000344209201040b40741c8896840010104441080c00300d40040c84070641142030074420383c1e40001044554032203480c60250001c3da0b40000504548a0306c3e00840c0c140070b140c6803500124054032401d0140c03900d803030f12081e0a034001c101c21180c035041c0550200ca480014804580488e01858900c0800d07e40183c441c001541c071540041d04a10001e0740810a203008155a03102d8507001e502061071049490a051228081d0107095 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 66035946 1250 66034696 66034699
    0x3060302091e0103020f010509030601061808070f03020607170f0d0e0a0f020f040e120c160b0d051302060d0605090604020a0203180105041502070806070504060e130209190311 77
    0x3a00008a010382d00e001400b81125411104400160391002c012035071030043c4010943c06129520010981d20f40122124801e4507420700c8400d240340c0c2d20780082d80e40380c80d541304010713410703880e101e0900c09410810001c017001c90280860780c0040c1140346200909a00540040520b00000706170707820030006074080d20f403049880c90010141000c15455882c620192500c00a200b405042c00e4150349440e00e8203d0f11002035002c0a40701d11580702041e1400c2980542811b50645c002e0b0040d0186404003001307082c082c1d5104100032400c140d1200f0f0860001c0c0800f034601c42c82e1041e010360440051f0349080003010a148400404100d0524100502c00203078405003c10740700380d005014621b4029800826a003d903076452070459042c191180060f162485690042e0078401010055071010a0300060503004450030001100c2090b512080c0407183d5005501800c1c00190384141200e0701031a050340c01078405900440014a001c0380d0703600152500000d540c0c03501c031103410003108105100d41d000c440b8555110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 66037196 1250 66035946 66035971
    0xe04060609110a18090e030304050d020604120c0303060515090103060801023109020f03090c060702060d05060f10110106291e040f151701090209030a0b070306030209 73
    0x50022071100340c3d009200c840401c205a221007070308045250088031009144000003041030640300260a5102e52044074165100d100c0d101070000210710000d0700512854116810076802c0810548c00c0740d00d9070400405404054a0b00300210b8030f90f0354154510310308050121020354641c034090000d0203480c2d55600035501648184050f910b8008915840403c0000601e81081485011512203080c0d001f2500801041403000c50151a00a084070007940038210260032250300000e480f0030003c06100d1031078005e4000b441804510440503850b088a50001030003402602014284008506441500d4040c900003a4800f03c60004d030000a03c0384402804440241c2c05241c900781003501c4c8240310644802403410303000103840181d01304a0840003030640d29000800c0e0b0340d980c0c83c90f4980b400030190145180c2d036800001e9500800e8003032645040420717862400c42c04103a1801c0380c004025000b20411b13503010b0203003074030520004000c00303502403040d445038800040e090f045005010301c2c400300400180b503021703 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 66038446 1250 66037196 66037211
    0x15031a01060504050f0301090b0a02091201020a0f0302210403020303010f060c1205090d0609050304051005030403090314030d020403050d0201050c0a08040b1503030a030903030c020a021f0512010e04060609 90
    0x10b41c4030044806840003a500c0141c407101c0400400c0c0102521000540400554001d10100300500d4004010090301164900c07500c00314680e07000c0c03c0340f28044010010401041280d0000d5000c0c3e00540101404098100c0b19000552100101e03803600301c4d411801600000010710001c1054064640500b90a14010341c40001070f6845910300c1206609030700c240000410f9102c82951100c190455a0740c0c00744d000e200d01e102626000e40d40b07411900030984160740e80e69109031410b00c545e0582e4071858165844440051842c0c0f0348075110b09074040514180e002c10170100030313540d0f00d03800100003d610032002440070022211009084510180442105080400010300c00592100c0c0d0f0a4000390030102180c00d58407100c044c080e2103404410104d0b014040400c11a84458059000c1d255690194400b80040d030359051081b40c54600b403090003503020108c94101c0f00e8204c485c031072098081d8180e081151422444008880c1d03030100984c418411481403108002c101f00c1d044c0507800040040e0f1005105d0328 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 66039696 1250 66038446 66038459
    0x1090605280203100b04090608010606170a0b030708012c0705030a15021308010902010201110310030308130506041b08010912030b0f062a06040f03110a050115031a01 73
    0x50750140c1407038041c0354011001c1800c848080c54240010031001c0e0400d80e45564034030903d406840c4503c1040b0055181000c001a024080d03511035511281c0d402e035483d01640d985081c0401400c80009254051040f4003000c42e401c2404d10411203070340500103903104000e214460b0940809801d10307400310300343c214050400540c0c41c0010030501d11036010b0441840318903130140181c000d02590041e9503036400c6c64000060726080c1036000018584c002c0c0d0082c4011110311442d009984401d0300c0090001505540c1040440e108010b481e0708071000110003120360405031200c900e00b40080d1070540741c1c600b900c00d14010030018903601200801001009114600c02d90b107840228440405000342419203800e28118687c1d210b030a141d44004000745840d07100d80404680d041c0700711058003524560346d584541c2100522000032442c0c8102d1b4090b5009407105820307070301203030302d60401180c44030303144103148596000a0342801026071299004211014041c03441c1000030b00f05050780c10f0803c1003080c540c01031024 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 66040946 1250 66039696 66039751
    0xa1e0503070611070515340606080d0804080405061806130f06020f06070e01020c040e01021b030708040302061b0708010c081e01030201180305120910020f030403031b120201090605 79
    0x1d403410b5402d0065400c030071f0702c0ca000129008094070100b6030400c901d4104124072540075006856410f400c60300810b00b04c440c1030b962200c0954000d0b001d401c06010820051070614010102c00c010600c00380000c11000c1701064954008080480c0c5440c0803070028800d80c4071114003000100341c184003e01c003900c5910411901c403031015041e4000c0240082c0000003503402003201c0c141038403002c0c10821001000c56102e50003500b00d4045808000b42020f0201000c074400001d030f03844035401032001d0789400d01d16400c02200da8040810380d4034188040c0310a16440300c041c810301d402007003000004202811500780c001c3c09400002c041d0140040070740c900d02190601c052606040d6a42070030656840c410107440310140caa510385c0b0017007040c480c0072191180b040000c00601034107801620642c911180f480800d9813507045200ca0764055134001d000c00c00110b40b051011001042c41c40121040002c03180d203480c00d40303420a1000c540541e44030700b050803c204843c8252a4003e1f9a041c5101303117207501c800f540c1034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 66042196 1250 66040946 66040957
    0xe0a060b010f0203040b1602010e030d0e030c0105040b030c03060d080a080a0c11150702012909060301090308130303060f0e041a010f090510120318080c0a1e0503070611070515 77
    0x2c25440c41c0707c0e800e0459000b92502051040004d04940c210680c09000400160356018068028090b80e5181c2c42c4a50080f0103039429510b00c103000c2030866542145940440e000140210b62140c2168444d90200d80e6035401810400c440b59100c0143e4070b440d403042030a039040010607008010300e0901c00e414800340400c550240700c546419a2041d51184402240034103454105c0802a0280801c81e2100c25031031058840c400506a0708aa15641c900c0f040608031454000701501080d080e20000380408d8800124000c11407090400052190b01c90314102c0c0340038090b0300300e284054480c0c004c0c801445004107644070940800511918290b06101071301e41d20010303521424100688940210f00f0580c1c0c00741e858000b4002004204200060b00e0900401e008112441c1245400c02c11101060b03010011030000c3c007980c2c002e0001103034103140107440c15050701c80c0d511019030326900da100460266000e1003200c0040c0055603441314101000c200c1075007040d0080d44010f01c10003410180c00780c1e440c07000f001c0d84d2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 66043446 1250 66042196 66042217
    0x40305070e0105060d1e060b070201030b0f03031207140a170a0c1b021c060b10052703010e071502160f030209090a050109080d060503060f01090c030e0a060b010f0203040b 75
    0x6070f00c0c603a0f440000c112107041100700c0c1515003807c0300880c281114101030214a8000da8081c0803400341e9100788080c548501c80041c0d01504204541782c4807413182245907403c040d051030400300b21500c07645040c8868010400300310000e40c2000c00b28000c00c404800341c035044000f146040007020340142c4090680c40340c400007404007212810218041d9a64411002a24509132a00940b000c1403440c02d60020b00d014401144660781011051003124442c8041d5104d142424200d8540c100d244401d00c10040c181d824400d91640d21920210740c01002800440d0081040784010300d81e604141c180a8204040740c8000582c000b82c0c00303030822005089102c4d2108880e01910f140e43d2a407684480c0c10304000554501905960810610b1300400550000808403140c002e401082802e4a0340300b09926000c0c2070710400407103140c0d071005000050b90350b805400102c1c172604000a01824460100c0c0c1406550002035990075a2079003004c886580000f11303800c407500c561016600d00f604011000030a0301a410141e0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 66044696 1250 66043446 66043451
    0xa0306080c010c0b1009110d05010b0c0c040902060702031504030906031401170102120705070c0e0402030c190807030c03020a1a03070e060d051906090b010c0219030b040305040305070e0105060d 85
    0xa4070f5a05e220465000f07000d185c0310600208102c125070440c00e5100320f25141e041303803a2800018841d002c035420b8500105a04029107014400602040094195200d046c1d902107800c100311801640c003008640300841d208490018241341902b0003a2a2204031b0b44132070107160034401e0014100744601034003415201c0856203c03e200c09910011070090044100356004800240c090081c040d4021010709481c9100714008060282c58010303d50700740c20b080e40c000f90103510070403100101e441c00c195182102110703105800b2075a65200031452400310f055000380c94010300030405000f5828407607010740c081c080b07179002110341800320072130150b0a1100501601c201302040045404681d03030340c422500e00b1080000e0510140c24004407200ca20741740e4a140c944880e00d080b030005803c40c445c0c0240190b0b000161607408641e01d0302c0d02807022001082c4500b0120303000e414004400200300c02940c0d070050b80260340e903a898500b98a032003460319004d0380064602072030b8000100054ac1e100406c450000f0a80a0003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 66045946 1250 66044696 66044701
    0x6050405030408031314030a0305030a02180406140108060a12020d060207081c0e01140c0c030409020a03140f0c07140c09010305011a010e090406110408060a020a0306080c010c0b 78
    0x5401c41c001c60b00f0210081c013001600342e240c500c1c030700b028100303941441e074070305100c0105174003090b40d40e80181d00002d0120740144002480021180e01a00c00003007204040d02850280d04000b40860352a504800340021410000400390350344400500d07030040040d0707440c03c40340d402c01044104601001d01d00901ca00b1100749144200030b156015111916407204e41c403512400301c0d00600070310840300300c1c03200c0d0301c0380c50004004850501401421000c0fa042d50848440f0707100d02c180340c4442e900c461070650036840101710008951311648001c0c00480015500040c078603961096046698001030204100031640000f03004d40140c0c034038101e40806600808070035528400051990400c0160520640c0c4141c400b8000402e202064100c0280c03034540d0b48003146241301c000c0040d1050440c1010f481e41010084000031b00103005580719601d0b1019024005040582d11070f40b1070300d0400c080f542601c410b038021a0083d030081d054000c0b030000e4444c1d10003800b610444a40003d0840c4d1621001500e203841c4c9102 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 66047196 1250 66045946 66045953
    0x905010806040b04021804030e010f05120106050c0106080a0f020a0b0a050f031012030e04241802091309060c050301030f030c060608100207110102060601120c0e130c02010501090c0507060504 84
    0x48442e11603c1309013411004d40740c2230a000d4040c50b0007580003804118100341c0702000600c10002c50b11030704068902c2403900d9003002d00440c3e20b03401c030400c1002c2943d40c0b030b680403540c008100400c0f24154401c501c5034a002c7d00c0c51041c4048440b00c2e40c021400c0301c9080c040381110542210680300e000c42511401500e80e9601101d03040d00400d1980702125400c500103041041c140c2c08000842c032968240c03014083ca086505403240f105200110b540c0410b1202481845006004405c0409410058801604003040c920009801c1d106580380c0520056891050707a0400c044c6004030b80180786141040d43c01c42d855501c8817102030421410060401c2505a0910100f00740c66005002a00d407400840d45601604c0340f0300c10095128036400c0d210080c1c440c0c0c088a0944c400249544a40303410f9403178002500b0380d4181c15019214494860062041d8151100030701c4d29242a44c01f03000380d02c1400411284000d0001034211401038110440060610105141480e003040840d4032844d4454000900c41d0354070700b03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 66048446 1250 66047196 66047209
    0x13021c060605030f06010903020a060509090c090f090a060b121b0301060c0803040f050d020102090a050a03020102150c0903010513020405061806060c011e0902090c04080d0e01180806010f0905010806040b0402 91
    0x108020b510031009000402c0c2cbd5039118024210300c1000b40c800000d540c91388042c0c042d1a002e13007055680d001900100404003802c04201c007581224080310702045041e03ca40340b0654542150003e03100605014041180d500010f11880d1880c0d0a5444001d286504203c0b005002045000010b0310311280007000c50f00b013040c00340744201841e070080180c580118400310024080d44c001d0b6100b6129100c0600045164034104040508481d41600182180244080790701554080141000c000d01d6050040c180c03552020b002c0c1030320a011160b0b910b541c5104c50320402080f030b0405040c060042001000940344070b01c01b19003030354000c80110f55540d04c401c0300640b0030380940464440310a405400350608440b007500342c0c0141c03042510840c1e03090b0072a543d020507075406000d1846104103030762220f80c1d80250325002c0c2c41c206e2030f07508062512481240c03208084107450403caa101c0c54566000074010406090601080c9018000014041c1321551511850a66410014001a203400440030129085541c0c80 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 66049696 1250 66048446 66048449
    0x907050d06030b060109090b0f011103130308040905011d010311190e01030203060c03040b0402040f11070c170f070312031404050109050706030b060a1d13021c060605030f060109 78
    0xc2000d00c5080d44038680020042d409aa0700c1c1c5c0800c84549010814101d140900a00020041c1c08050115803040045075a500c0a650b6811903000400c010052140441d51000146000e1403020ba5210300c2d00e0413400803514143d1000305110000c00300e40003580284084181100c2d044002440552a401d0020f000c104030f420710320303900200c0040001020400e006070141264000c8050b140c0503900c041c1407800500c421a030003008200b1100c00540180b600ea4460341e0514406000042c090a2151b2181034560090406441c05440208100000079520071448099040200070300882d44c55400c40564139200c5010042c1040344000765110024400e611842c0348500215424516040c2802d2803402010003550590f16402070000c0403c2c024040d010700042900e015041ca403034140101411508500320706101d48802e1152400e081031340e40e50401078610003040250040e983c1000c254280161684600c1104905042c032400300011a0403800766580150042c41d82d5920713941d103000486803070011307 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 66050946 1250 66049696 66049717
    0x809100828020c030412061503030203070b0a020403020d14010b1e091503030f04030309050102060c0304140c060309161401020d052d030402030105070e0a090209010521040b130c05090705 82
    0x21a000030140c1400006c06403442c000c4004000e2007a25842420105400d8013010380507034010004500003032600132155520500340c40d0300504094890740010b503100c4c2c4051050f5861000c403d54070001c80c4080c440c005034254112041e640c45821040228400c3c404d00290502c90b501480005840024603d000c07551424010280c90fa55001c510000607150054003054000408803080400c065000240d111701030f004030880c071800d40e50342d580c8800340d1220a01c40c552141c010102e015016841e45806540580008009484a01048140e03966000700a0703020b0b04074605038051480050360041540d0a0300308051600e140d403101d0100900c110810340080e07910010b2894211207411001c19030146010b58803c400a0002e41c0f21803e084800400868a49501c0f000f41f41c0200407841c3c0320b600074401114181401402c02c40900200c40e00b03056103c6000110b01c4040c3c041200300b0040580c059800704811407031400001d0207446803840703401603004030380c080c0c1c0b60503001ca04854010400d9030b003101d64 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 66052196 1250 66050946 66050953
    0x90c0c010e06010803070507090204060e060c010b0d030e180402060711030a0b0406050f0105010804020a0b0d060b030c0901020c06131203090b03100e060d0312020d180809100828020c 80
    0x1c2da130b0700c001d5503075100034001e8919009a00300440d0910050080b0380c200d80c100e5031580d51a007414000c1000c10703030000088031410365841003110550380b20001d0341d480090094171550ba90303a01f2401444542d02602803400c4104180c0e4040000681d141d41c203550f60309070031a409090400720100483d150102c070384c0c00989030940e00010001040040c2e003109224500c0260310078a1640d07288015280c071101500c00a40c044200c99043c080b062280d40a0488441c1003840410301d203588000c218007603401035800581c0d4104c0001c0c0e061480d601080341000c4020b003590081d1404c54040342c0c1200440050250721456100d1355103560915101e0a54000a4038101400707a903030f070400904280c0322410505c01d0715030580766900084d038141f5054046482d441e4047c1c985495042145c0d0340344009500c2100c0780a40542e0301c1d0100c8070a46925000d02840500c68600d46543d6640e820400c05074680310451074007081a81c20810000e02e2200c2a5a074100c81c04250f80c08030a40d40003200c202034020001c0511f054070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 66053446 1250 66052196 66052199
    0x90c050d060c0e0904050604060507050d060801020904050c030c030a09030e04110703020f190b1305010c09030501050c030c090d0f020405150118030b060613030b0103060203061806090c0c010e0601 86
    0x1140b0780c06041d21016580303c400b101a80e1205010102c001100c014001c0d40010700060003060f40c94001c02d51052403032034880c3c036003080440d0340003c0fa01d041d00203807070503903001c600f2450300e051a10441e07400c4008a084030341503140610003140248001000c00c0007140d00c3d2001705080500030a02042c441100030000d00451542d900d036103115401c14841a80144142c41c14060084404950112a03603200800c051411465444607151040d014254031080503003030f803d01000c10070030311415100c0410355841c14440c44c83e41c00c1103400d44001601084000344200b01f03009403030404a0031030f001440d05455107001140d02e400c142041c0c0351615000380d04213003030000704140740c01e00781a103005605003600e6104440c1c40b4050b04500101c214007000740300b0307400b400101d851440c4c140044c0856112080c80c40d81c071240c0366910906510420703881250301540202c117100e0b45240040080c981081e0491031140646004000241258030240060041d05400a282d048200081d08000c030100c038101c04689032035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 66054696 1250 66053446 66053453
    0x4030c03060f0c0c020102060c0a020a15020a09061d040e0c041a030d18030b04051c1706010f02070902090411190206060306041a0c0403060f060512030702010c06090c050d 75
    0x40000c410300b4420140f60030014a000782c0078203020f8281c942c06a00030011030ba180d000302401c60b840001c40e14254450070319100001524200e242d50600c0042d080580c41c1e180c0660060a2282c0c02d401071024801000c02d00420b40310014400344280a085401054500c94030002d18100880c00d10142d411070300b000c10f2801c4035441d40710f01c0d2000c040182c00301e40e420b010078141203562200601256421989100f0300b080400c803103c40094109025030195110340413082000c00b4400c89a101007004500140c40a2042c40030000d01960320000c00c1c00c100070b5440700910025201c41c240c1c0180c00c003055010031400029162070f80403e130303020b0b1407641c0580c7c1c41d030a10200d05615418101d085005214544c000b400034100801d02a024079408807150381080c164000612f4860401031100c0340ca90300a000010210301c2c2c40c01100c1803400e01c0b050001d802410a0107010303840d0280004c000c400c2c0e008002c2e500050340d000c03000e4110340760880c02c00034a844a9190840316010706510090f0b201c8003801140703050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 66055946 1250 66054696 66054701
    0x110c0105040c03030f1404050f0402090d0302210901020a1202031603030605040f02090d030e0409020604061116180504020f040207050d1205010608010b0711190f0905161404030c0306 80
    0x59074005c2d1030311303907500200704011200c9070342500000040b11070502c4100140e06101a14040722000103002505042c011800319001000100d026030041e404031840720003030385501100c02aa000b000c0d880604c1c1140384800071f0340d280d44940c2c000b00303180d0358102c00041c0c1900c2441620800e140940115101184500340207014160601032107100300d00c0d01102c041d041c0c0c0c180c4226050814043c0041c036200032581c5041c0ca62402206019030004c1d240c40030000143d60b0740c80108054041790326900328410030b41c20503e141c20403064810358100300320b001c10f000c42d4428030074246446001031030205485d81c5a1000c00d42820013021500e41040c000b281c900c0412102054080d02c115107661014082144040380e101907034000c1c410200030814040040c09061000304c01803154601503d034900324800c084c40810080110140d5000c10b4003c4803400744020794810750303441c0003030850f07143c00d008509115100250307214400c01d1003c244034080d501c050520900005031801140c010710004031096803405c10901 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 66057196 1250 66055946 66055949
    0xc0b0a090c050a050a03171201030c090e0604111c0512031801090b060d020607050f030c0c03010212011e09060b1e1201090e0106050a1202010e0a0b0d110c0105040c 72
    0x40010030748001140c01d0501e42c403a642100c1000f061040c403507185450b00a401161200c039010a10341c20040c25645054842186000714403611400020a1030075071400c0450b008100305400d1341c0c209809000200e50f05c0e85200c408010100c0e005282c8100013001140400c0c81c111b0700601c00d01985041100b000c0390503015620070b004494a102007240020000d5080354085400181250075840200d030b064241803048401880c03010740102d20f0070780c030342d182d083c5001d20740500c2c0d641c207178000240008403030010b002c40d8640083c20380c004d6040400b031203003000b02e10105000d80000d001d80600290100c1d130100f0762000c010712070000300300040343d19068a0040c6170720401d030320300480b0740c208070f9039000404032801c0341e0100c0e0210018083d50f908003460304010b8224064441d1007592105000720340c7c0c0ea9000c84507402082d2210400d04040540d2002400c4030701454000d40c806d40c02400c0030451048551700b10340001407240000242c150b0b58a903e04840c0c0102c54442042e903180c001040304001030820b4820 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 66058446 1250 66057196 66057203
    0xd021e07060501050a060203070b0c0702060c0a030e0105040503030403060c0c0218070f05030c03072001020a0c0209060316030602030601020304090608100e010e0703110a120b0f0c0f07030509010c0b0a09 89
    0x580c4c1c030707002400642000d61007039000680c410010a030105802c13120b120740180c0489910b030302c0c020311900028480d421200c03003118203400121010f02019041207400084a2013070a04600b0545004000382d107038004c510014006544600d00b613401148510041030856038000d055942643d0101e810300d01010341240c065010034402c80e40c2403109270041003a64828600c10355242d1a6640c0e01c101250000c84c4004115198035464014a04488082c000ba01503044c0b5503841d0505180c85004000080d1806045540a50401c403021031000b40e8007040b81055940050015a42e80c82d0140100d00e1889650b00c255a02880d21a003c03c10740b4020425403401003030100e00f07100d403807040b554003400c80c1d0640d03400080b0303640020410800a024407008540030400200003080c103640d5044280c50491000008544407aa803004100c4011010030100390852114800345081260301c890303445051040e008007409016001c80c0c0030030568440c640702094558401e8060406041c840c0fa06800b8140100c0c048 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 66059696 1250 66058446 66058451
    0x3040606080109080d1503140c0306060a030c061407121106060405010e131a0c0c0d020a0b0403050306041d0f010f11090907121e0c020309090a020d021e0706 69
    0x394002050245400d0180c200810034940100174003050018140040d2401c4510220308000010078495150908000403041c054205041450101410207100a0a2612492218605101040f07014428600342c1d02c50303080210210300e50140d0380c20580038000c4010191790f02c010071504007a900800303403265048050101d9015440c1c0350100816100c090195041c0e8101c01c3d0b0000d21410251088010901c0c0550964a08900b40814504881e4400c03a15502d810000141c03120240c90100010b00b4404203070310141240341495502d0385440040a000038041220100111300035507030b0350b44103c0d65807480700d0400840000c29800356031509118000798005518120310b1411000b260300450107504000f1f07809910b002c004104102401d200900488100320f00902c41c140d21690706e00c03458440038100c101401e5040310408103c0190bc2e401000030301150400d02408400c2d45492741a80c0d0070160f81c02001d80c885003800b81e200b00a00a601c078050542007100d00c144c03130500840b07009007107650140505 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 66060946 1250 66059696 66059699
    0x1005010b0702030604030815030106090e160b0a03050709090e0a0201030501050a0f0905070215040b19110306010e04020f0f040e0108190b1f181a060403060b0612090303040606 77
    0x80c0403501400401940540040c40003c3c0003178031501c14540e1166400c4520000302c2030b5400403030700711079158002000d002d6030f9444480b1840c40400c804207084620b80c02241c5e080b81002c0541c0f456004181c0c0e50028980c0b2500843c41e540d0040441e0b001400d000c02c0100720075040c07960a95620700741010180c0c0403031300e810b002060600f045000601a500c2404030701e50f00c180b42c60f240030020030b80101b0310421401a5041c8141070f14106d007010740524018100606582084010708a905203001044001107107001618000403c44d00d05580d4045403d00b48205800c90040202d00030340b1072040a0503003a50009011245104250094019075130340400d02d14140e030325407400780d0b590074000b001032012080e9030440100007500c00c3c0b40a035001044002101e928a01074070b40d203031000b006401c214201000d60442c5000c000181c814201c2d00c001c1c1801c00301c41071000ea00401e519105030300000c0c4c28a030300e95401c0900754882234106ca100c1c20921a8502191030842c100e5500d80e00280c4013180d086040070320 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 66062196 1250 66060946 66060959
    0x12070206060103061a040b1309020310030b06060901080705030a09050316031e0503040f1103010c08090105070309020109050d0501020f0d0204080601080604020603220f06020901020f0f030a030c0504080708100501 93
    0x42c01704040b10514070f4034035040c141081c01c4042e8100c03c50070311080840b00000b0911070344c180040d500411040704c20420715403c1d45031040c5180c00c010300460007101e0038055200d40b42c1e070041e8080e401c000141000e640e25102c4503400350117485100d0015289101c0013822040700d44006114100b07040c044d83d6154503400a0041844400501801c2130340018402d10110b13000c10200040d054119100e5514001c000146030040780c00c1d106420451700110740e0010400c001c0e210300780a80d5502102da45001c1082203502c0d40080d10300b80107401054000c62000d00d0500402c4002d60454041a030403542c690b0300c5896020210010f0360181c001c0c4c41540c010075000048680e000604075000f241c1c0209400d0650350f27a80c00c0c045020403000460601e0107030080300c00c004154080441c0040b40e015400151717a0f03c0d0000f00186c50300021200e28103642c0c0c4405002e082c0c501000c0f054401c4040c940c9008100815180c400f100c0500454100c580d0b10300072010001854100007908051209651304140300d03503a60707600b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 66063446 1250 66062196 66062219
    0x120207050709020306030312010605070212010c020604140a0c0b04031a0f0114040b19050f01050702030c0907090e01060f081501020d0c06110d09060b030c0a0306050c1207020606010306 81
    0x6402045036201e40000d011524054003c0e5034404000740c101d900b03008141c0d0009038424020786c001c00120307200180a03025400c007880e81c44002d450002c02804001c1d80710000950752100244064030501401500d804101000d110b0300c1c1180c0d40011719400c2d05915081c80442e10743c400e12088490058801c46e048003902c400080504c00d8060300d50340000c42e882c000201e50040c4400300465805661480810855951403004110070240505c40c500182d00346414051080d14002d54203051080600000005980c0040d03403608001d0250b481541b5901c41540c251050180781d0481c5090624000010501c15481441603070703098030540c0e40340815220000852109038040d041d41d401030308040400803485001d60a009252480f0392400900d5215003842d505858010a180c1c44030562290300c140107001c101d0103600c02d403400480c054220301c0d03816000100d9411281c400240101d07120000182a0660710050b07981003a00401c00a4051a2080c0001c2d1a041d08172011400309180c00e034041081905807 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 66064696 1250 66063446 66063457
    0x12070e040f1a010e06010905060f0d0b03010e0607050c01050112020f040e0c03030301060c051213031e080d060305060f0705031506070f060204030c06080f0106050708281202 76
    0x25245114191110703254440c440000340c406031120041d50442c42c068040d400001802000c419516029a040250004145a03500c2d80f01620800d814070006508003015030032140c55180c0b0340340014025586002080c0904100301e0020018041c2404120740260418001c2813064032210080000eaa00d03440c90003183c101c0c00001a401c42c403d05034417400742c142544200345286005c41103c040d0901c00340083d1440d4001d80240300000d8012070070f10308000d0100045052894410350503814084000e080e202c0600191002602000c40340707030280042c4013001a20789405401584881cdd41d40210031441c00607000c00c0c4803c4580d44100000135001c04100d4000758082c0009a5400c0e1440d210340d6215440500e844c45119880002004400009800d1403a0040340301c1c407a03540075849618504051080c00003d41c4204280b0110004000e02011903d04160544180d414680c1d00c51106040088450142a0002841c21500c1d20b036040c81810441090200345803036501c410311194500105010790244 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 66065946 1250 66064696 66064709
    0x21070b0c0304030302070f03021e010b06030a020a120c05031005120a0b0703110304150b01020601061e09090e010905210d1a030607030b03100902220612111207 70
    0x2008103456504000096800038040c2c507000d410110961100d2507000002c58080300540e0000030050215010007000e0710480040c18000c202c4064813001181c136070b1000400a6502d00c0e0300107414208d00703018800f104100707407480c0c038100001d03e080b4030068800d80c015104040c0510030b030900080c2c1c03443c282c2d1211414507000c0001d417601603415a5060030140015001c102810744540c8074600d610414405184140d0140c2d546425454604452400321a207540300c49045410140040c084190484d481044645150810882c002d200d21421112060076400c4485c806041c1101050140415007203c1c40b280d0141081d100c115072800c0c80b80003e03200d00d2030000758103001408648140002c0340e0299800d58060703080c4503542c0140b80d0000c0d050540803142500801e40d07480c4a00ea1900b4108041242d032001444204060200380d0001903690030302414900d111100c01c502e001c0c400040340c210300d00030403180100e4004a0311a162440c0070709518001e240c010000342c2150b400600c0d00080c02c4085982 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 66067196 1250 66065946 66065963
    0x1e0d060909030c1407090e0604060b0901080d05071b06020a0b090106050f0f041803080403020d0f0c1101020109020a1811070c0303050d29010f080f01060e01030b030f2107 75
    0x1c1c00d6941c2504d144188441034080c0c029140c001840040790700545007141407000150203585000e12300302044541040c6071501500075030005100c0c61f40300159022400c161800c040b9290080d500d0000805c0500d00d002805085040d80d0010b030702170b00041c42e180d8a074401c60840150340c0d120130b0454222501d51241d01d81c414500b601c101c406041c075941000381c1d10070142c0003080030201d844010110300c1130b04c0740403000204c1031420071044c50f43c1840980001d600310f1400d108c0d00000107100800c060264140a88440d84403040c41403160b000350700100d0050390142024000d150b03030303900c0300d00d240c0c0041c038112070300604266a07a401c189245c41110302d5554003000d0003200a045440c2210242c2291072900e9080369219000710440302c8681100b40b00d19001c000d522240200640010001c0100381e6103c401d001e40c0400b0305c8132004580009030f054501c1d0341b800ca0814107210004801030844050400c0c6c0500a210b00d80c0c4c000403022852107641d114103000c0c43d007090403c6414000901c201c0e18082d1030b07c40f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 66068446 1250 66067196 66067217
    0x1215030601061404091a0a092307032307170c0a030b0a120c090b03010203161103120a0203060a06050c07030605040f12020a15020405090609040302031e0d06090903 72
    0x3c0c0a00a006014030f4014801d9040c940c4402011040b24a00584c001c0d200d001c200015016103001c591100150840407424095150704802074400b01e800c0817440086a0241d0001070007892103544000f812030303981820361880841c003001c07102500c0000d641c078400145180e2442e06c01d808044941c41e001d13400801c0c1c15403424070b070b03010118001e000940b8850391040c540c04000510061072030311090740d04d009540e0348807445d18190000048400c0c0c003000781e002e0b0340140208405004034a61840e01244981844a0951415440c1c2401c0d4803d0b4a082a00385800d40c0c06e012000d02260302451281a044d1000c41a2940360360b410741d1180250308290034568071a1038180000b40c00b54002a030841e2240c007094003c1ca17010354a00030030008010340f0a005900c0317540841e0900180c0404c00d041c3c583c004400711f140904000100d01d408100a180c540240780003004142014800c1040f02d5001c102d92070070a002a55038000154a644a079032135a00360b074100640420305a1280c403685507040c1c0e05489180900 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 66069696 1250 66068446 66068459
    0xf0433060323070219050c0414150f0126010510020601080706110a021206040c05040b031009170c0d0e031515040605100201060906080a0804030212030405151215030601 74
    0x8001c146500314045c00820340c00c06190a0f100d20b24241c0b040d0094141014020f00740021140d03400040f0740311105103001d11101c62011a0005020401580d01ea81c02004100c016200783c0c00040d07090b10702c1212486d0f01310b52551401d14546c140c69040340c4010302c0035402c440480e9564428015003e00390001d000070010303035010303200301a060198901130700c3d2442115000111521000000600c068029104002c10003071140e0701074000c5c1100300d6041010002141c007080c0c2e04c0c042408548085541e412000003403048110b4000401c0d820303804016500e20b644a1400c0e100d014140808001c91111a51105140740210708101448122640c83c0034943c2c0348604440d2001207907800c02e400aa48a50210f4203840d1017102d480501d4054002080032440d061100c0c0445015078040803140d0000822880040c4030340e0101c40840b501110222204002e00e501e03c1c0c25031255034401c40c0e2201410700b190822041c20005001c0d8203215000c0c40c050350b0f403110300c00c0c42c10405ca40b50556041c4c100f6001032085 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 66070946 1250 66069696 66069761
    0xf0608010c39031706030105040c05120304051918140f0402061905030702070b0c0303040308251e170106081009051003020a05060a050403020f04330603 67
    0x22541035001484440c0044048810b440041410550000312070900000742e00d10b01000031500b065084d4007c204130715190300d80b9421321456000340c5100356099046c0d03103c480d00410666000d810010650004074841c900c0e22119980f551080c0c200502d41840b80d0160381d05184036480c07180e0041120314105a0314603640341c008000c010405ca900c584240200555078640f0381016203c1d003416190aa0349042c0044064a8404191302c40700c42401d0803c0801814000482078a40081e41030402c8540340c2c84200010a030115132103910601c80c50580005140300d9840000b0f810a620070b070601e80c481c207a040c00100e52400603800790b9400c9800c0c4c04010481e0b01e225620403980503804818902c107058840060300c065910644192034400003041b014015480c04440080080c501206c03814940410250040c0a40c00b4501c0b01078400c0080001291071070300c0e5034118001900c81c100c40303082d040c48032500d6600c02c580d5400e0040c020301b03418080416228000d00c00c2c3c5045031788081d80040c00c121441c0b0520007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 66072196 1250 66070946 66070997
    0xb030a03050d180b10170a0c0306020f040302030a030320030903030f0a0b06210a140109020708070210030507080f010b091e040c08010303260c07030e0a090f0608010c 73
    0x50307040f052020030300441c0f88545402d0148620a1401c3d0f0514a000d50040c440001c00c030f907951054200000440c00130308c090711850201e0380d0005025840320041903001109000b154400b0f034150003088101003c05074160b204941080c060035520302c000d8110001c102060102321221f8821703910800224205036401000701e42e0050407400045004540103010407020781003c006104070064803569a503e03407030040b8074a5400241c0039010030208501000700c0508080c180f081e000110f6001803030740e0900507003000b1140183e4000d0a1450400a03411000700141411500000040d00705c0c000b0908c00403101020074101d501d251280c0c1d0806c1401d1040100c0750681301c0d20854224118104004182c80754001c510100c40a03441c0d4046c15899410081c0c0070001720410035010340c604204000c2c060350818101c40e000b0108048082d154000383c54150b40c101118010380b540074100880004a011003078102c0c900c28011030174281709042e654001e0304e0a0f82c10480c5000b012500c078194040320362180010048 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 66073446 1250 66072196 66072221
    0xf0605180105031003020a091e0504050304170f03030c09030c0a0807090b0109090e07030212160e040312060b09030706020312060607020a0306110d180506010603020a02010f06090c030b030a03050d 86
    0x81d03d556503540011401da50623440084011303100e00b01c215080794500000029079001c4941804103203000c0d682d1503101d01c6940a0302541ea40c807000e84481c20503040000843c0510712104407507a03801d10602c0401550000c2c000d141c840d100700c000c10013150070324038494400ca4110700002c146d80d40c2808455030181440300102c030b0411900c91000102c1052a010f20030243c1071220181850703030708600522940407110300080d0465442090204100c0c454141c0312002c80d800d103c041d04d25502c1c4c40ca0300311894014000c4031031045060000201344510804010403c050302102280d16055490300180d03102d00031180c54070200c0f10103200180690a000005005040c801031000c0c12154503a50383d441101c0310010200b1708103c02140c0e0000043c201e21849003003061400080c00b80013084d998060f51080d05004000405401043c102e064a000b50080c511b180054002800810784071000100280941c0c00f58100003800c22440080c40d0402017541102160169070721454420320040310f0016101001004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 66074696 1250 66073446 66073471
    0xe1f020a020307050114010302010806061602011b05010903110c01090b0d020a02030c120a1403060904030e0a15020a02090a0b01021c020a0c120c09181e050304030c0f060518010503 79
    0x10000141c081c1b0903000d034054100483c0300554118000108012001041203000d100301300425820083c00c0c003070120841d0b1b8246072103c00d01e2120545004158110000242290f00f40342c041010507400c040b5194242044c2401c03598810200401141d0303030401803058000031a001c0102030103034600b540013002510954011249052100ca000d145460069005070000100100389214902c0e80881010704100e0440961410b50408400148100c94041d000030306000d0400801c2c0300310341318111000000d100130501010100c041520213034a654076210200e1065080800080d41c0013801c5c490081c1e00350042e802400c45407072001650006591110200c0d0130b5200d00e400420020310004d01070000703811092054650303180949402c0700c1c801800e4018819441c11300340100d0000c1c00d28a9074212494001c1c0340694448205014100042c10025010304503000c0050084180410b0102c00002c8178040140c90754036541d03a54049030203000d0140c12500000344261001115031188024581209042890 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 66075946 1250 66074696 66074707
    0x601030b06042606091b03011e0c140a020d08101203080a09080406090815010503031804020f030f04030809120702040207081603030605040608010603080f0a0203040902070b0a0e1f020a0203 83
    0x2440d01e8940105da0041d02a0300c6864017180418100040c00000901503000348010a20280d0740b8040c1c1d41c1c000b510740006a90340c1841e4000510844105240b4010300c1c1010fa600c28030315200031348400040203060b010401c1280850100b1491355044021940c2e0dd60a130348030010280e900301d070220300c003074001030606440ea6008404940080d00a0000707100326110310301070904d00b00c5000c0c10210144018104040184010070060724040111102c1d88506404000042e400200007070007402103840c8000c0c000c41c040200810b2600c041800ca0085000b034a406026a4610b4841039035080c0c92641329070120010321105006003130540291901c00d00c91000d0314285550000c030840008048902500000e80b6440c00b0003050402d031207502c1c094130055009100c4142551240b114903c06e40f0300c0095103907000260701c10380394400e10540d4090840304c0303030543d41c5c3e08040c00c00f200c6503c8207440c48542c10b860284000d0031613000050001c049101600504031420503038243c40c0094002d42e80000030760104105 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 66077196 1250 66075946 66076019
    0xa06030506031609050f06060c07050f04020f0301030b01060813170d14040b0406050c0a090302190503100f1d060a240b0d0e0303040f0f05030d02030a0506090601030b0604 75
    0x20780c0700181c00c1d402c13000030302850540c001051074800074107a64016682040100c07001c0390042100c01c2560400d45192115007881c00102d4024417900300f00300810000840080104404151401d04a64090351100000e4480722020f905008c100140240030700c102850340840311101c60050501c02c100800f0010710390014095950454004135022200ca5a1050801003005600c2c030610f608141038103036140c2880003400000d13203100e116000c040e2140c1e80301001001455810f02c0054007030f060150644070001030074683d50000d40003000c9603c0c089070401048a6400d60921540f03400611500000d084d55102c001c120310042c403910f25609404c41650305501580b101e90801c4d000241240e400c5c0595030a4072044e80411204150301341c81d07207038200704240004511200480c03021242c0010300c45c0668180381c07400d185540b00d4800301102690005c0200214151a40e04c41c6228040c240e5150b003407560b4003001142114244008568855801d12007448213200b0789024004c1011460050450311902e441b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 66078446 1250 66077196 66077233
    0x402030a020304050d050c15090f030f0703030e060709030f061b0f0306090903020d050a05041208040509060a0b1c20090a14091602101103060a0501080103020a0603050603 75
    0x190852000d980000900040000c2004031310151461032400504044181c15502e44810701c5813000032002c4184008161030032000d20804001d0b055240842e41d4441640c225509140c120f901c0940102c2e14100d144010031501180c928818281a40e032102981d0842d90341c00d0f0f10444403002500c400360741d056a1170400e00300482640d075448007602d0300c2e403841489510003002c0d99043c1d0049883d01c5d003090454400030b45c0008295141d29501c0c2801078072120507513001c4075176001d00e5200403070a8402c61243e80c00c0c070000701d0041007500e0b01038075444a01d54901e030600c985031407103110322442c01a0401c44805d48440b004020460380c06a20341c0421a413614000300c29141c0300e456401e03200d210b00052405410b1500d626140c0040080c1d0b0b6014a06903000e0000890080008040c40745103032900b00341d041410310910107866515004034007004928904010b046154000316603990080425000105a541c02a20081d040b80e50042411610500346442180a00303805009160188a008820702d092103611 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 66079696 1250 66078446 66078451
    0x15070501060b0310080705090105122112010602010b0a050f0102030d051e010e0108060601080703110c0706030c1b150603140a06050c090f0108060303040506070303062412090201030605040203 84
    0xb1039580d03440b800c220701a40c079224015072040d24141d1046004018580b902140181103480031a0f04218128801e0b0341c2d2810b2245420025401c0c04117901402c2400c80107101804450081594610f080e07030f01e40c10306a00322140d1044c6198841d072103c80401142ca002c0c0300718010a001841070341e050000d025050350541c0ca003520102c80160415903130307080b00c8100305102401401110340301c00306549400042622072030040c1003070381004002400281103a0180c0c1000f0f00407401c0540e0695540c21000c40c064550081e0700403880002e0526090300c080502c60b20080944a0711041400040c50141d61014a4a62209400c100140d02e42500001152102d0030349418111540d0217040c00210b503103002004c8a100030601180310178207010b80d40154660b200400c0c1d50001c02c2c2022501d64a42ca40003a10314061a448143c1c040030000303e50f4100b6901d07821080031500102c0d0528106868001404d0a007660000740c140001c40e0003901a80404294000c0d0305214010f040008440ea1214041000c2c0d80c000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 66080946 1250 66079696 66079709
    0x30203060f040c0503070c081605010b041a0a06050c0726010c030606140a0e09070201090308010f030201051c111201031a15130e06090d090e010803091507050106 71
    0x200401803541840c20044a001000320340800c05001c1a0750702034940d00000e01110104498002800104103a0f00f00702d40c41c103002442010607161891030914040c013a0340002500a9050065103400c4c00403040c114280fa02000705081c403000d0030201e0844403500080211401c501c91000000381c0400c240c2c004002145c111108020044d030200d00660941c0c1044800c42e080600e800c1080000d16070184a02c0031500c0c0c034501c883e0f62482c2c40c1e4001c0700e4096243c40c1b441e0703010004200f44011070b6015408002981e00c00e482c3e12603540e83c0d41514404601d45888040e002c038004000e05110342180c410f0801c490960107000140b01d01c1000b03030500e40c9403c078005013078400c00528010b20a200b45c1d2081ca8040f040002c03007001d0a81b812820388160245100e0815010307180300181c0f021890401d0300400308207001c91045031082e01d403440345075a03a1001502b507036020a00303224002c5180e8484030381c418103031540f80004616002d911001d02006401184c440150319900b4880d450010f4400c1c06504014200c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 66082196 1250 66080946 66080951
    0x313030c05011806091202031f02180906030a060507110604030207030605160e100903060f06050117090601060f0905102d020a0f11060408010507140702091504021903 73
    0x2444005018801d83c1d83c850441040c1601042004950204160003992841c0742d9410103034409202103840c0c051005100f00d05120550000701130300e10240d02408801c400c00445030314816410040c007030f5024060360b031650550007800d003210100d03050b600302c65081115460502480c0070021042d0341003180030345080b00141c20602d410010300449004a64000c0b1110000000086c0701e1a405003221090150300d1340221400540b00c0051806102d0881c01035400c017a050ac170400700c0c01f80c000c0c002d043c2c600900d800b04d008182030b420306565031081c59108a0700640100201e9080c01d60954401001ea1000c074200305e0780b6100840c0b651210b004240e44801d071303500c5042da02c40e5451a83d072048114140c500780060041c9005e0903c0c990300161422405420540c0c15070360305120b04101d000d802e40c1590311600b10100190002d00104150300c80e6201b41a981d03101042c1e95000303000d440962160090207588070009034081034191008101c5190780703840c0204011320300303000900d20100b07041da08807060010a5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 66083446 1250 66082196 66082199
    0x6210303150f09090c0d0809030712060c031107300c0b0906100e0a0204030602120108010f110706020313050106080f060606040608130f050a0c060e0d020f01110313030c 74
    0x10502d4005411900850b403110041c94152005507595000c03100c55449207412094000902c8181012140c208402405482501d5203c096411001301c41c0034080340e1043c941001468181d2080c4641c01e100c5055003512403030b00a0a4a84600d0158080e44100c4450a403850b01001136040c504245a003d0b66074072801801c002d0360904050142c00140b0b55001038018508022204004014010960305031180101854956403058002401540c0005089610010f2040d0795200041e2245040f15840002406500003821080d000e0390740549100103880e40c02c2c04079000091481d00a5039011110610640e17411842d41c5486095550340d500c80445900124280000700405101050b8004070035180b04d8a00b03841c2c00001048044028180c401081503247d044081002c1d0200c6543c0c031a80000880c0da41503602e04068407114401e1040310089524038030080982c4c1130501011310b84030380007480345400c00704100c01036406011840901503c1c1c042084044189144800342d100690f008034507003030700103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 66084696 1250 66083446 66083449
    0x3011410030c0e01030e070e0108010618060602030405010c02030c33161b030f0302010510060c170913050a1a120a11040e010f05060f01090b030621030315 68
    0x111401100c00080500b001100b070039650f0041540c48800c0c0c802e10f400034030344160b410040e04007015070300b00a50300300c1e41c90000680d1000542008041c0c0c1e01c201c40d402118004000c01034120b032038500c16440235070410310041000b580120711a1054074005002d407207480f444d5400040e905140005819021000400c15279413444803844100701c43d2140006d001d180041940a05082c05811000100071080200070215031581100780d802c02540c0c0000e84a04591440c50060701802c800c41d98405100312044000521a204880110810f6041800070001602c0c000d25108070b548104180c0340c100366620311110b22101c0c0341c840e240c480c0d80c1002001a41e00200d1550014144444041030b208095401d10700a640c080070424084080d40910318002c1401c148001c1000b03803a00c40d6108110703501c0d03c14048a00325580d04041e12940d400c90b0489010b080368401910184418029500e002c00240001005420700e2418040083d0300e2038212007550101c020014a15441161007180c0d081030442d502c0040d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 66085946 1250 66084696 66084709
    0x3030f06320d02010509040e03070b0708151005180609060d02030609130b011202220510080303071205091606120516050304020d02130606020c031b090402060708090402030114 77
    0x1104007154100146910343d00020164011008218400d80d03a4982c1800316040c04c0048640660740030300700618074580074074040c042e4403003125140020700140c81011481d02d0020303889400300ba481d848076410302e81d21490110801840c03080440c0c02446c20440c096590f03982d48003411170b101c800c0c10701507540d18108060280d15400074210743d20058a60b042e0400248850204030305441041c080c054450101e800002c2502c824a200c0084140c1c03141e4030701400e60b04d6170b081103218200c1c600298400c0360343c1e0301115540744422650300c0001102c201e0380c0080c801d40e5030001900700c00344204a5880385044100ca5111404540c802c0c004906540314501920849004055100d0f035001e441d0400c0350f12496001e81f0030b101c0100005e1040301160580b100310743d40c4840c000c2004003142c20400807203841d60800b035074501d0641c15252084c800e080001700c985141584590100e8400703811403060b0780340d650901820303410000701151405000e2105003041c3d120761000d1070081c0411a4910140041c440900c141d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 66087196 1250 66085946 66086039
    0xb0408010e0609030a11070302060403080304140f0d1103090a08160603020403120f120501060807020c1215040213020d0207060b01020604050615040204080a060b040606020d020a03030f06 82
    0x181d03400c410b0800c04002c4010059440582050400340f07034854000d10160308184042d00025440b500c0031501001b802142c1c800b55110f24400e10007802c0000380030302d00a50fa224000c0050043c1c4d881102481055886103132102c0c1070852503030449051040c020001200800950046443c581c41180c050020010300b8a0b01ca000f00ba503401d0852811b070030341e00c880c282040612818814032103400d5444000c680324414070322031442c44000c208941e50b1111001803002800741d85010040c401e81e400302d4486e162640c40d41c400e00903424002c046260b12a00700396040c08000b0003d030b03880b142c2141283c00c10320940c00141952660008016668655450041d04840c101c0c0c6030742e411507000700d041100089000511580010803401d6884d580b030b210300e0000c0d001c1d108942001c50b150140013107035001c12607142c20a1103241c008031010700801e03441d01c034121b0b43e48040100c0c020042e0302200800010070b019601c01810102c3e001408201551180110201000408289030310200f160302d070300a206400310750400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 66088446 1250 66087196 66087221
    0x10e01050a02030a0305060d0f0f020103050c09061b0102160302010c170f0a05041401090c03110402070507090e0a0f12031a0f190f030305130503030304020d0b1005030303010b040801 80
    0x38107241c1100d0000f0342e0b0f40616084c0406040ea92404510517584282e0510701d8554803c0d0003003107686081c684500602d0481c48102d01003801d10000c15007010303045090314040000a40414100440c005205243c202a29008903055500708000300e401c1c6080c041c0880c200f80a5000450b1020328058010403001d86001c0fa03a000000f21414040e52403800900c450b08054204808201c644640c02c0c080740d902442d0010300c40d0f030f61030710020f40b04020a40051104490152030480040703200c180070f21040e8032803a0f0703000b00f250b00101014005850742e98000c80c014210042140d04a8490766503070702c042400901d040c2c480015913500701e45039036818041d0400103038484030b80c80f504400d10004212880c040c1c2c041d680c440c4601c44e00391400810309120041c0289102464030321413076a40d04001e0020751061020040340000c0101c045214200082101e0051758054004901e04070142c4518104500192000000c00300190002541f550100043c502910000360080d40d0346142020b1700b421905c40c82610b4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 66089696 1250 66088446 66088457
    0x5150106020610090c0905030f011d0115030308040c0305030d05010509072a080f0307050304021804020d151808030702010b030604020a1a0c0f100f1a040c1101050a020702010e01 78
    0xc0c0f021282040c080468001c07400100b4007030740f0b102040d034818809410840e0036101e17a0001030b40601054004191440d001800a40c82c0c040204046080e1010510309500004460804100082c840c00d00b60b03034040c4c01007207994071640c1c83e070f52264119444084001c4116449900510081c07400c07180384c036046595400c0c600a80c040020b0542158a50402016003803001401140e0a10030750000300c400d6030b0603081545640e8501004080c0c49070700300f9a001e0703010300f2222425030000244d0410b81c03401160014581801d07004180d0340d040310070564400c003010180d1120f8681c0300c8a034820140107003a0707204e10310b965280c0ca003000c0000d0840c0c01000741c888c441d900c9a000e02000d070b103a500c81801135403018800100f03a2140e40418403000d08c00c41c032105140348940c441c10181c0078800b2400704200d5014040611040000400132400d9420351003600c403c00941116401e8946040c1d03002581e880c0181c10309007040318680d0f4050b401c4603401c440e15095180c000030020219030303020a841112107802d080c130 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 66090946 1250 66089696 66089701
    0xb040b060304050703200406091d071a03181c08090712021002030c12070b0705040e06040c0e0301060b040f0509010e0a0506040b1002010903030b04021e13030c03051501060206 77
    0xd0300d5032070213180700251000c000e0000d018403214111001513061300380030300700348082981e41d980c0700f00070160841800703105a820f500700080808040390390812100703654818690001d0140c4001c010b41d0000e0005d440070003501c3c80d804541c20092101c1402180c82583c102c184400240000d80710380b80003010650560070010307040c042660038415030443c1c96016074081403000790888040e459441102840038051044000c544180900c083c0245805032240701c4c1c50f0182d46910300309548500840c020449417034107200c0041d006041640c46003103050102e181000308d81c410740c80442e0840b066604a2a108003000406000d0000c074500641c004100070b49150107198980385403051408030160003110758503101c00114807255550341000050220003801c4100072080204041e000300414402100404c0c03e00c0180541864103100351461540e4607896140500305003241ca800f540c1c01411f03100344104010700040041840380b004807020390300c140001c00f80c0361664001c12418250582c0060215480a801c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 66092196 1250 66090946 66090953
    0x3030a0f0513051c030e0a05010903031209080c010e0f03040303050306011b0602040905060909010501050102030313030201180303091a01030807020409022403070f080906070e0a030c090b040b060304 87
    0x288500c0d600e124900603855949402d82c01448071032a61019030711034420029002c2c0d9031031104081180301c0c86078a034266400000c20501c260615284600c030701140e645442000861702880c40d01028040010000030361140da5640d494054100700586801130390344240301d1215410802100043c0385180006504103072455600034000e1000500c4241000b03070900140075428510740444451681c44003066465603120042c0a00400c4100c4038207124280e0003000c9005820306109480c140d44060b8051481c503652001030820010262a0450840d036840030255014112207181990080c4256070205034400c413070400100c02c031030030300007001d646001c0c42c0100001010715085400160b41070702d0100c0d02d4000303400000c2000d01410041d9900b44950401c840550400600030342c801c1c40760303488500000105900440354102c0441d100d1a465020202041c1901e0040c20000c500280044c000c9054a03107a40e40d0500313084130b55000c50402500e9040020035858140034404c1c8096082e1281c5045160544 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 66093446 1250 66092196 66092207
    0xa050102030717070f0501020d020702090a02090306011401110f0a062d0f060806041505070c020f0402030406110a080109110702030a030806130e060103050609010c0504090b0102070906180b03030a 86
    0x30103c0266000026141c0400c1a05140d811840741c100d80215203e1a01c0391410000c1d40c001e050480c40f65004000280700614140b00b0f0316170b00b80700034000717100580c00d0070102203645900070303406030502002c42e01d140541c00c010400412145a030a01030400d900c400d00e4400260340d4105413401d000f021a4155854070007200108015000000c00b01050816002450038010078050304101d4081c0a070000700810301480c04284042d40d04800802c10031640e035610100c888040f0081c0c000c3d48510140211031081c50180c0207103810600400c0f0018543d503040c10341d040144d022010758804200407000400031b00c0313054400ea824400303104807010300e808080c0d03000a48858905000500344007100d408101c4a03282c0020104407604401c90030005880c201380c40716681c040034402142c182c420f550015001c40410700901441800303a440302401d103810001c041c00600602d1030514110b00c14641c1c0040e81240394060f80d030007442e800e40e48102034802001001c0940c0ca00b00341c454000e50042252155056101 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 66094696 1250 66093446 66093473
    0x100c02120913020a020606010f03050105030318060904090f0519020604050904060f15080c03121b0a20010305070801030302120a050f1909060e0306010302040e19060b0a0501020307 79
    0x404180d079120034120004281181c2101080e410300d101003045108981c00045103400384800340c94030b60380143c1c0c0c00e208038280c54090103443e1b010b030820720041d510380034080b2648079401c50040015080c001e1600200e0200c442100e03084d01d04000703608142e4240507040c4020031078a80c2d54a0740400603207241c1c001c41e00c1351040d40700d2203000d55240d2001405100e400c0e0702c90954400d88800600c190800c0c1c601700708811000f4000c0080c5401540c0700f007800d62500151081d4050342c0040341034141042c2d020b150199006076045450300307015844002c7d0001d4031940810008181380ca92600e040034004c8001011610300078500024001500700500111381c000840c03158114520040c140e5800c83c005048603035001380c202101b0742650108201880030200c0c00c43c1d5005000d0391b940d489802d540c400d012912a202a1005171b0103070000d000610141c14160004810069240c044581040240594085a28880030203441c407950b2038072a01060301e040d031201c1008010074802141005500d8403841c856007100c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 66095946 1250 66094696 66094723
    0x30b01111903050d1b020309100503010f0515070501110715090b0c0d0902060c0a050d020724090e1e01050312090405090a140610051008071404080f030903100c02 71
    0x22855144c803095640288944520741c40e401e500f40351600d000a9540e070030000d078092080004004000311984540283d904803000341c0c00e000720182c540410702c5034580910603141102c40c0e04000402c0401d001340134009601240b185055610304103400c111843c4903202040400842c00c040914001c1082e0500481e040140044043d560703001c8191221b000b0819204025006103021900490b40c800200b0b019003001e005005958001112032f004036201c841c80d006640c844d240074500701c03a401800c998180400a1030b414184541919501021200b150440304507800500300307103d0703900070000740070f8050041406900424088100705e047c00082e000720a2000d008076901d100040300b040d010030200800c02e4016601161946640380c80750380b100c00403180080c45401c4844e00081c00e050001050030400801c0e960340000d41c4409200302d505203192150448000c00500010450040c01d00c10043d00d200408010740c0e030799800c08107050511406d440a02c0000c0d02e005c6888d01c54079000f150000c104001c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 66097196 1250 66095946 66095957
    0x4080c0f1e030c031005150a050901030f05010605060c0c040606020d1211040512060f0702030f0301030602033c0109020c07150314040609030e090114040b1f030b01111903 75
    0x10310000b083ca03100c072000006a061150002d001860889a03010314000d941403207548891a020138184140c4110900c0f509410020715030042000c195000903400c0c14511810000c14240d58903c0000d196030442d40d4000300356004104a181ca91170144102030003402240041d0428611000c4007400304900464005601a00d82c814031000d41d040702c044401034032004282d041c03440c200c0d1100e10f541b12021544018040c044d14081890a4000403c0d203051108101040785542c1c2140d48086c0650405081000100180d040ca01038035001340156801103040c5405a144001031590500598001a03100442c0c003441041207070786c00080400e00c00c003034642010f41002c0403003030550104c004281e440104919800b40b132050004001e00c3e6080050710034065522219280920307002c01900c01020721800090f98400721203540281081e0304114503080005000d111100d0310440d80e6002c3c840c4c507800c040e0020f40e1310840407a07075603002a2100e140f0300703802000708408100e250011025a1454070068107004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 66098446 1250 66097196 66097249
    0x80d1e0806031b0a0f06090e070c020f061602030f0105071205090c09061c110a06030b0f01030c020f060c1b0304060e09040c091509050604020a0c150207080a0504080c0f 74
    0x8035044d188600601c0900c40035000660380b8a03000300104040d000388500391030321201055006204604902083c1d800034103040018440c0c0c0b040003519400100f60030100c5a160345010056034050000c4007908040c80b0001c02e85103810316004007040c50038200a2285460141400095074001400c1d0307208002c19101a0b00321b0311207100040c3d1a04001d001000c900341e421b06018104100079465941c5200d040d0703120401580c46010a4090700c501003000e6800500510703040181d0361180e0008020141a401075071205000c8001d00c5050000854600c01c5080c0700007820088001051040b070081009400690704044c2018402080304e0f00d41641a4440d120302c2c400308090241e0f00c44e91400800c1c1c7c40004008201010144254851251203080a0185000c0004800342003d008480001070507549204041519607206464030780280c050540300c81d824060280020840700082014a1041d16010b4440349480e00f11450604100540b40c00f80b081d070b070804105a140c100f100100200851401d24a11 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 66099696 1250 66098446 66098449
    0x602061306020c1b0103050109060e0a050a0b12010608060702070e070807020309040c0804020f010e03120f070b0108150901020a14030702010f022b09020105040302090a06080d1e0806031b 82
    0x3d0260080301c01203030044c01d40100301c607031081c440884046020380341886985e1f40c1b440404104e50302c5120b01c104561027480094044100390344074a602801c0000005034195062340071a850811030807440007503a54414040c00310903800c2000c83d50001c502d2000b80b0056090441070322850700094071a00078001c0300008120224001e06c103071000040050001c00c404101400d00400406054031f0590040115401c5980c044d4880c0c4c81c1388401c0100600102480f40c4031810b540c00302da0140d000d620030381c0780c00d10040b40000c4100d98924001e0016034010841d00780f151421003005031001d400302d40b071a80704115407002240c01645181104500f01409a240da80310013042e4058488902c48034030803403000035224903030103111800601c0100e45499910b41c0c121342a40110407140414006800301c0c1040c0000c000600d80210358962208190101290090361280c0103854040705d452010041507024558110a03207601c00c2c3c0e2443e6410b62b00d050f013054100031000c0b0b91103200410114002211403c108140d9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 66100946 1250 66099696 66099701
    0x607060b091303030f09082712030a11010207151a0405012327040c0305060108061b0a23040b040e01060f050a0207050f0a0b0a0c020a0f0602061306 65
    0x4120054030316030180c03908000040350220040c0e0200c000c01e20704103a005d00c0300310b140301d031400305039120361198a48240062075203680046c1603401d00200c5001d020200c043d450702c00080b0100400c00004644070012079030050301e880c0811246142d5684144030900214449010489110f0194803000031481e12070400000344050402006800c03a0510000007001c5540085000d18485141c807940001a201803c010806e10350080c4a03000440101c0000b119030031001f0420b4101e4421142400712555964449080400036400303441141c01c9081040881e405050712030240752004170a8030310700744600301c001d4031740482d5500e100c07020114810f11038070140b069000c40303001d006040d24042d00e5543c1c03445000c01c0542e0901901000070100e0100000740e0780034405950000c1d01c0794015029281c180b109202003d40c0e10000c41c1c6c0e00c1214003400090700301c5450010040351500d543c4104030446c01d4010322894880b0350b40051107a0516030b40400c000e0fa4082080da800203070080c288640c221060030039001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 66102196 1250 66100946 66100961
    0x2030a0e0d0903060b0f0303030103060b0f10021606030207120e010219140c040504171c09110f06042913060c05010f0203191e050c18030303010501020c060706 70
    0x4500c1011100741000303801c1141082101c0c4240c00501280101c0c1081c4036100d0304101e04107426034801e00c01400060b459800101d6103840c0a0920301c9141280c000243d040302e5074014070f0000d03800c0f50802500141d03690b14010060034080c141036290090075540c0c440100050b8010304100324240319218100c0c0e10a02000c0241d08000e08161070080090401c2000c3c0003c18004035998401d07800c203004075007000d020b601d205603004090150000c82c00e8800341020b900c100350114240c180000c20000f00803440c45040c1990f40148040903406403810240302c0d279903031060011842180103000c200318071051f404542d001d50251503200d84400c0c500e0041c0c2d10041c0100e00358048081c901c190041441a80700240d01c03680c0c0d00503c000d000050740a5038920492105076400120540c0c000d00d03c01c0c121210b6009445c1c0240c1300410800c0074048801244100c80e400d8074020a005e0001440c1c1d40030300840708078044102d4040f4061880d65140c600040c0d40c91543c408054010540455154180500c60740b01c8007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 66103446 1250 66102196 66102221
    0x606051e0d200c01060806090a030f0215011404150b0901030f0204050a0608040b0f040c0302060304080c0d02030c010c090f0501080618130204050901090215030901060810020c0607080f060402030a 86
    0x60b50350800700c180b404542101d002c0300320355881c0c041c0008101a0009031980201d90b42c2c4042c003841d03200c640301241e0110700058500700350302c60440d081c80c141c07080d0b4080c1c5000340105081c0c0d460100400e405c00c01a11a001403511241c2e602840520001e1518003c030303a42240c1c02d007400640c18034800c848001900035540151343c02440c440d00040e1840c1c0040f8000c2c4102e2141c150350a0541d10411030b400c50764010303a40a010010240307801c1c001030a0050085400902400d13a45e8203140c0505d0781c103464000718203041401a00080790b810031400c0240521646c400c1c160515040d07050411035036420390364030b034801c607410404120f01040c0b0580300d040b812022800c2c0d06540681515004580400c2481d990780b003240601d1410300000c0c502c80c81841411101a0300030500652021021060007460b00058805602950780301c6000803600d004001c2c100c0e0781038a4400140e200d0000180040c20018024855014044c8120410410b400f00381c50455101d00b0480d0010385a45a111b0b00d900104070303600094 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 66104696 1250 66103446 66103481
    0xd0606080303071715040209040b03010f090309120308060409060b0d0503030f010f0b071205130609030b0901050c030c0705010204030b04060914010b0f010305150d0c03060606051e0d 80
    0x81036980c0e0100040d803240d03646850f8110310307000c0ca2400201400046480e401c4007481042c80b420a49402e80040004178030003840800d60803000300000b821078800001c08403640340c0e95501c003020140c00150304070040c468854076040007a8580c13009043c40c40020f100921903070b911802d0748200181c40d8800c81c0385140291079900c200c00c051074a940e5036030007603800d41300242c1110b00000705542901480b4007598030301d07110942403010a6852803c0400c03d204134200f40308051200e840400a04280c0c280100a00c0c1c0e9440d0110f0320714103141c8d2100d54068290380c0c00d6410703c41000460500b500440790051881c10320556204c0560404500902558000034840c440036001c3c0014490030790000400c40d40a01418115141d41d40342440c00c80341c480403da034111800d0705410401d50302941c0100d9001c03083c41c03075803c0004a041d000a01d0724240c01401c459450360000c0c00d20501402e44240c0d0090710881c10040c0c9032010f00c00085a2540e00e003804c2040c100d034001550460301d06c0340d820403030640c80d155401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 66105946 1250 66104696 66104699
    0x305010203070f0e0409020607031815090306050610140304060e070608061002010c090b09120304120b090c150703050c0706051803030304021c051203130b01060e010f0503060d0606 79
    0x105943c4100101ea40010805107070b0113030fa031900348940690180e0041a2610f0684a540e06036041003680d40d030044109003074000020030f80c0c0c551007018004282c40d544c43c8822821403600d00d00300e41c00608804d0007501d2400340700b14080e801441001030251002007468903544ca40c50204050b100a004400490140ca440040c000f500982540d0088404070b451569140c00c101049080b1070807180c02c10001a541c1c0803c121003851180240401788025000e14102a09018458a154031030307400310030807480400000302400074250180390001c800f07001910f010903420000030194034411110a940c9100026458109401001280d101e0b00401058400481e40c80724050515040641190382d6800221a43c00303a5160100c1203e210300e500034441220901079042950300007410000883c2d041c07041013110002c4142140195100c0c540e0441e050b81104042d14285800d0310b07042e032181d800c1c0080d040441303007141e811054001010b03035940351464481c1d50b0100010055003016502408580c0351850 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 66107196 1250 66105946 66105961
    0x705070608061206090d0f021504080a08100305070620190212010c1d06070c030c14060301081923010e060702030405030d05030903070204050109020903100b010e04150305010203 78
    0x100c2071041800711030f0000031804503203080d80ca8000840d00743c5040d4005032400c960140c0550400114202c80d841114141d4001c0c030300d1031228010555007500c0010020807140d440035030122a1a030f010381900c03503a0303c071580b5560782d140d507070f800a00070603003840921081e500ca40b03125864031058140c41d8008881e912000c2000320340b81c100c03102e0026802060b100c15544100541402044028401542e03031003485100402c003400d1404241d920079038402010062100070410780000640514000c141c080b000d030b40b40400003811041c2d14a402806413406200400c1055808038030070082c0007036043e0804951446141000c030682400440040d110480811980c0c00d220541c41054048400d20440b0b40750f1b21688002d0ba541e000d41d1056590540c8100790800105129501035500103031683e080300d08016041d4005011344400b40c2010124960104480b15075107000c004580000804400030081b140e65000000c0c04000c80d0780c1054081c45c0c407060514110003d424088008540000c003c540b241400c0d46d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 66108446 1250 66107196 66107207
    0xc0d030504060f090807050f011a0f0d0501050c13090b0109060e030a0804090c080a09050a031101060b1801121505120309030f070e0f090307120c0f0b0604140906040605090307050706 80
    0x751b064800740b00b0810742070600c0340144140c2900d291450b5100309640b4800c400c119829042020444c0c001c4028441d080c0060802d004a60007041d05201c51a118202ea94507480040d01661120001504119049641d66004a903030741c140d82c8140380010021506102182c03506525800003022014005800101c50308503a00c010201000c3d03680700340c8107444107001c800598442d070b40b0152042d0005121f90340040c0c050081c240050348420008210b0382e6641142c441c0c10340015021040c02c011019800c0c1056034001765441c000501c003081000803d1304000c0c10451081c290041c0ca0003154040358201c1d4400c401c20644d580403500808581e0b0340410000166200c801c680304d40e99a0a1407140410700040300c0e180c105d4840d012100041d03040040e0343c3c403603658a85c403d40807002440b51406c0e40038045148131031307280000c9000e60b01c5070040e0f051000900c011541c00d044098100030604091181001c0b000c01d00c250010380040c00800c040c0c4071602c8240c00c6104200d4002d02c0351090000018003960040e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 66109696 1250 66108446 66108457
    0x915010e0a06120b06040b0310060303020c09160207061d04050103060e010b060301060f0f0e12010618020a02071503110c0f0705040903021c110307140f01020c0d030504060f0908 78
    0xc1002e0040560b52a03205407205602c1100400c00500c101c00038060381030981c84502e00e075100070100c1d540600e03442c9102c0d0803521141c0040d00142c00000c1096003500382221910741000c03404c000c2002085417408000c1d180c02441c02660108040348415481c2400f107101c01d01c144010003842048075584d285401c07001050340503c044a25424119074011038684041603e048840c1915a1660070889050840e2201d4510f6082024000080c54000942d100d841d10000c01003054000040e0796403c14060100a806441e100344401d0300400803c0000d40c0d022034000c1c211401e000d0010207024038860b0a80103071403211480514560045449080b00c1c0001460a0801680109903003455844005110175604183c2000e03016a010002500e003400380051032513040801d030300d4007060182c1c1228902e030540d4010f41003a01ca9140c0114008200f090502901c000c41000100851030508005107a40d1680e6211304603200380f43d910f0340020280007468021410039407803400200070f000c504e4902003640e0b4020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 66110946 1250 66109696 66109711
    0x3051b030a0b07021c09051c0b070806030321040507090c050f1e13030b060a030b0c0d112a0a0209041b090f0501080c01210c020a06050406060602120a170915010e 71
    0x105841c1407c0c5038802d080803030b088e54000f0503500950b601c0c4e45c002c1d06e080d04058450743c0c051104011031010000001a44040e24100d061000c5950600d4107010346049640e41101205a281c40c203002000c5401c48111001c42c0d00744e440c600d0b281d0340917034031001c501d0b043c3d0340085d0200040021107580c0070500c1103690007900e11a05881c4503031344540c4103010301c0b6141808028142030510020035a031080700e030b0140c640c4402e000b001007607104040840308a42e0f004444a00604260b103002e0248403c6a0356042c410902510000c02c8400c2250b0001080b0100284c030250240400441d20800080c0301507110019021882c8144169150300d07000ba00140004d03c6813100c1c038003030349020040d01d41c801d40303900a0504244041c5a4050755000b80c90006011014541e0154421141c102000400500079140b04034048c0c000065554602800603003400603010003220005000c000c00300f4082d405c11800000c4000d40003419a40e41d0f0b601c1d8205282c620010701211078084888000141c40b003414050b00e115003a03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 66112196 1250 66110946 66110959
    0x2040614100905010e0409060e1510080c030307060e120f0a09060302070302070512151003030e10020d0311090306040b0a06080316080a090312030603051b030a0b07021c0905 76
    0x1c0d5004958490303090003194002540c11525260038a01034002c1500c0e14001c00001410140c0c0c0d1a201c0d00e0702c841e0f400e014000c1000c20702000850041d1041c120000c007000c1c00078200c140000f03000681c49114807540140754a030f4801201192f50010058818091900c800c0d607680c034014003165000c00d4020a290a002821501000c15982e1083c02030350300c4140d245d0000d1081c507043c0001c20a01d640654a5030200c2e01c650f2030402e055160b518010f40c0100b48640c100c40071641941402410389408075002c6001c1c0c40d103444000f0304a07900240d00207100446140000b00301030104202e215602c2894072090381803140c101407100b40b0420540450040164060400113143c3e11100143c590050480c880c01c0508220f1650b00402c0050000341038482c1d0700e00d400c420060f102c0e50389c496030048403c200070009582d01020f0080010030004405141c1c0503100c86501760712a10002907640303505241c000c00708002c0c08082001d80b4004c014000c40300c00c50b101480418070780203100514104003071058901c81c0300d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 66113446 1250 66112196 66112219
    0xb0408091203030f062b050102090a03110405060a050a1502031603020607081f0b0c100e1501060c0816030e03100b03060a05010e0c03220803041b0b0d0b01050702040614 74
    0xd0502c00c00c146e2410800940090403410728054030540400840030748065408201c4801c4550b5107044030805035206200300021081d650041c402101c200402d25030103500c0c13070f8009000b6a501c035214541250a05903040800e8802c034581282036000d44446005003d28002d0300790b04050300812540c4c0309016568a54403903940702100c4034100100041c07407003400d001c929014042c42e04400028a1000d02c3c400442c1e248a00ca21a10702c00c49031400d0755140e054000a0710f41c0c5010101c18445401070280e8038004050320311a444401d0103108510310310326a0268180e000c004c25009150b00b0480c554000d054564600074102010041c114620107a8864000c00b40000d400918510400f4141c490068441d94540c4e03c0d004504010b0344050040814201d16030304002508510780c0401e0065440340d65019141c0c02c1c186032512030700718121000102c1c0101500144502c0d54140181d8440000144010400068820040e40d07070f8450300704086d410506004010802400340f650140c0b203c08240c401042e4003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 66114696 1250 66113446 66113449
    0x503010b0109180e010b03070806040311010207020102030a2703060c020106081204090c170705130b090108040209060409050a050633100504090e07060201110708070b0408091203030f06 81
    0x402040c00b99024000d6001040006403d45511203441030580030300018401c2d4000d00081c3c90440300760b00c400c80c2e691105003048101036100b00ca880b044c0452a00a40c1032907405da00103034581c002d261003102080b01108280c07402c50341c000300b0744000507801e1040804417a140d0602c02d014240100d00b501c050340c2005000528204001142c9820800401e1403034245810002d0500103450650b41c0385042084035000c2c00c0000a81c100c0417400b5060545459070345132050a45100c0c401c2540c4e002d6840b22a040c0070080144c1d8000c1e030440d070301070b504440d404080d680705070000e40200340010003d021881001c0341c28007041703000505070303015600d001c9510b012032030358000b19203405005d5030005080340600b0403104400d080c114180903401398107080007411b1a413510081d10881da00030025200940c08500100031172502881130382042814148282d2400d0700b240c071191014480c400000b00710008010001d414441c0c5441560480800203000c0500340650300601d96581c1c0041d14104080c00f0400d000c14101d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 66115946 1250 66114696 66114707
    0x203090f07120209060d060b060f040f0501080405150919051f0509030a03020c191a0f10050f15030906010e010e010608040308060d12110106080303010e1303030f020a090503010b01 79
    0x5a00805041c09591020240200d512141408494280d08c400d140d9a107543c07803030083c240c00c1400d0205544c6451502d5000701f090340c510b1b84014103006180080c0b1001ca4400314039501c040110201181d441e803500d208030391902d01410000341304604941c41150401c800424021071f202c1c03d4203552210030180d14492000c480c2c01f5106112242d008114004805019402070300900c1d80c441b040d540107000920301100c42100004084589a0b501d050302e5080070f01141026401c03d40e80c00451101c1c1c034040c100480c4014030f40c0a403e12505240321400940e544c0c40c82c400704203404007400d8540344d00304110440e07950715003800f40001d415203000011400c610240750f0350b0304946041d0703580f002c00d86035910151210381c4c001d041203400011070701070750000c2280510304118514899580c810304a00c0341d007c0c0ca0859506812890f4aa0800c100400c00010303003907030032500070713103c510b0042651205150030703401000c44002c1120303110300224802e00029080003003041111801d500902c035404942c801142d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 66117196 1250 66115946 66115979
    0x1020a020d080c1e27010503060103090c0510050a08010b070503030402010807030f0e0309030f07030506040206090109031b180905100e01021b03360105030a0b040203090f07 76
    0x6a01c59041011450300c608240380e08855074441c054a0014220324141d15480d903505140300300c4800040b5a4202c030101c01d60710038240c100b0320f240d803903e0036010002061480040d22040c100360301c031100d43c0d042c481400120f40042000401c1e5a40d2150341d6140a01944c2100c000b21001c14040b00000490402d0101100d42d0749034000b010354a55a520f13801510f0200000e054081017665074404200d80c00224455a202c1c580407070011602c4d80b94440c10185031100c02d885510160308075080401c0028400124240c0041c0d04445641e19140504e004840303141d080e0f0720280828816a20306501d04e040c3c109040103230341e180f03215010114003039003005040d10f9640000400c107501070046059034117015403206200091500015145c00b0358540510880110f002804090343c00004002800d0185c0c0b00d09030f005a40541100c10900d55102c0b03550300880c0b18051051b040c0040000011400c0c000342e401400c41d2100180b00315103c0c2080b48082e90f5075418481c40c0e140d80e105103080414941640c0c441140d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 66118446 1250 66117196 66117217
    0x1b010e060601110607081003060e10150513180209070c030210050705030711010e1006050a14060406030207050321040209090f07050f0d050102040e0912070f030507020d021f0306080102 81
    0x1440c0c1c417400011680d045000301701e4261843c0e4414003000180450040c0b01100589e50010610640c2100010040768603004481c048042d1070780e81005070341c50f04c41041100382c06c0090700180740780c1b0301c4000e02c0d4100031814000394400041c1c41003002003a08141c42200c0c1d10300036400c981400424001c66003c0b90400d0b11420046081440001d111920a001122509040d1000070907502e00c108100c40ca011103516107062880e80342e80b001c1c0301030305100c0c04080040078a1025030709041c10714008640648101d0280310304160700021340d6400c0c032408004a070007000f40e09151001d001000101504030030000c0e174040f1310034002d40303001c07458045e00040c911203a03d14420250041a152000b00308060000c0003003660401c04c8940560301090080c40900001c003850004214546000296103040031002400340c070050a040c01614045042c0d4036501440d00e034541082a9103100d0f03400010f5010201e9040290300000702d440690811203e9a10341416076140e8400b070142c59102e104d02800c1c5d024255601 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 66119696 1250 66118446 66118453
    0x10c0206130b07140a030209270105060706021213020f010207050918070905010b07031115070806130501030602130e090604080a11010203010902040e06270702031b010e06060111 78
    0x201d01055907100c6040d04000d060a00200c0859034182c09403a6030002040c0c4008070b5404181400b050802241911045400c0707051213003680740341c07002c800040f8018041c1074040c1070049106001c11107103a0454000c245500c50b1110f592400d40301c102103007001510100d02620181e1414405540006000410740304010400303249903481c40d04010010084500c425035500c40c807400003030f4070b00361481920702a02c00a000a40c1d46c80e40d0703040c06000c40c0b03d0300e408145103500054120b00c8079107101c0c5c0c2440d00304a580c5032a144980780e203400101006041c9a05807034061510300000308000c11a801440040360070201c0c40c000e259900814540c04000700c40a1000e9003240703000a000400120090949070805d0410400c0c2003000e2860300e0880c4c0003604150a003560019043c480d0b0312090782c2190b0b01c11012600025070014180030040f40b032090855115000313803c4001f180300c280c002e00a5a801800180842d2952409040054041d00f01c00400040030702450002c1981e07035100c1c00c4071000c40d4000b10000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 66120946 1250 66119696 66119731
    0x140c0424050112020d0e0a0210020609070b0f0705010f060611010603030e0f0d140718020405100e0103020408010c0e091005060a120615030203190203070f03050a0f0204030c08010c0206 81
    0x5480c40120142003d02c110340c2004100792029040c459298285003d100400c02606c0a2051003124003240c0c80000965101c6800c100030f541780000d648080c0c030300d000c80c8140c607158480880300a5016005009001d9401e000c228180c0c1b0110358000c00c1111030ba65500b16410080d400ca56080303034803d000c080c1c009a2000c04d03041160030959040400c0f100c002e0141e241c40720a944903200d80c40006040260f1907040b03580d0420191a0b03071a002c042c04100c4440452401d450880080c1500e0400c1c8509024401a002d0140007070f8000d81c1071364000d20050f07000f4814002d0400008140c0301110034624403d0308050049100d4034580c805401c01e49102810302c07480c1c042d40c2c04040e40c0310301c50705c41c4003001d00740c8549000c00c881d001e074030b05004401055200940c50341070614020000c0d8507000c55158400f03205004000701d41d640001c41101400b990300380000e0765200d000c05400078040c040e110707001181c0000b43c00403c00880308080d208a8103524000c0040d0402ca40d401ca0f1104015251190b9000301d9085 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 66122196 1250 66120946 66120949
    0x50d0209040807080c0319050909010e06040e01050a0c02010f14070c050304031a06030607020c090c0a091e060f0504030f0b1503010f0506031501030c150c140c042405 73
    0x203058006000340c1e241810821240c4e01c01c101c40d80401c018075030681000c18005003547c41c25640d114032140074207102d030038440942c001c10811001482103480924545c8003084550b21030390301071003d500040000303101c9407030160384502c064203945000b60015803908401040340f5085114041c2481c085808601c42da03119040200e80c44141038030250703000d002c10031001000401c3c40412001008006408082500d0040e00b014101080182010155000508005115918040c140798800303107122a107611018640c0e000c9485030078036000041d0000002d050000d460402160000464009a40315103011004880882e964015440300038480305948040c07000250704103004d01d900065a401148241c2000c2c8006402e4448540f920010241c2d0350307052064a0070288a6404901d8911001010651440c2c4c0c49090b141098450b441e2040c0b2040c962421461003807001003075080d000b01c41561040703480381c1559112415421064415807a0018441850300710841c448120030201030a0395201e441c140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 66123446 1250 66122196 66122209
    0x1061a0f04121b06030605090c0306090105011803020a080a061506020307060b01050f0d090c09020406080609092509050612031209120c0c09070c02091609030b01090203070f0504050d02 81
    0x707030112070030002800c0050a401c02d40402c03c0052200d40c0e07021079002c3c03a06062200d030301c40107051083e08150401c100039954550110450444d4420320301020781100c05400c2041064280d04001d5000111201c005017031400001d840c0d4460340100c000700a200304045580c40846914422040942c1007031002d603000c900503034400c00c0700b100c060420514103030030720303103080c5090748100c60107a025981c0343e15490030700220b6140c0d24040d003d40d0104510749814040054800351004000d10710031060400025021407050008010030310750341c800c0045266400032580b035072204034060b91014910f031a002410500c0c0c5120a00410254900507515100d260308501d560380d80014101c107140e12070014030520f003005840040002d50700703850207402140e0351082000390f44071001c0c080030100840103501e070001d03a07a04400c254000b9031610007007003e250302c40815100b6107520351000d001452503600000d41000f89400a5100751459030320a0007603540410705940c1c902440c000c69070460a145001801814a403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 66124696 1250 66123446 66123479
    0x150e0a0515070513060201090507080d091202030109050a0807050607181518080c0910060e0910050d0305030106110d05030a15120c06020714030c010309140703030201061a0f04 77
    0x1868504e240030024420b0f0b40030b215459020000507955030722110180322041c00b0080c003402c07480001c2c154080d190702005102c14443d002d8035007080d0f0110105421035500b503116511540e0b00405813a00d24050b0300b096022500010015600da0040b44000341c6078520600c5011084885041075100490624401000745122003004006014691905418070500c982c0000001d0a2220040c040940c1c14402c0c045411806004004031040e504028050340b6040003070100255030950f6515013558402d038100300034882a50116403c504150401c1003850b0b403100045050764281d482e06000c50342200c040c160f603024001c5003200000e00c10300204803510490740182c0e400c1b01032038000a005030386841102c80f4400045400310f40800e0715a004000320fa4040c41100001d00d1101151000116000d0110707894a403c5120603041590700c80c03400d010420300e01400c50111409000302c500c000c1d12490080d0091006028880c1c103170035641d02910200214800725030352884400c10007810f0a290488848040081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 66125946 1250 66124696 66124711
    0x510050a030902090f01090c090e04030e150a090509011215050901091b06030506120a170720120a051009030507050a0308060a05040204060f0e010e0409150e0a0515 72
    0xb00c11501025a444680c8640260340003000308202d545006c002804070b8001c031030b40e007050001564007001070b0b0700250f070004e5029402d400d00540840c00c0500044204480c0c0c0d07902c100386103020640c001020740c0640d400058500c25921852143d0302d841c07001e460302d400100020a80b580031010308000603629001290410384000011542202d01d684100720f40c8103449a00503811052007003040302030340c0360058a410520175140030004a0700180f1854a40400c45400b400301c0d5004101c22074000c007124200c4480c030f07403c90442003408131903914080203c101c841c4200d100e403c80e00d55a12250350f000c58028031a41e4880000c111009a9607a124041c0c62049025001d0120078004400840d00501c1000f03042c610030364030101e49160020401c900d02c103054006500451040c00180b08994021100000c42c01d001d08000803c41c06e0003004982426035902060f410030b003414113420801924407030350300d0340d4040c400f42440130818a0614a5480282c401d000e8141e80c040710880655034540070410350408213 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 66127196 1250 66125946 66125951
    0x1030f14010e01060b09040f0506010804080c12040303020c01090f0609050904020f22110f0d0209040608030c0f010b090f010e04060f1b0e180a0e0307171308070510050a03 75
    0x14000b81c0d05003140c010303030700c90056418002941092840c05209103141100c0036a402c2102c0e050080c0001c0c8840c0300240014054000001d08020180c0c0400c480c1d055800720b400c0c40c07a0380f10f03202e103802900c074543c4524180c04580e10400114600d03664403555420303291a5611000c12610f801d00300203580074007074003d83e04585002d242494580f921640c8a800c0f2002160100c15001d411201c1001c403444841c0659115109001e20f03551480c0f030704115180203035403a0025841e1120880014028a072036070080e0001d120002d14030400d5440490703200c440f66204e40080082804080c20321030416800c490010b1020002001408110107406105820a010340000501075804450003012a1106441e840c1d0415500401034142540f258503045c0380d0105407841c0d0704a000c0c0203030300280b0540107000d1003401034032114a904544020425a0101900b001500b050050003c41d002586d9103e0b0810910301c1200d0000420308140001d445412100054400350b10b002030b20400311040d42000514508158 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 66128446 1250 66127196 66127211
    0x2060c180a08010f060816050916170f180a0c030803190207050303040209010b070c0501031d010f0209091003030507110f090403020705091005090117071701060305070e01030f1401 79
    0xa02c24440c800c00c000e0f202c0300008240d4101526203140c40d81c40584c07011044041e6070144802d841ea17083e615000160030360340000405000805450151811210504041d13001040103665224410031900555070000c40002102c0b5000c2225103c180c4c144001d007401c00c100c001080000c2451004642c02b85400f40a442460400c840040c1664082c001c2607410b0340c008002d1000754600011024010700e465117207140392030b0290780c5241c1e001d40b0611640e81030590301d4403110724440058007040040307144403000700502d401c072800e0320009412122019001f1071a090000d64440028045001540c1d00360703c5a40c1004c03416640c101c3c41a04910400707800a60400c490201d5403169510180601d00c42c2d00580450703418441486000d10b001048950500d0806108010544442c001c05043d91507160147e169507008424045ca450fa440d4405902c1078100024081681c006602000650303204030191703110780b640d580c540060010207010140185160300c2013080028029100001001b07002000401c040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 66129696 1250 66128446 66128459
    0x61906080a12080c0304030c020d020102120a050310060e032a060a051207080112030507020f031e10051014041104060f03051605070201120207020306070c02090702060c180a 76
    0x1041600c11580c0b24080c0d041958a150000c110079070200300094280d08500d440c0e01c0c024415404104041c2c01202c48a0400081d64400c3c8080080c2d41c0d00c41d02c005a540c180f02400800990044820b0983c8103204880030403054412640d40001250007802440d218180320342031181425910321021040c6a040304603080c6881e410054490032480d030b00e401d9203c04414a00c505c40c047c00800718001c014404e0014080010543d034918005a01481e11035141c400c0b5101141c0031130801d10030940d151003502e24802c002141c0e080c00c541c000201505941d8519000490030054900540343e0f42c0c0f01484051061041250741c002c18490a8070081012450510000d090312641d4004e400101c0028500f01c400c0003065014003506812000c545201c000d80c09980070010f146008989000b410014002941003d81c00d154040c8c880c1650004c0560b1080d00742030401a00c51298204101c1c01124100c0000700d82c0390000c202c4601c609001c402603450888619200014040482c804a030320802c500030100c0c4a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 66130946 1250 66129696 66129703
    0x414181c0f0e0d031d060d05090102040f090b010e1c020d05010b030f030c0a0308041506060201050a0c020f06041205070803150a0b0301080d05070609020402031501090909030206190608 81
    0x8411094540315039201c1080300003410b5401c54031119008100d802c4034000042d5100f140c9020b08036003807560038050125800092060311840c0c41d10a5100d0400d030601600b0501035005000300c070327810211404c074030f0b5641c00c0100c20346841c404e4480c0880c10721030304d1185a0801399603205076510768032240c9200082e2030b03000a5040300114016a100d0b0b540304804017072400c0c10040322a000201c4001141400c034149801d982d25020a14002d007001800b00c04241000304001084144008010051045c82d444a000034002c00c011a040108903040c400131081d000d00104402032500c031103502a041c0d650315611040101c4282a0102041110402c150808140c01001560242c0c00030101c11041203515410084600400c2e0410482203204200421400c00700264032003d400090504a884800a09006000700700144cad010b90098000001c000f4909012004141c41010076240d03c40c41c16194031812080b46c00e00480100540c3c8480c3c0420840d0701c8040004441103603e640100d41e00c1e0311400708906 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 66132196 1250 66130946 66130993
    0x804120f06110913020a030209120d0e0a03020d0f15020703090e0606040b1204050109020d060f0f0c0e0409050a0c08060714120105040e010f051008010b041418 70
    0x201111601403050400c0380500402040400842e49141421800c80000d82d84c4076081d04001c0310f160380041d20070702c5a03000340c0558950010041c2524002c4601440c0e268640c01d075203055030005802c0c0d1800090f2450041d104c08182c9802604100c4124103030b81c0c1c0c5d04010344107581c00ba00e401e4818100440c843c200350004284d054441e581c0e5003140c0d8501401c40c901e005001d400c8600c105005d1105025002443c002e0311000c4102107510f114036206c505086004055a004c0070b13422001d089554030601ca00c54100900c2100041d108200140300520b40c401201e222a000d1400200404d42016292401e40c1001040a0042d426035101d9602581d07403956003655988004d04a8000104001c195074100c175003172141451b001899854600502480c1c45c1045050003030394841d80c0d5030241c40d1802107095100302a4030664610400070390810102e0342c00c0a691503c104400f960030012503941d142041e005840e40c00d140103044489984500c20025082e03070b040c5107100354510440180c4000103030100110130 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 66133446 1250 66132196 66132203
    0x1020a1e0303090602180901050414071b021e0f12100209120709230709360501050301060501020c09010603020714030a260f0c03090106050619020f120d0504080412 72
    0x80320440700403c0c0040b1f030505a000354810391401c4002ca417100e5212201681c003140c60310341a02a61040c84450413065513103c070203900692407089031000300240110100f58502d04a07030b660703401030b0b0042c00c10019284401003d03075207400402180448510680140420b900c0003400d64044400d500102441c0c001d40741e104807003507521145041281401062503100141c0700c0710742ca524a00d809800500708100d18450300a0136000b01d000401c007044048070540c00800035411407800d1000c00560301014000c20301816100303528102002503150300002c1c00100040c0041d000c040c00e0303841e00c0ca06900035000310f1804d58070b816001d403000d802648140b004009000081d2180100c01d08120020a664112141075942c10b100d00e405000c3d42032500c1e80b4150788121407005c100c0d50780d0b8400042c54090300180d80100e03000140403986914583c41e012420f800c45e2419421140b10024015146584000700505010104020030050107062442d40141c0d41c0720b070282807120301e8a583d4400e420311181c15241d0a5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 66134696 1250 66133446 66133477
    0xc01020310050a03050a032d0801060e100806090a0209130207060501170a020906130c0801080f03090a140d0f14060106050309100510120302070303090501020a1e0303090602 76
    0x304071020107900400103014103440703035a0000d0840e40c40c140e0320001c40d400501441203050904003071380552055150385d40d111052051523000e40b200d020348000002e001e04004a19030101b000050308103a00b01c010104000e41d1080110b496580c2071100d12280600080c0d0555020840c0c40782d251225600804040c07007194006a450fa11820182d084aa040c1c0209005921180d40702c8d400c0c0e0400a200e841e40b5404940b10001510f81000103a02400164071881a540c04c01810041c0180c00051050484286005440810109203000768981c4102c040b013550125402100384022100b00013010b10000010303145021215075500c890480f06040c00c022aa100c54502007014600740a00071203005120609156041d818500c00854550f9681603400510540d60750001d0b8008413807030004002080d850801078a09021414000d40303c14032804240c0101e00c0855001038954070002d440703614550019440728040b221341503003a2207a000000d06a08250303c6407a60b4010440c184001c08000444202d00c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 66135946 1250 66134696 66134701
    0x1c0c0314070608010506070b011e081617010207050706121401090c0f1107060525030206042009040204020703021c0f030609050f043203090111030304050a030e030307080c010203 78
    0x10060341d8160012405628107200103400200c000300c8e5541074030280110810030201071984501c0041a81d0302c01c00f01d502c12007090580030000d020780c0a054800b2007800301004040b8580c42400d03885080e01c02070659208040821407148117200d20100c607c0c00190102e040c09165401c82420202a0088096240d0790011098503540282c64807005010905001c002e290882d40c16a4503846c41c1d114a1090160000342c0e143c000c092441c0c0051107100f601181c92100800f030030000e584240803141102c41e10100d00c16420f00d24501030100c030074818010701c03004041d991507090001a4200c0c0500318158410030743e04103800f5000f0087c001c28820141e6800f0604c80003010010f00741c40e0142c1c40b02c0c80240c5080107104542c10500b601a61140d0054444140c5a00b4103281ca207880011a050003000d50b207450800385400d001000070465035800b42d0300c2c0403071602d0300ca410540706e200039140148994401303161140060b015191014031030b000242901d090440d56141c0b24490b03071280c0030740e0500e41d500004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 66137196 1250 66135946 66135959
    0x4110c03120709050d0515090a0b190e030f16030504091407030c0302090105030a09020612010902040810050c0a0806150f0304050f0109080423130902040c08061c0c031407 75
    0x31924010a01103411014005903a20b440e44c0703d0740981031198587d07004000240110340c00308004208103030300c01d14080c43c2e86040445584803200b0302c501850b1081c2031100c900e85804000044c0c4410b9411101c0c0c4138501f0501c05442d100070b266046c000c40a1005c10f000c00182c0c04130510603402c1c42c0d2045d0060302064a0720050040031180e26054040034144103000b6945030780d900074241d0782d20031404040011100ca9038000146c450141d9042080703590803400c00032900042640140c02141d51440444d0316003845105940300760b801c1100e0395281e0f0708044c0040c100d0346100707580311501b06030058a10142a00031b085000200d50010701c800c0c3c0e68817400410302c0100a0708224004141788140d008003d0850140d58520350340c0704600c035402c0d103a040e01c0c5103d542550048080680490014403100030360382c0124145001d0100510140d02c120324100e490000035000c0c51001d481514000d10103506003150401000014069082c152501014803101000045050042c0041070ba02a07004000e02e80c90003d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 66138446 1250 66137196 66137207
    0x409200103021e031306021606060501090605030705090406150c02010e09070c03110709020304030c060b010c02061c0f140610020703030507150b0a03030f031104030b010504110c031207 81
    0x4404a04240c8100520941208500f041110860100058650303a032520341210189000480015107440d01c006030748a19007581c001d80c5a0350318402c440a000d1641c0c1c44006549a00310f600c21880070400820000340c01030b00c150014071110500510018485485a03940c040081d400486a400300e000542002c0940d81c01c0713860400100e8089075140d40518148100404c6070320708000c0141881000c0450a0b5030341401d1218034003410b240fa170115103034642410b0050584130040d509403101480d000d48000d2075440b41c07901e114001d4000d481c2c0d600d00701562004603580344007140d00d51821940c03100c02d5054401c0c43e0044480440801c0194042401c1180070042d181081010346030656012400030000a40c00000766403d40d9000700f0034030800034110304401c014110850429511640c19240801051782080d0140b8010801c0da42c200000c101d03030b001c800500e100b540001340c007100050004012500d00740d00051002e08184038000d003800c0f10500c0462a540101c0801100c5d151000d00b04101070741d014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 66139696 1250 66138446 66138503
    0x41215110405150c03070b0c071b0f06050309070b130308030a0605030606010801081005271e1f0203060301140405070306050a090305031501051303030203120c04030c150903020409 79
    0xf240160701e030107451080c00d80e4034490401c0040100c0c000304000b803c019840000c0e09c4507a03400c030480715503842c0f0200850250801c18000c40420040921001c90054030a20a49100d070000e200100000b03070030305006030403a800070710300e034000031040314004000140d0780b40203075001d047c501c0720104425013007400301414060000e140300c0c100401d600042204400000d070344540001540000102c6458103900c00c599481c05074400032503441680c0c2803003170000000446109812401402c03542079840d00c0810380d1100c0b0904c0c42510400401c001e46c0b10340040c0c0c0ea0080d500008010000600c055820800031203d95003141d042e030f06034001c00010401d000c11401000c0e440301203800308204028a17640c02038030030302000c1d04454005004000d071169a074020340845a10040c04100300340d5050f640e140085d83c2e81c5c8038040180c4030002c0040490155a121000c0d07a081e04c0d40950862748103820314806540007551089440200315410f0000000340c0c03218450b003629640102d90251410300f20075903614100020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 66140946 1250 66139696 66139729
    0x2806060230031b040f120302010c03110a140c0604080c0d0207030b0a0509010b090a0b041b2c10050307030b090c03011203111b010f0504030503041215110405 69
    0xc0c40400d8464542001100c3d44181d45822040c0090460b080f060040d010340e410050860307214200100b10030811030310b01191184241c0c001e100003985408106c0954000000641c2d50b11428040f80401c1800b131022402040c82a45880b801c201041001c036140910a45081e60340c3d500010f6083c40c090001d1040c0c95018040c3d0005062003403850351403a100f91001000082c01940d5a00880c040c45400c0d04000040d0740d0003440d44101d810701c0c0c80494000e0a041c1e00e00343c4a945040001045540000030564411a103500c400321501e41801584403042c5190b64000303040f02041142c402243e5640b8007282558890766038140c0c4900d42550302074103c0c1e4403850202e02c140980b03420410100404000c80e03041d580424040300b54203030701d4541602c014440080703078013080c09261003030340074414010400318403998241d032980342d290703070441040e41c1c5072046003c050036a40080000b4800c0c0901c2c40c1070072405911a450100d05021031444000445400b000c4418107044006010042c628005c081d51190102 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 66142196 1250 66140946 66141013
    0xa0f060f0809100209030c040504080c1516051e0a050409051f05040b01090b040308070201020d08071205070e030307030e0a0605041410050c0307030801080d0c0b28060602 75
    0x2d140031031039503c03014100048072040d00040c02c0305d602c0d1030900404110b00d4000c5c0c010300107401c00707182c4008d460f0031804060b031340f07032003141c02d441141c0084990300b0f400340708100003680900180c114119956480fa03504826424500c10324081007481d4100100030300e01e61130f55807584a500b0011040c060b14000340c200713442d00740c816050f82191a42518814222101100d002a429004000688000005070710141c00d5100100340001806800c3c1700820351107100364251064006003200a544c002c40584040d03000550442007401d40d1a05903001c9034200c1c03010709101444e507210000091079540700120031400244480c01e900070f14104120604013406250070441d041a040010412503010b40c50b04a6100c1d80440c036002640c01d004404944860300445c05480d550112402c2c060000f500a1088031311a2282e51021f83c82d55100b030b03450184003a44500d1706010354503051121921440351b00136241c10314004140b42440c1e10240d1003404010801500900102c070385030780480c80010440f9040e00d1a149 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 66143446 1250 66142196 66142201
    0x120403030b0409020603060904060b060403050313060512010b09011e030b030c090624070c0303110709050c0703050702040e070626010303140d0906020304031d0328110a0f060f08 78
    0x241c1c1d0f9000e80c0da0092007901c6400e2325039070724282440078110308844950040e1000402000b40480400200030a4601c0d802540303140d40e45040803900e03072013008501e28410b186c401c0140900b40e0002c0c001d04181c50149020b5000c044130300980d0b14541d2140e001040400e40c0c0304050082400d0520404031054401c589200c250f160130808a10a144000300400c4030800744141004203446440595211079001803211424540307030303c2c1c003030006494805012090b10074104006442201402994400d413516161141000e60591f07080e11150000031040ba1310940f0740c900030030414030800418000703161907595500d000d90348100c041106240b00704100500400c810040c400f103a0040280c1302c01c0324a0f41c1d0303d03a5844d16018040e1005090000004049030b00020610040c107038010440e00d150519211016a402c8091003055655025040381010700e1189860f214400d25803040d454808600800c00c001c126040d5000194141d0718980110b03071402c0060b6070900c1311130f0303005015403001d00300ca0511400302d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 66144696 1250 66143446 66143449
    0x30f0a0e0604020306070c0f050607171003020d02040f021204050319030902180403021c02150108010c140a0e040e0d080f1302151c09050f01060302010815040b0303120403030b040902 80
    0x502005202409107c1c5544509040014040c1060300740c5800406848403030a006000509510f0341c129209166802d80000c01d034074890420368082144d90060410311040040d40c248000340c04030402543c4e01903401d0000e03421410302d041c0d02c14417403407243c000342d031f50f80b54000c1590602400712598042014901058400181c403510030a40c942800e541d01c40a15a64a140480c13810104040b030b030b00c044244c614021001da4000981001c031b1a9040c1588c0035582c5c840c00200d08030380741c00000703600044081c04180c210070000c4008114a03002880c104100c00044008101070351031501403081140d1000309941d01c090351100c0740c140c0150340024500c3c8242803800f48401c0c3d60003042c402034031074102c2040c0f40c2c03000c0030003500b00c52010015417250340f598010801c2c240003c15007048190384030f000b10381c00c8090910043c41034005981d8141c542c8030b4030ba01c40080c1382002c0313445004060f42080d41c401c4405015502003014044c24454102e1006492509180041c00c0c0c440560f0030a00941c1085800e4005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 66145946 1250 66144696 66144703
    0x7030216030e0112020414310629030f0702070f060504031b0806151f110c100909020306060706050c130e0601051605070504050c070506100b0406050d02090303030f0a0e06040203 78
    0x71508111000c203583c1c406207140d030b10080c0381020741c84d215140b540401803040c13140390000c2080700c40039403c890b000c40c100e444140d1190515000c440ac00c00c4100005403d80762000104c54024000d441143c541c9500c50720110344c2800300c0d41040d004a480410104100070b4200c0141540000481b0104041032404030440d03900d00e006841c5041c50325811410420584032901403281d8410040b03401d2800740c010300005020401c1c0354208401c103019a0040813001e050408203445420556aa03d40c038441c0b070103241c60001c1d0800340450b64064020050038000c0f480501495000b0b400041202c0c1c1c0c0e580b0302441c000b809075202da1140303402c02c80d040200400c5a8100c5c0954000340c40e0124015041034143c078100c0d003002d801d42c0040398028981402d00038000c0103000a04041031103038081340c0154031800801c540403880c6100303400e120b51040205110981c8a20041c04c0d070010343c0000581001114000241950005c0322010903001d10902004041c0c200d50040c590300301e0110000c1c2c185c1d0300302500030030303207 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 66147196 1250 66145946 66145979
    0xc16110306071d0402040b1b0a0204110406030b03060606091009090c030b0907140301140415030b0610021605010e03071d0402041404020d020f06040b2709010f0e07030216030e01120204 81
    0x42808d500d0080790b0030313009011680c0546d50040041004800807110307201e4030733001402005d0000780f504154110504001403814040d01000304501d00f00100241003280d440e0700314114504100c403a000c00260505640140d40e20110389440c086141400b040500000768401001001040300c084e60384c8413071100c5601184d040d0b4800c80030b000801c0c410407002c135010f0402ca82044820b0a8019000018424280c11040c041d4000300c2c2c8069450201d80d10480ea94a260385503040441e0310103804210310360107026900c8050402400f076074041d607a200b40e552001d00740710082c0c02d01c00301d01d0300c00c11045281a100700001a01e522101c4401c1e03003419004904103506542c80203000d040d40c4600c0c0e54007580e0725010780e002003a41d856032950303030101070707070404c00b0100070590009403880210320210705854040e00c0c243c162881c210401c04202c0c503000001880001c0a0038482c00d0503400c002c0c80f250144c103c4d403030682080c0240c482e4015004190001000c2028180c220f9a41a2040c8414403031798085114461 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 66148446 1250 66147196 66147217
    0x51303091e080307120807030e1b030c12010c0e04290a150513090506031213260601060503090c010e040e06010f03120302030c16110306071d0402040b 66
    0x46820010704404203216540c000c0c003514440401e0000800044203103241c41000356a94000e001d841d41d0005400b600c409051140c5660005601f030f4850703029180c03604038083d0f00142280c0d541840c00c0c000c0b65030f5403120040d14003103035120750201390030303540110404032800e00603681000051501c1641d01c9894881c040540d8015030340031a9448031743e9030070301e0350b00240c1058480b0344400e04890001521076071106100700600c0c00380601c0001c0c40d144a114241c42006d018010344130b1002c85c030030700c407491b41d1010800c1c861a880021001c2080d0414811905081039041d1842070b105d50140b840c245450300582c014402c10404008001c020900469000300140080c00c120900c00c00d18400280a4480740300112210311541000250900c2c401007400200c03806040750081510091b030045090b80320403600d100c01c002c010000342090100c481000401c0c00d000f10310f00201ca0703102c40300081c14201c0646480000560501e0070b403098014000b4001d500e1802124112300e41890300400b14801c0c0074000045 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 66149696 1250 66148446 66148469
    0x16051e0304230d030e12061905010b0703090302151309020a0219050c060a0210110301060f050703080c0702240c01151202040c05040801020d0204060e010f0c08090d0803090606030105130309 83
    0x58410303120b14801103945d00114065508502d031008c1e070500c092408011000a185c02d286c0005035070b40004d0200e0301c2035601341c0c0da0040403500710380a00400c0560b000320803800001c10410800601070604030880500891180581c3d02c12030000d00a2a200c0284600b42000d002040c80c4400a074002076103640240050300d0968403002c107420240e08007030014050031849400c0035040d941c804407801c0154140c503da40c903001c2c0d8549580c03a080790302e40111400100440ca20700701240450002101502c500780c8002d000d04c5004d10946460b45540180c1090203034003410105009075150402e000c1c00c001c41c0040d82c2050400d5241480c4081c0b020421080640143d0740e0b4003000040904c550102c4002d001180e000f99502c00030102c1b914001c0d8090b1180c14005120004140d038990b02c541002050440301e81e41341c40c24040b442d21020500c1d44403580455111105101c2000020012380156220304542d001030042803030b01506240c20754000420300f5084804030003c807000a03030086180803d03101e802210 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 66150946 1250 66149696 66149717
    0x19032a050706020d0e06010f030506070e0a0902210612030403080a0306050306040c061806270825120f0f110d06020a111216051e0304230d03 62
    0x3a1440e01c2096000b801c110b00000d0f01c81290a101d42010301803403041001c0b1505170380d0b585000e0f0510b0a03903010050183e0801404a1881486420f0074a9081001400b0303903455641c40b040c003800c981c0070100c28000000c0d01c1295160340d0b625035000551140082c2c1d500350304a0070320b1000a441b0700c1603002c0140f0b050741c04902000182e110b58801006008081d0444801d814542840c520204861080c4000140c4100d901e40354491800613960855009441e8841c5580500c40c440c9010036031981b450f044540903140000e001141003144541d070907400300b44d4140954220110803110b501541241e0b00d0810700a12440000340704401200c1e12580080ca03040803460145000c02031501a600c4003680706401c003c2103402d21882c0d0303000b1700307003040d850320b40107007020300012400c4c0c071401680d401e580c640905001c02d54880e6030032400b11010901c0b84064034500303d500e00c188103e04c2858003520302641e201250900c040c0c6412031481d29841c3e8202400800580d03e0170020300e00000e02c0600030100440d8240 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 66152196 1250 66150946 66151031
    0xc03071406030a0207020a03150f1a0108070c06060b04051504080703030809010f0606031409010908030610030f020307050403120201090206030604020705030c06070e03070b0403020d061d0f01021903 87
    0x150351102d0b03401445031003007503503a0270101d5646007440700c80c1000c5454104e2039400e002c075034854a01041103400e062407692880200650341405c0040004040c801d804200030300045540c480d03503016000000c54681c035941002c06018403c26042550380071f0500c1004244021400082c0c01c604603607042c5020101aa03888200b10301600c1c01c08800d1022908068010409640607007000c000e464a6540a18890b501c81c07140074243c690800010b84442c0b0304101258550606d41e0312018000614240480e14620700c1c1c61500499100f1030b580e8001900100e000e00c1004100d240c0100340c101e0750700c024400390500f030b00015082d10014001911491340000c1c07060405c40c050064901c251565025101c80d40341180003d001c004408150602c01d008000012501014540580782506e4014290340300c00710459441d24001d0000c010201090002e02c070041c80304980802443c040101c800c0005a16507101d034180c150424610b411440c00d1604000c010381070f0310b2450007011861114040304101c1301d240c500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 66153446 1250 66152196 66152201
    0x715050c0409020403060204170a020114160203060f0711072d0306020d051b0c06060409020f0a090207110409022d04020c06010e090102091f02070e090c01020c03071406030a 76
    0x2848902c48600100740007051007519405001118801e14480310805030003629607440c1d03082c085c0000c2c00300e41100c44a0845c402c40718080c1004001c3c9029000c11003c10350006031400a0403604c10301101030001c1041000c99002110310302c182c03400c000404416003405003120300001040c40c0b944c00740440c015400d03c10300d801c00d0291300458000700b085645003000c00c400005004d0403511002e2503541c00e42aa0100494071003191000000c010250017561075410401c0098480070300f0070703a40604842da03202560750700c0d5089800100750b04d0000582d64021440e00f020380c051401d0b0418411450800202c0c05602e81812044540202c0e04101c3e2070712014014203980c80915249098200d8404519480860000640309040e100700c500c8179403d941e2100091030030703031099400706600714044070f03001945118400c0c0c8803140580d907401695407603526400c00b8224a2030032036201c82103034014000c41401e940c040c4178000d9040004d5010744025414020103903154001d2120070380c0135a20000000700d5100456 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 66154696 1250 66153446 66153449
    0x2280203010917180306070207030816020a0602100c090501090303030f0608010e01090b0c0f040b070c0504110702040c020f1e280b0c0319020706021216020d03020715050c04 76
    0xf112040a03081e0342e540c014a0b900610810400382205415459181c5000208240b044046a00030300c201f50a41da5150740d01c1c3c02c0008040041c1c11060518401a55072100340006002e041d4010300c0c180c0030a4240c003058a85081c0c0c52001d110381c5840600283e40e01000c1c0905480c0c0504001c07884425400004009000e554051075041d4640084800500c4040d0884c03c00d840c0210300044080e101c0364416407051140c1a0142c1c5001401c010401c00d088030b113000703801130602619081c0d40540d030380e10115065421400d40c404c0204000100e1030b0031481c1c0362140300c4900c0310500c024054000d0880d40655500c080a0103025610302985184ad5001001c00000002040d03104050044211140d2a440c903c0a054000c46004c61000c0c00a401801c0d8070090b01e124031907100361448520030a203002c40003940440010b99a007a002c1208115008001080a010f032500c2504580e11405816000381084a00d0007200b0801d4010480d5401040c50484000c040d4440180005825240c82d004c1e008a403145 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 66155946 1250 66154696 66154703
    0x915030326070806030708121b0a0c030303090b0703020c0604031d030307080a0318030203090135070906171b04180606030f0e0616090515030603010c022802030109 72
    0x1200204000c2c80e5100c140d450040109a0031a03614507141c0754103030303150034102c02d181ea1440d034207100520410805401f0f9580107180c600503111400020345800d40144180d40007900407a8403030a242041299444170b890f030248113481d085042c580000030311929031001501c00740c2088586040288103100d105002d80000400504403540c0f5041d030b00e0035140b5900f1211352440807a01d000450040c0c10000749411000755415400396140c200e0242c01510241402881c002810110050303101d468526106041c03000050311401046d5071034918070007003424003150442003c21503a0320a03181c00d40e450070071580d0000d90080003c0c035000203034403501b403030360040b0b41c000803e5949141c0307240351408640d8801416103180d9601404110391203030300d11040d1a4202d000039941c0e400f010009018603105104800b5610b0549810180c255071000021265181d800321181d6401c000000c0c800c0f185424882e0500741a0280040d040744003000e101004090301c80c039031462900542007001c0c0c00310354080d032041484551 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 66157196 1250 66155946 66156017
    0x9010f0e040204090f0b0901060807090b031f03060e0106080706090b09180f0109050114010915090801020a030204050a09180201050313020406032003160612090b04061509150303 78
    0x2041040101400406e103840d401840d20b48004600300b0300c900001d612406950302e604201520b0040c600d20386901c018080c890360303050821032100280d01c06e072011000354024840030401d07110301e40c07a460844807a50300890040c0d00c0f1050405c4503d8118611000b00e4203540a030396100c51180e004101c0541e4000c003081070144082d030030010b0301d500c0945454180e40305600100030503a224114818000308644a141c08105a09410060a43c00b5601c80440c0d1045141400d02c65540d41c40351401d80c0c000504060100f90007003403c3c000c03418124490401484903603c14402c40581034814141c810501601904120002002a20749100e21400151503540a84100b1105a813810080c080e52181c80714149256044205403005280000c1c032510304a0620309180915440e00b40241c8184425101078921640c6500c808400320700452aa28400c0d800b400002c10000c03601c401c0c86c2031520461f048030405038600005582e910001c0401402035075418201400342030f0341903a00c40d4500c01c080d045203080d9031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 66158446 1250 66157196 66157211
    0xe060a18030c0e0903040e0a02030a090203101a0105030103020609040b0114030a091205190e0a0b07080301050a1e0501050706020d1e0c020114040b060103020c030a110c040209010f0e04020409 84
    0x4400074112040f90f02041d07100695132240420141c17070748120710440100784090340c081032080c1c3d081d5009540040303a441e40010541f0441e030120b070425a0603044d1410190799a44081482e03941c05400349010358003442c02a28641c11940062010f0140340300260140c1d50305d01e208152640a0301000101c05050101507440e03140420882c005040c4000c1d080701c102944801410740107010344180c4030000303021484400c1c40d03d01801d0803550030450280c00c9920001da481c1c0002c0f10a4450004c004180c0180c01c443d90b250b040109000007114a544506041000d0262100b443c45010240c54103a5000b41380003940ca10044c02c1200107401200c55240f102e5161048c1c402c0c4a4441f000900800d494080042c099418520070680c2220350700b0f01c401c2c01c3c0c020714500040000e030b0340380e540f140e000105041c01418482405030701351864014292240104010b0020280401000c119120306440c0465007076103040224000209103c01e04c1c0c0124091001d158040e05150b900c54040d2400340452101c01c00007034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 66159696 1250 66158446 66158453
    0x7090509120708040609050103020708031501050d14010e062205072c21030901030207020301090b0106020d08010801091a070903020909010c080105040203040305030f07030b03060f09010f0b010e060a1803 89
    0x103900c035200e00c80202d582106c0005682d40280281d4429a4000710f50606540c0c80128208071901c1c07001d4403504101c8100020301a6441c0d520a003000f140e8501540e04056050400240ca5030030040c103118490340b1182400c1c08003c505020220704496034801c041560f840e0074100b41e4078903035038030049150b1081c5403c05400842d415021420244800c6894015081202c041e40c544d007110342111304035603003007004071401d40e50103500200f210a20180001079013a03c1520750070183e40080e0003000040c0c01104001c108943e0000d0503d0260590a000700400c40c880d40d281d40c5007c0078207551040c0e084100c070019035005c0c000d9040d01300640c1c0140c800241d52500100c1d2078020030b0810000c0e00800c11041c00890745045c10300c01e41707200b5513050300e038180385884040c10f5401d8510b00600d00800c040d15107001e00300644040c4503071401505101500109801c0081110703003550901c0130070343c009501d041001d1126a034486540e8690f4a02611495940d110760074045a030f5243c503564001c111840b850001082 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 66160946 1250 66159696 66159713
    0xb070308040303180512070302030409090f051b030309090c0c2b0e09010311120a05030717070c140d0507080a020406051005070201050f0c0f01051602010905070905091207 75
    0x30342c860f40c0d0400951841da10380c800701008190000d0420360020004000500c140001441c6d002e019004403420955284aa541592002e0004039040c03803c003100002045801c03c0350752061440c412138420303595104d0300404c1d900d000321101544245440008190141000b00886080c40080340c141c68040c003446040b111030403443c01820b114065641c110030789181c810b003540c59030160000c0645019910310788030741c0c901141c0182142d600c803841030f203643e400e0380081091a504607c56000396403611781a041440308105551802c9807039403001c000083c0010301c1205020290703011003082a01d142c0e055008a900e03484145801000c41c460007801283c0c0040c001a07480c1c80610851b0140901c68a031001d2002c2030115070b808802207001804644010b6004001070f000c1d0151a0311405d00702030b00e513a1064500030001586801c0b0382d40d624207100f805512043c10008000441c0000e1000e0b5940385d0ba041d9480706079201d00001c0f990b66102150350a0420f12a1014070b2802401c520b4403581541004040e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 66162196 1250 66160946 66160951
    0xe0f0a0e0a09110a0f150509030a050f15010503100c1b05060402100c050601061b0803010e0a050a050106020a0b040f06110c0106060201142a03010906030b01080309030d0c0c0b070308 80
    0x54019003002e05003c986000d6140e1070568403e4402c0305100c1d4984516015014420043e030400e00000b44081d0100c0d80701040141c802c20b02401c02030400c2040c9810160804800084110058080100600c0952000218010440c10380b03600081d00060200040740c0002100c0401d00e440280d64581e0f100348038000407984d005900071140d1200d09018014191188140890000d1007a00185c004111b02d601a00032080500e040400082081d251607035584059030098024141c40c6000c113040c003403078032114810341d9400030803001c1c104900e5040031400b0b035039075013a42001032001101c0c10005003040030003400740c0c841645c41442442a1000741000141d9078000301c041040541c684180003c0c054814082c0340320000d0300d12880324080d1038074a402c4014002400346600c2610b9001b40c101c550722845402507008090815001420301c1c1140742446410b1810b9200ca8243d81c400d0004107550f55020407012207125287c00e2040c9600043c1c501020840f045a0285a00745804a0070506050700304900e00c0c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 66163446 1250 66162196 66162203
    0x218010f05010e030a0f0b1302130c020606030705060d0f020c010609020319060e040305030a2408010b01031a0603040f0807060f0e0604050d21020403140d08070e0f0a0e0a09 76
    0x200403d00360310034155a070201e03c00140611641d115084042085445000d0700100f0081d820124600d0507000314801d0a00001c0e0009010781d81c528041d6000d50520009030446e1084003d440c1c4d0903c1c00300080d40b02d006400d02c00a0042e07464880f10880c0d186541100c1c5080980c0c4001c0c032100350780d413050340020741045940109240c1c2038100600e41d115140b00b00c00c15683d4901e194245501e4a07201141d80340c00c0207051450300755490380312110240840c480134603d0f48401c0c4075000042d05094030300d400c0d42d041d00e0410b030615080005821303c01c0201d541c1c031003d00400765209134480e034890400e140440480ca00280840d10001104000d001e903d0b01b180d9482d400301c440620400031081e244940d680000c0b1006881d58110101e2983c2692140b4000c41c2e03205840001c00c2c1e0401d02d41d2804c0d400300c1e40320303500490300400c0714006c051945c0c00074012411481018241200149400c0707030050300c1c1c002d89010306032150310040c0398186c072503803400075003803340901418540d886d107441802d01b0000d2183c0d03031098 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 66164696 1250 66163446 66163457
    0x8090108010b030906190b0d06060305071a030a0209010212160b060607021c02131103090106080d0801060509010201180605041a070c0212010b10050406090603060308160218010f0501 80
    0x10807849100e208403409071201000414240e946c0580502610060f070a8020410303845000c1500d956682030f80c000b4029000d80d000150b2a46945407662910ba01c40e030042607454440300c00690b214103490b050365802a01d642c0003694070000c2d400101d0034032146030041e031786441021482e10700a03120800302012003442034a10054603102c100c10885540503810300250b100b02480000f07000c4462200002c8800c0d4800f4010460610340b81e54503005071f0b8240c02d0350016240c0007200304240050240a400f00030041c03d00039180c0a48041e41c010314100b0305000d20f03424890005007030011a4802d41c000d80500d20805010408034102c2d04d80b00015190603501640d444403045110506513022605290050920340c59012443c0703880d60070b00020f040a0300da0f00c00295a1034100d022180c03a441d05440003260300b9a5103c0c0e42d682041406009a001030f0050360816150480038000101d09008450003096000c181d01d801d02c07014400a01030012000c210002c44195500006100e501d01c5482001c0d40e0342602d0b81c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 66165946 1250 66164696 66164699
    0x5010e070201110405130f0b040c0203070203011401030507050d0503040e160f0e010203030a1107020a0b190903050606011103220801060902090a0e070c0f050a020a12230106050307030809010801 85
    0x185894004d038003606510922034458034012541580c070401c0042c036444000300d02c020410700080c0880d12804205800f50304006580011450213200b25000e1507a0603c0380e11455056445003035a41c241e5000d5903000e4a41445140140102002590000c0c81c841004807250b140081d070500907502600303101e0001c680154646c022041c02002c1c80d21100c1e106900075070840c0c1c0d660b0708510140031031011031401c280e400c0010302c0160b02c55566080c007400f4034030212965610401c1303a081c46207040740000010044116003c0c40000d00200c0c103160054400d1030845402038501d000340d404e512440c42c440c00442c0c1554a14105621003d1001e800c40303030440d0082200c00d03a40c00e503c006920403d0802c80d848003c0000c1030054a41c00901c5942100091411210108069075241101d1102d00e10070b0f202035000c03a019404616018a080f0050301c01c40c100c0500a00d01343e43c8140c415200b402083c0008515042070249040095001c0c0c001404010121046030340d0300d08241a84c0c0d03001c84902c90008010000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 66167196 1250 66165946 66165971
    0x312112505030f0c012007080303061207030f17040504050f010312030c05040302130e030301030803040b01090b06070b06031204090608061303051204031701030b0f070206090304030f020a0302030105010e070201 92
    0x4000704000d442c6801303820a0380151004648180700418040b0310300711900610300c07003400200b00701e40203402d04000541d0380b070801000b00801c0a00c01c80e404d210783e45c810b071760901c001401c402d480061a540716a079009041700c880c4c41e505a40c000c603040240c00034601001c1040715402348040071b049900130603140ba013402c2e41304030407410f50f09524a24400704408000c10001400c5c401421082c00c004104005060011200018116442a402035078419004418401803000d0110801d0040000000070001420150b02040d05401420405403000000724000713102910b0600414840d180c1c602c000559a507212160b041c01020b181c0585a424400c840c00030b406802020000321541b50192192410803031a0494280041d0000f403040701006040c659610b044818001814042c5114084090b4549414260030343c00d80401041030003158031550610203032540101c1240c0649411a04000c4018190300100302d031100107900c025010b41c43c0400014100c024406000d0081050303034000c0c40940c0d200c10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 66168446 1250 66167196 66167203
    0x807030501050a0512070e0c040603060801140106120b0a17010f0b0d081803030412110a0f05060d180f030206010b191b05011401050103061e031211250503 68
    0x5883c0d04095101824401450b00c089580c59032011341003201e9405440b0340100014882c00c0e80d025564606c0480c00340011909809554041c1c84230b00c000300f00d0a0080f07601ca0181e00010303c212414064522031041003030840da0400610000090503244846035603e2741d618001000010701c1816500c4d00d481d403144090035000b4030301c52940007810702860340001d0b00c4052103648500f0105d181500c005180411503102800a0401403280344580d80e01880b517070170303da49c110b80302008441c442d03404004180440401d80d800e1700c0686109845c9161501004190301004160400d00460560401803056080100c01903121180324465820b0320a00e9903154a42c003500e02500d064410707011004002040282c1c41002c100203200c5090107085607004040c2c854508440944c40307008400030003500107120a5030140039010091050103841e9101c1002c440b004071078504c03140401010310f0491500f81c071a03188584041d0084a01000540c0c1814a003603202c003001d04131803110114215100440015a031a010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 66169696 1250 66168446 66168449
    0x50d0f030f2306030f0105040f03110105190209060408011505030c010f0e06070c051809060105030a030c0803070c02120d080a021602040903091505031803090d060b0604090911010807030501 83
    0x300100d11000c01d100501c0b9110900040000f5054422011a00d00b0803100740a400c0c002d80c0503100c04141d00c0c2036400c0090003407005201070752290781800c1c144403007154400060070500012100050716036100d840080c0d040d03c16503102d0b100a41c2007411031600c007660300008800301d45044040f105081802001511001510004100440c2180c1816116420108010b1040502c1b542071425880c0c2c84400249545015a820410010b0780c00c08201e0079450400180c0d0140208800404516041c0c0c5d400a00540c8418402400c403800800412500e6001c1d0301c8040748182d00801c80b024010008180a94542c0140c0241c400035005002140103090140300302c50701d2080204182c09070284540034070001e050a04400c404111412200103140c4d0a540360180d088605a9100350752410030305c2144036107148030352074120190002c101840d801e681e003000080c155036100b100807411125500002e0030074003881d84400000350925055904000d80c1d0700030b11304081e81c2601c4d240c00b603484209084048500c00d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 66170946 1250 66169696 66169721
    0xf27040603020904080f09040f05060108090714060708040e01080312060f0a03240c02010e0c03030c0303070807140f0403120804020303030a0b030c0402040609030213110301060c0f050d0f030f 84
    0x31000440d000c43d50310300c000d06d006882e0415983c07802e00814041380440390f907200e04840d1956034005001d540e40e844200300d0381000114004100d824242804082c02429220303000f03128480001d0f002e070810115000b6900100b0444000b5100380da500c210310764503030744074030101429100e207031000540c80c1c60b02d0446001c42c0d1002800c0014454255600c0010043c840c50288800c4e801100011050301007a00500c02e050109500108030182c3c046502441c14030a8214503200f50000d01c580007040c2c10000540303600c040189000c07042e50321061000d540b4400084100c41c41090001404203900345588020400c80b4444c17003640551090302c0600710361110098900950540080000c030b8031209084c0c02104601c20300030140d0b46408400c000060032039015038010004268415810425480c0250802003100e4001034103000314a162200e021071448140264030a102030f07000268140405001400f4040d540b110445000e00210755001e4146034502c85e0490000342050b0341c84112540502542c841d0450 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 66172196 1250 66170946 66170959
    0x2301030b2401030902030307060507050c0f0304030f0201081b070c06080117100209150706060608060603040302060105041e02030406050a05010609080c04020706020c0607030507030b06070b160201020f2704060302 93
    0x50840110084d0003c40d0059a0511040c42070748042a210b104560003040720f130312620383d9481130140050501c24045140c50070394100340310402c0407070344c2020b004003c03550910b00004c40307a03601c1034003200c1c0303c03454188060b41c0140460325108005c841080902514101c0d11020a035a0340c411441800842c000031f220702c69040f85112035158219900502040f0700d0041022074081c0005000c00c426820620066074142e0701d03220704021407500900f0458101d942590040d02c1c514013602c020355100e08c18843c081c0525510400e80c82c2c3e10400c1503991410111101e0150b41c0c9041c14101203000c3d15042d2071030328146180c6000001c880380252440c00484205078003a0084007120713410000207411070202940c403940c08000307100000006018041c42214580c03000203040c10010001002c4030020f845840c000c207001c005480115800002c000da200004e8040000c207020303480d608901a024030900c0725000940440c03114141712120300900c01c4244401c051191100f004001c202c1070310b0080c800a50840d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 66173446 1250 66172196 66172261
    0x7121d0a020409030203040801090602040e072a21030b0108180a0b060a08010606020d4d0607090e0a05040305090105031506030a050402090f01050603070f02012301030b 74
    0x3060f0300400c0050f4004e0064a00f41640c901e0441d09640d0080b20032104d44e540040c007030140244c003928064100d0303160b1902040000c0303d0810a0210710184030042651500c0702c02080400040052801074080854680c1e60b15041081014000d0655045981d011943d8400010340f032480207614075a204843c40c4c014241042540c0b110f414010340a0461500300100f07100202d1400024064080205029030090000d900092001804d10300050194041007003c642404240c00f84201d03420910501013809210220045420710b80100c1c609a03030300018080e0508108180e07411403106411588000140441552040104800c8420482e0001c0106201b4421407550f9481480610390000c02000d80c03503000711049002944a4000700e84a81e02c03da201d8080204604003248a5a0080104414001194144000514140030061140081090712410110428801d401c8000000c481c030f040c3c05002c400160300c3d00c2c0940400d020030b8408a180001003480186c1c190452010900402000e140c030f034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 66174696 1250 66173446 66173449
    0x7020c010c02040e060403090305100203010501090501050d2903010c050c06041403070c080102041406090117060607080301030501050a0b0307060903080d0608010f0603020321030406051b0307121d0a02 88
    0x3075641001c141c1c1c226540d00c2496810a03800c1000314002e901a031107002409140d407034421303d000e540340c41c03184d84a0300600041050f80d800c1001c10043d51002d003080307900c8141040710540203040d048500d1640a0f08040e039107aa5450000035004240707019402403020076203116003500c02e4411a45007820b1036100c0d2000402190504c2140301c0303614204410780e894240540c0b51040096900c3e0801b10b030b81e95000804010b03c552044846807692019a0603e0070b000030308002170074412441c000b010a503c3c40c82c00142865485004030b524003a80545015201d58690030301070f00804007101c03014010b07490b21a95002e146800a120400c07a82550b48500200c1c4c00d540e141540740d049950308008003500c8110214240d0020300603050905112100058201d2540c01014540002c40340b80b2169182c030200d40240140d00c00e4100ca40c010341090340401c4d96200d10f502078607581203010030441d45440110500c40c00036400085c0700d04d40040103109019020016944203030244508081d40c0702d55200c1c10500005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 66175946 1250 66174696 66174707
    0x40b0411030c0d110316020606150315060f0c0a05070b040f180902040504060c080c03010803040905040c05180406060902030610030e0106030219050306010f290906120105040e0607020c01 82
    0x1082c3d00e000010445000c070b0020340e030581c0c10580d019507220f140c00d203040c40c15590421485a21400490311a4400701d1411584031407440042d00000c40700001c3c56400c80c03180c480c10125007080c080b00014594500c145c900503038460703040401c215050300501100140e500d001c02c081d503054403da10322000c0700c18a03052551030182c071070900210f0401d884292020269540c1c0c410395100313900554000c550401001c6006200d08002403030000100300510044c40390f0000001904c041d0717250401d0005003034859080c030000903802684440d600000d109035064550340e1080b4503601540c481c0f4001d10000340c8414507201680800c99400d50480e80611120f07540d5072081d00712100b240142000014102e03140d80100300c011204138001c100d030781031158040001e41410404030f401098480b84c2c00d9250740c14460800c003410184084549594080b08880005400c680d0407140f221500030245943d424660301c8803001d210f400d1160b244100d161101c070b030348001408a62a80b0541465014200740303084003005541 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 66177196 1250 66175946 66175957
    0x509060f0910120f0506071404061b050601031b08010209030303160e040e1e2407090914070906020d0e041e020408030c01060602070b161103100902040b0411030c 71
    0x4010b80080003820814401c07034400c980e401480380245100c0582801c0e4648030005d05034408009040664403104c0d040001074805461140c50980a1000c10f140318000407084094040d1841c05064000820032407058410140c02d51130010003444e0f50383d81c5030400c0c01c0740a0060300c00e4154104000181c078600c0d0320b2441d8000c6507500e0900006218000f8086001ca0b18003a4000d142c690000d050304440c81504c0319086e455280100051101c1c000011860201642e010500720032500f5880100d8003c5000c3d406203406049003803001c02118801001d0341004007026185407000c80c00380b5001040c1c80e0710200b40c00ca1600340c240c80c0c07401220910801d100080410240e07003900120a081102d0050203580014002003d05100854491a960f0b0503907003120090741c48503047d50b00111041142d010360200b500d5040c0040c1801c0e4008482070b0400100741d220310142a9418021103d6411300d42e001d9500c00c40006000f0344003000b107030b024071083c0030488128020f60f80c00c1c02b42c2400016400040b246c01400b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 66178446 1250 66177196 66177211
    0x3140a0302040b070501050405011a0a052b0615230907050408150421020d030c0e100c0302060f09030f0d06120309030611124302070509060f09 63
    0x14035080d0b840b100200e55070407401c02105c0750394641d0184000d002090145080c2c2c64a14403064410750001e0b40007807124051446954020604542a60f68500c178030102440224840c4c03030700c08140c4166183c44001807600015181088404440210b54103182d01e148104410b40031580c0402c0b149800104040b115000381807004002c410072004c1045c0d502400004504440c010a24009083c1454410b00010798608440032182114414801c0c05a00049403902c804160400080104404004941b06c00060703070010b80203107000650501d0b01c6e610015501e44a4000c0e0700381c0c0e10f580c544103551013403d20103075010401548240800c02c03d000da410014040020305141c0003070001e685021140421407030321700580c0811070140c010010700115001d4030b1000301100e4102e5140c4845045c030b80b281c5010160041c4079030080b40140507070300800072461514094034400b440f80d10303100c2083c003c0700a041c100a00c4e0b0043c0551000013419051801e9800c0c080d0900804180c940c46000c0180026640000c0064 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 66179696 1250 66178446 66178451
    0x7080901030519110901090b0a050322050d0507030305070207050f120f0d020105010302100503010f0e0402040209030715030e190b1b07050a030e030d1d030a060f020d0507020a03140a03 81
    0x104642803840f03007407100e00c4e01c0406507444010250014100444541c015900c85408020ba65400c0d9071280031242e01070700c2003039208070f412200074046000158449000342a171161071150001181c022002d04035941c4a42d40520060360303000ca04903102c05040c4035840d08000c6104203006a0b00d808004c40c4440c2940314129800c110080f14a00d00e00010100100c0151b596071005009508242403100c1d135546850400c40d1a5500d050884c00031030203280b05040240003070308041030440da201e804442012100030700700d601980e22085e4a04542402c4459403020074078200100c034103a0004103254402d201400e41118a0040c00e464055000200a01c00c8a800003006c040601c402c0307017403000e4602e0724043d000622450803203140c040c000c410112030366031080c0d0000039101405984213102d1141072302d071a0f01031b005110008005c00e1034000714100003000e850410f070340b0301e02e0074059074098410707ca0074042c1804651074403542641c45006002c1e0190000e910f103107010015040d071200411103090a803400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 66180946 1250 66179696 66179731
    0x31103070807110111120f0d0b040c02010f0b040b0a0b0a0306050901030309050114090306130302010626010b04020406021203041a040506070201060504020f0d1113030c1703070809010305 82
    0xe0034060351080070111550200c4141201c2c3d03e5900489081031100d060b00101286d602818035140507000e0504444135840c0c0000d010300d58119540c1100c3c400c1403014005101c0342c1d58419019001c2c00311000c00611003494014602142c0c0b80c030303004010089402a2640700504d040a02c014180e82c001108202455116100003680303469050b1090f0003180a03990300d40d03801e410240014142080000c2440342c0072001d00c0041116540452800e80088541a5100c0605007500d8240d014000e507500604404294400088412108a9041c114611244001c1010841c21010042280110301641005034800c003049510700c0340c000011038000d8040e01a08030074103c46048840c241000300c604640301c0e00050113000c041c5809016160180404603000d5042035000d46a002440c091f81e400025159211903580c1c0c6e0000341002100c43c1d512a0f158002095602c134103060740221418414805000c8400c0b200c132003229000f20a40c1c0c20030382e110410078034001d40d0a0046000d0b18010b07110540844c4502d10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 66182196 1250 66180946 66180953
    0x40c0e01050409020d060e010e0a0b09010303090605030603010f02030c04030212030a080711010e0607121503120f0504080d0207080d030903170403050c0f060714031b0f310909020d03110307 83
    0x1200c8d00800091105110520700040510280c1c2e10141c4418001c0c1210001440000d81100303104003a01c0c0d05190003512990303043c0001e0301400b03800289100f03086c800018003c1c450a203074024002d5030f00035504a520394a2082030315940f48100c1c1c0340e0340001401503010502c480e1286080c0c461407903021001003030640d80c982e0200d0401e10183c9000b40450000800071040f01218004c020000e4420804529043e245440d8442400d0140c0f0207074041101840ca542405401203050390301900007401210500b91205002079a00c0c442805031a40501c07409030601c1400e40720303000700d0fa98554980d44d030f074808000510415224450180c003c800f8011700f0700103841b440c4810407038400c0c0c094880c3c00800c0c0604080d0006000350210390815080c02c02d0400802c2000d02101c111940c9a03840d04100075a200141e1305590214024061344540035000c58102c1c1084c050640c995440615061000c02c1550303580b4500c080413100707040c2c4000d403c6400e10003980e0129014201e0052101030240c1500e2800b0307520703035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 66183446 1250 66182196 66182219
    0xd140a0305041b0602240f04020108130b090309090c0f07121413030b0907030206120417030c03070306060804050c1002030405060c01020c0706050a051803070b0a0e040c0e01050409020d06 82
    0x700544c005a00c01c040b222090442e0710900d035004a01e0040040311414620584907946000420290600c41d01e400450300c5d80c4c0c8032004903607106400c1510904603090101c041a100c0e480b10751200d120745401c2010400011800040750100c400d241605441c02846655030258101e00984180601007000c495000040d45030004103445980b5494200b0141d0075443c045041020143c466600365004503018001a01c510084030000c0c02950414070300f030303502c5240603416114034002c10040300101109110f54010704401650043c01c01d03860500803030303807a048100c600c4081207030081d1980c1d10040208ad028140f06039480d88407019441903030f1030b140d00d8401242072a0302442c1e1540c3c1076940080c03c1481da40c03080c05814003501c0c1c3c524100f0700e0f000d100d0800404901500704980202440035000c8640d90743c0070400032008116021100343c4440b83e5203006080302405252060042c0d0805d00c0302c65140c0e100b000300c074292842c143c450f941000c2c05c03c0f01c41e01c02034009186180c05507507a120040381291780389 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 66184696 1250 66183446 66183449
    0x60e150c06040302010c03020903070501030b0d05010603030519020a030e010c030e0301020c07050307051008270a0b0915060603011403010b0a1203021b03100203060409060603140d140a0305041b 85
    0x34000c004600345450002d08459050441c50100351050020701465500813070882c1c2200c409207000328000300e41200089000000e14070043c40c5600c0c0003070000405070002c02900700c682121030440c80d0b00000950590310381000b07840042c00100c903200302c03030074641c000d00180014600a180c102001d0b03011402080c221ba00c00840b002c0103a0000204000ca45010409040941020366032030120782111070018007411005805000020704142140c2c40846103002c0707468220200358100e0308542954184181d81c80010341d01c40009000b070f14200b142c0740b80303c4a8110701484010702104e2031a0710700707120006210b03e940195607142d52640c2800c220303070361140c0041000c0c1107000400302100c04c0a1078060325101030566043c0100c1c84401400b0180d980200f02c10075004000c15025a41c3c0c0c0d82c020004004191010000303046a00d41000401406152504041c5e4075120754100c4414040e108801e0714440100c0b2000f0500b00020000040c145110740c229503000381c42040e203107201d08001252111740c005079 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 66185946 1250 66184696 66184717
    0x52502030706120f020f0306060a020a060504061401050402071104020c0124080105180a1104090f06051b09130b0109081506100908030d05220c09050a0b0a060e15 71
    0x3d010303600d00d5042c0502c01ea100b9101441e10440c60301107843c610040602000788124030982000c125484118024446004d40ba9030010f000c02c258603052a01030b000308903221200c014688003900108003410030b842118005038002015840c440320b10000c11010b58400c14604002c2e54031030506001d880d90300340040f040b0400b07607c0c518a401c2e081c11a91801c540c80200052418005103244146403400400c6001c00d10f6040260310f25801c110501180180001c42001044001c0b40700120f0103004256100c01c0c0140c0b1400c170042d14070b030032641150b43e05009189401d035201348072128030703158100e003503001409e41c060606240f42981c2c1d0300d503001400c1491180c5000c550b820320004200943c42d2044240a2201c0a07051a81201341000c01440c0e40e0700582c200801c0c0b481e55040460290350800f800e11144180c10404030300055014074200d03100b041144108544941030a01207800507425000302c042844000d080015968501034007103811503041b040d03054000170060210321608002600030802d0050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 66187053 1107 66185946 66185957
    0x1171305120a020c0102070501080105060d091703091b0102030307270504110403060b060903030901140d02030a0603020f0406150c03120204090903140901052502030706 74
    0x1a450600329003007500818840351031680082c10841d004403c0c2e01341c45610303903900015a40a042800f03410390141042c480d441d5221170541c0000c4425014245440344649000c85207034556206560320421900185048564484032060b1403c15110a2000f90701e5032400d0b6000515030b44102d860a000081c269601e1503940981e0f0034020f000d072000401c100214003802e8030160681e8428801210039074100903071001c2e6454010165601d546010f0045d51800c0c03084401140c0003529902c1444011005100c1d030481b03c040383c80918440c20317200000184450460042101c0c039000341d00e070030744078a00b4190240401c0d151401090b050354002d003000307419100340b40b80982d844440c1d0042d1141d4a13102140000b0f042804c0c0c1c200f4001c8601030744401502d40c81058030b88500b40b01d400381c00e50200d0410007518150f4402e648012101400681ca8071002c01d481e0780c00282082d074541d115900140 = true := by decide +kernel

theorem cover : BRFrame.Cov 66007196 66187053 := by
  have h0 := BRFrame.cov_init 66007196
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66007196 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 66007196 ≤ n) (h2 : n < 66187053) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
