-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3413
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:35:12.968924+00:00
-- url     : https://prove2.me/submissions/9393bc8b-3c36-4fa5-9520-9a8280d68f35

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 613669064 ≤ n < 613848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 613670314 1250 613669064 613669073
    0x90114340504151d04060f051011100504050f0c2b0c0e0601030f0b09040602160f0318090905060601030509030c2a0105120c07110d051e0f0604 63
    0x91040810a824aa4241690385400101c00c4070200515800506290b04c0c0c032402102118448069080c111024454141002c0b2100c2c0044268806e1520603210004070103001750045d401d420900d82d0030000e40d1942106000008050201039608644602c1081000141600c003c07a050410743c5009108041c0070560f0300c0c4034120f05c40f001c4400410a005000c611001402c5401000018000c1602030561460154009070440e503100141c014a2070802148008558420900d954465400080140ca652041021b0085d01030120070081031002018403c006158010581c0300034503c90f5110135110030344912b40d410940340080340052840d4020000300c3e50a6001e80c10240e44098201d04036410041c0000b4914606004042c2c410039092003002030405001c0342070041241d00c2c102307003842ea28145008807030700c4d43e02c00020110340899034085410020005501041d00344003200806d08100141181800c903160525038950007010040380205440118000c218010030b000c462019284d00d686035104c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 613671564 1250 613670314 613670401
    0x5120105010804081204030e0102060709030506060d0303090b040503070b0a020c030304020d031e0c0b0c04050a09090303020405060a03020c01060524071a100e0f011a1e03090114 78
    0x8a411130700a101d00314000c107401107910b200300e000350759194000308880006800c202018024800700710f860384050012490004a0320340041058404a9a2004a05044004004c0300100410541c0300700f0501083c0b0400001a113501402055045019103405143d03000305d01c00e5030303c6001c06400030b100217805840c00b10144600c15000f070400c00e180b000341c01c000e24198a40e6515400209144450307031810702c801c407100c15500945900a0f240b402c2e04020010b01055071921424071040e840305006030425100e5015100100030203032682d038842c089000f014000e5046507000004640c0b0b4601e000a280c0f0b09040d243d00c1001c00800d01103120310803289003041c940e000c0d10081d1003594034541040c160200c2501e000b03106191000e018614a824908421500035001c1c0c4100352400801006003c3302c015103004141c0c1001141e400da40d80c41c05219440480340501c0d0890300c0c18200441042080b04064000d1100c035220160918202d079110303003d9102040c5580c1001514030030f030700c00345071030b801c544031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 613672814 1250 613671564 613671571
    0x60a02090a0905060d0803090703030e04020403051f0624110a080406030902061c020319060305060a02030a0e0609030c0d05130e060a03060903030b181b030c0c072301051201050108 79
    0x2040e0705c42e20075003912035840c4d55000790b4002d411540032030310800c20305900410140c3c0d03280b0300f128290710b803d1440d01e40941c4d07041c01210790282a51004985c1501c0000e680c0a8802000d08064103410191030400e0904085000c180400100d001c01d03000c00400c00c00800d40100d080d0b84601240d0504d803c00100314024002c00c0d80407a008a4104110b48040440c101e54000507101800050796a141600c040e00141d00c0350b0708243c01c03581c18804140002071020409541c40644100016200e60b50554000003910f06040781d400c00707004100500fc1d18210200c000c3c00c00300f40c0107003201c0070740c401a40201c403503100c0d46141000103803d58000b40a07001d92004a00c0d08041c0040c4402c01403516a1181e6044a030741c03c00440c0401c1d40c540e424801c03420008280c541451044020071040c0c900f100d8241c40b505003183c44900101c8000001401c0400a0400c0e20307800380d983e0040f14034003603c5510707035000e0485030a180740c1a07540e00c0391062550740c03003401101e0310101c40201c030003003c0c2d103410300640d03a012002d07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 613674064 1250 613672814 613672819
    0x2c150a0203070f12060302180106030e0316080906040504090b0a0e0d020715090b132303060a0b0118080f010b03071a0702030a060f0b0a0b0a09061b0204050117060a02090a090506 78
    0x105000800b583d00c408205200306002340700e0700c3d00d40d4074043d006001c8824001140e4802e400130304c04000780e20a480ca910f0140c680281690b0b036201c0503980000c07501d10954001d15401031601c0b561800f403001142c4018490b003003540040143c09d640c2000c0a075143e06003803040005a21050017070001103803045005185a0850802603406a1110846205a00078010b103120680c0c000c4810400e01248060000e040079144051702c080412423400700713444074002000400745540715841e40400e82d10403145200713030314120969104450307102e0700b44a4a4400318605221190f027802c00c548941c2c5000b05040b011650050034460590002405403d440d810145080c0d900d8064219050042101030081c00b18060850a0000f20200d08104010010005402141c0c2c81e18050041602c4150801c06900554085041ca144044000d0480c82959801c0d0311000f1b40090030180001611030225010082c102040d00580302903945001c1018124060090259409031a000041181846d076600140d08206c02 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 613675314 1250 613674064 613674071
    0x3030b0f191a07060e030d0b0915060318030c0d020709050c0306091807120614150402090a031a0708010b030c07110102030706090510150302060901032c150a0203070f12 74
    0x100d0312444c080300c1800075015000c0d0000102000c100c8118483d002060104803141c0b00c403410501551000300301504400e40c01818000040703240340404000701c4944c450440700b1640d9640c1c1c4186e41a40310b020040700b03880588220103001c00c008601e409040d114034882e802c01e03130941d62517904110071400041c014001c000b48031040407031340540602042024043c02e558460b181c0d1240e145c03220841d03242100030f42011800009100380e80e007071911910314822046070050b84070307807050001480340c03080703a84000e000e0301512078035101015485054038800e40460711201900d17030303980c110b14800f84021282841440d908010100006401d8001d4800420040c41120705000c0255107400c101d910202c400d4400b80d001c00003810300c0f000f1500031030840305103204845079038501c0e643c00b0030f102e80598a8401c0c10f041d1a14015000181d4030325400744030192000709008568840c203102500c441d0140020b80b000307100f01002402d1700b10365002310303401100e5907030300d2520011000204440c290078860a81d41c500b901e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 613676564 1250 613675314 613675327
    0xf0e1c12090e01030f0b1612020906210105040507051903152c06030f030d0e24040b0a02030f0711072310030b01140304020a050d03030b0f191a 63
    0x82e07031070302c907800b03544135803012102844182000c0552990050801e148040805550080680e1119a28040d5890001d003da02e61503540f00080050184506805d0341804410002d00c00348c2405c0030003412202c00f52010052a190184101e4543c0304e401c000c04500c882041c0b0041080d44680d1002041000400c0000c01e203035103c4001080b10394844400d00c1c0d60311504001003a0300d07540c4825007a0045001c82c0100002007110a820b5100e024185042007002c2d518030000c11010005c1c4090072045601d400a1120400545411710300301d03000382d030305a8204500d2000995191260710841c0e019251080c541243e50742d03041e600301ca00c0f0034904c1c5041c83c1c9000324400003455007140f0380f01c01c0c00c6080700800b5944c0c810000c400c1c840004503815466003017500b848540481a40c000320220845210294210794030b83d554000304403407200540c405c0b0f07001440100600e0030b00d54140d0001c00d030240304850440b0120500e008007c0254103801c080e00c00d48035400020030544954525405800d03940d51009410200e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 613677814 1250 613676564 613676579
    0x3030f0a0612050c030d081303050721020a03030605090c0702120703050105101a0f0f03150d0b09190c180f0c09180203010f0e06030f0a030f0e1c1209 66
    0x310b0844003140c0561050304111400c2c03505002c6019080100e00c2c141d01031385048142c114184042c460003800340400084c1210130310030800a945030f450502098805000c0c010b100c002c0d030350850800e0540020303250040c04640c502e840301c607003030081a8a001d03442c10071800b5002c00a160344014040b01e064820903900200046082c040d85d03214050800541e00310a01c0c1120b944450207030340030240800c6004000d0801440e040406580d1400319091a41c0c0d140e51340d1182502c03030180c0d90303144a94051a002d0704213007081450820031340b041c0e02010a46084154000e483e80e158080c1c0c4070000e101c01c0411605122082c41028081c10030b2040d5400071030103000c0003101100b00e45980c4c44550004144800901a0b5400030325183c220130f180c0710045256600d480711601780700303100c0e002d684695428500030803d681c0d4100202c41c0740740c1400c010369103066494078020b071030784003800c85241c00709108650903040c52411424074210307610952084200300e421a9a0703840c81c05a034161030003d0040820010a071003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 613679064 1250 613677814 613677839
    0xe010518090f1e0603030729130c05032e0b090414010b0d0b07080403050408010509011401080c150d020c030a020706031803020a23100f0e0a0503030f0a06 68
    0x9018503041d4980c0c0d420041c2c508803500103100e03c040c89202080080c00300b940c4001088501d420f401000180801c80d0120481070043c1600d1000c2c000000860140890b09480c1105d003030441c1d101d0108402c2c2da9a80d00c05040d242c0000b0200700c004110044065840f42540c42e28855a4074141a00040c880c21140700090000340180c0e07098481b0000c00400c4d1804001c00d1042d03441880c400c0b038654440082c40c0d6101e0100540c024581c030304109030500810201070042042d01c001e4000f440080c00b1900c0e02c6d162660023040000c581011410300c0000005a11401044c40303e40d02c20058401402c16503600101e800710f0740095a52807000b0f0f420400e000d1008000d0000e44110480b59020f009202c1c41c01400500b50380180140c81c41c020810340e4400006078000400c801266809210f602c036107410051b404c0b4220740c00c4014100a40104542801607144550141056010b20101004850134058a541d030325841008020055481040420795600070300744581d03404001640c0100b0102d48072a08607002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 613680314 1250 613679064 613679071
    0x70f0e040903170906040804120c03060f050a1104062019031205070914130e03041401110a03020c0d15020d2306060a11010e070b1306030c0e01051809 66
    0x191404180800700c42100150f603007000085009002505103500c0315003580c4102c3c40781011400d40d45564404008980d0b501c0b03001190002020404003031500c00410140030100d558802441c51303d40072411982d64102550706983c1c10382d0303424510b4251000c8803201c0140400b1a0101c038851100400d0590403810310030382510f0b219a0b20b500c0c4001c211400042916400b40c0580c05101c1842c8007030100000003100340850400481c3d90440c0f40c809071440c030b0010180782d48410003a001c0001c000c10440010028503a480b8400c3e40c2d10a6110040b104490315940040c40040050f0021544000d4514007100d846840b2401080174407041030408003200101e92002d900d0009a0f03413161844d00d40c83c0300380d05900e00d5094640c1d4007240342c0d250030b50007c0e120f84549600c04c001d00803440700c6403400c0e000940c081c0021806c8a4101d65100f92904008e800799040f140200380d40c640413880200340d02d8840d0041000a2159484071817a0601d020015112508802080b0304406000311340c2c0c49940d81d0303400300e8900 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 613681564 1250 613680314 613680317
    0x21c050a0206010902030402030307020f01121104140f1807020708070e0a050c19031a0301020301030b090d090f0e180303070905040e030a1407050102190201051504090803070f0e040903 81
    0xd85180100c4040d0408005034052403407a8414420000940c501000326041daa504a80e0300b481c482c8104c00680c0e50803521a81c080526161041c9400100000c100600545036003411403145000c0c80010080e20b603101d9045640c02c20301400c08207151161612020b50000b407a401912501c9403548542c44c9007042d19444000b1400302e220911190220903c5800d4202110b405480d03c0c04500b81c542c0e10346201c0c07205140d0205503844400c0340314040e840c1d90056000c04000e00956a030b5070341c3d081c104a185020350b00c10701c007070107507890f8083d4881c0914016403c6508582c50540300d503280907a030f4000d03981c0080210f409250044c01c810f1a140050004601c01c0c4e11036110301503203a0404051108503010700710400d0716540204182650309410554204481422100031540c481d51f614105004e030041c0404607020601d981342003003455406400c094401c0c100a000d2104038074a180c200070654000190107080d8403020000320302142c0c400c040c408041c5909080202ca0030040601080c120340040d20180e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 613682814 1250 613681564 613681567
    0x207080d12050f01060203180112060e09010b091b0d390f0905060c0102040b070f1a06010804030c02010e03070b1b0c0f120709060603050411040614040c021c05 70
    0x2510341d00c1d507100b5503401190b00401c0b004190704145000e5501d21594003603103502e03500c050b50300300b0b031368404d4001110740f0070524424012603588105441d1a4041500c03207091950030009942590708050240e14483c2c400d4009c20658000c1140c100c5103958854098078502c1a103481115452049000d803284401041c0040010084403500c10310101ca01e411810004006560100d120016840190001030700e0044176500d1b07855101b035105a00a02c920f62045110000c04100031040c0b205213000c60031100e00512000d5522044811381d580c2da4002240e029010400300d40100300803034860382c1c60381d25651040c107100e6413295aa100007450501c00c2e90000c40046000250300300e03200c21014210586410300ba0040034100342407400611400d00d6050118020360760190103140704c2004101c0200100300e01d01d02081900e0b110074004020f890f08a0702602d00760512050400f031403d080c403410003210502c00c084c1c40c0c2500c0c17007010030015002010041c0210311483c80060b07824107012400715aa5601c644515 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 613684064 1250 613682814 613682837
    0x30207061406010e04090201050d0b030a020a15020d05041a0a0c020a090e0d031407081e0c09011b0c09050a09050613030807090807121703040309050411090a0b03070207080d 76
    0x180b80b0204c4d102028012802d1003983c0b00141d8022058135104a061103021070614a4080424a4410901e0f0003a5000080520018640c0131a00208100000650a0f076030a0902e014082d02d0310302c2103109040110501c0c40301c1e400e00306070f00301c041c010507903182c038003144c51403039680000d007294120350800700c0c91640e2544000c9241c40e080184448007015403c06100d0f40002c29401c03130340c00ca40144182d080c01548030000c2d50f18404204007120307480c400703e141042828105c0d8a0300036600113084580c00f04a50008100064030b248054040c0c1136400038494102d141030030080006020090482d22040e070721000ca0000080c01400201e00c28080d83c1c03981200c0c04e8040c20001c186950107003070301c82402000c3c01c05105680c00072846000341e81d0174081c4a50740e511107140c032140c04030f01440305108111021003884101a0700c444000c0407188100ea0a03c000c1c1407541e1402d46c42d05c41c4a064591001100d5010882d6080603000b40d948414140196070000c0c0c0d845842a00709500304400c83c0010701b4000e1070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 613685314 1250 613684064 613684067
    0x31502041715010609080a021e1206061504080c0d0213020703180b2110030f050a0209150a031709040203010308070c09050c0a0302030406060b0417010e03131503020706140601 77
    0xb16401002c0d03038a00518140c6c80d0020540d2240740c400c0020307004400320b1000c00021914013541c0c107450391025140350715240740440182d4035500e040c2c0c0c501d031190b050700c0e00841e03180710804156400c1d11001d0014007021900102085090284000103d1f080180c01d802007009140c54401380807640c1c041d0b10760380e5400c98042c01c4044c640c43d2070780154644807000c0c0310386a000c82c0c10342940301380d41c003400300d40507025155115440e04081c1c5640c8000d2060b140003450008102c0c6c049a03080c8414426100329055403a02c901141800140740c0215801c004258010000700c0e84088103d45900003001500c0c1c070b008029004581070f60700036003013a9141c007030010312803007000072241c1c01c003008000070f400810890030700100c071800611030b1000c0407081507004808541800310f9540b00e40d00400c2154602503440355504202c580039440c4100725030a55181003200c60440d032000c011160070302000c02d003003008542000c201780c8040e007600700c540003015400d1000d000002d400388100704411410311030040707040c58080b00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 613686564 1250 613685314 613685353
    0x1309060b0a05030f0a0b210d0201290d0506012c01030b0a091109070f1b02030c040c02070f080a111806040e0c040f0f0c180315020417 59
    0x2104180000c10032071480d80e902205480c0c110340c0300501041591269030840000c0c1c0340d41e20103154043d483c60a4a05540c0b0042c2490b40700e1174908065607140601180f0981c200d80029044c100c20882c03103910118400d440802070406228001c1c10010080003503111589804803d811080c034a941c400341e101110110141c8540c8000320010050b0790300c0d81165246580114007038940703841b240c2c9a10445040200540071114604005072400c180351414020081c40080714031541c80101d01c0d0314154112041040c4041601140c02038014070040c68010305201c0104180c0ca104c0c41140900e0501080410800107810000c0038003000510041042c1d050000042808a082a1080000500842c0740c0000b0f248050f500c44c00032100001c200266100f06810110458607455000c1c1ca090700e042d04489c0f40394422030b240e110141041103100c86080042e201000091803258000031400e108200003040011481c40240544102500f015a0741d20100070141c2c00a606003101e03003007106000000c2000c0c1d60f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 613687814 1250 613686564 613686569
    0x1409010f0312081905040323250c05030715020d05190c080903070f0e06010804030203070602130f0e070815280f08070303020c0102060f060d050a0206130906 69
    0x304000300d1440c2d9074281d5400d1880348081c103000051001442e8078064030b15140708441005000e10891400b403a0003000c41c0c0d00c0301a028110721070000d0003401043c0304000c2d0b41c803035072068508031480000c10300901c40074810a202118000007000003c10581c4080c0000300c0146a03126a805042c1071120029081c4a04110304504114040c441d021036145096085007060401e818810003070b02c1141000d0225101d40c2101340c0e05032140c024001400c0c1072146040c5d0844070300f00d1000700b1070b44840c001150b103010180d034041d005a00a120f55404107100d0780c0103007103c02542e844020640c0d91440d00403008007140d4044180c41204d003041041454218080551101400068000d0382c4980d00024038140c2c05051020100620325503c035500b110051440d4028046001110300700c0c4d83c1d40d02041d0b0703907900c8a0104400602503200c02d1401075000003034443c09408482040c146941d1080240044d0810b071071015296440740c82c0302e84000d42c40383c900400707503a101003d110416900b00031141c0d00384c1d01070b0f6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 613689064 1250 613687814 613687829
    0x70e06030105270a050106170c03070303081f081902030c030c150a02030f03010b040320010507060207030c200109120b01090506010212040902040f060302131a13140901 74
    0x110400241d01041d280340d012140d404036003075881035540c00e8410324000303031000000c5c0590705c0c001d07010030640003901d804c0b003a001083c011140048401e20030b1503140c0e105844018042900c01c0c4c089010074040614044885506d4070702002d04560b95040e0b203140c94405440b0300c240000e008021010f608080c45034200305502a4010813569180300c020503088052400d60b13498240000c07408441880c42402241c1441d00c0c92046207480e56103801c4c0c0c000c915405840102d400c40340680800909000b80001a0754201c0c0503140ea41c00c248240d201d001c06984500800c9042020107010000000c500b6844040701441412070ad00710004003400142100350740d5006900c0c000b40394032004c00081c1d4120142c0d41502c05001022803a0745a4400503450011341e0300064500d40340225010800c425150701403c2218618032210038100d0740c1d10000e500302d100300310006500200d0007000340321100c5151010300700d10300300c00768440c540360041c44044000d2180c0d800402d40914401d260b4101440d04058890140229 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 613690314 1250 613689064 613689071
    0xb030f010905060d02040e0f06040c0503012d110c10051b07050c1212070b07120203010b07200414090c060f040918061b020d0905010c0b0c0904020c070e060301 70
    0x7850009404c00341c066002031041d500d41d08040500d200074031040300d000081303204549681c02c003490031101000040c02594020340c07803c00c001c400d00c0e034800c409500d409048940080201c0000f600174020305015803180c3c00140b0704000580408100700440c1c107610004403030000c3e01e0b05060010660b4001d004140100952060041072b01140c0f0220354034034000300c2102c00000e982c4000105e0350030700c0304d042140b641110002c680c0b20140b04c505420b451050708a5540c8010105108810104034002030180c0e10b4420b205014400009000e410380c02034411070304007042c200030f04507400501a03e8100162034100b951100034027841e40420808040682c00483d15142050102e0b0209101c80c003ca01c10103041c261140e00d10307064201030211401d007140d000030040c4940d0300389448111130840003508140042c441c1c000c001460500c0754003202c0565105a4421107a2101911500b51152010b00120b40c485000c01520040760340700d10091540c844120087d00169203451038401441e0801041a4000d905 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 613691564 1250 613690314 613690321
    0xd1505120c060c010b060313050c0102060f270106080706090b09010e060304080c0d0504060809070312030b0307090f06081005061302030406150611120c2805070b030f010905 76
    0x1c90000154a001d0b40e040780c42d00c110510705405451140d0205802c01c178000b040c03114292030210109803240c0250102d45c0c034810350030012039075480c040f51508040e804002c00f007000020450032240590f8000d5040400c02c0205189141c219500795004400c1640315050800200c0d070030010240091411b40941420280341e40b0001e0140b20444140621540b4000006420000c0800540c0c80c8072919900711030750152850005801540305010303204c0480c20000000e40d600c200000c031401540d074040d0041100100e4400b0540242546003881c030341c18000c0480214006400e481000d11aa6082c00f0100d002c1d482e04a00900308140346210f421900d007030604208007922403540001c890410070380700590326556814581300038407440307100160700d800e607903000150181d020940c1081000b8050030350700b5200c6200d440020610613404e0400080d0469911440d042420b50130307441d248414941003042400456441b141800300a400c1520100c10101c1030018001d20401071a015140081003008a0308 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 613692814 1250 613691564 613691599
    0x80105120102120a23010b120604020a1d01230304210905090601120207050609060a090506010504090201020c12010f1a03060a0504140a030815010c0308070e0301110d1505 75
    0x480003042c0c2025951641201044000c4401410445c0c80b00c640d03143d0406e5031130300303c40031403640f0002107042e81c40e00c00d40c0861010302d01032003100c6091710607842e120001900c0583d8501c94511560b4143e05120044021000c2c1c29aa882d04807840d0070094241c41d0340c0c1c0380520b0b044a84190f080d91100400d00c070003104102d402d03001a010400d513001150b407814543d9403c00100c40e81c0c10640480e0116034000716040081000010b00786000d20074110986502d81d540070a6581110381c442806000d56100740c004000f20f0900d03600c041c3d281401881914501a004004170340d4044c04102c041c0c01036036413149504141d042c1032088580c00310550351140d80c3c0d000b18100195854a001c0e281c00f080c20b80d40c2002c00c04110b200e60342402c2040041e03043da42912180c0c00c001e06484000c451a12440c0c003044c000c070489600c100d8422487e02d515489801040d1501c5008480000c10124200d4056582c1e01c82144070000b08009080c3e4a0200b90001c42d41c442c1c1003440850388583c50780558000c9002d440304040e0714 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 613694064 1250 613692814 613692847
    0x40c03110703030e0102160501020c0f060c0904050a0902211c080411010c02041e060b0405090c03040f080403210c03081b090a092a1403071806080105120102 69
    0x710341603d4085007920301200300500910480c07028142942c840e80c221010080c043d00502450390f080b00a031904c50140890300c071b860301411074021241440c104000101460b066000750b40200c07040c800001c015603507a0120701a00085c40c0c0007201c0e4a04052000500b82e001c100c1c03c06840000d400107204200c521401811a4a0240009105151010520110303901c500c3c0003c8032076400030b1007808070644498035118860001c0394040a81c505001c004030301000701c01d0440303045640107805211941c0d5040c40146081d04003900c1240e14080c004040c0010420900142c4040c50244500a00a0740710568a40644500c0112601805051925100400d81180d101a40040094000d41040e651040b00c001240304038940141d011500480105103620160300c4803c403800401d423030303e40d8500302621411648201105940000b60040c4009042104a0018603003000709030a020442d00000c3c00d8a4002a400350041c000103105440100000e02c2c00d04603e02c00e007080e04008610b000c0d048203102c41c12 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 613695314 1250 613694064 613694077
    0x70c0203030d090303090506190b06031009090c0f180b01170f0903070b16080123040902010e041d0c0103020c0705060304020d0c12110907050a110118060902040c0311 73
    0x516070760340103d40c1450701035003015030810703448420741d0321500d071140c02014583d59000251030000d1810700f030348555040500490f4000d03207071244040022440c11318040c010f480c20000071250b00403510130005070000e8014041340580500900d1540e03c0346488001e908848c0301016181c1009510181340c514100e0780c08000d9001901840901e8076a614880381c54030310302c6802d50003450421501d003041045640865042c0390b01041d503484400599950204202000e0b900ba4502403803141c1040c94403441c42d1030752021006a1040c1080e10b080401440002d0441e400401600f004400c08800607030307580402e00109411050900f41103040102c906110360741c0c0c0b8981e0080602440c4000042030955a1700000150850703400300e003d924080e02c80344003202c24030b1005070807500800f0810a0f41814940404030500c101120f17941c0609050f840c4808481d8003c01c1030319010a9540d500640d001c1030b5541e2006071a0501551012505041c2c501c140000c0301d414101c1c1c03030101072800d0100d260160202045512 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 613696564 1250 613695314 613695337
    0x1020c19080327030708190c0312020a140d1b0908100e0102130f060207050402120f04020d140c013507271503050702061b040b041409070c020303 64
    0x107860314102c3c04a5a48500740090455101c041031075000c001c56a001004901981c59183c111000e00610a552291990713100070041806121150344150150707028148940d00b80c03500a24401c80401d9040082e446040521002515103424102d425862035030446d0500031407a14000c0e003807038580c0c0c0c651240740300c030300e4004c1103a02d50144401754039094040c0d6407810b40c030410030309155503200300a880c0050740d0b11401000d4001c1d07010000b05894a8800e807914600c1240351205c51356101c58400084090046c002c9900c070395510100c1001c2402821390800034000700c00141008442c4400150140d440e9520303178400c0303030f038080e01c08202550b092084c02425105598401b005840e500416503d480d50f5410000d002200c01001745601403600201000312507250300740c003500a0748842c4c00c030165041225803c000d81d0010000c03032400c203500c0c110310b07182400002000782416103034a040b4200c2d5110350b100c00000821103401182616180a240b80c1003000b43c20140303441e24950b40401e459024414020320f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 613697814 1250 613696564 613696591
    0x20706050901050c0a1b0f06140403060507020a1a1f08030d0c0c0b0c19030203040c0308030619080c040e06010f051e0414070206010501181a0c0601030501020c190803 73
    0x6030215040081c0038000380d103c2021043d01403030400001b8450300a00c600f0540e40c1d1401000901540a80128000015000c61ba2450031742151200301c05090003910220851140200c207a0104803803e00007840702c1c1d030a07240707100c680c01d01503c0317040c9505201c4100d01c0720407414441000240c070004122000e81c0c80c502c00c01701d50041d03103050507200b10142640142008240304200304a49a01c0790003440b404100c100c4901503103494500c21000c0340811940200350b441c0c85942070010a01c1c11703002d181e1241c0c0040900000c150034486418404000da4040120b6a010b585000c0b050729150050400342e10003200180382662508000401380c401c1da01c90640900252149405450020b900c180c06d030800180091000440039243c0404000b0704941c01c00040c001e5600214441d0721404858540c00c25900300e00e0360380c0303050214039400714286030403103003040408104c01d40303401905126490086000d1000180c50380c4940b04103d081120f02c406040e8618040c140754400152882c060300c0e08280d80b80140d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 613699064 1250 613697814 613697827
    0x30d050907120b07021b0303070201080411061602091b19051b0303062803170d140a0510060f211d010b1203030609040318180c02070605090105 63
    0x1030306090141c1c00400b2003490b4a0201c0e410300c42024410780c0914415070844149001c0d00004204010707060601580c160002c1040c1400b40d071103000d94a0b0058050800407020103810070001300164008202e441c203c0840d4500b100030b500d843c0c407480e9480012a081115021002c1c20360888510403001d4089407082034105262081d03105a05803143c8190390340402c2002001d2202e8140c2e6500200c521074450390320f0a8111840315100b4031403070401107a00905111090455039450402c0440f8440410040014040c0b601003003414000c2039080400d0742c15800442c14600c002c070042e1240106900e5109983c40300c1000003a51010101030307000882d1800c0300320103114191448070709034044034941001d81401403080c04a80010825036405503040f000704086600f4109010b50904a020310101d107800c1840000d9182c2003109100780d11610030700d00010100540c50246121112a400010718640301e88400b03440c2142909c80e03000d04d45180d0000341000e0713160400041c141d22413015054100140810315 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 613700314 1250 613699064 613699081
    0x1303230405060a031b0309020907031d011107120306140f2e0314040f140a060f0203160c02101404080f03070c0515070b190c0207060e060c030d05 64
    0x25240070340070040900b5501d002c0c4500003000380840324824101c00102c0460100076601911800c400b9a82c0a08210031340d9035130a10135401130512890300d000c0c000c5545503250319400700384a03032001d44018503034030740d2a05164240281c252107d00060002c0c540740c04070038002c040c0c590402c0902480c00300d0b420303107402040390081003103000c0c01c407400c0900f041c018402d070003088001160f45804290b83d94042107450400d100d024455081540c1c05441b070007000c109900860806401051034289c02c40443d4101c8140307955040882c0d4455961281c21540401400380e00c10700e0030410714150fa0f040c600000c1c07004071900000c001d680c3d43c20708031040c04075114a41303c21500260036100102a040d0660310386001c5600d09a8880d80000d5007107440a821540100c1d041c9801c0308054070905850403050300b4102266644000c0d01790140c284220080c42007401c491500c09c0d80215040610103501074a025440e20350064140c104844555100c0c0c94103014112a000c000010b907262103010207800708894580306d41 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 613701564 1250 613700314 613700317
    0x2040b0d021807080c040b0904020c070308070308040303050a02070206191209030816090e15041107060e070b0c0d0e18180f0a020a05061e03130b130323 67
    0x80094026031071480b107080259004284601c19a150b07180c1c1000c80d074801d18410a184030718050150703e0002442044068103265000c2e090300f2944600700c501d4540c07039031903070103503600824012400140315801308020198140212a000154900b003903041100550000c0c5c0e00d0f010f00c1c000b0380145081c2800d01082e15214085410305006c51034400c200e500d0180c2402016914107e4181c2070098800300f07454120741c40340d991142200c280310b80d01c02841e20380800136040460780c650b495500030b480d0003a4204901191000f00f000300d00c50040042e003907011000643c20142c00313501001c0301007424004481e042902080c1c0d440000c41034a00341c6d152490403c00100303007007075141621045003000b800300520032909a8800c003200500900b00c8038254118420300d5500e140b0201300039041030303042d2001c1140d810000c016207461200d180d1013842d030405800b01100d0070b070030441d2260822145642c3c0314041c0189006016041060500602c41308d030388644010b059520300d2104104103108064203080c0c401c00840 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 613702814 1250 613701564 613701589
    0x3120f060d020415050f0a0e0c03090a0c060305062814061e091306030312020c192a03170703050f070b0109110702090115020106261203100302040b 65
    0x24410048404090f00d05481c4c8aa94020940200ea12180034403540c94105014000c6904a45441c6580d81d2026519423484d08040d22780d804610030350380c0b8400000e92010f980c0703001e028103940c002030f68070b420402c02103105a000100305003007040c1c020000f642082ca00c0d040d820303180a500b41c2441a90382c08042500d83c82032000012903182400408100c1030114002800003100490320443e52200149030502219010704c8010041590070812a218000e41e8001d00901892a001d462044641d1002e015003035841c810106d40010a0141c500101031030346020441c5100006201e00781d480c110f03a90000c0c40598030395803519030745000c5100c0702094410422a103000f00e050140645511682ca000c1300c8060b020700802005500f040000b2072500c14000aa56009800401c640056460991100074905d800030a80046548514008c14400540908080c070403002d0b0301600e80e1080c51410f050308080b031481001004c0b80c2e00300180001d0f001d0201c100c03026660100d400140500116002414081810 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 613704064 1250 613702814 613702819
    0xe010c05030f0706150b120a2c0d090608010b0f250c05010f0c060e010b12100f020304050d030b040b0406080d08070e01120510031406160203120f060d02 67
    0x402c05450b50805000d0545907118031070500c0740c04030042c021160588240959104403100740321101d181d80044400c036821500035071000403551b03a005020035404d5001d40101c1203c4030580b4640840450802c2034004603c22480c0c403000803820090000d15402040c45502088034005c00c80c81e07041800c5d4000c5820385580d00c208442d40034811008000c400355034007402c1d81e20f0f4001e4800040d0310b5000318840c25400d881540d455030110242d9544d08014682c120514040d0340d030703c0003c500c064030b400314210140c04a0400818203a420140b010040d14495111001083d0060084c0400641d00041503019110141000706940148501217002081030581d00c03035000d401c0120000b500040403c8007400555a030383c0f803904540c2c8201080da60226105e0510b80055035803007100c8500001c3e580f0090f04040a4002120055035a403180208040d003c9502c494540001040c8a000140d0901ca156444802d001550810485409400c405032004190802444a00d000603030700759260a0082d000c0e07a0700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 613705314 1250 613704064 613704067
    0x906050d06170a12020619150314100e0d2309040204091b0201060b0d11041701020307090e040201080103230f030d1a06031512070618060507030905010e010c0503 71
    0x4150b80d559980c02c2086040c2d494000d07180f2000400703440814501d1042c4020241d940003854444945001001400300c0d8041c8800b0880021000800c1d2007002921200d04c10000c055044900b08201e0890780c41d00c4021307001c0e81c8000d450408403500304005c410a480803054910303d18080b070041e0005e621030601c205602501c0064046440301e0142c0c4030707482c3d9040c1c03400c1c1d0000301240c0c101c007a4202d52060040340d042240c240704100320140186c01864008950b80c54003414103a8425200d9680100d00404080b02d075000700c10400040c2c1d103c200764004100c00d4070304545a04090300060002c0c4818040580080d409071809110002c01c0b4900180c3d512528048500220181c0b8850307403207421483d01c8030b1040d801c01169822503405078040c09080310000702010301c2c41e15404508601c60428520098214071201261035400c0302c1405040000c20103078a8100c0158944080c20803200b850741c00c81011f004080c008040031940c440990001c8d07807401c0c00c00c0076035250b6540050f101c61020a038001d005200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 613706564 1250 613705314 613705349
    0x3040e100e071701031e0c0b21010b0708090a080d020a050c10200106030b1003050c0616260408010b210d081306020c060405060a020405010906050d06 66
    0x80350030002252646503100001c0d445240003114001810f8000d41d1000c80e001c0c0061001c5002c009011500886031140b050001d201940c070800303248101c0d440748c00038680101d440c0010724800c00d0f4004080030b102d070500c0d19640c10011492030354040c0e604e02401d076003004510004a6221019214043c2c10010212401a400e241000f5076a03032110304229202d000d28000448541003242031003a01c000152201c0d0703120144001c1d4001e43c40f003070704d004201964030f0f80c0b0f000001ca01464842802460401e4180d041d49007581040c51600c005054803074083c0b04100b000940b000d01d007030031a030344445e80071030003030030a0034040d00a4015141c05a445d003001640020001541c0c14150300014031102c09440034091840e201d20403502d8443c09000c80401c80d081311008100e418890103001b030b0712080581042c1203480f41c40c0c440d0382c100d8004420b08030076540860284418004100450707603014258000652038241050700081440c40188601810703c88040742500b001a1190820780280100c04164440b00d00e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 613707814 1250 613706564 613706581
    0x190603080d0c08070e0105030915130308060613090207061113060e09060907110a170409050f0405120a0201020c061608010806090606010c03170906011409010510080903040e 76
    0x2401070701c0d1a070100e4540340b00021002c2c0101d149600c91407040d203640320f0f600704010040d40c55a00082880805029550319402c45c42e040d1800b8a00850300a01451022521071034090700303105000e8034103031207048248001c0200e021140300c200d003507840c41e10015803610301e207240c940d01502c4c81000e4440c01c0080030a0340040701803012101d01c2145c60f181d8590381d100e00040184070304801c050301c40e16000076909000403021401000181c1000100b00c2c1210070804460720b6104410400302c1030401102d2000908000600141c0a0560441e1055906000300e0030281c0d07880d0303170b90b2030981412040407802003541802d0307034001c0d03060f10452481c2405803420391402800d1030692140340c7c05100c01142e110f00002c04c0c10b42d0001042c9204401440092400340c0741c080042d0303540d41d5506821000c11100c0304485030508a40c4030102e000b05042c0d0001c000315414003003017402400104a5190140030690010030031540c80074088030051109003803140e815241e0310225800e52213079802204c0f0100d44c13502402500f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 613709064 1250 613707814 613707817
    0x6071821151e051b03040b0606131a0717190e0d020901090b1c0b0103020d0822170c01090b0d0603211e1d04020418060305010b010309020306010b0319060308 69
    0x7a802460710314944c52540c40100c80e0703800140c4000c0c00703042074800041d07001c0c02e03e500102900e084100e02c80c0049a075032601000c0c5007034440401d00c21144081160020026840151700343c003001c2030a12420301a440d0940301e07401404c1354060040100d000d807250b07140d8898005a15105401501ca01025a180c6210300d01411007034404030b008842e0ba0361805580034514000300803042e80a6840c804507441d603000c02447c00a82001aa0503910800c070207800c5518225012160a03590700802e906c291516002203c91420700004281580100384440c0050703138000c6004040d51004800c03503481e48940c0c0c984000401c0d150300b0051072081400b03050038030030a40441f00d02c058901991044c800c1e203a0515511180d6400da4020000300d49031b0b241d540980d1180e0150650701d864064001818103640f802c0041101102900418586a80b030030188103201d001e010300c801460342800d0038003601640341e0102380d4481d01442181981d901c00300114550315890040c80070044007854051014507140e04245219 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 613710314 1250 613709064 613709071
    0x3340c0b0714120a0216050a2a030b09011803020a061109100e011727030a020303011809080d020405281203020f06071821151e05 57
    0x580c62584001880300d8800c1c078050602c002c079540384030f041243c00509030031000000341c00160100d8081c03203080c40014a0400f18040b0a004000038006e01c0d902e030800318a060b04448810790111500404031145150b4446024106c0e5404504031141b5642d100c5010700401d40940000311400001d4109402e0503400641c01f001140a88410801510b240e40031245900c1284400d40d0840c1003010710340c0645018243c824042e00c01030405c89148215426003504030501102c01c0b0443c01c0c0d4039119200c030780d00066071342c0407090789003002180307400000c50029660f400148251244d40c0c421000e001c11075103142c4c20214081d82c3c459000c3d81c0701d00314848050042c0d0014010b0b10700503002041e11f0140d40b07607000c0c1c0544100003d10b038114012030a010140c002e83e445660160203620414004a40c401c208000283c41050039542d81124010a56030321900141207074040500f00401411211940c003221104200391076010912000c180100711054024103e05440d410014000c15403100c80b00c1c01c035800c0303a80b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 613711564 1250 613710314 613710323
    0x30504030c06050a36170106090e0c0928020d0513240e0307050a0515040506130c091a01110d0e0409050703020d1104050f0c03340c 58
    0x161241011165406000b03803200018520071002c4010085001c00341c00c0013840d43d0b941711500da16424012180c0e40c1168400c881641c0b040c022200303110b1080c4076030301c0074200c40752050240d103520002541c0d0307442c855452144506114000b02c0c07440c180014002884400c0c000404401188501c4000001c0d0403a4010314851424040050700c40c00d040d0443d1004280d01c02003080302c0381e0300302801c511600c1c035148004d42d2580e900c00e26200c0e2008100068404603101c0c000511703200e5458a480c9041030481402c100700030355007805010014501062080c0e008401d01e81c1c5409244190030b0000401d40313a9845010410324002d5400c032455455400c09000b408281c864a61844004002540d109402c480d20350015405802c2c981c1d20386800d8000a140e58010002ca600c2c494403a0001400e01000020880b000071034a803440215042501543c5d91040303004040c0c40c2e052621700007170481440018020016190101550b0304041c0385030104581c0103485005c401000340e560b0401400116204a0546 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 613712814 1250 613711564 613711583
    0xf1203011d0112060b01020f01020c0a06180807140c06070b0411090702030426010c170901021201050603090a1e020112020a0e01051b0a0f0b070206061e03070803030403050403 77
    0x710100384090140d4126002e040c4102010042e81d03c1d08802420410091390443c00b66a007c400d03084000d0000d8025002c3c0c60000d001c0800381850a803089551031b5200002d2800441003010214159a0071750b000d2581220701c3d0620090302880060815414079111684603401042c4d85c0184800c0c0c414041c030441c429400d003804140c0305010412604811629000142d10401080c401d10010003080006411030350038841c1900c04540303481c0e0945c0c01883c08040040e0818041100403101d16072500e401c40d029038021468504101040303808490305000c0d0328042c402c00030100382e4030b00c02009403042068001c240c0c420105401d41c240ca000d003175501001d03030000700201070403403141d0141d200b1184102c28548602032094204e000646007500240c07108103042440c50140c400da41818010070700c01e50301c034079140c60b203405051610417403802c0301500314400c40d40050100619925503060310001e030034030308281802807a0440002842c0c00e4868000413500c1c000403051008040c2c03c0009802038170b20400e64003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 613714064 1250 613712814 613712849
    0x2040e0f270606040e101407021e0703021507020d080307030b06040e04020910240f0f080f06060c0318040b030604030909110d0c0f080604180206030601020f120301 72
    0x41c0160351a100c1495407070b810500c00304038545040e90200ba040c42464080d51100c0c100701d0844006c0728120f49000c04004a0380042240c00d03981880041c601c1c0d40d89002400da03943c0c83d428041d41d82e103200c1c000240079501d10b0303500001c0250f10000341ca02980e4010070291503403007e4030307140d00c86410035680880440d0134482c1010481c6010700655081c1c0300390246811180d070780c90b020459030410140030f20030000d1310103d000ca041d400110b41d05c2c5a10300e108a004254040c103d00091030341250120070000c200211101010703a980c00710002d9000f0306010070240300d40e141c620000348035114854040d05584000502074001704020214859128401c45007001142c00790700505444000c21076004000404d081d4082c420b247e42c1c0d0b03029403018504540b6450800b50740d0024074045a110300111004202080980e4002ca60710082e240d501032800c0d54181300318120551500c941002c4c2c00b600a01c224800700000301c0345c0e4800c0024100040003001122a0482041c06ca220a503100780910811600207142c0ca = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 613715314 1250 613714064 613714111
    0xa031b05160e100806271006050f04060b090d060b03070e011e030c0b03070e0a080c0907020718020d091208010f05010903030e0607050a120207180603050d050d02040e0f 74
    0x7a011201140c0203060709036185046d0304000c038212449040c5a00643c0b2030005014010080100740d92a86000001c1c15400c00040000e102008220980315509068041c800540344406542c03640c0000e64401a5117402885c040c405884181115a0148158903002075222014603101d0f0403210f50038003a2848200d07030803a000101c03e00703010150040c00800c508000081c4041700a5512828074a0400c0c542c2d11070100190413903201360b03c003904a03801420b0002840c6400c6128641051590008020880c6002d006000001c40800e19821140e40491900f82e0032615802010314294016040f200d4266554005040614203000b10b5a11b16508070700032403154000c0b40b4800c266a010303140c244500807840200081c6600c420421181e5000c3c1d00c06a00018031003032180c102c211095009058041d0618242050021126040002d41c50400340c0400100c1c8000c034801c0b028820500c0c16036569241c03154258040c2c0700c1c96004080d02c0c0c00d90b41c104102180d0421545002d803204100000c507400c1041d02 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 613716564 1250 613715314 613715341
    0x130603031b140a03031b2d050d02040b040f080c0d02040e0c04060803030a0c230f120106020a15051b090f04020d06050a0501050a020a031b05160e 64
    0x14007184040d800011080c007102180c100e26407240c4207412144140d450702c0d80c10000214421030100340c80748284c04000f8100900e06c0b8051000e4039000c10713505d41030301044095082c2c156041000c402024a0107040720300c120211460003001203015552243e031141802103542c824456000c007198812008903c0200c0032686121312003008040c9540c010140d001c010040070f8a50503036a10740b081107813220b169101c40c000c41d0010300d0894059522860b1108440f0300b91190200032030100050000d0941102c2440c030180039401da1030701000d075201e49216003010105d01c00c400c80400d41300010800000c60306d90019519402a101c0e00300d610011782414025000d8940a0314223014280e20100c2d400c841c1500358001d840784000003070540301800e28150100701240e00601314a4007207510b504003801181403000406001700400e10304689406e06141009490300c00004c002420400142c86001281c058114525a402d4208041c1c80d000d03400100450344d103420724881c00d100d4501c0e51300044c959040c00700 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 613717814 1250 613716564 613716569
    0x70501080717180f160b09010503012c0c0705010f2a090b0a0905090105010c050316170a0201020a030b0307061d06130e040c0506070804120c0b0f04051306 68
    0x1140c4041801c503469030300944080c01001c42248650700188a0f0085804102001302078100784003400085001e16043c5000b1034180d0400e5001c0d50081080031200e0360b11004480c11a0030000d083ca60b610701003101c0d07034181000b40d5604100c0c0300c00300090007003414800d401802c0b1036110360b000704100d5400c200e15200362180086c4c3c030b81080c054258a1b4501052368006060381c6007552410f0050b56880f0244501039410410070f0400003182d8040030700c44da00f000c100d0540500024203100e0501d200d596291940c9110b619000032640c44940a10300420052603001d8481d0301c9413107841d645440f081e82d8002d00175000b40d0101e0f40041d00740420803110f4200403c0c080252686503071800e5105900d03268206011405100c4580c10001c20003405451082c0e2200307010142c00b5041e00080d031810981020140801a0340011784510707000c12540c00001c003400202c50403180c50740b00e50011150310f420711100b2480c0c40ea204054901000500c40f40490140004100303541049400580c1c0464030022030040300c0050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 613719064 1250 613717814 613717817
    0xf0f030f030c09151b05030c010605030c090112031b0605010e0f0a050105060919121a07020111030f09190308090d02030304050709020f04091a012c04020f0d0501030506090705010807 80
    0xd210000b03054490040720424502c5e186030b01e92020f0307803075850307928603440302c8441c0d0340c540d541c1c41082c4000c0c0307014050f4104e411001c44850b81d40d0350505199810890344090002c083c481c0001c07040150095804905500d1170304040e04200d02d69484600ba20501070407517074140f840705804009103001c0e240e4844c4e07505990340a0000381c1402c1280c0180300c002c1c0034004008003100b400b03c1c00000c0c1e5490781184511494402c04c1e544103000c0000c01d040805440c094085000d59042002c80c0100703800c07180541f98014528480f4022944078200003031b08104455410018100a0508110905420400c0716010301c03e01012207042218641007241c4a00064034000c00030b42080e0b20810082410303801400756a003c680c3c4c01454a070b5104220401c641c80c5003070039415080c075808010303055a0021804444c040800c052003a0208502c001b500f403505045042034030440d4003003012603040c3d41301c40c10b07910040011300c010001561241041c81c7c1c2d07164103e850300403902c100c50380401c207548a602c007603000d078905 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 613720314 1250 613719064 613719089
    0x11030c06011e0306090c0e011a09060d110d090b0105030a0201080f09160611010b040c120507180e0103050f030703050706090f0204050109020c0d090f0e040f0f030f030c09 75
    0x200204000d550107002c21400928441080c08800304295100c2c00c01443c0c80368029119403864070611803544041640a01500c40446e445c00076242c004030100c40f92001e0481e13007aa1f880c030780c05a01c1d40082448240018a03080003181c01804100c1c25403020154a000d0084068240c0c0d841d030070540d4804680c80020300042070100854246407019039441d81240c031000580f075030401889100e41444034990722100005191814a10f0509403c0c4101c0ca0f5100003981d0034000d036210070801520100803002500011581c1d031000910301803045510900c9002c0090b09025402c0d46d807080600c80b0300742800199480d00800c4118809203034000102d6510580c1a140d09090409940320b8000420340310005032a526103010ba001e0045c1d5451084c907020700428040140c480760030208103031030180a602c0500030320020200502402d0003031000003040302d008420b660b41a54a910b45102400d12400009028802d01c040540805401c124a2441d00003256010000c0d1146000b08a480072403e10038080030044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 613721564 1250 613720314 613720319
    0x30b0307091b2f0a0b01060306030b0f2e0509010b0306090c070303020403150204171f0b010e030d050301051309080a05031302130c1202030f130516030c030311030c0601 74
    0x34840d83d18425100c00021003403925841101941c0000468405603035045030410300100440310708641d0240086140400c0a141586e482541400c00600303140d401c0301d03420000a000341e501c22064000c0d03214441b120b6041d0a82c20001014240440c09140d1241a0000c00421140118400d036840341d54020481500e50300c03100e131580381d01c5e407005105404140c1c0070040440800d40c001900d509c0320125980043c0c4e5241303404001e409050600c0555902908000c80c00c48543e0b8140c1c4040c0d240c602e03001d500003000f412040060341c40d031301414032841e0103000782e240c40b80d03005404c580a14121142640d02104600340412200f00b1207583c9480184070b160107000240d0583c1c440c0000d0b581c44400f00700c103900080800c0c0c0000d50000c458015a03d00c9641b2105940d400551115000c0380d99003128905604600300b0702d560880104000b8030408a000e19a08040c003031001c00c00c807211414400c00d518401d842d440341004441c00459000030b03808a600303e0700e1585101c0c0300008407400849039001401180c1d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 613722814 1250 613721564 613721567
    0x4080f06061e060d06120204050a0b03060a0c02011401170f062203030906240501030b0105070212070308040f0833060406170a061b020615040609020406030b0307091b 73
    0x4000030010380003c000d00a01c000802d103403061101a0603c490210220051031040000307480000380000c6c9c3c46814960301231015100082c5640d004525080c01003018051484100e00400240810b9031241c5949400003d280211502004111815105442140007403040ba6659810240c481c2158000c601045101d60010f2209106007c2d01c07900c1c02159040e600c0d1184019203840e00300801450124200f14108100d0140701107006090030f090502c10340005000280c400e000302034000e4021001c04601c00c5050005110403005140d00c03009030b81d2100e0311800a0407000c2d081d030156000601c1044a02116017600d10240500d055014644442c4414180281c40d001c402c040c000e1500681c9aa9012420000c0b800d461044e103240300c8010605800d445c104101a00d50f4511122150502114a143e0155000c2055940f05c070038600b0800f0f207420804040f07001011b9503844425401d00c0410013007000c992580242c6a440c1040301203800040c0c5440a00040f203124608484420241040881c5a10b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 613724064 1250 613722814 613722859
    0x30115030b060304060f0b040b0a050904080d051303030c140f090f04020a0c0b010b090f06211005030f060106050a0c060b030d180902070c061d0d050304080f0606 71
    0x8004928010440c8a041070210314560420b5404075119900d030707180340c01005040d200750f4045200896050040902d060003080004c40c1038013920f401800c49100260a2160a40442e81e06441c1c40784104414070b49620b05000d180f0000000702c00181c200308034503518520800540b4018060420140c0c40c240c1099258465a4403101c02143c0150028180040b150b4887c80601601c6040303440d0029200523900d081e51601c44142c0000c0c0580c0c900348009103060721217480c2c0340d110311416902c1a644580103510803800c500240080c90001e20207208100d40203071804c01c0303e005c6580640c2200c0302d481880801c107071950001d008401c00604103214500c002031081c0e0545944034020000040d00005040100b82010030000990703002c0f800c1c0b07251072480f107034040007500020000c4410440c00c0503015500e400700d00c40f8510801d400c01076054008922440c500d0380e499102c2d013004002000c002250315201c0d841e40c1041c41094124010015020814140810001c1c82024010910310540d032140920000c0c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 613725314 1250 613724064 613724099
    0x20a0e061f03140c030106110609070b160606032001020109150c090b0d050106110d050f0f0c0613150c091a0f0c010608071d0609040206091003020706200301 69
    0x30151500038208640d03200f207018901034101082142d580750304108000c0d0038602d000d40c8882903603000300100150111302080000c140c0b039901480c1561040f00360340b030780301210441001405182c600b40000003080304238a4a40f031110380102e2050b040404160042e800ca0351001d00261480c900404801980100ca5106883e000f4007414003246454460004a0307254020f40700b0f40b01095566001400219004500c1043e510304403001415003001108009119024640c1464200b603404190340c03915002c0d4105030350800049008840b114900304501000f06e020006040d940081496416180000704bc00b41d0062000d8503100c805c11b03645000d81d507045000340d081d0100c050180c144426001c8000040081c0300382e15032100003054141c10030541070f0030300110764050304100c024a505003150011400400364171441c01c80b0b0320b40c010755440c004a030f458850428ac143c1d02c1340001610940d140d415070702812081d03000c0c11003000142008100d0704c00224444051041104040c80104009203004e5a003808 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 613726564 1250 613725314 613725317
    0x61b020109091a03010e0a120509150c010506040501380d150e0601090e160908030c010f1808040302060c0106080109030e01020d1d06072904020a0e061f 67
    0x412581d1220380c2c100302d07402e20b1980d881003180e203c0b04030800e26003401080803009400016000905c1c0d180d4800ca05181b980106c6014131401103608081940d40e504022000c03000101001d9641104c414240d00900080350203d01c568503200c0080b48890160040175400c02001200c0707065418540c1240444010700c03104100002c50802400c140c10380c660080a551030440203803910760500b0729100701442e40005120504211800004012003903a03940083d8200c1e004d07511803051100070010494124081d40c02041203880001072401038900154001ca90410740c8000401c0380864101101d44c40e1000c5400107005400140070034005483e0072001071071103000c42c00000409960702c242840c01c0d506000300690111b409003002441c2c9580520000c0314000e49481e00c0b644403000c070b00031250030030320403400c05000c0d0001007a0a03003004401080c41820341462010001c054201c00103103c42c05404076001c90040b000722800243c3d00003e0071040d402550010496281e01e20f81440724103441306851039500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 613727814 1250 613726564 613726577
    0x60a090b09012013210203060f06010801060e1807020714012c06070b010f05040c02060403091815090203041a130b1e040605070e031f0905030c0f0a02031006061b0201 73
    0x50b80303902485c245c01c5485002c1c2d5100e907000c1800e004040c1404802043d0074080d00d06402000f01c80d80e0300c1051581590303003904102032031080110119000c0400301040b08100e080d1b400500c01141c0d0002240011a0517484070341d9604950300e4011150340c1201c0801c40c00c2c2800c088039400740c1c40d071381709401c000210015100c6401c00c0059241c81c42101000c2e84010031007144120103003c0d50505008403c10880a80003c010314100303607030010401c020a200b281c0700d001140701c9064869070f803600324800e4a43e0b000c080e000d000e900c8002c03000c020b50040d50300700e80440c000c04140c62070300300040a051040304c0740c0649200e0460306403114000300320300500c00d4405000010210382010015507000d4050b50058000003240c1c82c0c168000303001400d91940740c6109901220720007120b000b159003108405040d4141c0402e8040541c40c0c52491401501c0c80c140171402000d2003050700d2100040c11244440c000c4003140d0100c01714002160440c1e4007070141c1310010300316070a0311601d11032001c4242d00d424418174002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 613729064 1250 613727814 613727819
    0x9150e06121902091c02040b03010207061d0f06010611030412030e0a050603090d11030c0a050d030c030c09050d141204090501080304050d0311010e060a090b09012013 73
    0x340c025404080000311021240090004041d400d070030025803002d07020402c5181c40d101100061078020b0316141d4800d46100340146000710f49850700f041c0541c0d100900295218142d514286020300894208050000180b04000c0b02460740001c281c5d410ba041a005416580d00780b82007191604204d521144480c4010440001c115403240b40036407115019545200c1c80c0c030035610802030311911940c0010310912083c024043c6003170001c039034110f0744245802c0901140a510050030b0840c0941c2c0d01d806000d01881c120f0034144040410110380040890b54100041100410258207d0303882e03040320000108480c100b0310480c10403540c06816a030180c1240c2007408004c3c1e24003880c201c161460f2021903e008203041100405502a0714003400c4510f02442c00d050801020030b01c981c0020801070b0410020582609040d5800e40c000065071282000f0741c4c880d4908170b10301002074480c040c0b0841d404200b2100207589440306100301001000d00b60003c202e03086917104201d825800101880c050200c129400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 613730314 1250 613729064 613729069
    0x70c0c0503120c100c053004061e020c06040b092113140f01050906040e0735040201120605030313210f060f14100503010501120309150e 60
    0x240303400d94082000480e50b0f06642401582481d411000030a1042e0604c2ca0140f0722a03003103029a01d03101819500401c403022000e110142010150014034001c4100505010500100ba0403c000c20382d82c1241380c442c070035448491003080f842005040455070304058007140c00034101003c8150804056011641c5401c00300400d041d12110071118030803c050002508522490100341c840e00419880000c0480103070700310007085e00406c140340d889041000c0012404102d554070b00a44024145150000065140a0703001808c234a480c80d414030303200c041c3c2d90b10302c5829800b400246865003000316030301781c810740f11640191000417448000516080d00d03481d011802d40c400f0000f609089400d242c000d0f0402d841c2c100f01000320100ca03001a403010100c851502c002c05e905101c56520564030030000a516640c02500c0002131900307104130380da40e51002052180101035103800700182c0701c04400030401ca0b42e07601c1d0111034600780220002c010030381100c410402c00f0502d201c0781145107040d0611401000c01c5800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 613731564 1250 613730314 613730323
    0x15090f061903050103150614060702030109050706020d1205091b0102190b0103060c03020906160c0b160209010501110d0806040b101706010e310e0106050301180b070c0c0503 76
    0xd0741002030382d5040100f0501903842140000c3c0c40c890403040010900303102c100c03107914a01c0b40060b0f01480e0000f82c142e0454400354408002940c0280584030407544810000303407154240041080010440403048205401c42d104081c0100d0305070000b03040b1a6482c0740f04014401d81180c040f4158001c00180c41c010740c514140018006110352000009517041d8604082151010040385040500c14070409005072a0f5004449803100320003038050713420013985131041109105070050352042c6070201f8005400541e00e00400c030128400c5030130781082e80c1c030764004441c60343c0b500b10221800e500c000302d250b04590055000c160005400380004c2500d40551020401c1101d401200000081580b5140c4400c10200f0b81c10300d40265091030030803280f0ba44000010542280451030b046052051101a07850442500001c41800b4000c00f09021440c030100e0068024001881114013035401e00e079135944502e59580c2c02e2012568405802c1e040d513124850102c82c52084400b048490740500320010800f541c0402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 613732814 1250 613731564 613731607
    0x1801210b1503010e03090306012d0909060e0a0c0530030912010b060306041d010504081b060f0408030601021e030901030c0e0108011a0d0e010903030b15090f06 70
    0x100180071a441402414211540e0000012a50b0005c1c004a0485d95000c5011070460320803811000203241c0d001d1307071400700d402e400d00304071151080c0190000d03444404d90405007901d8025581005190202002143c4446c1e0400b03004184d01071020703061005240c8101c60704c2803400c0c1c40818003100321440f400008224290b500c103d0f0107034004102c0304801e01e000d60703c501401d0781d140020f06c118000e60002c1900741c007024019510843d06d88107070790342403811013016401020248000b03100504003814850f003d50302000d807603010240309000d260b800400004115008441c0103826100c07030b0fa1183c481c42410b40000d04070783d045005030446100c2c0c03c0010600711044511180140d03640700302000026040317030030940340d1205104c0e80d104502e1141c0c0e005543c0710704407138030348105141562304004088910312888d0b00502c4000c0c5040070140d440c2c5e40550204030464800d4a0030000d024102c0c00f042400d001207030740c3e841c010300100308030005400c0115180000b1003001d0704180c02d00d600882e02c49660403000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 613734064 1250 613732814 613732831
    0x203180f0a060b0307060e0d020409060c1e0f021209030f0d2705130504020f130e0c06040503030421230715021905030706020406110105061801210b 65
    0x3501c00c20901005104810615000720002c08146145c05c41c0035207003841c01002140b0811000c1d00c44070a5440d140c1003850303216030001003045034801314a17003e41081c0032104c6035001e10203202d50701c00b1818014880c80800041540041030344030000320120740b2030b600220300305070940034405440d001c209040069610300c03a4507445101c3c0d039109001c009111a9609660b2070b41c120700d4014108032580300c2c107107159031040b00b0100124050342c40c0e0001c2000c503284503030416000b94101d207030206800c00c03a81c03000150301040030980c0c10070131900c0100452401070b8041e0541c03542040000304134100841d2101c2a514100100e02e01c030510842d115080750034240c0c50320a03c0c041d100c0c0c2040d0004203041c48110081c0c8481c0c41c0c00000050410f000030341d108940410420050040294101885010800e80e140560300c85070955884d521283c000788803400c803c09414440d820034012842ca80f500344c190821690881c00040c1c116807074200d0402012005502103030075442030540350004601d415160a1081200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 613735314 1250 613734064 613734073
    0xd080f04030501020c0d1b12030905010e0f0c091003020a0e0a110f0a030c080c0414010908030a020115080616210f0e0c0411070308310b010b0703020705040203180f 72
    0x40d0007411000b02c03190b49542d81c070090b408040006450490309016034103185000100181c10b862f10318010400340c220f6401307602c00d50b00314550311140002d6021174039009403044040d0340c490ba0084602410301d804025409110344400740010200c2e0807005601091102010400031454000c1d0403440d07100206d112410000010030020743e94040c01404c0282046141001c5c0070b103460110200240114041c2403440e800824039072070a41c0c480c41a235800741001c4010350f50703280c840c00c00c0a4001c0140780d800a850905090f0001003c0101049582c480d01c48000c0011024dc100b01e002c94042c504078045e1030360b080102d60300d980ca9030b02c944502c8a140b03107e0071000030135801034400a403911300701c255868403450509e104914810b0b6840c0585010503030505103243c203500c80d0b40c03500c010060210300310002c03071140f00d824001040050a40c44405030140b06078071002d0740c9481950000e40b16844000c0e0159004100c1000716040c25070095600540361030303442c140c4481c01c00c0500c0c10060320009202c0c40d640b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 613736564 1250 613735314 613735333
    0x305040e24120f010203010e0105090c16020120060424020c1b0409140604061d0309090c0c1510050a0e04030807090306020705031b07050d080f04030501020c 69
    0x20305140103821522441d140c0ea46074044400c0c221854200d1014a401030041800d452050b040410108481d511400300039522584c4900b1003140c9a60244a090710420300c0d540850000003100d400c840b600c025500241940d018076030010358a25400484a281c058074191400b1205082408590b01a071b00c2140d40d2000c0c2591202c40031450902000e0f40340b0080d2041040c150302400008031682d1010707040c4c00460b522001c1400040042074a4030000e0000018841da200d0070100100707003d4800c2d8812070042006861010212144504115100030651f104100b10407451611082a962001d0280c0669141c58141206581400410703840d21148401c103400b4803581d4003011141e031029204c251441c5002c0752412410342c444c5c0030045e001030203005128010446035449030301d125015541000003590b8503002440c040381d03240e0200a45c20300d0741443d5103020081d04004030724841151001030031340c1a81c080540340d8404030380c400740707405440c027004000020015100780003502443c41c100d400343c0184d25 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 613737814 1250 613736564 613736579
    0x503030a06050a080705041d1903020f03090603010b2d070b060909031210092904090507360501060809150705030901091b0f090e190503040909030504 66
    0x141d4079084507100300c2d14404140030541e0700003a1142112030403100130401e6090784110000724110608a604070b80901d80743c10b50300100008141d42c600e072096003202d002c00311880e11280c403070103080c42c0207911620402c010040307950503201030096000101019000c40700381039041150f60980201800c10000c002c0381482c140085035480355442441075418549034070302260740680b20310030841c6150302c109100300482c407103021500c0444007401545004001580002c400001480c080c0d006210369140040c4100310242014010121482d510900600e6564140400e43d144188520100200c801c2035400c0300a2700d9682d42c0c002e08000707428420008595040103c0246100070040540701c82e1341c4058a80100c884295150310350001c9946401600c81c1c441b680124007600b02c080c4060300202d00c0051110004002d5001c00c1c0454420580317429040790b81e080000309591540348161000c1d0402c0d11002000d602402c51611450b110318156840c007900d5183c1041140d00e402c00607800240c001c00c0902000d03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 613739064 1250 613737814 613737821
    0x1a03060a0f060509040b162105010314011a090903091804050d1b290a06050301150b03010312050403020d050c04050f1302130225051c0c030305041e0503030a 69
    0x1000e05030b500402e249080d44440a03207010203400030078080d492078160280c41d440307080130000300c86590300c407068588d9404110340040e11080c007064a010029101c00c0945040500c030302190040e4415009010344440300404c00c15030b20007401c00701c6a0208001071100c0d60b071400c40d28214020300c0c4121500d10300f440e080440c644040c8034031680510582c546400c2c3c191a91801401900303500c034064175281e16201d940b21020b0200960b080d02074501c5c00060064415642d044901038a07000d4000b0404c01c031180050341d108000340d00c41d1811b0480e0400061000c50000103441541c1810760528030300d030503a40e41c0820300c0e80303e884400b41c496030011100c2c00c039586050701a450308401c80c00e080302103a042c90344801d10044e0240301c0082c40344482a11140448906030150756041d10711414844110504000911078130342d4111085031306015040c501a880b285505000310300c40941d549502551850b0343d4160001d010280056030b0450102c9070f01003141e130806801c51080c611503805035840c1d0a00000399030a5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 613740314 1250 613739064 613739069
    0x12190507030c050d03050301150903080f0712180902030901090516060807090e07050705010e06090c03071a0f07030309021522050603060d06060e130302060901020a020307061a03060a0f06 82
    0x40c003c13007a201010035800410703681520004c04000c50101143c3d40301740d542e000030b540003c0150001041410840703016001038025180a007105c205503064000c0112000e189080c03400103c0301c9000f03030030301c0300403101d502951b8801038040c0009030f001e003030352101c0e4981164071280e24402101500144407940d400303401c2c0d5420000300d003010101507061072181070140310b000300b1803810030901245003000d2003025001041d404082c1400e6883d41e081c010704098544a080c0c0400d07000388510107000910b84042d43c01e888049403940403413070030011450251082030780401c4040d4105600c0380d080d800941d90300003880300303482c0b0000561680c034800c100ca03003c480c2c0c0c041058140c02d022071810810058460200b01c0c0c5c0c0c00386007110400e501c7c0005217015402010a82c120581e06d6104008100c0e0949404200c0c06405000790211501176030344000050a074890125444016042803000c1000a1090740050156100c0306070f4100b001c07991100480d00e03040c070880380074801c65182c040d0749030711000d5445100003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 613741564 1250 613740314 613740319
    0x1090c090e1e0d0f1b0b011a12012d060e0901050301020a0e040f0603080f0301060212070f02090421080115020a0b0f06060f0a2a1112190507030c05 65
    0x30b001d00c070320041c1d0761120340241000e424000c280d455440b5807485180aa12014440c100852840145d0f041c498003044090041c041da6074000150160600d0148041e01d210320702066038041581e081c40301000304080d030340d0928140282e04100c1c80c00d10700d04800c80303071010345025540c0010000307904040001d000e1040e070000f030280e4410400e09080c2c50340010412400b0741d040d500031403452024916800240a1a4005030104001040b0b12805481e40802035041361b0150b0f080310303029000710888071880e03c642c2000a048150000d6000c0050038640301c090762207402101c0059542c01145201ca0ba00368403c102c010005480710700600401e40c3d103000c00d880b06403041c8000d000e070611030342d02c00f030002401a02c07190f1191403590003c1d07003503501c0c4c030f084030301101c680c050340b03525000d0064000d40701c4024400c00c0c079207011301c000040000c00f5000d045104d03800d40003c5040080e403985424801001d401c11114031160140b11080c0400550020381c1361005071044000b0480c036403450803c56081c0c03509810992 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 613742814 1250 613741564 613741603
    0x18010e060c030a0c08331e040f0e0607031121071e1b0f06020f1806031003140703060507090504050a0204050916030204080d03091103060f071101090c090e 68
    0x80035442150803c11b0310340e034645014000c01d03250f03842e02c109069000150740140300e103c1440b9122805581040b4100054806102001c40c82c800801a100d91101e01100e5621120018050502c00d4112280540e00900300350310304095040380c9001c0c081c0b480d03144903051303918800b030020041c0e110114900f402c6008804115424603080c005119400c0c240703117510307961404186c000c00c0c0000030108040380c9074088001c560b14210f42070700d0300068101c16401450024415410f1105050201c02c9034400c118035031180c80e030a820741e0b60341d0708411030141000c01d091007600720100004034541306540c040c0190392128042140340c00d0800040e80d100400705d60000b401800204a0380d116030b008950041c103400340d003d82d25110007000314001e01943d0301c000c001c0c1c0719003c0710f80800e0340c0691140000a02809132041140c031040c0c141940c0d03403000d80d600c03058551310750b00140b4aa8031824492921008250000c2200d08564451250402003900302e225903513598141e0a0400034100940000401c038070b0303c1740 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 613744064 1250 613742814 613742821
    0xa02070b07142d030115091203020c0402211503010f061406090d0c060f09060206100506090a030b090d200709050403120c02010b1e060318010e060c030a0c08 69
    0xc44440c0140b80c901c001c0328825985024200e5240424240c6083c0d18240951312582d440706402c41d02d4040800502c081031950300701280c58110802650041f0b40c054008040d200c2e14102030100960113506020f440f1a8803545607a80140c01100d90360103003540c070a400d4000809501014211440c501900c1c85032454004c0400110000320502c2c503082c44111000d82c2c85e40403070b17000300e01080003081d0014105010004085412900032642004906032640c6240c04503483e40d005907590001502c3d03034100390840304000c01c00da00d020350060044039400351100030440c2d640c2d9965105c4103801d0b113401942d600301d46150300c0b800b40d200740c0400307a041d4090140d00e103940c13800e00219100c42c0a401044521a00e4200060502d4055101131a00c000501d4041141c1c0e510040b00900819042a4243c45051951701303000c000036100d414241f5214000300381c0c615544030402850a1541c0e00b071075203d142e5403503c0000141540510050b845203445400065403494144c60600442d00b1140e101c00900c101c10007407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 613745314 1250 613744064 613744097
    0x21609090f0b06030102130e1b071109070207230f030303070906122703090f052803081b070f140409051501060507060b030c0d081608030a02070b07 65
    0x140007596003001c1c20034110307120781d40405d0282c442c01b000314158012050000801109a68a1500c00c501100704502580d4540a102e842449454009031499100c0841c1c140c05141080d081a0002400e00445030f4469890300d0480510342020401008c2a512481e4200c1a05145100301d0601908901462551506840140c0001854083d9404000001c2c00c98850702000703900640038880040141c03000039100034990341440400103c01c80009998650000780c00000c8191501614030040410210f507410529041a0751640d500d00210340e0a0b9120000c0802c1e5210024010703904078415140010320200001c6280c08450b034407031007056484d960104281d2011101c6e0407042d000813500868441500c1c1011850054032403510880c1c00080c00000450725000f00083c0046d130700c0b80200f8403807a068502011b8a528020607442d070402c0070104811b0018003144001c3c9421300c43c02c400701c4083c450701d4550070f4180e0012070f0369810f06540015160240400c0441a55001240f0300d00f402040014410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 613746564 1250 613745314 613745333
    0x17010b030a12080a0b0901030825051902010201090605131e030f030b0d020a180f0501030209160210020c2419050a090213061502150106200d02160909 66
    0x70710b010040320b640850045080e94001900000000b1300d002c200e546c5071305010440340d000150811318545020120703030018056400c0c6444050f04034018250391718206041b03110014500700c0881c11556103400110000d0094829240103040e08101018244420b1419a49003075642c40302c2d4803082c001002038000260b106003403c1494445140104042c3d010001040800908078802540441103c0022941c0000841400030140c01e03564188660b80c0c0c1c00130404100c2c0c03000e000c080c0d0407076855400601325110316000710030000c07000c1c412620340746c03080382807401242c1003614481120380219250068000c07202c1d14403000c4003840c03400c2500c2070405441060b0440140310105018075212800a116117600303900c030545544c1c015040c26511400d10150500605490040d0746800b6861052410304610004054000c04940030706800d00c2d034200002030300c1176000f003070115007050420201001e00501c10301021000e580d81e50000e0040320600301c3c440c10540800d800c661081c91400317286401103481881d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 613747814 1250 613746564 613746593
    0xa0f060507020607020f0619020706051905150603161b0807030207090e03160501061511280b1b28031808070c0e1e06010203090a050405060a0503010617010b030a 71
    0x1e000b00100007008d2148064018001c01514943c900070801844c142c0f0b449480300041c0b03c86004101c2950303079030321610a0a45c0e803280d0039003010040c00020311482c040412510340e8a15420040102c4525843e1030b2120151030303c00302c51a07403001c2408410140c0401c06079010f0320300f402c000c1c80880403050315aa500e005207026910f1410f8802c0440d400c1c03107421b521840142c1714007801440c030300d0020707040a4450035031040800800c2c1b00341c12001c0551071032980d051070010520004a020a01180c5800c5642c03c0054410700031040100c4004070b441141c030b001844004041003907110000c20000405005694542417081814101795481c0442500e034185965181c1c2c1c020700c040d846807011b0500340341980261304900d03805d940c020180304188070240c000b0300c080d1070004560f03c22583c4a6004a0300ea000d120403554002101e51000c0c4103e1415420140e481030001c0c0c03284910642c0d840010342541d0140d8004001e800751101107003454442805060307a1800150011f100d05403296985a181e07460b0301 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 613749064 1250 613747814 613747831
    0x100906060225242c0a050316050d0515012303070303050a1d030304030615120209040609060f0f061d100b09130e070e0f1501050a020a0f060507020607020f06 69
    0x600101807090280c00030304204c84403074510b03c6013400600507980e021010525070521503e07100b8400102403400144a16142503100414656a0724000500c0012100b000085030b45005000c2c4001c454060000308034000e1191800c480722002007103c183c0c0c90218179840150080c0c20002c1e0034070200f900842100c000c100c40386050040034640300c008130f094691001480394075020001d0300006000c640d40185d0024140d031140e8000345e545e40d910320304152a0b00034009400090f500c000601180b42d07076010f8400540580c2010926806041c414011641c164060a0b030a40e030312001806824945403184046008800404000e401c150b500845422182c1c400d00400e18000500200d243e115500d10580300007070b428051003024008a400e81d203d9809014040c230503400100040c2004400d030382590f0040e1411049590a0389034080110303401e80c0001682d400f9446600030701000294681006044540030703c00c00035240c28003d0000381072020203060542154000c082c420448400450910f4000c4602d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 613750314 1250 613749064 613749119
    0x50606070f1502070f0819090f061b020315010801051003080f090f09010b0406030b0108131203110d0e07060e03030a0c021f02010209150c0304050405100906060225 72
    0x14407001070103072113107410051049a5903c800800c02c007511018000e00544d1066811041001c0d14049070403509a10400b8090050034504110ba64020b0000341c030042c00c4051f4101000c0401c0d00400d1404058107003465004605000400c1501802c1c41283e400001c0300203030181d41e91035911140c03828080d070b8205440070710001601020607901d80910f803d004101501da41d4180da542e0301f01d01441c0d0450302c50440440c1c01d03c1e0000141e984181d00a0f0320400000762710810101481e01c0e00305103000001d039100f085c559168100403008803404041c00c0c0440c0030041c00324170100001581401c0134a81c0c3d1125081c0041190807025981d00031003a100e5081940c5051411030200c1d00000312840c0d00d505580604c4096459048001c5174103400a14407000c042c0c0e0140e2900281c80601002d6128814030b000e4160000d100a1107540340c203420450300b241c54a00d000300c000e0b0701c51071004116000c42e81314001590110042e115a0702d50405260303003400d06415911201440c28401900c0819240c41a2010064 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 613751564 1250 613750314 613750343
    0x6050102010606141b070b0318150a02180405010b0901260118020d050f0103030e0a051f02070803130e0f0402100e01020a140706120515090702070b0c0a06050606070f 73
    0x4d02804100a00705c40c00304865040386d407076460020075801600e0a2642c0300c44004a0403810400060010300032049800c04006a5612000c800003900540d00d40602c00c10035030410315090351103000b520702a0010010b41640d80c9081b10000d000060149030107842c0d032000100603141c2c1c3e04041111411070302d80c1cbe003c42e006108000d0110740280304041c03801e2080c40c90042400381002c0d40004a905880c42500c45500c0d200d0301104108200a06105882c1d210b95921380c140d15110120031025404800da0040306d50703103601c446916003560000703640420149082c2d10704008609c5141d8181350000c0c0704084082c040e007000d8002c58203002c1048030020600c090076107084043c4e44200b0041c00700c150402c2501501540c441c262036252000b6126203000208140700f00e840c075402d9807180e81e018141003075203440785d400c05500b4042404001040f400650042590020f05200008010440d035418078000d0034004c076491030058125a030280200740a61010300035a80082c80c0e402c1801c0d034103034006811368410304 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 613752814 1250 613751564 613751587
    0xa02060a1107062003120403030c0908070905040b0112050703030507020a0513050901050115021b010e031006050306160c030c1b030507090f090b13080409060e0403030605010201060614 81
    0x4250054400c051091000000c1e40c95030200724a481c4d80b01900c8889a0003101d81c140c0f5983e4050407a180d005881c00c1c07000b10300000c0c003a0748107801006060920907405c9aa88101c942440c42e070780d0200021607100c4007040100162111510301500c00d9010161655030b16446081d501c01142c00000d00348280050603e06659403071044074001c21005000551130302d0054000e002512050300d60f8011982040008540c3c50020b16134a584000283c0c0202800b50505c0313a1500702101c641440c40c10b21106c0e10b51007501c0d85040c003903107100244120000c1103561400e400d25250086c000c1080805800071200d0711281940076185041c02c030707050301d00300c0d55804071410080c18011124000c441059a031220020410401280903c01c9804024080000c500c000d0902e1043e01e090010060407810300b000018031030004a5002c80045001c1c074101408c198607281944200c0307a1580243c00c58241d030408010805506010b001c014040030710090100360700c3c2c14005000c00ca9585040d003845a00851a02c9400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 613754064 1250 613752814 613752827
    0x907031506050a20010e010c03020301060509041503080313030207050306010e0a0c030b03190203010b15070f030e030102130e0703110a110325031b020a1203020c10050301080f0601080a02060a 84
    0x82940301200028801045200d402491b8030304135803a441d424814a111640c0c041c0c42964100c0d81c150b1502454031620700e0401004081c0503200d04080303480724001002058402c00510700c200404090030018608034100a07140440d81d610052095118400602404201e00000c541000d181d11001c100401841c1059010b03000003800d10303030184030714603001040700e1740740d280700700d42500070b80007002042144410321048851681d0000c60120701041614000389000c01414030083c02407520766800c200d241d0000b400c0e40d011604a201416503d0307420304c5210559400c040c0c00c01c03510b090403c4503a1411810340402c4c010401c080d01071202c0240310120b00780d024000c407580c8610583c1400a1000f802413222280c10041d1420b07000123150b0000c0038100e8500350484480300d5001400303540201d2034074200300f80013001500203d08500410f24440016215040000c0000c0c01c0d03a00e0f000e8596042c16011447d02042281603403140d4840030041000d0000450802112034060b903a00c4e83e24a014181500c25 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 613755314 1250 613754064 613754087
    0x50f0306041d030406350916083d18080c06011422050a14091c0c02150c1c032004060e010804140f0c0907031506050a 52
    0x4a000b503618410309058040000d03c15540c1c15111800080d10707185004425604240307045400c03681c800c01d8030075030005540c1003c0e0b0183c00c10084482c40d02d602c1c3c0c7c4061543e400d90b8042c040f50341c03180d4640c1c1041c03856400d079000c1a015940c2d0070550010807001d5894403039030108290129a40c0c62214020700d039980d507150325205411400c1580e803180060000c66482e2802d11030f09a182003805048031443c5000a01087c401140c0c5443c20301ca55203007541e0200800c3c0140c607000030982e55001010050505002103481025502c001c2c102d070200311142c0350165142424104100840341241400607036031001c0001c01704440085031a25040d2440348145088480300300103a81c0d0201c01654580391b94141c0142880c050540caa1821043c00e0300251900f80c040c3d4080d440c0403600d4904001100e500c100300156016005104403512404d1046246091110003030001941340c0200c000c4013524100002c0d96904a4510304d02005400c401409203049000c1c140540c5040000004004040a01c41e00c0d61100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 613756564 1250 613755314 613755341
    0x3040b04051905030405031603020a0902090f0409030507050c010519030b060f03040507060f0c1221050a0f0501080d02032b1107061a0f0f1f11060901050106050f030604 74
    0x300d40c0b03864141036680c1e40261007843d01c02d00c03031560019028401c103520402102c1e400341418107598101100031019400441c80c50740c02400e42010000d03607680394000e00c1003450082d100c2e2680c6080c2401e002c0c0c10080800800c6040c44401c00075051940507141060110700e0b071500e00001c0b0300400b4000108144100314100031510400310a000070301c04041442e02c00c5031102c0e224040304089038002654850a01e11003c0c2510b5407015601210740d0299510322030600510140080781e4130011017640440384150380c0012003655400d950382e005a1a0f1180f603000d0070010000b48036541c3c5200c002583c3e4441e2503400c0b50342545216074501f142444030241c2c0101c8031441d60500180d01c002455041c190450b68040d6041820140e1200141802c0d81010703d040001171300c1a88014858024030072050741080361144c0103100f42d407810040d0990307070462480748205c540c0c0309080f10380780c00280d9140c000d000e01020903a0b4507107801000f1043e0080215810220500030790b5449645020000e0f0041245e14a1000d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 613757814 1250 613756564 613756603
    0x306050a0b0105041e031b081b031c1209052d0703110d060e0c1302030f06010f020a050105130c080303150d0c0801020d0506011b0b040f05070521060c090603040b0405 73
    0x201c82407c2590b09420b8035861001c603400c0305100700c1040700c0b04000f202010b406800c030b69100100e0315404164102041d02c103090001030301c0e00e1841d059044508003202a209500808e0802c0d24801021080d1821900180384107030a07a04511402c540300c400e540b00007412062040400c4101d40c4400c43c6950359550004000c02201d20810314040d29981d600034014494038868400c88181c0280d071096a00600400c682040d00e42d40c4c11006481d01420111004158440c000c0c0c0240058000d02846c0d125000c01030848483c0070103407401c880700c9a0660414040e80e08144104190000003400d03101f102d49049170002505540e44c1401c00400c038207a080011154000108540030700e065410040c02000c003032383c8000c09410102c803a20f4800c8003400300100302c08550300100d000b2400b00f03400485190b0141c0700f41c0c4e0120740d645000420002c2c00c0160400c064000c0c00f08645000418070919a00414001036580303801e54080000d2581d1100034801090113100c240800c05204007000b07010f100400c0300340d200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 613759064 1250 613757814 613757843
    0x90f06010e03070e101211102a1106040b030a09030c0b150f030c01120b0612090a0501152d030b070c2001021f09080703090306050a0b0105041e03 64
    0x1009134811074804103410786000001400d54071580b0480c000c030307800c41c0391380200d04065410050b803541c0c030100c10010400c14801040303c02a01c0d299103c503c101103503a030908044c251904946800c120003041e40310310810700041040c60740c0201200d0340301ca289107001503c14200d18003035502c20401000070b40051107410402417001c0420f401042594811180c9010041400080658402d250998103000a001411076140c88200350440810190f0040141c3c0c10801d1490f00b046444404544040a0368001064a27090040030300c9280b21123080904500203450404880c007440401c17030a4451a20105028002400c80e14854540080c45d4840c4284000e4285040003c005440d2080180e50005860078400c0403150300b00328651081506030041c01c020b030f100e940c50a001d02c00504658021513143c0e01003c000a141c2401004103c0c441e8642d40c0b612400c608180701240c0b0014001f030101403501480b507403640e030014151400c6072401c4950300c080c4600c820185a0094099100510283c01c81244 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 613760314 1250 613759064 613759079
    0xb0307050a020c190515090409061407020304050306041401020c10060906060201060503100513050d0c0308060306060f090c040e010f061b2604050306040c0503060c0405090f06010e0307 81
    0x604404441d42d00f1181c155081c042008414240040c20801c0040941c42c2000380307040450514018001040e03c890400707480002090540304156008c8904c199507071320000e2030340c03044c40100e40c20a44520007141054144008a641c585010303001400c3e18020034001601907809404580034056001e05030b481c480c81281801e40075202da8003c0b2070343c00d820203502207061841480381b1011a04000c0c02000130304103e0107040b008001c0a0204c055113040b040442c808101d00b00314070803658405569600d040100c5080050420384003801c00d501c40c0d00504144141c658400d40d90700ca10090880c0e00c088252900210040244a0369000c170003010340708000014858440c0500700c048074096114010030a101c8062950030f41840c5400030542640104007141c0030003c41c0400001402c20907110349020303280c5c00040e05d80b4508890440d0841c9030408c0c2404942014069580c201c01740128407818142801c0000b8421880213040c401c0c44c020300c50001d4143d0307105030f44401601501405803400c060f1142c01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 613761564 1250 613760314 613760317
    0x705061806040213021c06031214251a07090e06010206070e0a150e04050a0204051e060d09110f0a0612090f08040e010e070e0d0609050a020a0b07020909012c070b030705 74
    0x10307940189403c2703203180407500568440021444c2408800d1401201c0114002001807250508445903c01240040011500c1e1900341c4c4141d13004105c3c02715468046002022180780303420082c1d440d800b84007400f0310f070b907000204103411401e241400e00d4110001d20200d1004641c0d0380c0b080e0001094602401030f5550000403070120301c201600c01b480159a21038028041e80700d18480c1607000086480803179010f4002c0c083c40d1062410007403000d0310b0580c8a800c2034081c1c5880d01420ba44404501c43c020240785803406464007007135003d4440300092464040b024002c880c0f21103c40c4070803a190301140007005a51841d0302d5410340c4c001000c9480d103845840c15201200d0074040d40da424000c1e68040f4015074020030078030202020090200100090603030b0b8040240c400d0410454003445040c14203001a9141d08805001c8c00f822200b03d502c4103114010054440e00c003409191180e490138100e140c01405804440342810741c030560b503501d081c1000c0c001502c0d0030b105034059a80c04d0070210500010301d80c005e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 613762814 1250 613761564 613761569
    0xc06110406030c030b120d05030417030106050306180f0a0b03070909111201141311030f0c031009020d0b062704030f110a1203020f070501020705061806040213021c06 73
    0x3a130803c00d200c003150a2000320110b0790743d03281301d90b40315100e0040000d110300001c540c0310b07119071003c4075400300a81104149070820f800c400302150b00403040040e40c1c00e002400302096544244410071609007029a0001c0c50400b0346110155912140c481507240c0b4100000720013040c8010080180140c0c0c0d0614004649800300c20500c640403014801d03000d01c0341406240c01c1c801c0c1040160b0440d8454500c0318440440211041b9507da11000d0044215a810301c529084041c141000d070a20040c43c03010903041c01454511340442030b02c0c01a8042c003503241c410141e448954050403542898680700001243c0c3e0580d402c0c10120b4071030300e04110703044001c210071300e038015482900d40c8401c404103800c040d16a40c402c0000b150031a803043c20b18502207444400c51005a482d030f824014a002c6003c425082c40b6485000244c40c40e0f900091544208031040290f580e00050010145810b00303091406540c5800700904045d1242002c03c44400114000f0750403944c0205c0c000030200c000a001e400780c98050201031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 613764064 1250 613762814 613762817
    0x2090402071b2603040603020a090305011b020d2a0201090312050d0b0405130b040c0b0a020f06010506030c1c060b0d0c0909020f0406080912070339030c06110406030c 73
    0x20b03100c1c0c250702e5007443c0072400140340e48024500302810180c045000f0340000c01c618040015014000003c1361084c41840e814030616803005503920305120b4042c0c40d1211440c21b0000304155024280e64000c2000341107801402c4002450141d0b20803800100e139003d20310380000d0450060101070661858203c0d00805028910541c00c1c40259017001c04c20046480c100e460869403080420808001124605026440b0348588070001d41c168440c054500746401103045140568054408052842010000f0381e00514040301d100d40796260441013002e0600910307500d559194074600c100c40907101c0f190040c6001e0610b00403190340340e50b454400c20019040d0361210380f02048d083c41010600c8035550084030b8040000003844c900e410301c1e1110403211840003d180a41070b002d070700e05918556040000508801e07005c1d94640303c1c0d02906800c0680340c000c04002408024160a0031251030682e0342c00c030b107068185c050030142d020394018103040010702840c0a0002c842803002402090480d0035078050704050409 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 613765314 1250 613764064 613764089
    0x90e0303010f060e01051c060e2e06090e10091e050906040b060607240912020705090a1d1f0b0a0f150212160209131502090402071b 58
    0x7a5101074030106604e044c61400141c0800800000d03540e901000228002c0800340000c0031a618104500148010340390703ca0710544213420a2a1070111480b0a50b200b84105450138459141c844003a00c01c0c400b520510000210410028081c0c0c00b02003528401014078050a00c0002810201016400c1d12000101c2402d4600341c046800d03c0c02c0020410f10456000d58421110f4858404010740c0d604135000071208443c04201c00c440c44209111708104800c101d06001c115070070b161a042c6840040c00707482a086601805040000d991404101742d0440b050410029101d294424541c003642c40115038060740c1d12440300c844501001c016200c0f01c0e03014820004212240b40103081040c148098411510034691102c0c1c2400091000c000d406030b10495401181c40320040007440c3d81c400d4100300341d0034415202c1c0708441f6043d41403a81c001d551000c0036900c00c07141c11583c2e40e140001c141049880080480e804070301c3d50030a483c0c642c112845c0c6038103c8071800c0b07070360054500b607039401e5071a0041014051a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 613766564 1250 613765314 613765319
    0x8070f03061a032a06040e01050301050105010c030e2b0b0411031207080306010201060f030f05060601050703050d0903020304080a0605090f0c0a0320180402010e0a060e06090a090e0303010f 83
    0x1600380e0410032000c000f009400c0d4a00040c80880c18500c50b41010305810000c00c200030b41036580c075070040c0010607e41c004030342d5941c503001c101821110141e004030705210b401001440042d034494104980c04004441410f540f0001600039200c281b0791096402d60004880002c0d0305021250311654460703480307070040c000c0030b81310701c81851344400140041c40c40d602c2c400d0243e0710028084001139a4800c1041c0f00010302181c0d26101d004003600a42e005a03a9140c2c640c4090091010510482d907200c4000c0c20300704e02d000d2a07135800a02c01c0c8105001500000d5440043e04109803080c402c03a0000e01030343c02216202d00c0d00f814004024001510010424400c0000f04806401d0201d5140c005403402007002d0616172468030b6409458140c03000c0703908201c0d0040921a42e40e522503801c0742113004071007083c0406207424800034001440444e0464032800c0c800e0070400409a00c001e120f003030070308140d683e507858241900c0420882402030704005091414481030107005080080510b040300c03845a0360782c1082e41e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 613767814 1250 613766564 613766591
    0x506060406270509011404150507030b06160327140906031513080703051c0608030d09050f0303040f020a090c02030a0c08091906030b03011a041508070f0306 69
    0x82c1c4402800c50150303440510b050a01c900d55006651060705400040780c40105400c1c0041c0308007084078202c80c0440c3ca001d1545c3c0ca0b6480340720f0b041e44407946080401101d42864001021400f40d40c0c8000f05441500074035004052160b4140c5480b145011703941540c0851500120072030a142d401f4004221f58503640020035850303d464294059034020380a80200b19a44040b50903058000f0b0480500302c0a6640040011303d04c5402010258080d41e5000d40383c410703100d0000c580304202029030803402d08002040c405090048110b81840141b02c02c0056407201300e142a9042c80c40c1600e548006010200030801844030f00383e400c2c00311038800c8484800ea40c0d101c1190908a48444400c40c0040e4000d01c90115058042c03601d010ad0305004080c424100031240c400620301c0325082d60310407074500301020100512900b41c00303104503100c403c1b0001d1052004141415010300004000300e84038070384031005049c5030004441001c01806940f000d0703514054551034136240c0b64500d40f1085410790b00d0003600d1000b00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 613769064 1250 613767814 613767839
    0x10e061512040b060a0f06210b280b070b04020a0e090601030f0f08030412140403020d081b0f066909011b0203040b0304080d0204030506060406 63
    0x400141c0840482c1d19941c44065200c800100440d8022110900119503c4480410032009000c1541c405800202881d840c004590245000088443c03c0400c0700000f40c2d00ca5031088c0d464403c61160b5010b01c0c14100c1140080f0841d41d0085118a00014818040c040a02c11062007a402603400d10728442e9202400500c100086403800c2e4141c0195005000003402090610101c6005141c205204203e9494200e0f86510030f803000c8408a00b204040c901d1203401400c900855000c01c84654109843c42d0082038025000c024010640c41c0d00060202c05036000048021224124004844540000a08450340c40006442d030045410b803403a0903d0509800c48254152031951085054180394032102c5100102c1d0059000c0401c1c5000b07400300e9103115112030640007801c41000b00d0f4100c904243c211507003181c1008030b160710004920102181950780002c2101c048030742c030340410b43d0349580314100b4809078001c030b800c0ca14a4500001d00001400400500240644022582007040c6541e82c0b030a01e000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 613770314 1250 613769064 613769077
    0xc05011404082d0d0902030d05030618180703030801090510030c032003030a03060303090b3c0d1d0d090b09010207031704080d03050613110d05010e0615 67
    0x42c4a000c028503400315048075600780d400000c00300024142e20460219800c0ca402008002c42c0ca10780e2041d1a40075450100141440682641450341c0342d42050740206241c20b840c1c03412045106070310f00114084550050764a00911f40d22015101a2900c0e0320b0003c2801400380f1409400305c0c2090080b90746450766107000c01c04c9a5210405000561031940d4905001050751030090f0b00d07030580c1083c0305550310241f0040841e82c10300d41d40021164198507001d04103501903044008150404d10215190000c1e42152102214a02007070380c50702100c60110500030b8010700a42c82c20034030045540e0b0f81c2604260410015140f0601c02d44002003030600009540d861a40c4500000038280d0608105540190008004c61031041c030640b41416141d131508080c41d482c540041c0e020303030340010302048801c40c244500c190141c01840d0901c210b04018000803029000d00342c40c068095514600e429288030f440c001c41d265940c85100501042d039481e034500440e00ca08942d618000e8450405c440c4e1030210300f000300c1c1c0320b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 613771564 1250 613770314 613770323
    0x813140d0c140c0a062a0b010807080a05060406200d0204090c050a08150415120308070f09060807090e0a0501061b0209041704170f0c010f051210050a060c05011404 72
    0xd1364948482128a05c4c0f07141d600079010301441070f500e04141c01115402d11031902070010102194907000c8001c0c03501401da8005100c5170411142e2600040000c10420740141c1c2144010800740c0c1071510411800b0f01c010200c4441840002e00c6400075a03181e0041c00448200103410070250300981410341d4a841640009000038105200091090144a444c0c10310014007600002300f42d1071244030a0400c007226003000b8201c805401d110b804243c1d200d424550f0080d154600b25042c0070002c1c501510b00d240c1d6000c0d100074002c1c0440002d104500c00d0b60500002c00401b60300e20101e00700146c02c500100070a001d1400019102003d0080c40c4110f000b0180030b480d800707418070055507900c0c0c17a1003000c1203180c5482401003900b04000601801201c11101107155500080c03e05c4a003103406c1c851074400c8104010b410b000c0700c02810448650800e050310703801c181a184002c030700d50b2004100500c100c21604400da010206960119080782c3c091484501c151003000200300c0b010351511050002442110000c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 613772814 1250 613771564 613771579
    0x50d080c03190f1e0e01110c062802031f0515040b090f030a030504240c030806010903051e06010b0306030307080c2409061302010813140d0c140c 64
    0x9103040c095400402400f50488000403a08100c450502c40301803030180d00d92244e500c40c1c0118100140c28031407402d140212600203450b2507407003624142c403603000400ca0341c090107110046010041e1121384070f0550b00c1135100300f1503580c900f1840e20007100000a82c94801c42c03a582202207220f09245010345070346000c0107089030a10b40740424110090341302e4031403940c001400031200703d41c036102048900c4170b1a1080d2105a112402c1c60a05454908240b0005007000321004050182c06c0d0842050200c0c50340510382415a0360710180103940d441d82d145d000804912130b00140f228100900d604403925a9480004e65010b03907030b10808100c59000680d142641608100114400106140b0040c180360900100750b4403035586262105c560106002e46030f070030030001d500070049407010a000003030384131100345071000322001250002040c01c1e400506419104c2041003c0500b400a13602341c20006100800454021800910703000b0155040d02004640c41811510f101c00043c8010070603259113180a000360 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 613774064 1250 613772814 613772851
    0x11030d1d0102030c0a060e0d031a01080618010303050a0e0d021f020f01020d0c0e010807080601080612060a09020108011d06010302031009090c1701060b0f0322050d080c03 75
    0x1400c00c024403803a0681944070401019410540078809504600c4c000c0900140760390003003104909000020902c0c8041502e080500e004c81d0351184015021101d003881c0001442d039400000c00e0003440306d000384190784200c0b500000200741d4020010a0000266943c4440041e207100a1040d44045001d0003035004203c031404a643e0031072091160208420352046480741c2d15040300c42c5007241e100c600071403e002e40b03403022202003031b0700104600c2480e00f0038600421903240091340145510710242c122030400400101040e00c9988000200064007440426111142011207408000f0a07c0550403800300361103400019204400c003154000d8184007a00c1d2503070716510000110700a500052401c0c449405800d400301e55244a8864150060b20a003854001d160911381402014500f400c0d00a80a0b0306041040c010b0075100016120440c20450080c0d84039101c449152803061000c050018138200014910010300500060921803614151a006415100d0103034800c5e41e84012920f5075145192502d50 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 613775314 1250 613774064 613774097
    0x60e0105040c050d0b0f15120a1208042f0604080304050a08071206022203050d1101020f042102061210080c092202091303080c040f05090705040b031311030d 69
    0x7084e404628801c0303681e01c3c80108000900b6106803044000809c0c0c3c85965032100300030401000e0125516542089a460302d0280d8840c15000c0110240414081221280c0195010b030003a15030300f102d200a0925490705d071a086426541d801ca8411140f190a50400018043c0c00200d044800c0d1003448040c08500700003500d0b820044d600902011402c2c1c1030391008a0211100c2c50b2760400a10301c80d03005444451900304005140c01c661110081081c1d10420030b00341c0c80040c0c00c048908480800c4815442c0ea0044060a2621845602c01a4000d00e001901142a00031006043d02c141c0010b0300d01000350340c403952284c0e91000c29081d09a0040d00f02808605110307072a9042c0d10701441582030184c030079005130340421140320341510030340d9512009181100c200b58000c2509907015200c083d600d410305107803d8a035413104c0702a1058070b000f038100d000403501d06031003a0200e401030038241490641d40c1c1041d590781c44030031001802c19121035110045000d41841e0108405c003100c02c0035998a500344003504c40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 613776564 1250 613775314 613775341
    0x1302040f151107090903020f06090705011214010b072d0305160501110306011d0a030206070309120807060515240702030a0b060a0e0c04060516060e0105040c050d0b 72
    0x115040c080102d41d01510715500708044000703808161004078090f659460003920f810609070075211035130401d400304800b481c400100d08088410920f800c03590074901c00b1482c001014039403140301c804480d41001240c031328001030041190742e204540b00502d00780d144140301007139445401300107040e00c00d00d0303090400719224501528201c02e5444246508480558425084030340e0446c507103075800700120411103503681020240c50b90007100d56802d072100f503031940024690031807404020b00c03958000c00c0c03000c00d0601c20f0484101078820b440082c00329414034141210117400c40e41c01201c8142c14800000e0404101d000044e184000140c950b5100000310f01510604403c0c0d00c10b80141c2c0d90b01806440013507a420003030a40d040d4024030a60303049080443c21b01c0355001090f00300306080e035200c0c4c040c0700c0c41000501c200c41c125130711031420503102c294185089151341c5104802400403401e0098150b0f454034190f01c410b0040f445052005000c955a400f0303c141d500380380750040c2c90300d041c1030002204a0500c1c0c0313 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 613777814 1250 613776564 613776599
    0x91a04110f01140a0306030c050a1805100e0907030203010c0e0102060403120b04090c1d0c070f0c0f030b0f0105031b06071e05030a030501081603020f0111030a0e1302040f 75
    0x50020050324030b40742c07282c0f140c1c01c1490480c00094480c1000c00c2401164022100038001c140c403244032190030500c0c9090405445850024842c1d40c5200043c0700c000040b030344034042e1501c10500b05140c20002400c070381e94622070000b81d10a500c0c0c600c07800007490180a0f42c0c10740c000182c01400c0c1c3d66031151400d451008001502040880e251800f010607541c440c4900704c441c61184460055242c101030160b4400407603100154403481d0300d44141301c2d011a6000541e4010350b80841c1e0312500200c0d0707142441d44070b00c0941c4002000c01030045c0102c20030030100d0407184100c4182c113800b1003980c1d9800c1056a102940d4061071050404106010441e0400c80001c1064034000c00c41c0403d50401800880304c02d1070301c0742c820398190b000890100c120b10f506014490060506000a210908401d03c0c41351a180543c440284540f518100115450340034118043c106c2114005032901ca042c24480586410303020000e00c1c0c442c0c400301e10941c1d01c00c0c0451080d10181d89001c0400825030b030909058000400180 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 613779064 1250 613777814 613777817
    0xf02161d060d0b01060f110a0203031614070306230426040e130b0106080402060d09030c060f1a0105120c0f0d020409020d050f161409090406091a04110f01 68
    0x50b4140d00204031000c51044c002c1056035950901c04101080040c405410440b00308a2900a0040800980c0c0c0010503144c0e006801d00600b84a40f0035403030074003030318400001e14150a000b03401f000014001181d102a031424045140c12815654421071540001e5045500510484074841a80c0b00b40440d105040b0301c10140c1940a8603180c0c42e504c185e002d560048448911491082d4141c01c2089201d4805500510301c1e420050388905150703000a405024080b404903841e42d40301c24400502d03105140b0040d0840d0020010800305410340c41403c05046005100b00e07891418100d150702135407284084a004d548072682a00765a2031340030118416a01015080003040c0e0180100080d0b554184002c000a0002d0000140e903240d01d01c44520556200405c500220101c160070417080c4040e048213000079003228500032508200030924040c460040c2c9407143e400202076020071040041d55880341c1a154012852500c0d0360350b5002502c00340c1c401c100d5000b02181c80142021310030713041074000c0c00e902c840e05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 613780314 1250 613779064 613779079
    0x615090b101409060d06030b090106081501030206250f06110a05030a0509150903030f250f0219060509071509150203091005121005030c1905030703030f02161d06 71
    0xc00100051b180b082d0401c0e50010b04039003d00144076000d1041400810040024224441a40c7d120340440d450501c0083c0c060030300040c514016015407413040744010103003585440390340640e05043c5600200c3c03000880301c951803d1380c2202e507504460305170b8507803403a250b69561842e0b660f00c180314094400904100d126128500d60915a9010783c0f00701442150400001d41d2a850000e444001c4250302802058510a9040e1444408169400040e1405003242000d000c2c041c0c040c54101e10307006507261110929010700da403810030041280c0003103000b509014116450303584c444003061541c0c00f074581040b0100303400000400001c3c480c480300130349500450050340c3c184400b400100f03504544852405000030780000b650308403a41e4445e100c0f038000d030a80010252271070a00c1d0110390b84010340400700d8841c000102c0c034800c0c032004103a0010094039010b41941c0c44a5a81e143c0038140b0401c6543c494050300854440160f1071000c804c03c602110440841080c100000d10010040000040c09140d002043c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 613781564 1250 613780314 613780327
    0xe070503010203071805090105100f020c04050a09150b0a0e101d06010f082a190503011a0306030d0302070204021611030c0102030715050601020a0615090b10140906 72
    0x142071000c0d5220304c68646504044000e441001c204000c800d8101c81d100d02c1d40580184404c1d2200e82420304681600d0412840e40749104000768030b811200c0d4441030b4824117003400c20441d103c85420041505114900100741000800b9501c0191030809c14a99008003e500301042510709045000e82c011407440302ea50a450b449248200300310203071080701d0640701c1c50182031003034a50740200710000c3c442552400040c00c2c101800d40075440001c0300100d04401144509252800d240001140c420384007070001101103600b0000c02401c141c20910484058920001413441c00c92814000c80b40f041100070f001d80011005813400f076000750010101660032503401e0010281030485100c101c90018001d40704280c44601520401d85400f0075a48190304540081c88100000f82e20000801e507503402d21000440c2c1c5a882c0f200403498400e034200c01404c543e061644182d0402112000722096071402d00052000ca40304d0014094814914015603000401c201c0d0364034492101e16003d40b02d1180b005041602d40b06 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 613782814 1250 613781564 613781569
    0x9041112070305060a060c1a101706160c031707031107060e10090305190c050a030509040f06051807121e05060301180807081b0f0c060405130e0705 65
    0x4900716510004641e0780e400344400d41c030706954104014000c9162015042005640310381c01c01d82c1c0d40a03a0100707a80d100e40130030b07000300c1003080c0407010b840e03000c01003500210001e40c42641e5a406480802c0004110031a00c0300300351041000b10120b81d00740c1c544070808060320a03060510030f8001c260303008140c1e0b0781c00384000351500400149006805840041140d45140310418240882e00c003040b004140382585e0040080c1d01306c419181e0390008070700440c20240350318006458010400d0001022401103606810405421201030401e5840a07036041082c0079a04020304d0858100c0e024050f031001201440050f5000c682c440702e607004c602407505041d2020843c1c81c0703c060f0740400845103105c0c01c0d03106103202074648510519510010480c000c1c0911140242a00400307090000050000c04000503440240110383c800c40b007040701400310340b19051050350103007501e40220601080f800c2c06040c100402c0345c54800c060720107440f0024403004c03200140618040c02030007100c001c0309950181d9140010141d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 613784064 1250 613782814 613782847
    0x3020a0b1905090f100c0e0d0807080c30030a2408010b0118030b010e090c0a0f0501020c010f0807121b0201020a09120b0103031215080c1005040b090411 67
    0x10b49541c0000d00401c0a848140e90030310030517101c0b502e400c0d07281840c02400316912020b600907098003500c42d0326a203103035401c04044034420301e40d000d8910880002d20954502c2c00041180d9a01c00c2c104960068026000d03600f0720084800340801c000120910104001040c540d00c10380e40035614010310035100c0d507202c021032108401540168541e96441384003040c039580000c04031908020800d5a1141e06045503030b1030505071810300462114402450000311301d80d0040101c1c032004a03000300030301507081d9111803c404038800c5009a900600881c60b184049501031004184084426203070b1b180a80c0e52840c080310b0380d00c4510750705103106884105800c03100740401016000a90310342e0003d81d031240448400307811a04641e209601e1065003c018902040309842064103481d85072504034441040c65842601503e800c0502c0301130901c1780c0c00c0c00608c0075000685007e00103010740b0b161442017900c0f4001c0d280d6004520568000e0350341042600c0003494254400c00d00c00c900401410305202084000c50440b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 613785314 1250 613784064 613784071
    0x100e060702040b0d140f0115051011070e0c0310090b030604060b0109030c08071406040e0c0708070b071101050705070317040203160e070210050402030a02040f0e0102070b04020f030a03020a0b1905 86
    0x5d03504903184010b0340c01028000c52402c1340c025803803403501c54500f1010901014103413000b00100050000e003c1440d5100740b1600000703150044100f446130424522248440d0300a4601d1031000d0038201000603000b505010320b46445a005016221a1340c1e0b40c3c8600025040c04001e02d410003810075004800100100501800740800340d001380321540c1800005540c801d001c2104600c59001884100070030040c404101c0d5004100c0c44c0c140341c60311650301d4030300c2240c000d00c10300800c1c42c00c402040060840d400281c0580c040a040002e100c2d6480e141c0041e41d05d44901500980000c550303c40f034214020f40c01290540142c40a82105c0101030540d4620a0441c56500151101c0f001e15052012155042014602c140d13008101007143e030030280d000076550440c10800070300441c1c036018480c05111142c0d10603035102e21902e000359980d8089140042d0f90b968200c50481c8555a03035501e000c028180080c4090b1400d6158009100d0300d4001d40383c4400110004000c81d401c0e0320a000030b40c2c490400c0b400380f50300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 613786564 1250 613785314 613785353
    0x40b241e071101080408070314070804090506100503100b03090a140f0606030115260f010f0f020304051513020307030c0923070e060c1209100e060702040b0d 69
    0x21245124a480b403201865410110f0412510009000c0440c441c1004c540c2c020351b00d4240080c01c500c1c03280305401c0601a040000e0300c0d0220100f070005071200180c1000307102c0c040032a000c03004d12007040b100383d965000503200f9124018100340213001400621000359001801101180e01c980c80540e14000036020002011000d50401c0b09040c501c0041005000c1d00140101c00a00c02c2c1c07410500c46400c450b0841c0324400100e01e09080141028030b00f9444072490341800401c0d03803078030306296000501a0001100c0e60001602d46801280340c00054801c0d640a56407000142c2400705070346c400049282e8014102c1c010391456068904010ba9040121740011032051910103400b6141c07556403812945802da001240325012005800c142e40d2010480d5809003075800c00944101d541d00101e0010301880410301164402d04031040c0082101002800c0d0600007225524800768807100c0803074803109045100b030782010050000d0742c018503041e00001550340c1e01030a0500c1408058a034441d2001c1440340b40c84 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 613787814 1250 613786564 613786567
    0xd03090312050109200c060f06060904052a070c09020717130608070206040c0b160b1311030307050312191e0c030603050c090c0c030f09010806040b241e 67
    0x102e5500d100d100c98443c0c251700a182d18100f1034488a0300361580c05c000d2002e038516406000003421a83d0b400c0c140e8000c9d01340034000304a1450211580d411265198075102c4041028010211203054a001242c503040d40c080a0109030f03500d02a150000303908010001c59541000f00080218801802e02411105c1403640f0803041c11480c180004c1c0078460094448411500020100700101e462820014203c07400719191135030314660000180307000c140c81c400017080705000b141486043c01c01c0740c0c0324103d0240500e202902c040d00260401d40e0700d210302c1708000c007160010b0044558944648030201c0d800819080218400c084019000c021640c800e1030b5100c0340300b04a082e40014170031510400b50610144d080410401c0d00b9901d44076a00e009904145129190540014070003c400c94182e5a051b10650201ca40760f100d82c1d03820702442c6d04034017446800545690000380d60343c50320b40a0f00c441c01c01c0142001c0312601000c1151280c1c0413001030a4a003050041201800166442d24131191040b115203425 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 613789064 1250 613787814 613787831
    0x1403030103020414090c10030e010c11100504030801090b0a0b03070c030e03030c100902181914060108040623190e01020a051c090b040c030b10080d03090312050109 72
    0xf01c11a03040c1c285a0307808413807a1040000d21040041e00024580003103c5628058008920072030260024101c1041c0c15400c00c0800100301da000840368513040d41c140240d500101d40030502070100d540403103010b000900d030040100094540b0b580f001090000140000b0a150740b10700e01000d40b0f03070040d035941e000120150105000d055004a0700468248114065850300c80300e08500b40d61505607180b10315003142c0c1c48501004540c0e61041807030032100210303480012840c0a070b141e4490030398052840180d082c100403404281c0048900e006100d100140c4419045031601d0b2501802090700d40982030b000d403500c0407059001014111420720480600d4042c21600c80342c1ca1440042e504e20121308203c1e0ba0041c00440da1290300700b0305035180c0142c40c008031400800020007400c00b9002c200c901074558610b4000f444103008140301440150b83c040c900c449400d44035111040c002c18034500c00c04010350401d042c401380c0d080c4203400582002d130003843c0031402e0b2604410641d044401c01c2c0e0246007090b40e0399049 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 613790314 1250 613789064 613789069
    0x6280504080a08091b010e010302090a060e19080a030f120e0f1204120222050903281418040509010207020a06020d1b140d0c0506130305070b0a09140303010302 70
    0x410752284c000c6014043e600e1388a43d80c648070b2031100c801103040c0701c42d82c9011401030b4466030503150000c00c01803c00030329695aa60241190102c594583d028041c122140018800c80c40c4590f02107440b0704001f0410742e40652411130350300007451142010000501d0080202803c5405a040780e0b400401c00340041840c0c001c0c046160050010100c4902c010511007003040c2c040e907115020215406840b904414815048002c60388140b0030404c0c1034091030132090000788032001004d8a581d146443c003140403030b54541c58090f28919140c0c403042c0060201a100307803071101840043c0407074030030540010300761001041c005010340f241240e110307295a501144480c1503143c581c075048000c0c00280060a80d8405803030380142003007403101046600040d012540c0c410081c03001850010540c0f0581580c07110608550f000f4000c0d41804815103480c82000701250b0444102101c42c107800e94161a00c61411180380d5803a02042d000400ca0b000c0a582e41012502080041c110701002c07039181d0014660325810341c0704 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 613791564 1250 613790314 613790327
    0x1a13050f060411090402032502010213050a0302100c080c0714090a05062103130e040b01090618051806070203190302030c090618060c070f080f06280504080a 69
    0x807491041d800c2000e5200300600f804202c640003042903501580e60b40c1c406194048041c2d46141c0030a4541004040145495065000d80148041d089076103c02540d00d0f000c0122a485600000c1d6012440081102c1c03082c3c00f480c20300c01140c0c428144903061007020000f107410700c802580003400100c080000400e0500d0480da100354400e4940d0400c0100d81800004034003004021088581c400310700072141041c00800700b06440d00000d0504c1400802038403540901c80000b0152130403110f140381c140002c20071600c14000c038020b88000982240c0b80c803480c0500b0901030200036288040000505c0c01c1e90102c02c0c4107024280c80341919400071039072040e841c45140101c034900600b2404040c07050082c040b48198038030850b80580006c841c0c0301d84030b0b1540658412004642d5070f03a0751b844170000501030322080010598204445101543c1008903986913902c1d61180c0e000301c482d160f039400030000030f00c1680408a0b2429030941d059030610321245451005030444030291010b0340d40034030105076460469030040c0d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 613792814 1250 613791564 613791571
    0x2030901120e0a080d06091503060c030603080a1d04050a0e0f060f011511100608010e1f11041809120e0d1713120201030b0d05060a1a13050f 62
    0x7410080c1c400c00c442c106484040d44200101400c1c3c00140c6500c1c0c0f4003642d0003030405808604002c000c03100015007000c01100711848111001410304d02c0c0d00b0303e142d000b8800d0b00122a0001d40035454071414080c2180c03858641200306103d0b6011501c0362954ad2281c2c850b0521400e00c210000407500da0b0440400e250804000140c2101e038448020403980c0792504064604641051418102d402c0301ca0070141c41900703800413034080e5446503108400205c0950380002040303d9451008001e05001036042c0d50301d4003c00344281481c011120711204981c0c4c0c1d2a80708801d0840d40c0b20003035040c00d44508105104003200454128019140e071054010300c40041c3c0621011301ea9420310001281111006c986442c407402005800f00703140601c0d141c00440c80400b29a204161203a500c00600e4641351158811248031030280d00092030050035001c3d0b818028003501e030290300310b0000e010b83d50724a160744001d003942540e1041c1c2c002e0f82c2c0540078034984038095222a000e64040b0081558909201603070790000000303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 613794064 1250 613792814 613792847
    0x3060604030611031f2d1707051201060819020d0b0703050901060b03070c02130e031308010e03090d111302190e010806060403021c0507030b160207050105121503030a02030901 77
    0x400080103d525085d508846000c4900075040042c2c13104203480842c0700003507101001049107c0d0003004249030102d144010303120120360f0080046080c2120a089881c94011300216900440e15100f841e503a508480e00c0c8a44010070803411111541d55242e6644000c0d078540c404251520300340100100280038042c098030300c000c003240c02c611b04110001c0c0460703a44a070190090a9144d0b060b5450480b5401c2004114110401c0301c0e500c90b0948044090b0001a20503c090f40d40303018218004280040210380ba40c040003081e00c00e50380d038940c65620103035421030595980080c54051004240519002400c29507200d1840d2058050f90440050203240e050000c50381041101410801d0533a120340540d000d59070103880140064510001401482d501420003030018464900001b0401288502d03161040640320191440383e035500c00280e903122814011103003c00c2081c4105201c180701100e6190b07210f0310410042500500400209095600c043c030302c040181c000054290095810861028001d80355 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 613795314 1250 613794064 613794121
    0x507082d1504030302130b0a0c050105130201020c1201020d0c0c060e060426071a040c0b031e190f0f0c143106090302010e03030a08010501050306060403061103 70
    0x105020455204801003000f0249540030400c40000304050251b200548900c046141d0740e2000c09901400d000340011089803d90b003400c00062503941440c115509642d4181c00030702e10303400c690042024800b0301c141e07030504641d0700f4012465210b4041c021041e0100f181e469800c001c1ca1181800720945036002d821095070b920810500000410b0422990701101c2c41305001c180e5021145401720140c442c00748092f095500b007140d190788a1540c081c0150145102e0210401015030342c62030040c0ca40400c0b20f880c10220901c0000d00c0550080140107580065a0945d01c03082c0005003e07220211440200c04024a6917078043e080d803006072512900e17072400410308165140c50140b03006041d403440b0303401a841440d00b408500001c0c101d21001e00c600240c02450250055544407031000700005d00511050b030008110020083c0f00e0305012040f26041c0000f6640c18005a0034000150307880d90014108903044002000000089a0184103419007081c00c0820107540e4200000311104042020818511482030b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 613796564 1250 613795314 613795333
    0x1150f020309031c0905150309060603120d0207020109180f110903030d091109090609060121030c140102122409070f0302040e04060b0316050d0308040507082d 70
    0x800240000c803004c1c1454404c4419140c0c044100d954121603804241c00ca05900041c03100c905103d0080c40c03140d046a401c83d4a16690302d402c041c0d40700e145203a04511250204040c520405898000b00342140c01070406620883d503a502100400300400c4a040d08650744884c09030300c0c0c0c030890103941a014203021a8a0800003040300003504c03407040c051004d88060303440303401c181046429032003031400e6100103000c9034540c50722400303003038035002c0884864026014440001c00d042c02c408240d96065103400c4503e44030f1038400e503410f0316012500ea400391444c00341c0d11b801842d0700c042400240042c1c00002407030f18081c00e00800e00b0b00b66442541090f641d9880046203814152109800350b940f040e1680b030130741c00b030307100d10302080d00240b10726045450413564400820045c003441d908400c4d003000b000e801f00c4080c1c84da50304245400c034100c1e000742030740710702da41c103004000c44d00c200c035140e800034028802d440e1a50f81e684283c602d4502e2010300ca95422822612450384034080c0270f907902d50a40030001a007034000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 613797814 1250 613796564 613796569
    0xc0201080609060a171204030f060c02071406030613020c0106140a06051213050d03020301031101081603091a0114034b1b0a0f050913081201150f020309 67
    0xf5076005d40d480c20b1241095005072080c0c108049a048010704031005da0b01c0f601c9091150503160104010350f1402d0901e003488282900c0010a14200c60044071020190760300e80342001503551000e85160307485240041d0b21006c0b00001d01c024010203074290000510320b031408064444002d020810b541c425040c1400802840c1d07080011107582c159412a041c0b46079a5103003183c1d214002660018000b803141c541c820010759003641c000d50680c0d01a509901d5292140030045440d00303030443d4103607042c19440c0100c182c2c40e0b00941003d01007a00c60034079003600e0700301d150b00660050001d920903d8481c0391020790032154101404045e1100e448070f00f42d00c2c00c0300f26101c102001e4030000322841030318075a0f421022181c0c26140c0007200341c0c40c41c030750150b40c0312018442d220311440c82c0d20080c561050b882c1e4240000e2000c0f01400100469101400707102940d9642510b60286800c022019a500c0030f04000c01c14030010840101c60107801c04a00000e52004441002040c2c1c0c0e050844801c251b47c010046100182e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 613799064 1250 613797814 613797829
    0xa080316030309020d120206040c05030f0c01051624141015050909160905010c050604060504020d0c030c0612020327030c030d050a0c14040905250c020108060906 71
    0x41e01800c012410b4011480810301103602804060a08000640c0d240400f590110782180240e018954001c41036403507104241d283c045203100040c1c41c0c0d00c20141c81c030383c0754025006071528a014400b0030340301009c0c5803900c0308140c00d4140203008041c041c02c0d0f2035050034054030640300b4200450105012601d4444841080d0081c2c50054240088410340041e5906d8415001c0318002c24002d4001d02d50703420305500c1c4052041c0c0000c07410f00407651401340403ca0794030a200041510790084024215525151640b0008107400380050780c210720168417003008108440d2040740214400c3ca40411000d240110040145031540000c0310b00d54010028014403401d1508072110150b4135183d41c4c6a02c181d4241c12914503c01c06030b240e401c5010114410000d0006075000078451001c031501400990050503040701c001c909140301d40b011b640d050009105a00b007a51000303600105886125403c05125040c08280111421035000003807540003ea03001c5580c03120496821140540340300700383e41001d40c00210320 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 613800314 1250 613799064 613799107
    0x1e01021b07060918020904021207020f030306130f231b03130b0a0f15180207030203040b130f2705040b13050c0d030503010305060903030603060712020c06070302090a0803 75
    0x844441003130321030360741183c0d55440b00030011980e0b240366950140d070308501200c2040145c0100811941d24100120807240300e108003c2052224200c40e16426006003544412482000e656001503603101e43c0302200d03000c1c0641050321480b013515107181c14887d040c0d442e40110a0088091007400130410b107a0441e00c0c060341c3c0c0034400f032006590711902c2600814501240c2e00c0442c0c00d10030203c0e800096140c101059407444500c0380c03c003c2000644405038403c03801c4c000d00683c4208002c20614507000040c2200760020140018226520b60428000703480f6900810350b030000341d4055140300410302040080b04040e0a50501480c6410349a8441d000300041c03c2c40e407085180590001007160074050f080e00080002d00803003c1200c1e030b050041131a002400304941c2e0303102c2c5101046030f14000000703407441000000e005081d165100d5008452100c008a00e00160640a02038a1794104040c0920341c8640070700c0d640144c8407201041002100210f076440541c0300c0c7c00070031510382030b9101511440340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 613801564 1250 613800314 613800329
    0x3050d11070c0f290301092a1e0c0302060106030b040221041a10051003020c1506030106060e010c300f09151e021e01021b070609 57
    0x6400c40424015506840380040003003011a0740b4901040040905001109403008201d200103040c52000c0343d0000304809030360507580342c40140300400c04a00190040402c00780743e11040c1403004000e80d0212100c41c504404100400c000c00c40042c0c412031701070309201c04007002d498006240146620080c0d103c0006028090415441d50329800a5448175012034a0884060807007958020401c40b0306c02d407040040d1800c5403001d0010408a0600c0c0205111038040c00512000c0f00b8114500810011803118207c00041455000d121203001081c00b400f80c0c600710f05110001030568074040c81018215a140d40011040c800074a0012042e039070300800c81801181d0000102e40d505200300c401f42c044019600d00c4801c1c151034554078031070865200401f2144200305441d02d258071915402003140c00814503566400082c1c0e07288aa10034030401d28160500091140140c88464100c000842c1403032103441c1c900e00c1c4982d000110313280104414110240d040000c80040d0081c0c40c1001001460b4207002d05c240c46 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 613802814 1250 613801564 613801571
    0x200313120c0f03030c050c0307030c050c010305191a090906090c0907050f07020d022d0409030f0e1201151e12030f02011118130515010f11070608090f0a03050d 70
    0x49059029504031070813203d141f4106c030703102c0c400c520b0010501c1c654901c0486d490f01501440c0c1c7d006502a001d994015005207511050001460104200800c0e0416000c804c2100303107450b03400d90b40c80700402d044c002c800d048040c1c00300d46490b090360351900d10800b03900b9015503d92810485250351203020380c3c2450003100c900b00d0792b440b024000107070059406400658884000081e018410303070004a100f039140c100c850b011000344107000800040f26110040500800c030314402500c200361290940b01000d4000419680c3d04d07601d02004035084441040511700310002c06441405080aa030709801e000d2441248204c42d920b0070014003058a850074140142070003c03042040604d98003e422200c001c2500d801b000f074448140c0e1010307420074002c80b111140640040c440480c014242800746038032030082c0751a01c040980201004480402c2030f0701b074240420603011002031800c60240926001483c1c01d0391914441d050070b0039114200001408112000d501c04088080081c1d0040d0a90ba004c024450000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 613804064 1250 613802814 613802831
    0x20a15061a09011b2f040204080102090a0602010903080417070c09271728020607030605010521060604030c03080702180702060105060f0d020c010905060105060715200313120c0f0303 80
    0x80205d00380d400c03895a0b029001050225003100305601408041e00203c03030a00141da9100800d130308a44c4040c1000d00041c4540e0b0000e0081000d0412003142030f007400180e5442d245250700c0b40780f0010312940000d1400d0b611a50818086800150350002d0050100300c0594500c1681d9a842240109041c500c0d2035010041280d400054030102e1802171146609800050781e982103500945550b01204c4650100380b03000300110341544100241d411611800d8820802d41a48041400c42504000e07c0f543d0b11903020880400050700c41c070b4008006500c5444000e450b06140e104000c1c0440074900d0102d8401021030030408200d600040d03880c1110002d44406941e01c00c3d8003446a114400e015000000070700000b41038170845015404640f02c01e000340150717292a600c0383c0400419116620700a006840c0328072810b0401e0455500c145200155401e000311104c01c6000e0202e810380003100e100c14020000e007203130b0303080c8182c80c000762440010701d02d081400d1801542d11000c21007411030b0003504166a48410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 613805314 1250 613804064 613804133
    0x4060b03010e04050a1b06080c071101140c010911040b0f031b0613030b0a050a060609090e0f07060c0b1501121d07080f070b0307020a15061a09011b 65
    0x1211010350440c0300145845070300a0180386c0c01c4102e105850011300d020001801c0c618103501640c040c20340c001c480319810203884004403000088198500148070040000e020f65010920035041c503603116070090103c503c00b9101b08421036404210f010300403840401008426500450707044c520380b482051410313a170704001011401c540075510503890143c65a10010081c00009240f00b4030490120300c0602140d950110141c0544442d8410000418090081030045014640103101c0044643c2d00b200e031805564910140b4111a50f400300b0003190501c0e80c40c03414081d000024940c03004003c1134080c404852940000c0103429000703030061289039a2100030020315080104103005042034011240d14580f113415080e21050b190740c1d02c00041c4500d1000241c1c1d0581001664410040794000c2c00e107c140503100c0c0c41140e4404042c00080e40da9807c008a200d010700030054591044100c1d20546030b0401800240400035000502d81481c032083c170108001441e000c1c0489003400105d40c1c0d6a2803a00d42c07020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 613806564 1250 613805314 613805323
    0xa061209061503020405181f110d02042619050a02120c1206090c04021e030a0c030c0e0d23060f160f0804030e061c1a04060b03010e0405 60
    0x34000d200300d0800b601c0001010061204600362030085a04118030b84501c02e46074100d10100c0d000d603050303800036400704403181e110b000308407510109140701280102800130410360070b40c080f042c420255640072400344044944100814000000d04213a0400b441c1c148003010754550302c10340058401040c142d00c65040142c244402d1520725400340c080c00700442041b89403502d80b200d00d00014014040d4481c0342000040005400b4020031f21030300600840c10f07801c403d1001035484107080310b0b140c0c840b00d1070300309040d806ca90045100e245010b0000070440c070103400050549004913140010814048510780403952010200322206a005100d130a07040303141304c11401120b8051036106054040c403c2082010088001440d201d60312554418408c030440f06000d40d1540400e502240c00030310701300001800a40503042150803020024a0075050400e041007043d142d4182c20f002e40c0e0074540b601aa00720b003401000e0351500c0000b00329400d01803103052082c0000306001c144144035582d11100301160602c1010710 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 613807814 1250 613806564 613806581
    0x40b0402070c0e3d0302120a0203070b030601320706060512030c060c1e0705030c06010f0803180411030c04170303040c09091103030a02070608060406050a0612 70
    0x520640d21851503090a0440545a205240c00d0200e01e00c000b07040004101003040c4d1406030b01c84c070048842060060381da40f07800d558a12568010303802e28040056a40e005042c86490807000040502070b00758414075042040580c495200e290003031040c089260b03003118601d00c10781e4020f410a11811100c6807a44a000c001c4030980e414284c00051200901036660090b03025100151000982c03001119501e9640307108029202045411035004103541498080050940e02071101c103040003003441d00309011480d130085a08803003a50000650b031034446070600c8820700400d1080c0e00301c02c2103031070240e00544034441e0482108541c4151004010f10b59203c3d48416004e1032120810390300c074585219007004c0380d07000d40034000c0c5014002400b0110110000200d0f8802d40e4040c21040c5240d103400400405400003583c01c56400c0d180d28440406910b041000d001c6000c0a540101111840c0110103800040e026001901880c00c0a50034049622a00000d100b1500075182000300c0080740c8001c48000c09052 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 613809064 1250 613807814 613807819
    0xa08010512122709150d06020c100c080a05011a0f13060906170103031d030a170a030621110109080a08090f010c0c0b0a1101141f06170402040b 63
    0xb007442070b100c81500d0520f850148080c0408a82088140700b001041242107400c20310780602c1006030005401c080320103060103407041d5400350500040c2041641031005901e140c12b05140c0d901a440403495202c07400ba900000c0c440300c2080035505009200702c6140c40301c00c48244118000031015540e5031a00c0454000307400000c80d610503152266401400e40015104400c00100c7c2c415400d00c100010510050403a54540c650312504c0341c81c001d40002c0c2c113030601141035050141d104040041502c90081041400d5040c500581c0c4a980e940080d040714181e0f089044030200c4015801c0240f011186130204031034101c1d0b6695040b0101d80012609008541c0105100c1d0040c800440c040001c00f0340604a1048102c0341041611240c100440c0c10071840003020300500ca04c013004001d42e440c848020641d0881c185040c00b0803240c0c07035030940d0949a0300031010b030043d83c6400c20010507160070143d141c100060340e59440e0a052a0010007060b02c0c5003440402d01140c503200124003107540b10741c052040310801 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 613810314 1250 613809064 613809067
    0x7291605070219081e0a020d02010c0b04030305040c14280f092a170405071d0108060606030705030a0c1806080a0617070b18030f0a060b01050a0801051212 68
    0x2c0e03c2d1440803420452141e20310340d1280030f222a1400741c00400c40090a80024000e184111b51502000600082a501030341404003040c0c40002140c1d600d1207145c483d90103070310301182c01d0034240390401d84809690310025101004080c4000700340d0b5850440381103001d6a185514008070f2200c0740b0100e10030070780d21800b1059402000080d018149030444005100c0d448805020441f9401800c00010554588040021251450324802c0c0740180030081d0880d014004a41490352a0158280c00000b021003802c88a07043d40010040c19204102460380490141c0e8003500798103056101a25501001d4244240140c640300d50700c0d623051050340310b6000d01c031450291041d00365441c0d01c007610340740043d9910001c440c01c2c25004681c055117201d982404480c20002480001e03e072401c40c607955040310300c019841101c0c001120403241d070f0400030304221b4040b60014054075444c80c58400211015111954184201880350316407040c0c114004a044038030685400001c012080c00b61428440b1405100c03400000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 613811564 1250 613810314 613810339
    0x309090a02121f05010801031a090f0d02160819140f0a20010f120f0207020a08010203101e0e040807020a031b05060715090302100e03072916050702 65
    0x21801451460f07031000d04912412107448a0046401d460f0074000075240303030620044905941c03814002540d0008030041941d5000c2d201c459500c0c107284007900c142c80141d000c1d02218070313a42c41d41a44000245000d01c01041d00c8032110000841075840030401501c2690304409401e4030300c06c24044000380300592825030b60349001130b00d0324030303005a0003445d018510001c84260741c0c03840d4000e0102d02036800343c9071503101d270030395481040c9070280c8140c604804c100c40d0240450b90050300c400e200c007809000b4450015841e4504880d44081c2200564000c9465802e49050460607420403580c0105540c5a5048070f039841e03965040c060f21902ca5a14000d401c00480b0200100307001e0400440140c0411011a1015182d0703140704011041c0580d100150023644e40c0d4441038107055035540072003051413290050307c007044000a0b02d0412035110400a0381c160f08001078010810403407001112000c0c41d03c1500d00c8541000c560005c0c1d8a0701d004102e54001c06510503103409240c01903081d5034201d50b004115038550300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 613812814 1250 613811564 613811581
    0x602070819180b03040201140307170408070303050606130e1b070b090705030307380c0301080c06120601080402060409112a060f06040f050108010e0d110309090a0212 73
    0x10207800d41c11008001c0002c011078410700b40030440b4004d0303805a484104480f0380030707000901540050416414441000c1403412140d80201c90750384124003400c100d94603043c007401e0250a5401c01440244990010800c10001d000441e6911041d9104018011004c1d6035034800f030b52081600c1c02d103100e01d14a005c26881d040080c00d00d48988204200400d592509954400341540c0c5d020b07100c4020315a581c160082e042c500c4d1400b80c9003588400c1c00d2008807806171154542040002c0940f200c00c042c003000001800071034410000c40302984015103400e40b928100528020385030f403020f481141000340e01e901107425503030313407074180d50180021203010000c0441400042c8065031084009102d030401400844558042c1049880c180300c00803005005180d843d60300ca00d400c2100101010740c403943e00d403501043c0308010700ca80b03400f0f0218400000b82c00c0e20184609440c0c8000c440f901c0c000c101031943c10001400d004070a03904142c0054035200c0b07680c1c80e0300274007002074040c882c259603a52a07200704112200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 613814064 1250 613812814 613812827
    0x40501020712030b010c060b0301020909091e0304030f0b060103200705060c04051c03020f0105270d090b0a0306030f05010506090109090b0f090a170d0c0206130602070819 75
    0x1e5110300c00101c8090111003040d0155070000f40d4290125032040c00602c003040c480d40200c2ca04800081c001458080c0c03410010780c0c445400daa8162007607010642040000ca00040d00e410300442c420000c6040c9455130391074216200c000031000b03000e03441034000715440b640260002d03802c41500d0a08500041041210485260000da8060f20a48200404145000303a540c049405a131406021143c0c10380d0201c000042d1010481802c400718895600b04881030a0284546401291011120150188030420040c01a4100f820424807a000721032000c2444e80c1003100030b000c84071043c903403035180c11400409030000d00d01544054401244170400d60300700301040d40704601c42d5034101c2c1c02441690f2a10101c500710f0b19010401050b8501e05404143c443c8145804958403021200880d500c0c1000b81d5501400385c810b80103884009a800300b411035041e031050090b207006080d00d00c01400d0f5840d00410300d040340302d04000080c020a81c00a0501c0912a940d8100c404070801d502d4030510707a40420000a102 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 613815314 1250 613814064 613814077
    0xe06010806100f03020d08090a0b070c0e0a05060102100b0f1207060305090d05031f15020a05010b0402210a0e07081c0f0807081012030c050d03090b07081e04050102 72
    0x10451104007082c001614109542920717000b078211000020159582001a4801120194001030a102c002034030790301c641c000c008484c403451100001f1880d200c45110750400260400098504040402c170303059a0008160307180901881010820550200201d1000518404016040085000d40002d0341070005045006c035405a40c007000340d551107201c503649404484180d81c0c0060802c0010860411001e025013101d800c0100b80a54903e648003882e9606030b00c0d0070141740150b0400d0f81070800740704080c422502c9210003a20107528045400801c140c8c05004205010240307409080840c1c0241000d038840111040348604a5860940700c0c0181c81d42c40f18524502e85000214400c4e900e1410310510703482010003241e40b201c4403541c0303030302e41d05480303c2134020b0900100400042000807000d03401183c0490070750098a440d003440b44d0508001d82048282c0359881c0c28541005401d40014422485003640940d00c4e107410305858496010014840c00543d030385082d042c24000c1880148141035004001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 613816564 1250 613815314 613815331
    0xd090209010803130317040b0a02010f1401080d14091008090c03010920040b060409020a080c13030f0c1e1e050609120712082511040f0e06010806 64
    0xc960398608041c2d80d40d00c6842ca10000203c548803040000441e0381a810381c82003641143c131410291503c44950305504005400301c010307912000502c1c41c081d8580300c2e266440500d90448803056062003822562003002c0d00c140c41c00c00095880600c07480c40041c068a04d0b041c00204600504404a00d000b400820700703582c07c50702409050404a030902c0c051082225695000c1c11764450000b82030004641d025180e804103030031540792515002280d580c0d00003040606002c820060b187c10036007000030100c0304018400f245408040046661801c80701102030101c0b980071200b01d59809880c90130503000749441d4041d03200542c808150b40a001000080201070340c1c0300d0b8158142c48280c8140283d14000c140c420590070a02c10484010740e070400101c2140c0d00740d080070480b40c1d034036545ca1950f158240150b0301515044400f00e0840021560340023108444102281e05110141c0c50340c451419466400105502c40d540e203400741503811800380c020300710144a250a86400f580c7d20f010a0751900c01c22524150b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 613817814 1250 613816564 613816579
    0x5040e16020f0f0c010c0305070f0b07090515031f08010c020601090c08060a03141218010f0c120302070f0807110307090e0a060c0e060d1a04020702091303140d0902 72
    0xc640010401d0014060f43d0042401100d40f200650300b00c2c2c0c0041064080060422040c004180c844410f4040710b4815030020b102c41c54000c80044c04c0ba0340940000e84070f07481c003175464031010042200b5a500542070303003804592641007451240510101d41d0080e4903d50803d030741000c007580c0120342d05048075075011003800341c0450107008480b015400c403003441e4050081401480800c480c1251b403050b2041c42011103088803540705a12401c3d400400b440310030b07450030720a01e8140c0d50340509809880000c42c20800d9080c1c0c4d407603440881d040e00715400c09d4100f59000c40c085051060015000740010740140d211507456010341400003440c03002c0d0003510701920904a0000b0383e000d5074824400100859409001d8811040e80d0300e001a151031a10801044042e56000003d0341c0d440c002816801604900019924818480207011010003218580b2851050000300056111208182d610584002a0703844040282c5400d450a404039a80150382c1040400c1581c00200f4640c80541d4840c001c03035044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 613819064 1250 613817814 613817833
    0x18060f15120e100c020f0a0c030c05030d02070603020a0e090a022a0c0418120f030e0c0120010906020a1206080f120310081516080103020102071505040e1602 69
    0x58480282d04504103038010059003d10070402e902002d5119618810f4a464611010381d06107800c2189a0503110706d502e410b8200302304212202440000c10054019041900c1408801f03034032200513114610506400156201c0d0603840741511140e8000014804081420b1603460f420003500541c0420038a0350300541c0c8404499541e07400c0801c0894480020700c0554451002e001c040c0c110f1800c80c04407008100443d80005801c0d65004204058a41d105240e01d0489d1000409603403007400c15030f08030740002107201d009036030011401c181c41d110029062202c2c840745207150b00400f0002c8028000d54404628502d2150341302c0b0b0800e802410000042c084592146c0c801e03500d4000303040c11190150702c04441d042068020401541d84440001d825260b205e60b501411400e04a880c541c10000002d04420000000d034203949205808889242c586480d40c10b40c1d0020b5914071280c02000c504060b140c0900c2c0089226100302c401401c07070354100c1807440c20b10203d03000c10075104900350070160042540d030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 613820314 1250 613819064 613819097
    0x809031c14130c09020a0e04020316121505101116050109060206090d1b060e0607110c0a0504051503120702030c0612040803041a04031709030a0918060f15 68
    0x101d003283e002501c1c044483d04d4080d60400035400855242d041c0585d01c820f024503955144040c0d80f10b9002c4030500c0d100b101c0381d408000d01c5141240d4500f20351030301c2c014080d0303410b034444170145040c1c0e0402c0c0ca2450500580f0341c0c0030f866210707981d03440c000300340724040494400c0111920500e0854034283c807407800307107070f240e460a0383c507003108454008050f4041c29941034003070300c0ba60941c21072880790740110044c5016a25820305850071481d0480041e4415420701030a60380c480584140c1c0c0d0034400241c4140d8601200003821f100813403160038841c035140c1e00070400d6414110300c8112500c200804985c20300008072468101900801005c1c0d200e401071098000060500b0421110008410444a403032544c0b15650081240c001600c143c980765901c003280105103d005a055010b240030307440d40201d140034040407000c06207008011201641061103170030303d01038001c0040419103600d00d0303030760030800c5a01d4a1a401800b1541c41420568030103e400202c41450032090040440b880d1f1b10b406014402e11403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 613821564 1250 613820314 613820341
    0x30c020f0a031b2a03020117070206070e01020123041514010b13030605010b0705060a0c0c06180f0b310201080636090606100809031c14 60
    0x200500820703d0014406404000200142ca102c0d00c80d4440d06100b001c4011000914800020030b01408400d846050013907607001a442d41c2d5800c142c5020709450f24182000035200c41c03000d4a080140075003410f0080e4160b00039003001c80304c0515100035051841e0103071182d4820703580940703055503601107030810040a1680790040c1094501042c203058101c1e480d04007204000c0d03001035840b0f10b810401c12804800a0442d01441d4000c01c801503286803101030504040781401070140018140514020031696140c0e00700500c1d1170340340d8004074001003c5580e4007400c1010000c0100041001c550550843d04000f01d00020901821282a0020480e08000500da011455014029030000451402900107600c5501c00950240000c2c20340101078504c0a154072005002040030780500702010485800404a841002e80c00600d10004003024240f500c04101040b03020000c1e0001c000e07811000070000c2030100110b46600140000c816a101034459101d00140b104124071030140c0300c00f00204020380c44c0c004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 613822814 1250 613821564 613821583
    0x9180103020102070308030a020f0a0c02270a0e01060b03090d1b05190503160309080c09150d03050f0f04091107051203060d020a140103051b18010e0907030c020f 71
    0x3c004101190035621a05500d800c01000c03142000d0702045410050413030a030183c8240c150588a5180d11182441005061140c18094003031941d14050b00c2e014030000c4020382604241c4000d4001001405280c031175006d80f01682103040c0e070420000601c403807034500040c141c05660559440c0252400e004465040750a9150800341003a072103100f40385200c0e0b00c3c4100324100c4910400c01c807450841414210761104c04140381c00c1d00410309035541000340e0041406181d0b00c440c0100c45411003880d02001901d00a0342807850540501144111032003054090011988030140e80300c0302a482d0038416107507080c0e41e8010f000c0c03e042c1030304041000a5079940f101c20f9981450707010000c0c2624600030801c104007032304000c0c12940c2c8030940c0401d00000d81c440074050700150100528000f101c00d01080090142c407805065184ca0149a00440041d0801c0000741c40100f5404505901c0d40312425004940341000d050034240d04c03031020301c10710600e6609a8010300d100e0310030b9000c3c0c2d5034410000400e2602d64020303c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 613824064 1250 613822814 613822817
    0x806090303010b0906090306070e04050a0b030a0f0203071d060f0402180103050403091208030a05060f010f030b01180b0315150a0e060705030403080c06010b040b0405012d05091801030201 82
    0x1e00040c0030220360308002d4501e40c00050402410002c41d04000381ca0080c0a84000f008503216130919451800c143c002c09911902000042c405248140b02180d40c48525401c05041322410140da0021947e040c4401ca0050a1000285c071117001400950301d44640c09840e168450741d42c0c5208481242401e00a45a10003000341d250a640c8060000540280c80e000744114200b206481000c03448403202100401c00078000c549886c2c4910b82003a40c0d40031980050126807248030a00d01d021800e03071740034403010034542640c900070900e03000305401a50b85460385003a880040311554004501144001c000d1885a8020b03001083d0f0100080241b000365004000400588041005202e9403d401121052040c44019141300c0c03070800c0580b151820345e081a002180c12200005282c845650704105080c050701003980901d180526102420390144036030f00c503d6041c806641110b8000d0501040d41000c134111645003065540f255260044c515400740c0880b40c03152094a400031034181081f803105043e03d906 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 613825314 1250 613824064 613824067
    0x5060f1510210e010509030703020c0a0f0b0706020d1a01030b010905060f1b010e06011502070e04030e010c060609060602070e010305070909080c0a1a0c1207050901030b0319030908060903 82
    0x4038402c080c070280308071198100c039141c07070001e4540ea009110381071194490001958844006290082c1000300000450b0322074101c4500505c003048503008490211154080c10b0380e625102403038040c0107401055a4242e4051410300445410040440300d034604203402d80e8100300050b48600152460070032801b0703494201c4400e100340388202d40c4110050a81c61007020034003d141d002140303070710700751140e0440c40c0b03070160080c4004201920b051580000900300c240054000a41000e00180520b40024405410801107105102c6aa400b601c45054102e03045403080c003100d6207500a4401a01951050340014800c05800081e015000740c501c1d0f06981e07000019000180c60900000c000d400c070f500080d0f81010040259190141c801c000d4441d42030311801c3d030b001140d0f019100c1556045002000041a00d008008400c4052100d101c1c160b400760550821a88a0741503400403001803080d0070f00b0380e4162043e070100d045810108021075010700e100c1e40d913881c100350b01c4d103440707a0312a10151103c03620baa00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 613826564 1250 613825314 613825337
    0xf0e0a1409060a1518021210030b07031a090a0603030f0f020a02061e0c15220b070e030a061a010905090403050717070605070807020c0f0105031305060f1510 69
    0x800307030801c0d41007455040d000d0b013a00340c496020924034032019620844171580000e4240286242c80c0e0500d0748000140703400f10405146454950351003800818002c10955035456071244151210071007074001c50050416607652920303050260040641d400143e02103600503407c01405413003680307400078821040e4041c0c13909110302d5082c40100e0304040c102500324089000000309643d0501c01404010208100500408030010940c000b0414090310002600030742e80f08407004088000300f01600710341d00440030171040e41e444904887c0e0b051425049541409940c0b110014006150001080380348242c1040015040000040d00c443741d1a1107100d4025080034002000300340182c010b0f1803c18000c2c41d51a05881a0004180c10380e403040408a4400c0d0303840040c40500d681c41026a80d0200301e5000802e060400078001807145034400100c3c0341008000400101809108081110041e40c410f08407216030604a0400c1e88110b42110501100c02d14910340783e440742342110000000460710f0f1565a680d18 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 613827814 1250 613826564 613826581
    0x209010e100501140d0510030b06010311041205072c0108030a1707120c0815040902030c0d080d02030108010e06101d0c0c0604030302030a0b09011404150f0e0a140906 73
    0x1880a5118000c130f005000905c240082030090074800c100e4090791980d02c40c00c52034a06206680a00b886040600e400c445c10310900350341040318207440f640e586142901625207009071901740d4542010700071010b4803891800d44000c844003003594007150290340c3c1c0c9503038855444954a0040529600005500f101050008508071042c40d4020300300381f801c0070030103100e80f80300b009580c50b0040d018002107555041213650440c540c140e0f1034111040f20240f01400903600081e0303840700105841803003207003420340042c100013095081b1154104030403000e540ba90795440d1414000c2000f0a0409000d0049000103101c11071407840302c809aa45c4041c01880340d0007034a02902c0c40100090101d040e12908000781404680c0170020284254420b079000750381e07480c2280c41c15040d603480345001801214a0700051003482c03501500402120000e03030b0001810002141e100140d018160f0000303031081c2c0d84c0c007004190651403a584a2184000c40030601c29508400041d030043c050443c0e07507103443d0301300030003044070340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 613829064 1250 613827814 613827827
    0x90609060c0a0b1f0501030509100b04021e090f03030a2705090f0105040f0903050706020708120c1210080c010c020102070f180b0d030207120204090b040f0209010e100501 75
    0x1407692422169080a143d440083d1008107a88070540303c6000b40d111001003e940d0b0525000e01402e10301880581030030b8204036a101d1005000000031612100c0c40003403a2200d5040d104151503c041c845040c031b60652030801e1641c820034030300340254140300880c0e84a050004c00c5035040c0019030703103802c110003403280c523810080c4181d04064040c11580000141540d6040710241c00369007030004018855140c40d0402c000c84000851078a091780c100b80c40800031a800109a460164004d040980d4441442c07620109038807a180d840c03a0505903180500407160612006400b194450010040203921a02c104600d50740341813280110075071203543c2c0810035510030914a8000f07441801242c01c026110603020010141c40c0d08030602078510000a4a08078940d8003500701c0051094604411414a98400940f64415402100b4900340041008421515241e01480d4035603042611011035081c10301e0000d42c0c84101110a030710070584070001085101e030190103d40103000303641c6000b0031f8914180043d06d99 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 613830314 1250 613829064 613829077
    0xf0201020316210f0507110a03050106030c1d060a0501120902060a02010b0f06071a0907080d09031a151c0f030503040c0f08070302040f1806150b09060906 68
    0x45000501402d2828031040407809074281c4140c001c2001c035007014101100e10203400c9507040802040041c0d485003a50428100c0f04020303000184849040c0c54800420140b04541c1d000600540c64940d0000c184000039200340191003144030540c0110502240c0a0b4808005540d01a4428a058803c0103a136014000c9000e1006003008040340540940d00096000d4020026a10250b511920000d1aa1901402828201030700316041d07410b058458032403504040c0c07212040640c0380c1c0240c002c00d905001c04c00001c0011702c110170440e150701d1000310000b8400c041e03501c000c41d00d140d40ca002407800c03901c0e0b408041d40b04e15410342035584c04169840820801d014444807680c00400b000000c0d1011407003041d50000441c0c001d4503420303985c0c2000c1c0750490750340499a1201d81e9050b502103041c411000081204021a40c0448011a40b06180790300d88004102c00030b05039414030031000301c500410070300d070300414504511072651041243c2c0d40d83c0d074545148070301100d50394080d0041282c41400d28100010b00300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 613831564 1250 613830314 613830317
    0x7020304180c03290a080307080405040905030c010c031b17070e0f060d06060e01080403080f0612061f0b04050f0607170408010203060f0a05130f1b09140315040f0201 73
    0x2200600114501303000301c1c0040c0300aa400500b0380180100f41424a03008000f02820002180b5010351503d9050039400f85000781032060b521900d42209003c4100186ca1449854400802046034a10001f80c018801645c8400c401d04813058040540350140b910b464089101c0e11182002d40e603258004c1b541800400d500650200b61007078a0031823a16441c002e0803020b20056800a03100d03040c9a4060180a6122007040c1002018010080000d9010b400290480100c4d07a6801094540038000303114050401d10a9810b48120410003c9001504a80c210000b0294038030b69440c41d01d84104210328443c0340a21a000241c49001800a0801d140104400c9003d400007015522014500056035403080d40300d00800e079004018043d041c84d0a4494401c600400c271100d840035447c1001062108402030510b420351795559884020f4103480350000298207900240c00b54510030100d00151a00c400350007105103da1a10300c80c0070742c0d403d000846000680c0d91b06402c070503550743c03a502e1910048140b0412070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 613832814 1250 613831564 613831571
    0x130503030a1113081005130c0e04050c0d03080708060102160b03151801170303163f050c090123041802030105040c03050708060d0c0513050f07020304180c03 69
    0x3c500382843c44040010f400c250303000d44030302415001c00d83c0071b46501500c401c1c5a07000d4002e6244c001a90703081007908a80d440c2e0785081d0540d0f03076410700714100010f0807402900003080c0300c1c0072010503501c90384091045199403640a540d40f9000012031b540e030034000c00307800c0e1500082e50501c51150040b010b1580603100e19000708001e44854041003140700c030001051346400510005100801124400b07440c1ea0400400950071460f08480e01000c000f4449031201c24003040c50400f030000c091842d4540c80340a00c821300e1003007001d0903039907c0c520b4102404102d08840d280001040e10300c0a0310b401c42d034418005944102036081440e180d004000c51081458124480410001a00620751022600310324412100141c4070361400e02071005903001111610201803070602000003003900320240d140c104c901514240c20110592404001242c050341085903c02041541080e07880344a40080d1f2041810040080180c1c07203640c01039941e802240640800b4281c1000340768141505a4804110040710b417a020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 613834064 1250 613832814 613832827
    0x12030c03040311120a080f0d020c0f0715020115051c0c06020a030e0d02010c03031116050c0a06091503020d0f0905010c08070f0816020f06130b130503030a11 69
    0x6038a5540260700481d001100708592010030b242001c202c201d464124405842d0707070700455944800c036102c3d140d12140e50303600100342040402003030382c1075640014451045990900d07650344410343c3d034400c0d8803500411408034150350401e0303403042c0a5a440c6040700501068000c0c101401c11001c03034440d161303044514482d40040b1000c56000e480f514018903558000e0203075461107040c020300090318064824003400306032a5080050b640200c100604076090324000a02c030548881c4640c03540b0501a01c0d9480c0f0041031500014003a020440c988440412a0b018034400d6603814241d500312000d11401c01400e403045049460a03000b03800610b0f014051b000300090b00780d0750381e01c0041201c44615041c0c0f92031307560f241d80c80d04003070f003110080e500004d042c00c2040a40503440402400510024455944691400c8590301041e00130444120020408410f6070300f685801c95a000d806103074801c1c2580c02c404501c020443d920400e0303061801094021000d986982c0c0c640300a980138007071068a4000900040041c07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 613835314 1250 613834064 613834087
    0x10b0711061809070f0e010801140409080405030a1104050912040e0a02070b0c0904060f0b0a050c07080a0311150408071101270801140705070201080405010b0a030c06111b1203 77
    0x49101308001d884e0120b80307906180b801400032a6a81a19060000140050044000c80c00320040c0d4910b04490100d690505461304a070030b40200d50040360148125804401042a0010b06101001c010755040082ea40e81400b080e0359000d002c0000c440c1e6860800c014403843e80c00b010706580c4094400005482d00380b550fa01c900000408499013900c101022808031560b01c0d00740100c134014440ea24415000a003800002141407094005581c00c4c4940041c59070100b0303105205a500824200c025120650f14074100684a10405982102540074040c001d1205143c0d2840c0c00340620b4001c414a0b043c41042d98038102e002c1c00c0003040074180001c11b09900982200c081017070361484081c1d180041010720b040c60080c00d49031801c16135110506808208901e1650142c00d07500c0c00b60702440c00012a80380c9050280c0140400c2c1c0010b6004600c0c2d0300d000c014004243d52000c122902c503581d212070891941315007601c2e241c0110f20032408100b000010322291401d50303803664480b04c85078160b1703292a110120 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 613836564 1250 613835314 613835329
    0x2109051306050306100f0b2110050109080111071103010f06090f0e01050c0730020c13021309020a1403250504080d030f0b04140f010b07110618 63
    0x103500c4a6a0301c80c0814070203410140310703158208051100c62000c0900709595202c1c18501801000000040866428031415076a8101d20896581250700c0480e405d04060301100b507a0540503042c045010f0389000a0904014414140d0310791001c400c5506143c010703614075170701c4240f50240700d5040d9200d0791080781c800c94a1244000411412800003000481051424162400d002203080740381d01d418204520102802c0c1203808003544000b00c03945420f405170b400060051860460b004d5061070340b001e5070b40c094000031000c41624048428040c0803101c41307403000991041250010040360540410000c8a0701600030700400307031060800340702903c80d00640320100e4104a42d2107500c844c80b20150b0f40080060f140000c0b0300035461420510707060402c2812652200080314a20402d50788000580900342c6c19440264403100080040c44402220140c100d94400f040e14104a40d807204000052100c7e015011550f107590302010045200c40d094042004503000802ca69440c081c1840040f00240c9d038000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 613837814 1250 613836564 613836589
    0xb0a0908031303141b0d020d050607081b0f09010309020a05030d08060f01030e120304030e09040609060b0901080c1c4b1b170d02100603210905 63
    0xc0b80c0894440c9103042c0240c403011110074821041d04960040154100c903103c2e401d04104003503591441e00389a903c041140c04e0084400540303640a29801c2c0852a6802000c0c10f01510120306890040c103105592560180700700c0e002d00d846007004100c1c0d00080d5000780c2000c94041c2c0020b0000da4416a0795000c84d052810b100740c10400034081c04100202460200c41c060344001080c138040100c0041c1c03007011355590351720905090082d0400310006040520466003000c00220151005c207540c01e061400c1310140400c4e000c200c0c0c1c22030400800020600340308550783e04070b0321b031480140110380d110b10038400142c00d1084000810421400850b0200da100061200203031100d100316060703164611140050310742e03000e40c035042810002d00b6a08200d4660710302109035580003c6841c1c407591640f245103040070389681c40203c0c9040c000150480c0d20a001c2080c805d000d180350282c442010041d41040c04550803400006e04039103004840c005140c40b007000203a0400c100e0304015030130648410003d1068610076 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 613839064 1250 613837814 613837837
    0x1030501122a0b0d1d030a0c1719030515060d090c050909070609060302040302090402120c0918012714120408010c12020c0a02060915071103060c0f040b0a090803 71
    0xb403460140300384c6224015013030103019415421500c1001d84152a4452070100d50b081018100051041c0114094141024044800c00d507a9403864000541e10408035800f10b000424600b10000e06c84c0300d07085c0d400c8800c1480003427540d071800d0942c84c910801450709480a6580000128004c0f07426160300d03101d180038242d2003008007242850004000c2400c0203980000007014018002040141c84210180e900581d0494444d08140c04000c02039281c01e07841604180d200b0380c00b0042c03050201000403d00441074040d8024042c0384004184140613122600700c070840b034819070000c0400b140500d000c3c203c0c41c0d4401416504821072503d00718000f82c1040c0c104840d5650b490318000503240d084034101c04a0540e141055080102d10307145c40d41c03641d4220401030b0194400045600e016600d240d20385046a190340c6106485a6090400f00c0510740c2c4040003034002c2c461070010856460321441603950800e0074021061500742404807520300707508141d45210030f2202068000c80c00d4501400a4006403000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 613840314 1250 613839064 613839067
    0x815010e011a04052e03060f0b07150b040b10030510091118040b130504050d0e1f09050d051c05090f060f04080a050607080601030501122a0b 62
    0x400e0345852040106074044200c0070a1428842d403580315107000c0e40c08aa80450b5886400e41c1811486110108510ba9454150102d40400440c4941660143c404d44008c42c0308010001e880782c520a4051213005c00141124200c001800030b07201d1a81c200c590b941320301800105600a0741004203001c0c032444660000440c1c0c80e41c04100c4007095141009005200b0458240140e850460416030140328400901c444440e492600c0f00366500c554010341e6900da0b0203406c110720551402d40b480000c00058508803100c0c01203440c03c01299220300383c00301c2d511400074020710b4071140d130507504860310480e0210078042c800968030018256855000c0503100d10b0191340600351003004101c3d450f01e5441c0700d0300602c0a000c41131188a00544400c09000b520a100b80d03404c03592040c40e4642c00e8054001d6030700100c3c0302d1040d500c03040104040410214020201a140e030740031515000d0043d810f8070024098102c3c07031088000d90f0130108005104400c0805981c80c1c42c410291500e0110711b4448170070390480c00e0700020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 613841564 1250 613840314 613840319
    0x7080c010510030f080304052e150f12030c0218091c120c050c1618140408180a030b0114120712290f09010b090106030510081501 57
    0x102070003880e601010540600c072181c0e04554551200b40d088040107000401e012001408001e8100300707101140d000d506404640307030030030400b0700d9000c204861042145828244218503441d0a9401c040545418540312022141014080842c2c40d103000c405030708004180c800000580c44801032404058802d6921141501d0a002d829140410071b8054060000355441c030450303d0780d4040c0603034031020801c1502103843c60103004201d0b254060405850918040d0020301984104020141d4007181c2e10144980821036a200084046841c215410315000070380750005000500c0f81d00042001000341180310b6030b041d4401d8041882c00c1c1280d0021242c0c40700c100c0060046080e9007614001041080350300d0074071780150102084e02c541d01032143d032001c02c10400d525010804150001c540c03081000780394035002d402c9001c02e0601c16006940113200c0491a00100d003c004042c081d510b00c0950184c40d595045c0d00e412001c80c0142401070036811f00070345010002c10002810701406681c005400901000d550 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 613842814 1250 613841564 613841587
    0x13020406080a170a020a020a0b03180f0d030c14120438100e090d091a030402091005040906230112260a03360803100503030708 56
    0x1400c41d00240348680c840c0101c940000c0c0b0212000039001c40d5012020303240e8801e244140c0c948051144000e43c0408174941c08214080e06002552180c0700000609142c04100b009150712003620680c0030070305801040440ca940c9000f9082840d454140b1700d010349205880d9241c1507410707000305c0c0c0700001e14400d0303000340400c0c48440d4444d2202c58000044000400314500b03544c84019051903e50000c030589400012000c00d43ca0241c0e038010f200720b500702141840d11a40b41500c540d52868060041002036101040722842c01e05c98026191000c2001403a5131511f408022000d130008180c072421000c001000300d6280c665010310071141d8495007001c24040380e603403880d00c10704401c02642c040045202c1e0040007041118100341c1941a00700c101c1010340d1003d0300150355003427400d11070309819220010302c40c48a5549030b405019125413881800401103d0f81042203446141203406140d050b804031005004511100019a004022150812106d507510401300c0e0654000306020303101305002141c0480b158 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 613844064 1250 613842814 613842821
    0x50c0a061211090d060f1d06091507210608030408010b030105131e0609120f1101060b04060e030109050706020d122913051512011104050103110d05130204 68
    0x20341202c14180004071000c14082c15036580d0182032035444804644110005070710480202c4911041d1074052004040c041d0703551081902c5c1085248103181c81d1001b89107500c62000c1c0200615601c3c2050b10403501c034403010000c0d60314044450070313544000c00030303800c0c03000c000400c020441c1000208061424904241c00c40718020143e400703080071400e03c0000654410040b4405101104001040c0d07038090504400501209100500e24041140c800c50702d41d0b04051801c1840070650b440d000c000d04c0d0442d446007030700c58621680b10075200611090250b24001d60706480c50010203400010f050807181c40e041d00d07000e6030380d1060000d600440740301c000b640d86c40342a82040709004201071021003d0f00902120207800f001c0d60145d05445401074041c3c0303544040000c40e41020000c414490790401507504802d051041c04814821030f07804400c009452018002c441c10620740c0320b8498241440d01c0010f4024040c13410007400c08650804c803900c100d16552140741d000310a0b418034035152141c0744c410b01c801c6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 613845314 1250 613844064 613844081
    0x9020f1206181209040507120f02040f0605210c13031101020c100801180902210f01150308030a02070503040f08010c08270304050a080f0c0406080d0c050c0a0612 71
    0x680c00120b5111040b5841004403661135505840001c0c02e41e8450008661540da0f40b41c07074140b203904010041030820300517006401600c08502c10095040c1d0303a02810f640a202e03d0500355561a480810944804801e0520300d51080c094127810b454402401031103001c00c1c4643d001191642c5a0fa403000f441560b04101d0181416010b4401e210850b64900d0040c002c0e4805128070782c03200c0b10008181407620101c1e080a0794150340a080e0070503138125030240c100c4405249011400d90310594141c60407010050249851031400301203118001c0b0304548400c411588000c0801803c59020002c0310001117040000304000c01c180003030b05c54000d0a04005609407144040d8460400062a040c090f404050850b50000e031509843e20031240c230b050140a40c01e501a5900a503881000154009407610010511103804201a010349640489840c05c0004035900c6018820b85a4060300402640f1402081c00201c02805101114075895041001980510041e04400002001030504482070030f02402401e02 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 613846564 1250 613845314 613845361
    0xe10020d0b150f03090a021c0b06090c0a120b0901030b070f02010603080906070201030f060602031b06090c010f0c02040c0c050f0f060703020a0302091908280609020f1206 75
    0x84030040d03046980b280e02407510600304181001020600c0c0f8202009032503c007a0b40605051001c0c842c07100ba200003651a1001900d000700f0f02e800040c000d10309002800e11440310032461a04050803140101c410780f40201000040700e5071080d4814071039885c012668000c600c01d54210a1501e05400300411110600200348290b80c10440144009000c46007900e071825030640d074554848055000480181001c0410848403524181001c1086036002c4018820898022510284030700050f030102e0303503440100c420340910340004861005075131080d0300400c60b41c40342e440c224802d0401038002804a503100d00c07825000ca0030700c1c0f4250f410000180b00013003415141e040a840103204401e03034a505c514000300b50000b0503030f00060180201e406035059900014020380b018500348001281840c0b211558002c0b94514481c5c02c401c00ca0b0009051041e40d45881d6820602c101c1c062285d03600c401414200c0030481c0e0000180001aa20b61101d00300428200841c5008010a042c15040800800c0d9014405034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 613847814 1250 613846564 613846579
    0xd051003021f0c170d05010306020307020106050d0506013302030a0e0d0b04140f060c070215070c0315020d0905010f050a14060d1704060e040c03020304240e10020d0b 73
    0x1440d0036001807800464940018030b840310b5903c484040c013000e10a6100060340e040c6800b0003c414043d0742c0e4051841a00306030001c206c0b45466401700020441040402429540134000500103220400c1c44808400da0300c207050003480c0e2070443c5580c8400d22040c200401a4004950404003c0e030000703500d420a00140c17030540e45c066050b04d80c0466603a0050024040c1c030810541740444040c200310341c1030716142c0c003000d41345141450205000194050301e4160303c109099403443c103030b203002c5034102d51401d40d02c1401e48002925543d0f901d1056182100c80d002c2040e400d000d2400800080d0180e0f10030760348140000641c2c440e41d24008000c44d4800b400842c090b626101d000c1300c0e0000d100c4042504840d0031070304020103803e546032140b8116400f0300040a001c0002c680001c0480c1c019a81c0385c01500100c0e02801480c540f41812003c0f030108440c00b404c1d100055080b00901c0380f403150410600a4107040100780345003003662051a0400c004c081c2840158005031b43e000350001c52107608a42032085a610 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 613848920 1106 613847814 613847869
    0x151504030309050918030d0b0114040303081902210402031c0801030302070b1201172e0b0307030803190b0d080409051b16080d05100302 60
    0x1402034011801080c220305e610204103144402e840020350414001c00d842c030b0007408000907214140803951400440b600d40f103c0c0100b02840c041e0300d03130006900301076007100c0d50704086041019500c0d10502c6041e80c80d18000021041c0c3d807801041d5103005407140d00001c2d0030024045d00124240c8011820341c0d80807600710804604881c040d030207543c0d841d03945a08003a00e500c02d1a041520003170340800103000c0800d16190711071310004014100c801000340c1a580e080080c0b8401d8a54402e4140c0c80c82d86a6964854000c850603c0d00541c06001c00a1647e65981043d00015043c2403541d80070340351510240c0e8456204900e6207400400d000d462007158107050645920a002e01043c540c117181c00620340c007026260303446280c0c5080d91150324204903001803604a0a9216048828900811070310014034403d00420f030150036910f0010b071200c0c0c41c40c4104440c03420403c17640c8810740a4408003 = true := by decide +kernel

theorem cover : BRFrame.Cov 613669064 613848920 := by
  have h0 := BRFrame.cov_init 613669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 613669064 ≤ n) (h2 : n < 613848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
