-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4973
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:19:56.753155+00:00
-- url     : https://prove2.me/submissions/cc5e9078-0a09-4f9d-92a4-e3a84328aedc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 894244604 ≤ n < 894424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 894245854 1250 894244604 894244613
    0xc0302120106030e0706052209020c16120305130305060c0408010e060f1302040f020c0102070506090109020a1a0c100e010f0b01201005040c0510020d082202130203060109140d 77
    0x3c0007141c0c0d101c41110182d41d84d111a0b0230908006001c1d0803c8000103854042c0b591055140040740748100a001c01900024055401c0d1103030706c5001164145003056035555428000e4003100481e6100401e60704c03c1005100080405201a10170358000078020850b85130311045650340c03200c0035219403500d81c1803079010404000240300d482c100390b8005080807030503591941901080764021f880500d030996010818908019041c403e0540201d1214024400040b06800045c44420144200d5804000c1204184a51172280054030b426031800c5007622015a440001800500300c0498001c4d0b240d4603101080610700c440b031003840695081a92810000c0003400401c41d090b034920b01120055114074030303407a1150401ca000300d900c03541c403e10441e0074882c540b03814480740c81444d400400964210729003a0b82516802000554804044034107045a00840404061401c000b2540a500100515040f042c001c5a40d0001d40c0906020390360084403960710402ca860b583c2100f2181030f88100303601c42407800304 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 894247104 1250 894245854 894245857
    0x30f0910090c063501090e03030108060609250203072109030201030f112808071b020f121f020901021023090a0308061008040b0702100c0302120106030e070605 70
    0x2040b60501d0f0b84040c4d100301c10a130950701460311680d401c001e50070041c040011103014a0040c0c904000045040d0350400c42c0300c0b529004000c06960080074820f000682d0719542490258402410703144485072910f008100a40b20780c000340b010744500188400700301040e0840c08505505054a568070007140d0b08680c011006480d03020518101d41d0b4940c03200721800d80344407008040d4200a0000c80d50040c51200010265100d4041e203030b803e02005504014049810136003220100611001d1440c99511a20000b0240100410465044040c0b1904a031080c2400141f002c440503055420460f007074500141c25090b44a584100750040e0401c02886e44a506580c001c3c2041c42c0300d03400150303118881d007241d94203030060444010550f5400340058405041c0c01c031140c95000f100581d004014030101d0708015059100280c0018814221300d0001703802d4910078440400d450001d883d0074000301d0a003801c0140650040c030240414001898000aa520300038070505840f61410340103000520310381441611203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 894248354 1250 894247104 894247127
    0x8010e06010c05031c1d010b060a1110020a08100f05100305040c080d0909051b030414011b0504080106050a0501140f0403080406080f06090c16050a0206030f0910090c06 74
    0x798402417055060740c05c8801101d82402c011035000140c1d080654854600020340540c050009924009075500c190b203600e8101c0d00807180d907081803610007907040c603030916101141011916540c4041030348240f2a901c0a0541d000d0000502d40c0e000c0c49072941e10b41c4408102520500c0d50125900c3c4c5070400e09802608590f51203405a02c0f182a078544d500b8000e42803881c10141d00002071040003051003101c04910405070004010740b8014015442c0c03000c1d40380217100280014192240b20404400403060940156039072101c4851003031000c0c1410900540660018003542c4415400c00c40045100d0400409207800c5601c140d6646204001c5040422096808400740041150701088007001042044000307200510180c0d85032401c51070407070009002d01c0d0015000d68800c20b45c0c24140003102d0000d20588409090f107490a0640410b0340c9070040c079090608030000d401c44404420010b00d602480c2c82c89114417194010381742031401600e0240121a00f0b1000248225100ca6007406000c2c8a02200b000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 894249604 1250 894248354 894248363
    0xb01020703050d05030702060a06080d030b030c101d091506130e07080a05181203090a1e0b01050111100507120f1a01020705010918110403030503041208010e06010c 72
    0x55490791506403c2844001c0b2040110b0000001d2203021681001000c0e4080076428082112505014600d9168110601d0007400c043c1c41c1c030a419070b20364041c0702240380e00b0f2000b8441030030b212030f000004d0800b10a450f2450300400e10540d607008142080f01e5214800c011040580c40e0308061502003000700d400c220b130304c1d01e202c2c58440004640c81c100c6146450040002d030700c1e4600c4519020b01c2c04001d8800040040140d0821600d644091940000d50118568010700b00151030b5a04c07010b006251031000c2c01d005c0d009910681d401003900300309100480902d40582001c11440ea00e0300015600c402d607040410702c003030344080c03605400d41d1020f42c08190050510320307140901c88031010820080d13400c140c011842c5d181c0d48908001040c0c420900260314140c00380080c00d80c1d14074000028000701114402d00ca40340151600500103a100b40d808030724a270440e2180c01d626581ca900340140f554000300c41c11103c03011404206490a40255003540c100c6030f92901d1548243d68103401110444850305003104d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 894250854 1250 894249604 894249613
    0xc0e0d081303150513050d200a0303060f14010c081c0f0203091605060414030f0304060c030e01090311100e040f0b01020606040213060809030708070b0105040e010b01020304090b0102 80
    0x3980c1154408203100650258142c8218140f182480700200d420141014901459142420f000600c011070210b00b50340c07182c00d1104002d84640c0007594046c0d00c1c00d50b40c00007030080c181e00108147c1c05512000994902455000301c5648441e284541075071501000c0740403410200684001a4003030380140b82c0c211281d103001c06201f40c101d550354117903040308004011083c0c0100400540300010007402050005001c0407400981c0b80401044880c0300324010801080d44102035024262010400c1c0d0144000d5482101d580e00da440c44010242d001d5030508038001040c40701c3c0d003040ba40c072810070503081e242c20488205405000000300b060541c6000c41900034031210003c24040ba54840c840c4a1465905c40004148040200002030410700001e01481c400d03881032001d544007403000044031099605d2410200c035039454010400340345000c2c5140050444c2000034a41c0c08208581502c01c0c100c81007031350701740f007060307007a0b850f950a885029400c60700590044c002042811200e401c8154404018015903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 894252104 1250 894250854 894250867
    0xd110303040f031b0302060a1206120b040308070c11100e041118040513020f060415090e0a201e030903120c03070f051b1e0c01030c0e0d08 61
    0xa055070030a0b402515640c1c0d07102c1003041408041200e00e44903030284050745039000e0031503000409a003e042c51060401543d421404910200d03580080701801c4034644048078110545400c01e40c144040302d048000824100210300068050400b0480e1240d00c10701c90688400d04405009910340d1100e6800700300101d0348000011519540300d0159858003100800b42d44a44014442e0031071a51100a40d0046280808204084010034004110640e04a5070407115110810000701b4500079500a5200640740310500401150000b142d07004031032401d8000c946658480410008850324441700100c168800c18404080074200c1f4001c10a15031304400031003000404403060301c625001141d1000762903000141400e00102e100e659203505c00d100000c018518609200300401480c82e400d2960305200e4045a049940600580b0400358030650008480c15460031005404040d9149002c1801ca409049550310707855100740103107c02d039240758039290b141403986420301c4088801c2c4002900c0310203040c06107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 894253354 1250 894252104 894252109
    0x4021804150f0510080406050a141806010e0f070e04110403200409152304050c090903180607020a0905090a0b100608010506030a060e07121112060d11 66
    0x3071010100c0007a0865060500700281d007081061a500300c0d903c00c0b40000c0e8221070702c3e80c0c807680c1958041e030f0120001ca00758542c048000054445009901b102404c108104080c40c2043d4900c1a6500c011408a0f9126640d846070440340b200d00f96140d0030082908000901081e00810b0810500c06020300700150101d105400c11369160441d400c2201c040a00c1d070407004520810660141d80078108660400940243d40d646484030110300701c0500d07405481d130032082c0035010030b4080480d400034070554503d03503403416241107134541c407072910191320440100005c03808200e0000140d40c410312202c198442d4030108203013040900c2c5c212101c1281d01c5001c8600101d104011405014080c203480b40007800401000d19002481c2800200f00c40150340743c1d0b4508110700303a4041443c60445c0d10507140c2c566240c0300c5c0c00713400b8060302543c0c010310090701caa202808951644940141d0801e4220301040002119030641040c00f4410170750954070031082c080200c7d10628211b4440201144182014500c41098902 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 894254604 1250 894253354 894253361
    0x1b050f0706092306091009030f0f031707050d09080f04060e0306011d010909020118060203090f03030712050c071d010f0902130b0c030417060403031506020a0204021804 74
    0xc00005458032400c0100b0305100340c0800100a12455004030f000d00c1c0350214015000d03041e0350901c694561868222002c0c0940d880070043e50300005030168400180c100a0001200c941e021800a0703ca041c03103060383c0054201d19400342d02c496540034500005450b0030405880b020780280d900718801c000c01c0c052075030318a00410081c081c58403050b80c080d02800815051850582c030203005000310801142c04032200d4410300b81511400c200c0042e83c9542400125400302d0f0820040d6181c2c02d10240c0810980d03000005040c6d0b0307940445980c42401110780a15840e03014030500100140550428014218052000707850a11018000ca0361440d070755803000c440012424003504507503070084006104101c604101d80018240000040d40b400c803140d0401c5020340f5aa20545505684c04071f020f0381404c1050040383c000308015120039000e40c2e03122681e00c0d16418280d03011400b1918103030303220071000c079402000320072110750341c0240c0240d80b0640c003030202961111681100b00760807180c0118442e51a0310 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 894255854 1250 894254604 894254609
    0x12a11030d0509070b041a280c020a06230a0c0819170405030a0f020c060a051c0b0109090b0103090f050c01031a0d030c0f06110d051005011b050f07 65
    0x7000410541415540c0608112540c1c0010744e41304010442400051000c582241020700ca100c02c00e5030f80d0102108801412401084000d040c15a0041c0040745507884810310021034000c0741d110700b5480e80d484041d5a0301250344101460925240881d040d441840406170900fa280381c10442c0095035140d81d000002da114002c2c0c00c02403180c03502c014210700e5022041c4101c1c10600780780b00806044c15110796543e8011203100008104c030300d0f00d496915610a00004800c440d01819003510351352080c2016166401002c0102e100030a40810041020501c4c014100201d0307068484440207400e0083c010003616a105103941031544540504000400e601c1d03c003050f190180002d482c111480c20001400c0d07070003900b90040e5940031030054810755681c0440340c0d030646070f00d418010042c07403141c0b808180700104d2403405800e480c54125000340f05441c5400a1150310313000f503410002d540c1e030940300039406a00c90081d58002001c0600f041c5041450681a140c56401901215070300d03aa50304e0381b6481c2802a8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 894257104 1250 894255854 894255877
    0x90302010e19030c080d050f070605100b04080c13060605042d031110020d080720030a0903260313081209010b1801080303131a0a0c0e0102012a1103 65
    0x141340c100403000b0280000504030301a80343c410700e40000d20030806640c0c018040050030080d6900702281c040443c200310340d130003081c200759800c0d11580c1c0c0e00d4006440d00540d40f0854052242c490709919a0741c036502c105e01c01d4845648400781001e04010014200c1d00f50160340c010003c004c1e9a0b0f40300f406004a00d000d00440c840c2a580718801042000d0205c03124100b2481410340d4031502c803a80503a50000d030541d0b8401c03040c0ca400024000318160000440caa0703c811442c40340000540e40c3d82c203079406a540310a4900500c007200b051004ad1000f00222417015442e50070400c1c00348041074149014408400303003540512000380c10584080d90780c405449040d0354000e0942e40d101c0344440c017410005108281da58803112050255031422041c151648001010364692000c208401020822039107020104280b010090403071070300e00340c041d0000400306241440e000c120420914911584140180707543c501090840a01002d0700030310321580c0c0d0300466005000d00c1505011414245d108001070706031400306 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 894258354 1250 894257104 894257123
    0x703062c031305040b030a06020a021905070608011703032802390a02060307090f0f051f0c140f010f0f1b0c080a02010b060417060702010c090302010e1903 68
    0x1d500d50940302d200d540030500442c1070200c090b42990300400e03c280d4a0742c021001682d10f01d0040c0c4100d0520200744002402c0400920051051000009009041e504180c5031602e450b620307800c1c0f40c141d003e03041c01c2640b15a4030030400a20010002c1c819902112100d4150020046508003103009a8000c40380c150b040e00c2c100240f41800d100c1034004e42c401e101c81c2c038600c4048058414000e40d00c1e400c500b080a03000392000008200c4592041e43c4505c000c0501004a141840d10742c00140c2c83d4212500c201d510820030404101d50b0204141d1617000d44e02150b45850036980e05a0fa100390700d4404080d500c6034030f4000c13001080400d031401e0280701100006d2800c0000c449401c03010750021110010420400d200d0815a42012981c0218074190312907045a5101d8460210000803070140c16000b400c0e50b00502c000c540011030740c880e26002192680c0400c2618050f5a4100b4100c0c00c8848035026a000a0311a51080001d54001c1c40c44d2000d5403009000030041b0200364030052805007040d0701c00c4031020301 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 894259604 1250 894258354 894258367
    0xb090102061008250b032e06090524030112020a240513050a03060c0807030b0f040e10020a090e24040f02070204050c03070f0207080703062c03 63
    0xd05005031079009440b004007140703060800200c5561000e0394003030b00036440f618071040c00150a040e0600002400707052411a0b90b4540601003103031500a810903484210741e046492080b10580080c11000e8404507520206940d01d82010400420a0b000000441805410f52500c0940e0701a004501908030035601c0350281e1a2072041c4500010141d0001039040641043e0700c1303003440b0075519005035004900c0d15903111884203124090354049940300c4c1d03600c00240480041040001d8000840c441c0d05c2e9240c040041c2c1e03410320207a0a842e117015520394002c3d14a446041540361a80c000e214443e0400c0498040e14003580c000400c9038400004c1030081003c0840c1004403450002041d5031046403000c00c04500c0348420410303034a100145c2c210603c50f64540950f00b070300040c15415589110703001401403280303080140c00301c9059807096503004001001a88a4040b16000198080888040742c0040c188a451915071200920100c07180d528061029000e1409100d0211240080f1071000f0011716070300c01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 894260854 1250 894259604 894259607
    0xe1b09060c010e0d0e04110a030b1c030f0e0d021003230f0f240103021e0a11060105040b210f03070602180d0203191b08030903192d08040b0901 63
    0x17183c9600d094492401e218078040e038008413005503514207080303082c0072964842e05c10000d00c044150400480703150703c41d4a1a030080c540c0c02080f06c01d048001d40c840d401000c04001c1403015005201c0750180d0028200d0400e1030215200e40d011a1141d441c00c251005050422984d078a400c0c1000e4401c9001c0448030740c00d000d480a4020b04094000e00c041d02c1c20094080c1c10340c070302c0100689100700641416404211502c0c0681115021803400c0e0007103803999a1242c029401929185a80c4034000245c0b00e500004240c506052060340c102100041584040d4400c4500400c111350071034294000c2c42c00b52408080784060200042c0064a200f880c1c0562241021100b80410383c0902840070b00ca80e02a010721400f5841c040307404800d0a0161140c130350002c629007440300b5840080043d1104041401000040008020002d4510640b04038141c3e2143c20340303080d040b203040041360405440c1100c500705000000075600102034000e001107954a103c000c881e1101c0c81c040e0010360240c1030303200f0005a40b00042d0b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 894262104 1250 894260854 894260867
    0x227030d0206040f080a090f18140603070e04060e07170f0a0209010e150a17071509230904030302030106080708040b0a020d0207050a08090102070e1b09060c010e0d 72
    0x401900c0108110f18142d01e030610010091070001e028000c002a2202d80d507480380440d03c000d000514081c62000340c1d00e0b031610902c60703944c1a03811521840d2010f0150303140300030114540180f2004009109107400d01e2103030641e582000c1d00440d5030a0345e0317070704505041a0620500008110702080350080701c540c14095403d10748001000b0703503142c01038200300300141e54400c1243c0c1500d01c41565640c0d00d5840508005000d00400b9003654412410240025102d4010410104403000030081e1203110ba518400d4038410b100183c4544040344403010f0600c8145070042c0d045034911500003090485080c5000410307000d80b016101a40066000401030200036080307809a50841d100b494080c0041c038040d1500805204068440b160844e00000c0c20b0101110a4040d6801141c001095400442d21842c0801e4143c0c070400701140503014000d40050b1500e60a01c8480c403504035a1003e80119401850880c00c550108481ea50f01c00c0c0140040d15603d0024400c10090800d008014640c3c17030107142e00601803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 894263354 1250 894262104 894262123
    0xd111005011509090204030309060e01021e16080f0709150b0a08060f030d0f0f0e090f01060305060a03031e03091506170c0d020d02010e10090e0105010507030503070c06022703 77
    0x85c0100002c00010342d0102d5107a0880d100703450001d5220700c4482c0101c0c20000c1060422007030000034202e840c082030005c03440034040c485900003000102d0b0380d1100345855603541c00d080b00d41900038281c100030903000d5402c25079602d01c80c00c4100001c1500d91000c400c80b600810004400907000d00104009030038040c000d12200d800450051005c2d44280b43c0007499032010002c1141000040c0c400151701602540c0300040030000100302c2150f41c03034003004c0c1081440091181c180000e0816004c59800c3c00c0c0b076a2158103480d016654a0134101408505203441c40c118503494081549d9034401d10702190100c0742c0c4030103d03a0380786070120b4031615000c901303119810032002101240d0454030040c02240e17100b0015100507641901c003210070454600041c1c0350084040c080d03640100403c4981c070440c0c0e902800b00300c280c800100e4a100780c2c0c0d8072400115484c2c0104100140407400c01c0000c6100240914500b5950030302c20314002d482c0003034200030101041e10384064005220b98043c1504100d01e01489840755 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 894264604 1250 894263354 894263369
    0xb0103110405130b040609020c0a020a0905090a0f050c04060308071103010203010b160215030702060f070e0a030605090109080d2c0303070f02010e060124110d111005011509 76
    0x1e0600303140c0028601c0f9007955000c4100d60b920030658000b0b490301c1e0031610040c1700950b021511101d02e0300712540c480c1041f400491040000c2080030584034602d1142c68022140c250007041d101c00d8660b60489214429902602e40c0e21842107417030645d40c3d450103000c01462144c0c10860304c604181c41c0120f040038111868030310a900520050104003064402d0761002c80c44141c2c1c072060001540007084130603d040454442010001040200c1c56400050310341c0030f606030305c060030400d82e55094100c0e0760308018031070719a10010244040002c1b030810707040650840f5244000068042c01c43e901e007002035129400703c0202d10f03128040c0150f80301e03c0011901903020010711400400412017001c0b503c070301c4014485402e000d1100300450780681b00358815900e0200c40c600300d07a40f03541c41d4843c030102403002c0c01c0ca8400c16070b22648002d80e024404d64150100c003010703800400c46150b00340d01c2500e90420304c01403030703040c1d02c903045907054101e8141c003075180280500c0460685d5481076040042c000d880f01c5e00f1094 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 894265854 1250 894264604 894264607
    0x14070f090f0c0813020103020d020f071a1e1e240405090706180b0c0604021201090b071b051c09300c080303041110020c0a0e04031107090b010311 64
    0x460b125045031101d40e0114004892030019021440103030000d00442d122200c00e00d01c086881002e890703001008100072802503d4614140000000e5100750f100c0444040300c000750042c0400301041010702009030071400301ca000d25180c0d10481c480d00a5a00700321181952250782381552202d40c0c08894074005400401c0e2014020362400080c1d00d980c58060303110300810071041c280c55142d42040340a542c03001e0440c0e1240c0d1540c0301362445116644100546083c0c0c410354403245001124103051143e5450b0360303400030401801d0f80d0791000958410300b03088280f200401131032002c4000603c09104903c000039240300007814030721040500500001c1c0d190000142e400c03841d42d0090840e8510324102ca01d46a0324021510b070b901261402d6150800d10780c0c00300300c0d14030011050000f00004c00075004100e503002d880c038584420100700c08a23503500c82c0000d201e400000c094410700080e910980c08590050090410001c00c00d03400303c00c10701d042d000e68091a4016510005041c80e50381c907001d0b20010600c05240603 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 894267104 1250 894265854 894265871
    0x203090c041a011715061908221101030b0d0506150d033c05030403030c140406110c21121c0e010f020408150a050708060d14070f090f 59
    0x30b45000c007a20a00005031055030006408140c5d8a04203911140e00a80342c10348a03142c51520003803085141c030a02c03000c5804880040e044941030001e90701c4804c1c6100da03800007002552036001da80c0d000104210b0405407220743e6601e03941c4544106031003e5100740700400191400403007a1805200480800d8402c401d06041840401d0317001071089100784400402e1003130300005401120420b503a140702e0b064015407041070340100b00c1e00400038522560182d04c1c180700e00346102d0004c554146c2c4c54164400404070a100c180305032842160002100700c001011074140c0411240000d25428556100b0700c0038014118108914070b00621641046903410302c8414100b000c0d03100500400c0090340785823420543d407941d018088000c25089070020311645441190b4454807030280580342c1c0001c11518940a0f569400b19408550921907180701d00d010b90307504410754a07801c00300702805010b44003c2d07810311131110072882400340911000b001040300c50200d604083c82d14038008142c0748001000201e4034600505d8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 894268354 1250 894267104 894267107
    0xe130506010806310c0b07110306060a060c0f06020403080316032c03070b0f07260c03040c090c030506120c10052b02030402010e0306010617040804090203090c041a01 73
    0x91913000003010203808001c00c41c411155035940c030041c00b80c490359050308005085802400145545401001035003c690503602c149507817040166902500104450780401c01607101d004c0b80e01045100700110404201c107501e40d4001c0e604180c10540d144034001042c090076811041611840816900303041c007450054044643e00c458407200204180c2c0341d11041d00110380c0e001c0c02169801c80c0c0c05158095a414282c1c04440d404408550010101c0c1c8605c0c2f035034039031078842c807260840d010411415008569851481603120340000c2d01c01c0351803145400004c1010845802500c00301c414036a40002c440c0742c98400c1241507410300500c4070380354000101d58909502c03a034400300044005400c0c50390780c5e81b881203261f01c0c18402c0c50040c040e09840c1ca449105030310b183d0350021400349000b6a52844602018005c051b1201d4080c45924003254908a0600a12210780d0302c1da68000c3c01161007a00b0566940503100c180ea00440e00480c10750411040c50395540f4080c0315240008a20312802040100c00600 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 894269604 1250 894268354 894268381
    0xa021305030604150c0c0602030717180703171603030f0b0f090604091110270b030f102d1e0501031505211228090e130506010806 57
    0x409130100c80d10394a8000f01140502e100c0b03c801c5500c0002159245040080103200c101440100440754442c070000c1126000a18454510070403039001900310580741d1707035404001e02944002c600b5104c9007803004070780300c52068010004044c060b171000301c0c2510103640711804868a82d888240b28032890011504940c03195107444c0e1b0b100c0030a9400158400386c41c14801009000c50380700c01e07400203081001c2c807501a4000c1d4201003e1030400e0790703110702c18650558007403500920300503d0740c0c1040502c0010044010a1229a0880c01c3d030881407058035294103583c0319041030f6040719440c0d039240c02907000602c0c0d00c5800785401040741140b400e40d50203084140c080d4103809445001c0c100b680764520303500000ca84e40c114400900008200145c550034604040600c035000400c0d441e40d5004030345d0409880294007084a424504168481514040500f599080b001c040883c0d1000c10011400c0414207195590f130726805007082c0145441c6224880c64038524000050f001a80030b85c2000c0244091200c291a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 894270854 1250 894269604 894269633
    0x140d1206061220031306060e06010507030c1b030b0610031a0d020112140708180619090b09030d060b0f0301120807060207150e0105041203050a02120a021305030604 72
    0xc80c0464000520046801d8800d03030003030030314102d54000091008002d43c5d443d00718085071240034103203c00c43e41c0c2c070303c101000d440c1110000c0c0440ea082203003500185c8107140d120001071040340255200c56200c0c2420404020503001158103415a50034449645440c0c040f800c804c036464034060114041c480003683d080520324070410301841d03000300c84004681c046c49800c18140a6020100f28441455020036000003041e24200c0200b960040803603442c80000d41c0d501c0e010019480282119100d1a100b1000d19034440519030115644462610010f41d4440c1981c0c0205e902c1d20085440d50106502c071011118654080c800c04c0a00700f00002e0212506c0701600d046500c00040e80703244408905100c2c00740d12400c00001d107180e100143c06d0041011010790700300104c1c0003072020130511000c0f014140c02c03290203940103402c4040c0840c404e9030540c426041f180e48039000c0f20005d801c141001c107a0503c4c0c210182d808803110390b0040761071185400480000340c010003081b8020061030030a9100d400418440c00c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 894272104 1250 894270854 894270887
    0x7170a0903060501080f210f1207030c05210417030f0603161811210403030b09040305091005090a03050708060901050c071106091305060306070203092b140d120606 72
    0x101c00e4002da03089050140c401e80880c150230301d65160803505000010100c05c448000c00f09141400b06000188650290b800300b81201e460540512404402c0d182c1c4104000e02c122070400b01140782881c0c440300500618000d0440f035540d890765060640405052241641040c540411281810025030007540c01c00201c2d440c4030200094829044ad20b0341d00e442c80780d811460f0b507060840e903c00314040c0032010024801c80c0603540c00c0040400620410480541c01d86010380007c4060050110600c2d007040e40c0d9940c1d4140c0d0409500d403110b000045422038580e5403055413650400c02d4100200d060904c881c9a024010b00020842c601e0030040030a02c5018000020741001c144221400320b94440f0300c01c0b9400340f400141030b811070141c500250000b40000700c0701203000f80980b00204000c07600000a85c1e03800100107020450210102c04464458910b02e41c103802d520755800c510300d0100c3c0380341041c400c6d8201e0003000b4100c3d000303490340c5c0544440304005043c410949040410880c096104429400380f01d4030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 894273354 1250 894272104 894272143
    0x30a0f0213020309100e0118060f0603050d090602060a05010501021c02012901110a050d0302090a030b130b01150c150209032a061206040207170a0903060501080f 71
    0xa400840d1100c0714081101c0d160394400400c0c030020f11000a42180c0c1c12078805018080305425041807070036581c40403400d040d0301602d0001c000020700141c201d059090004a0300140d21a40c0392241403401c155041c0707034804200030400c14401d80d5814405d0704d0340a01c06481c00e0040c0c0d413500e00000e59441c0c04038603d1030460310001c03005480c54401c0d0000c80c1601805000810640c0d5a2044009100b2205800501003401030202c40080c00000c0707000184290011b0240c08030125040c401e801030f61001c01e0255000b40a018080002413100d0f140c907029284501091003c20a2481c10700d41b0008103801c12a009550640b481403150392080128030283d50101c43d90818500c081d91000c080e01800902980c10700400300c450b840640307245510100c480c1c0c0884c1c0c07100c1340400310092012500c1801402030100003040b0015083e800c5c107400070524140704668021081800400c6806c003500001c8000b400140860002c0050180c0c0d0300803140035184400c09000d03a080140400c680c0c0d41503407800010400710 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 894274604 1250 894273354 894273383
    0x9130c030c0c0506070516080703020c010e040516051804020c03130e040803010b390d030606080402120703020612060f0a21030e030709060f0801020f041a0405060f0c1b030a 76
    0x3c1f00418060095030100c0c440703480380200c0c030380a511501301014050002c2e049424450300d9103000d01405000e203000c550881002c845101e8221426405614082405c244020344940310752079610041c03003015035000c051a1100308844107400440500e6105050302007408040c0b0001c01e00d00c1c422281151034a00055a45207007410205004d240311680f0726031103a000010034149000480d600c440400e00000546143c40e45600f0194102d0310b880c084d0100080e9070790009801410a80c6003e9245c14507541190001c80e500c0e40043c01035884802e240000029071003d0115a0400410005410303804656154185080900c7c0700c00c81c0110343c21a0005080c14050481458092441c000c861003000d42a00c1c03405072903005080280c4564440c580f8a00c00409002841a8043c801c0d502c0b0700c0c1e203271400743d0703d0140b0700110403a041e11850001d1420b1503080100145075078443c0010320914502034000c0d52901001e05540d800e00091000480c507061415610132076a641c0401c040e00d42c1540305802003800303070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 894275854 1250 894274604 894274627
    0x70305041b080724020d0324090b01030b2d0301110a1107061706090a0f05130b0912041a0910091404050727030510200901020a0303020d0209130c030c0c05060705 71
    0xb500003540f003000230810000411050803179009018000b0003a00d060204416a00070302201049143c120040780810700d40c1e4016100c8004082201880024000700d02e050384d46000070126800f00c085c440205174600c0340640700400a0004100902d03030f50a10300030708400e00609417211080200501d1059090500103103150015900400054074401e0042129290041420380301d001e0822060720f4241c1e00e2400652140000628024256281c880c22424a85030540c003003680c1c0c036408c00707081c8906010b2240f4260764848100c51212049160780d0090701c1464103141c00d030303d05e820304c52882c0264104000c002c040c5400044c01802d00c10f0440b010402008030b107240c4204013407036410090131030007607101043e118200f907000842440c0020301902246107400100c0714440c811108500e0258004448030303400300e8043d038080d00303042d01064000351800003d0030000704616211048140c0071551105415445036062103034401c3c88045041502410300b42d0703100d040e03448034024103c03002c005000030201d0008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 894277104 1250 894275854 894275891
    0x1106250309060528110a03090804030f0b0604051503071403012003090f0a0b0a0c03270b0a18022b140d080609070305041b080724020d03 60
    0x1e81102e010449420061404040daa145120504e842035508044c00b11000841c03044c222140034503096035207482c901c11015800341105a000395140c4d0130620000000c50040b20000302c5081c86540126451f02e010820802100e8001d400c0152a02500d08070800d646c8000404100b66101c4132100e85680220303400090240a82e242e11010f208100035210600c40c550300301543c000c11b000300c1a68208000c64001c0d66032125200000303840c2e8074241010414040e1158010200025180b030701140b0240d600100c0300f0009030890030014154406034041c0103001705201600d0b000300e980f120500980029540240c18076150140103440b6a184441c104c403d0425004021001800c82c1c00040d408507003400d201c800203a020810070000e025080c08020114854a0509e2003440000d0820320542c4547d1001c07802041c000b00106e50107000829440c2c080c805014800006100000040014900300300403c4850401d10f02c1562051419210303c1d4601354000c604030b07011004604d000945102064260b8005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 894278354 1250 894277104 894277121
    0x20d0305061c0c090c03050108010f09030203030103060f060e090c01021606020a061d0d050d0506040501060c060506132c03040e04080a210b180402090c0715140103020111062503 78
    0x1061402c4550045c00350903402c840d04a50204008206c3d540da01103c00c01a41c006490040040e001000188005900e030790203240550941800001c0541d1100c4d00c13004820300903285015550301405216a00d9039041140000ca40301014500d6170031031900c40065070344c56060800505040e20740c460307082242d07042c0180c4100e0141c000308071451348501c40400362031030303100c2800c00c56998203007400142c0034285409104e049502c20703a40c032446d00085c1e0f141c1c40d004080c007629241c0c0c030001107c140c141504007030140c00510528042c0c202c5462010700f2158107441c040d4040e04030320390802c0c07008000740d8507100409540542c01c190007503502d5511080440704020560030002140349205220316440d4030f141c1c00020250002d55000c03030b140c04a020039420b4a48100c40081d80001250700282c034201c0d2407005017040d1885110981021961140000180d40003e03403034502d4078045400402c291360380039141100380340109018103400d00341500c85015542d064a002114088824000354840f0300c40d0b441080b8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 894279604 1250 894278354 894278369
    0xc0a05070506071707030c1b060213030803100504050c0f030912040923100501050c03072f090f16110319110f070504150f0803070201020d0305061c0c 66
    0x55450f0252018080f0b0501e6031201001151140010350f1083c0244601000b0030141d460b041c0d030600009128500305100c2c114115059a0207100842007801040e4080c4051071103609415128503160700c92000e030320880e601451083d424802408044413a0740229891184011541640c2e50313a4441701510b041c1c184131010802100025000660302c200380d00c00142412080c4080c641002c0c0c16251a030620416542100c041251803001c00031980208001c0000000d15016070707050807102e44800d40d080340c10007001d01100302c219401c00740c01481c1000000015030103c138411020304001c401c1545041000f00890180f51042d01d000c041e8074001d0701a501183d002100b200d9849200442c0390301d401d842001b500e03001c5252241c4040300d5003004509803402000e50401403030501d05e08002c110140a00a21005403a01c15aa010441405c0700b06107901038114900107560303d100074800246091030600c007001c01c144c40c2000340010340e40c5004000310040904145c004140203142080130080e03205911000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 894280854 1250 894279604 894279613
    0x40302090609040f051009051911040c020f1e0c03071a070204060506180a060e130f02040f0b04031e0c090f0b0402180a050402041a03100506030403050904230c0a050705 74
    0x1c9490b1121382048003914408c1c0b050b108d07084601702000a8040d40c00700000c0810800c6e0641521a0070a03034406c00340d02031144110341c5082c506054550a015603404002c10802d1403e40d015080082000614a1004d050b40100700861030311014410700c100c0c001804084002c0000c0b1001996615003000001e04001040030755108010340c0051040c52208c001030380240c40307907200040c080303004d441e80c1048038801400100610f6034038808400188001603180034080e501b8840403954000690f400c60143c4824000b1aa89070b08504080c2007880700c4980107000b2900300118500000d0340c20701c80354103c4102610200c2d10000000e200e9001c0c0c4498980307180c02520100c1e80c1041a20048041c18800c030742502c5e00700ea59603d501c28041070744628021410040901248184c40809140080d03901800180c003070038034552100001040c0d50310540d003c1e0006803021a41d14410314282c4200224487c40550014030b030781d2000b07120b030105d40b401040714910303081c0400d090344243d01a2088610440e4006c0554 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 894282104 1250 894280854 894280873
    0x1b0f03050f0c1e0d05180c041116322802101b08042102090f041a0a0f06050d0c0b0a03060803040f170d1e090e0a1d03040302090609040f05 61
    0x1b607160780391030403150b01c603091494240742403e1080da44c0c10a030050b261441d10501f004540250748103041e0880c3c10a501d01c01016084080c01110381c8110301004d02c890b422003440c0344070751034000101700c42c0e0f451051121800094034240944080c40c01da06031181c00001c00b00d4081a80c904c45002e019804070000b07000b01004102544d4024420340b402100c400140c0c0000400c000076010700a44d009420440c100040b620040802c46240d52180c843e0498426010404410b428200c400359072541460740c448a100060207524041c910140c141620042d50180150711050a500b05e544618030701c031031740041c051942911a0308010050b02c0040100c1c0c4d521940c500d10180b0b2010306205941e40c081d04100c0c0020200000301c4e8011146030590703100d518010501091450102005442805200c409180000ca1031500e0b8101803042500f06400a80c080702c0c03030102c61104074246d000300070385e800c10082400143e80e1900c004d50810802c1e10580307003503907070f500c0c00100c035101c030000c0a4050710841818 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 894283354 1250 894282104 894282121
    0xc050607030f030c090e0f0c1b06011401050f0714070b120f10030c0603270b090601052b061805030a1409180403031b0f03050f0c1e0d05 60
    0x4a020105181d0b010400403040304c004a4001020380105014803181c01c001c100e42149070218542c000f41d91040c42071030b001001001c035046003000c1d45480400d40013480108140407540f408100c00642c2800c040c1e00d803078500c141d20710051143d080010040d4002ea201c0320110703c81044160003810401c04002e50711308500000411204003202c0c480c1001c4c40b84000a202001c05040b01da007241d51041012180030305010080c2c01400100b0310004207220b44d0492007000581004500380c09034017503540381d4003d091200710513081810581050340074210882c180d095044d5400d07600650451032101502c90a4650701c0c0c806c000d440342c031002901000e00b03a000581071110110081c10501115100c2d01e600340da20f502403102c3ca004901d06142c0c00110700340780409255404589950180c840e1800244800742108000c0300e5520754402100000d02c0801441451601440341d40d8009044100740f03c81840e006804075490310541011014a00c001d513403000c00122040250382e000c000241c800d10041c13820002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 894284604 1250 894283354 894283367
    0x19030b011805060f0609090a0b0a0b09010e01020d0f1d150c10090506040b0a0f090b16050903122a011509020702030c04051306020c0c0f010908060f040c05060703 71
    0x1c45002d00d0640480c1c1030740380420300c2c1040e001001c0c0106050080700e604015041100404458109403148840c141d20f5407400d00d40c0d00a09940070003513450708441c42c001460400003856071410341d404030002901c41504070b4080c070311100040c501145075400c0040781200780382c144604560400c14200151881c6206540a0000c900240c0c00301d400e140411030040050301c001100c0030300300e90082008900400e1202c890745502070050f44c07002c0380111012071b0300c1c011251414420b4a60095803014011001d008841d010748803501440c1c050b081440000000303440e0354909066601d02c407070000d66049079681c04035a0314501c01140075002042c5000e419000d000e4482c0020542d00b0f040381500108450b14988251100749401a000b0403205003024140030041034040d0184290141715000303240051030301d0000700f20942c000b202406442c0d45800c2803004022040c43e6441c1402000c2105000e007800020714550700107906821220162a907040250020320f0980151380c0102c1c00040440c20f0581018 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 894285854 1250 894284604 894284639
    0x504140703050c03071403250c0506060604380714060c2a0304120606050f040b030d03020a1e0c0203070608010609060c0507080a1506081b19030b01 65
    0xc40500865542544043c100e100c01c548070408901300413032075450400c0b0318000d198407007020316505041081c08200403481c2d0295001b1a0000b0342056103d004000e002d201c116003200060301c400703042609000903c140c0b030404172031603e503d0000d000007000264141d41080511242c01c1070040d5103c40c142030103907119031ba14282000600c81c103c086034000e00c1240480c0c14851100705410a9104001c0c110a2800350740d08103010548820f001c042402d101c4040442c6542d0b110707040005110303141c0b1013070007544070003201c3c131a10031450007400034051f84001c16081591402071174016036074441c81200307469038a180701d15412003d6103c11061006a044910300400034000c404031540242c0e215030454900b1400d01940700014260307402000114015860303400d20030300c19410380c0c40207600c9154903450203943d100b068031807006031200200c8039511441448054140340c0040c0800113900c801f041d000008500c85a801110008024400340820100b040043d43e48000c80f1022941c1d02c040c80ba00d03421071070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 894287104 1250 894285854 894285857
    0x12912100f06020a020d021207030203061014040b03060408130f0f0801050610090b0721030c09060912030c050f1b0a0e040c030807031112180303090d0b06040605041407 74
    0x1800081101400010750013000d650085c410300e10301113a40e0a200e002d40c205140001c040c450070102000583e400d03c03085102d098407002070b1096500d401840c101e07040410400d0b6001e1454404e0105051b00e000c00c0380b41d8441e8200e014199203a94a0f238842114800903485410f00c05200c41e030114107254011210400c50362020000d001c5500c1790001c0003041c039001628035002c10f000700420801c4c140d411b4003410000d406100101c4445440c101911400300a2103556000030790380303000e21100103801c40603078009800c2e03030306d00381c40000d0070301240310600300000714042c040c0540d4100c089c041210810407161079103041015107880c081c41c288112100000200164445d8100fa00d02290b1058495113030340c46640c00111105000745551210380e01c40e801003c040d8100020150340c868004400c0040b10b5000c6827a500c8907075200c03400c040704000c1c00da0f1840500c3c030941003040300c2d01c0180e9a081c1069035250f000407101c10252640d00004008010320f61119030401c2c20900c01d03120340403101c1c41c00c502c5500329 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 894288354 1250 894287104 894287129
    0x30f0b0708010b09030a0b060d02040f0b031c08012303030c010f06120b010e0405010b03121c020309031c06081005060a09050c03040609030c0c12150501291210 70
    0x31540400c3e014012041165010b90220842d60f0200d040c120f00d030703030308824060030001103000650046000d462418001203640394440c21381044c203041c00c201c0f0039001d0142442c08441c4040004c00101204010322804c03410301d006400e4030548d1000009008218840141107913a983d560b204154060100c00e10028112440c010001502c40a2103084034002c503030010304103840340c0c00d140d84000184006402943d40d036585031901d00d0036440c00c01085405a9000c600703030f9280d035a4035004101415402105c825241e00510074080d061400009a0b020800744100c2e2211201c006030b0100001d040c00c1d0301070803c6215601d58030951203031507800300c2c0c02504151190000bc82d1603040a00c00d0b82d4054807503103c160b4007040090040f69481e480511420b200e450440f03000c03071460301c07821120b03d0241c0050034083d000803200340c01c0011409510001c00040d203030900003036140a8014054580c3d820450382c0150b0703220341d06940e0038440d404803407101d07240d002d08012030304068030918144a4140a1a00003000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 894289604 1250 894288354 894288359
    0x1d040516030e01020910080411040204080a0b0a0c0c1101021c09081b0a05012601030803090607030608070b130f080708060709030b0105130f0908130e0c03040b060a030f0b070801 78
    0xb0107000300c80300c000c006400c801c41d5240300342c000c44490350003d006480b000800b90441009903101c0c0000d10003400c039480240b0500c0000d080c080350025024224164041c940141c5c0d10940745c001160500080c1c002c00b15104078a80000140e04080220784580200d00c1ca00c0f020688454102150600382e4a100b001c5544100954055003681c58502865941c001d020343c10410256110303480c0c250209a0746000d13400300a11010446040f100203820440304403c002c82048691a02001480da1000d800d107010f0117460728040c01c0c581c940b9158081c0202241002601d000c2c02043c0c4206c1c0d800402e030002c541c0340002d50b1010401e4880f502802411013601484000c102054860000c10056940040300ca022a03480e09042065a030b0340d070301240e000c1980b03500001c40c109002c0e224102c40e80d8003076815950b940c51109003d14031000c0c103800078034511120310240100300c41c84030180c0707500552113440c1d0012602c405c4009408600c55034002082002d2403070444d002c104191807080d010700c0041d2203d05550742c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 894290854 1250 894289604 894289631
    0x110a0b1618030c0504180506040302011a0d150e03070506091c050a090909030e1c1e050a06020306031204031b0b0a020c0f21061b13061d04051603 64
    0x550348070103440c4000f501c400b403100d86055071180c100b103000d08181240d1240e10340e5031380c2d0510f8811901900583d41d1400c410f005040100c2c02100910700c22034010441101554414080035124860303903a85503900c1c550038006500070400c45404075007110484400d880c05a41c40d542e107410500d100b01c44100147e00c01810740b4028400d58640e44015204d40f100203060120407801800162819810030448441d09441511241031603513001180c000b00850001080c18507514445040e08400d01301920460481c012401c04a40c54048a83c801c0015a40e83c6844000030320f800c800304261580040d00240000030042409410111034580c4034010740307030382d50b907403091591809003101410150b0481d22440d011440c02c0c083c0c074030407010018aa000000c29100541104040406010619034080014050b850204940c541341c03071541e05c12407901c2c00e0024401d1141e40710741c600c00d80c400d00181d100d1002e03d0b0004014524010304024000f000280742600c2e0120f02942200329080101e445d01480c0100071 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 894292104 1250 894290854 894290897
    0xc0c010509010207181d3a110a02030d050d0c1704020d1a01060903060b0307050f09040303020d0203071d0907050a1b1b0513061203110a0b16 62
    0x34181600079155191134000300c0356481c000b4001c0c1c5c3c0c6444d560780741030000291004110780f409012520041c243c4014040003149031100da40314001c031400003010010482c0980d580f00800e807038418a40030140d06240c40b030036841c08070303008002503140c01000035040e149075002e8050b0400402c1d8100902800214810543d08103a920301e402d00180b4620780040c0240c1801c2100c03405091042d1003e961007181c064003441c09142c00c0c3c02560018840f20780c10000d00445005d88041c80c101100a050030358980400100402c1c019a10030340644410400142418004d0741aa860045103000039540d82c60241801840710421000c81240010f07207001e8104142000340045110303003c00c0d01c0d01440c11021180a51b00340c0c03082c002d1030700018158203882000900c514a044141103051410001442c24101006110f6180b545564600c80ca094410800072011035401084241c01d800e200c02e00d41c1c0c070070300302e1400c00f141d41001410180d940000c3c01914020f10a0345108800d040d900c01a211581d840a040a07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 894293354 1250 894292104 894292117
    0x304030f090f050d0f1401061502211e0d0c200615042c07210519060603060504111507080915040812042606150a05030a080c0c0105 58
    0x324403078404903030000d0407450161010502070780441b1000c4800002590945149400201d0400c40400158043c650100440018982e202c0d0407245da04c5410350b0382142501400c8244a200c00140040c6039076425040d00f194200840c1007414410110400000751851032800b41a9403180d00c848a0b03200b00d4680814900e00914094581e10608110b8404001c090518002500200701080c50404500e072101030518410141d0700c005001c40500c4d10780c422040044201040c4100c0c100d08102000181d40418900c0e021480342c2591591024030b820190300902894000034140c80c98141070109002158401c005150f104442140503100300d88644041805180301c020704046060203013818625080e10f0400039150042e203003d007002d0380c0e11142490000d80c00c48502d0318180010b818852078501902070703448180c91107880d004604021310340c281c0c1e0310300c01003424000d108062510710056681070341c801e00902c401411190095180c0c00d04406550110100045074070904c16449050b501820a6581 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 894294604 1250 894293354 894293359
    0x30115050c0c0f2205040c050f060403061a090702030c16290c0d0906020d0203040e010b0c0c0613090501050d02031c11060f1602010603080d1d01020304030f090f05 72
    0x195200d9090030310005031400350f8650381c031604024101941041425844c010f42400e0a000315842c282410280e038091160f40106000d07001001c00d1744002c0d25054100c40450741d210303200041030500419003802c08100400e1041d404523900080c00b030599400005401d0303000409040c0e0345000e012452845251400d441552410000d000002c1e80008810008905100d04080300070b00d4507a118802d242401c8803000c1070004913090340410b200541e810072000b00540024002185040d0400d002c00d10018014459904441c00c000341100402800b0b01048110400c082c000350b8550b91002c403c1c54403024140501c40200307150000000b500e1030010786060781c2680243c0900180440006100c119040018110082c846180c165601102c07042280724807034410301c3c0760408c0c181400980301201850643d1001d00f1681008014400300c0c0901c400c60b0503e8041000000ea503284901c1d500e60030401030301c0300b41c031154408800c00040c99000140e0103080d40c845e40e22040c0b0103440b5a20201c09820f580502074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 894295854 1250 894294604 894294613
    0x117010e0606011b020a06050705071403100e1c030606110a0f0308070c1e0309120b0f150306010e0115090803040b0a12091202010b0a060215130512030115050c 70
    0x1078055001d0f44c1c400c407518202080300c2d1410f90040d0041082140e042d401080001c40000b9083c1c2842418001c100151011400040c04207031820300003560b5050480230400e1640c0c0d245401b08100400b00000844150840c00718188003c0074000500245180e103d1400814005113415401c2800403c071520495806140360b0102c800702e460496000800904c1c0382c041c005100c1040000c5101d811800c40e1140d0705500042d541c000501d030003021032045500103003c0b00c20040310000003c0c0e88440160380031068106451032550345c2607003d5980e205101141e9014040c060020541440d1006414140c0740d80e011025261b0034003150403205c605040c801c100380b03500140401d002c200c405100421861000d850550704e5170018103000b074112115003108a500696084200064640a008103401c2820803501d030341c1242d24049001c0d4888101c82c0c041422b0003400000188408400300d8202a2290000101c1d030405010136030498040c0d10038041c01d808881402e00c5070b801c09101c2c0040700c003118140303000303007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 894297104 1250 894295854 894295861
    0x61e090c031c0e0d060b0a1d040b04020f0d0b18033a0f0f2405041113080d080609010312050c120a0504180926071a0117010e06 56
    0x62240000d824038000800c0300c5054444184c2d6900740d00b02c24402d00034000003030081d03504010000c14824641c1b20040158016580d0b14154541081c07c56006070407011503a010760b680c0c0700084880f407900117240d90044520501a0610a0f100403c0b80300710a22002c140b201444610825901e000e8040781c80c0001d00c1c1080044548100312514541115071800e800043c030200444110541e4059003000c0605a941c1040d48041e0105005801502080209082c1d81d51039004284000f103420b402518051600c81c4a030f82e01803101102111002d075885120082c3c06604c4080e246d4503038107000e410900090041c00450b4152826014190403603a0096440130750342c1000c0e0b010f542507044001041050b015510030700d01035582000081c41245259034500c0e654a04202080903010b00300c0d40d040e440c151608841c5000144001d1080ba00001d084c00d001e040c00c5132640c202d206902c2030800060903806c1885e80401c3c01c45840c12014143c414100c040f00755903540c1503405080b01c1e4482c00e0509940e0041010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 894298354 1250 894297104 894297133
    0x150f1e090518070b03220302010e03030a1418070b0a0215130c060e030c040902061909090f090f240213050f0301020a0815060408070e040203010e0a030507020120061e090c03 76
    0xf02100c07d11900000c2884145000c42c5030550308122903245855450f0b11303120f111000c59074105d61740400c0465034484a41001c0700f81076918132180c0a005d0803450006048203031607000300840355044400904d0449645014003d600d4201341d102c5045800801c002000314216000711461130001e4405002010010100c404000c080e0040345000e036004502006101c000b00301c4078041400e05500360300c580200c1c915082035174085491002c0142d8500d490005068001640480c0c00203065800a00c1761203101d05902c101d690760003901245402803840091400301a2107400408400c03110101c0d50b40d102da01240090500703038880c584043c0001003000c0300094840842c120f20250b00c503000303800a81015140c0c07205514113101c40e040b01460114080800003146000d0154450604c8a5000740911480c0c60b134002e0114010500001e0600083c1040000c004002000b944e03034900083c4200c401c103045c90b2000640c10203805410341030740c2480d94001003001c40d0008030001c1e01c15001d0000d0044140e204203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 894299604 1250 894298354 894298411
    0xa140718020319020a020d0915170714070b0105040506041b230a021606050c0304060809150109050403032f03060a0510050a0201150f1e090518070b03 66
    0x40101c1880f45442091072807055480504520180c07034000f40451500070b030000e032a04205a00198240d070103801480807156000c15482e520805209800340c03aa00c0300a130544003200c07890200604400c0119a840500205887c814103c0341c080c3e604000c15103a4806010950f40c03150141000e20f05c880441406140c42800082980303521082c90243c01da0000030b01040c0340d4411100700b00180d00c036140c06444100c0d1194280001c002c603080c01441c02040e074001648034041c5114078020b0000d01800600340745018005010180b070f0821081c20703690784a054840080609590a40000740f403c0c0d4883c10100c560b4052842e581c20405450786550801c0700907a41a601c020409a0401e500c075800250545801c000301e0360b51111902c600d07031554001e040003421200312513000c05401012040410001941030080000da96143d031500c815089100003c1444442e2a0301c0600e103945440104030303003c0502100b50840c241b240064a0440d50380d41440d01690000f5506074407405144203110302100020326 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 894300854 1250 894299604 894299611
    0xa080625030b010e010c030909021c061401170405070e0703020a0e0d0209150607060c0309050609010507090501111608100c0504080618100c0509040507030c0e120313080a1407180203 80
    0x24023504900e07160400308082e6000841842400b50b2840d804560a0300345d8058a0050300d1098405042200d00200080241112485c0c0c50110b2010130042010310605000b800c0190005107280e07091410901d00040081d03020f0101d00000600b652801c2040d460722011281c2490340080004a2503140c02c08500104030b0003d02e141d5101c0403c001280019980b03005484112406450010b84000c050402c06c7c2440d03801000c00d12143d00d4a0104052290020301c050140d1303000707107040404150f10481c6503142800403c100401e000c9190303000200b181e0300141030620002640c1d818030594001c0d1405813207501a6000310705441c0c100301d000880d140300c90250f64210b4521007041b41c4080401d0b50426040300d1180c20200c0004000045240711404c2074065250000c20500d000c0140c0c10980500405100d1031000040c032401210900c150641d40c10410b94610320202c0b5054a905a69044102c1e42c405441004030340010740141c925000c0e100110b41c540454206503d400e84a94039100d8500c002d40c0010b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 894302104 1250 894300854 894300857
    0x1203020d180f0b13080f0306220606110f1b0402040b03012c010806040b0405071a030906010b03010e1503031e0d0608010509030d05060a080625030b010e010c03 70
    0xc1c10010308804010889202482c020440c14000c40060700b000248004000c2150302e030444000c2d80c140014041c402152407800d68044c5070350f103e80703443c00054018286216189110744418100740a943e11a030300c0201200c1d920384900c000301c8000e0f101c00391030380b04850302d031110707600841e4140481462107000526100390060005150a403521402811904280c00030480d40d042d240d142d20181300d02c0040b070b41c400c00c0b4841045403e90301d068662540c9480003880208070900010202c0e041120030001c0d0f401410100d48248100c03003104011000f543c1048910400600c180d5000160f9101c800b011241aa00d04103280d10b03e45d0303201c98124445a94000b4041c1c0c0504c8100415501421200140005a00c400c40e8580d41c1c0e10009030f16200b130310709a40003140564501001e014800d1000401c440034120200804100b5561707046c0090900c0703101e175000006a01510040001142071038408294889100701040c1030b40c00001000c40851b100119a01e01199100c40f0640003503019900c906140f0388603 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 894303354 1250 894302104 894302111
    0x90c040e0304090501091b120e0709091e030c0813030c0f030620030109111603050c190f022101060b090406050303121f0812071703041203020d 63
    0x850222121485494050342002c1001d00c244103d40c05550b004001e450f2007031001800108800003512011803039881441094040724440d0300b940d401024100c2e4074102500d801950341c140003006802c0c4840d0454401050305040c03001c1c200000f690204082d0103a4403125100e07102e45d01c03032155030f1024045225111b0805000000900c2014018019100b0403911045183c030310701c1c3c8030040d00c1100c1140052038000c00223400915101c1c3d8192030440740494400300d89007021011160381440741848042c122810b0450070b1090540200042503188400412030f013011500c00e25100c5100600d20b402000c0c84503170085c030400762420b0300001420340c42d50291104c00c8001f034400e9074211142603006420300320b00412200c5440c5854803410005100940c0a189050413028070074420000c0100402e05490b0810940c1101140300c0c00d01002411020048401c0c0310710024401105820910040340c010b0b54072aa02c00d004000002600d0107198043c2801003103181c81030096020750040411540802c0c1d5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 894304604 1250 894303354 894303373
    0xa03180507081b0402030411040b04091502090909070303020d0c0c05030d1718060105040e0c03060103060603020f2e11100615030203090d05090a030b0c0d0c030c0e040509 75
    0x6051201070014400c100c02003070300000020303000711401e52001d03410b0b10076803040c0b04200104100600d142c408060444000404e05c4201c000a0010207011034040c20003428110410b00c00f030200d500414070310808969000c041d55908010319a200400c4c040100144c20012201030400c1c0900d410806c4c00340f01755441c3e13400c580c070360002c24a082070f0010b0382d01c0003c41d4002d401c4200c100c2881e01c1130f0419030702c04412401d10340400b1850350700c42040c8141800703181d6903140720500f100b05000082e0b090308020f05503113003540c1da030400301c010b00410f000c1644605642114003038140361440100310224943c81c840d10420711011205400d00b485d14143c0710500205410103c4014030622114001402102c0002074460404481900d41c44144002409162040051000076071000820440c620818a0310a5503403a1000102e40012090b41c00140814010000c2c000c441320104094140d0102c03c1000b000040c100510890640b900900010041501c0d078810301030f1402c041d0403883d8020040003c90344482c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 894305854 1250 894304604 894304613
    0x303140d06180b0f09071b0804030b19060504060608040f0203121c0f05040b01050d2a15030903050313030309021306030308130203030415021e0c030705150a0318 71
    0x290014403200c5015542c100c0c103183c918001020358404803041e140b00c1500e2400c944003900c440c4c60001066a00360140d0108000c11100740c0031100a140c3c4588564141d007450301c04c2840f0006211100c1481505211000c24070f418a8030034807003118907035a40d108994603152503101484c400304070266090b00a08400c0c4a0301c0407410000c145401000d42d8000300d41048040800884246012801807203041809020209550000d40d9056400032078410344448a03602d03002041d500c2c810403504150800c0c5010b00d1031490040c1080084980910030031090b2900024118200c072903201c0c006022601c140003284041194040205209100c2d040015a400c825000112080c80c58980e00e880c40b52602414400c00d0344c00751400f9040702c000010b04040c0c2206078000f03034681c06103000380441d4031051200c0460a9108100c098030404610282c40002d00040b18400c2d2071740d0300c0710b041c0d078001d1242110029203410403404c6002c4038900f02907040d0401c03900301412400f0300f0000304024015012440c0e10381c0440c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 894307104 1250 894305854 894305879
    0x31b12010b03150303030114060c0313060807031d0a08160507090501080c010c030e0405042306090d0f0c080d1d0705090a050705090d1b030809030f070303140d06 71
    0x81c1242050581c5034681407401001940c18400558060f400910041002c112011800e0303140800072920380d511109001c29891550296626100c52a90b110a0002e0850303009100300e80a442195014808600030310a12800c8138195110444207502c40f00f401e6011503281c0000c0c0000286c0c418101d103d42820b61540380c5012055000311a196980f50700401c8a88010441c400d8440401e0030484503060780754401520070000c0800c0680501d0700d03000000c1c00c000300014050402c1c2443e01c440300d2480484501940c0c0c540c3c00311040e1074103101c0d0482400c01c050151a0100351150990341c3c0b15aa0b044035a07a44509030800581c081e40c041c1c80703000030381c451407039082004100304018004042051401c01001501a0040c04050215280c0030600c6030700307680501114040c540a40d00c41c00c45101514000c3e0a82e1b9103000b103502000c025990210401024100610a4030812030840c7c0300b811011813105e840d2641d600c070040100381902c07004411347c40b194003d000310548100c400202150388040746c01c00c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 894308354 1250 894307104 894307109
    0x21100801020417070f0b0f0d09120c030806030c0a051e040216380405150a020d110c07060807120614091b16020409080c06040302070602030f031b1201 66
    0x101c46034144166807400c0400c02400102540c045210401b1300d050900c2d40d4030b214216141103541800a00c4404115003504801c00e0207a0020b61010b0001c400000102038440c41d4404a001030540404a1980e01d0005402c2c0c00c40c2d04004e10303c007101850031040049407070035801d09142440c3c250114000c1c0c0d54451000d0f0031110104045148500480e207412596020303164500c0301090031400b03224038040c1e03414045414001108070700c000c13941c4490609038035040c1c1714041c100900e03c4000401039070384001e030050a03c2500407002030012514000f0280054041d4501580351381c0d0280d841004603034400c0c0500d0743c04c0003a82c01c2c4030307244841c14160035095a54070f0300140c103409020702407512581024440f20b0740c41805c080910188001a02c81d0a4440c0b0a004d50814500c3d200d4005100795550b43e880840303a00e0340041c5c0142daa0207007060b0152601000c550035005400b80000010340b071800402169514020503080519558442c42c8a2030780a069501c00701c1300200c1480b80710304160740440031501 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 894309604 1250 894308354 894308369
    0xf0705010c020307030c060807020d080c0d2403060b1c0b07030903110303090d0f031803030218090114040606050a0509010f09031a0901050106020a02030c040b0f10030f0f02211008010204 82
    0x230246440302019103081106002d642c2044040410010350110120035181800045140414016015600c0005803200030818a0001440c902c001040200310b0788161401c0805481c2904115071302c0b04000400c03c0d13401c40150040703011000051203580b0a901106480c2d201e400c1041c2c59440703403202145550022980940c15a1140842c100700e2900046252880242846c0601c00107440d001c0c003c8025924101c010140350300800c3c00c001d80341d103990903844200740c00b40c0340c1005503075568001a10218007030041401a880c240002c030b078852082c003c03258510403e0300c403e464000e851740115011071051103c8820003000a40100c00a00c404144860784003044030004130f5410701c50030060858506a020100790751112020328016100400c024000706421940000c1202188010038078600320005425400700781d00c10106a90798256224a406401c110703001c00c07081000a0500c0300300d11541c01e07040c04850510600501c001442010194000981c100c815019a40e0f40314103826a08117410669 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 894310854 1250 894309604 894309617
    0x80318240c240415090c080a08071a100e0417070b0402030d0912031101110a02060405060114060403140a050615150a0801050d0303021903020a110f0705010c020307030c06 75
    0x201e8a222004111109068552070b8015600705a5142c2c1c694038030280004c0c050715102c0c0048400e00014440314001054002c4c2601e40c1c7c69014500b4544607409803400b2079080700c120700121086136100075020b1003130714000c25a00f0b8132030400b24100035144000380110307a003180a1008408509041c400f0b00200351151801460703d0400b441018240000340d140d55007002426841089a05a9a04620101c41c4c02d8106082c0c4021205504d03400340c8100d000d40501c0c80070009000d04400e50000f12507204502440a5030466601c034454550b1302440d065445512400a0006101150340c3c004181d18003103500d011185103600c0ea03610760b410441c04503284070290448c00d06840c03460400008031210032030f000190900c6c15030b4202000d4814a030602a40c2d019140b261011810140207a040780d18041c0c0d80c04421100700c0c041c81c4010040d50120035040c0002d00302c0d0fa08503803511000295120300b940010040c00b0b4240c200801102d9400c0f20880070307a8940300b0040c3c00008a1a0b40540c000a05040da42c3c50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 894312104 1250 894310854 894310873
    0x19170a0905090a050421031503030c03110111070602180909060105150f12040311010f060f05010f12050604110f040302030c06130303140c0f01090c080318240c 70
    0x30144001c001d00180c03180b414542017000281104000071000303000e0384111040d44003141c20803401003004002d010b4080d440700700c01009040c0c001d030711408410300ca40e55040c000f0b41003001246c01c2e0740d028152520010301c140b05803000240c454010b41081c1381c045008210424000000801954040c2ca13004542c0d004803005210908204408505418071542200d2404045800c4201a8402c01f2504650300380c19601040816118100210211511000078040b915202410b94000c014502c18000895649080019294010b20b113041060400b0346600303428092621011001c1c103802422168029a107800700c1d030301c1d4041d02c030141c5403010000401302d4886096105241c40c00d8002424030f8482d038030911904120804c140c03800016030758507241050b4003030704444054001d802002180c02c01030181045840c182c040561128241502030220a000d080d034602110744c0324442d034907020390310713403a075030f140d00080d0038054810181c0c8020180d4441d0804c1441c2a0b0507150703000030850302d44942005206 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 894313354 1250 894312104 894312109
    0x3020f0c100b130603020d12032903010c0c0203100f06081005040c0b030127090b01081501050a1401050c07030242031306060e07091d060319170a0905 66
    0x440b0010b03001c000802044c2d055400003495940790798001409034111a01c0ca0408034460380211460f242c44005000c0b481c2e41a518450304080c0c5454030600a42c80c007007442810500c06d603c05c14503550060007400f01002c41c20084030150200742910014252940b5002681401c00c008407c11303131050120024681c1090329040d100c01040c0c2d40a284c0c0f8050070700050104e42c40c1c00c0711045481c000e10320104030010f079940b0314030090310b656100904109074a40000418500205a0b80310880014840e012140e80303440801c00c94418900616100244644c3c84480d6940503038020030030b01c01c0c41c1c2c003102c2e00560342ea400035940c084c2400880d00000c1c1c42241a111800c6003104182c4031000e6405c001c4100001c0300c2d40c078621400000e004110614400031520140101c1e035006801800480640c44018a42000003502a600f64810480c1c00410407900c10300744000c2241caa0301541008010300304203206410a030100004803001962800303490341c81c440c1e42404003401032038a580355451b130242403482c0204 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 894314604 1250 894313354 894313369
    0x12090b0108030a14031608090a0611040501020123070e0f10050c0d0e060a030b06070c06020c030c0102070e1f0b0a1d010314010314010e03340305070303020f0c100b 72
    0x1350042085824818001808500810b440c0940d4252800c90007a980d21741105252078050540904004c0c58001001c0f0350084400c0180309442082e0000d20544095511070400d0700a4000b804125038081d00c0810910741c030400f09400c2110008101c001d10548410001d58004022400c100200c1d00008d00480c18090900c889110003015060900101c880074021030218400c0f5200c40c01050f554426040c011b9851034140c1d5291904040c600340481c1e150070000c0c1d50740e80300d8a0200c0c4070303100e080c40d82803180d0f100044400c152509036842285a840c0c1450907030000c100e940c2c402d02c0081c3e044401180845001000d8240d41c08155074041d0704810308130351072008114880103141050304000d0a15111540082c00744e04481d4032247c6551840384800d1611300503c00b60444082601001074004d82c0340250718082d0360080d103100580c1590002001c50109030200f03980c001804a0030500600c40803034002d5010740385940803440780e285040703406290141820310006808004503a035144072822800c2244 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 894315854 1250 894314604 894314627
    0x18020c1005040308070807020303010905070c0807030206010e1506071203090b0a0603030e010807231306021b03010509120c2e05010605040b180303040b1c0513020f0112090b0108030a 80
    0xc1c90001b50a1420009480344014000d80b250180c4900200c0c264a204503500702816401c81c6140e91141244c4c07074002c0d210b600070300c501c6220401400218200e1484d56a600303905031801064036241020315030784c030140050501c0128045c50b40c1c17400741c480401c0640501c01c0c03140907846000207149080d071a0140c0041e10103c10b40d4108445081000301c02c40c0c019040c001c061039035420985000c070f2400624203080c450070841c2c0813409005000014102d0300041d1520789245540e00c1ca44c3c0c00c80301c142c00d00d802c0b030788112814a0141d100f00b010150740c01070180101542c0a080d02603500c844030030000325200c14111038112020110b025040004541a80305590245c2550b20f4070500e468903000f110b031064000e0b4840381000e081110181186990104101c40051050140840d103c1c000c4141d0490289070706500c509820703013410000384840c0c0c3c070714100605a40c1d00400c074509001005004440c80d100012043c100d0558a810010202d49071440240c000e201340401540d40b003a50001c000c00b000d0700032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 894317104 1250 894315854 894315857
    0x13031205030c1204020d060f140112020f011b020612070f022109010c060e0a2001120e030d2c0c061e0d020414010905030a0c18020c100504030807 64
    0x10300c284450511050704a50942d502854000a04d44841c0002080543d01440c003c05031454800811a802e0b200c0d0451224603508044ca0400c1381e9842d09624202c400b070540c025480540c15000340b00303a600030042e003107085540306500450243d03590b006c00c60030351001a005110701040c000b00144198450107200f003070040351019011036400a600e00142448043c02500420700100e410001030344164814a2041d030051020300c80011050001611040319a0007640d290101c031070004000a001003041d000140103030350300041c0811424450000708a10b50001600d802304008940001400340506422a041c00c0c0301044841c00104c82100e401c0c0c1d588a80b00715681003004120196620841a00d4485064940203051044c1d80080298540b050300c0803100d51601c0410086540c12580070102080e0744280c82c0d4a03426a1903808059071196460801461044501d005200440c7c040154800d07155501c10050306005401890070305042e628410306404070b654004002c1030540c090019908040b90303 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 894318354 1250 894317104 894317107
    0x302040f0b12060108150301051f050a0e07051b0109030e190e0109093201050c09091503010f091407050409030f2d050c0c03010b060d0b1513031205 65
    0x1400080c2c148500014282410311407010300180c3c03144144109010324000080013000586080e215000c0108250090032804800070200031440303003028025602540c00100c54201c840d030b502001124940d010083c1d640581d02c3c1420004080c000074041d00d22203510948441c40002500750038450082503032032404268004c1c103801044a06400344c1a41d05403a80e5100c041103c1119051910303118039049032200310b162012240034100e4007044212007640083c3d0b0002c0c00ba50300c55003603400090081d5695245c0c000503030f501140d004455218a8140100c01400101c0d41500d042e1101040740c00c026001c0e00c0081407002c018000340424051038000d044111801c00050f582c2c0e440003000042c0c010902014001168221500c04510800c50544200290308003140c581400e41c0041141d0088030000d861440349051000003490107016081c44070b80042c00c03481c00c1a400c00000c0004d018202c3e20950841c461000280390703c0c010703900500d050802a07824445061070346c5000b0b0100140100b8942c10440e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 894319604 1250 894318354 894318367
    0x2104151a131a04180f0c03140601080610050f09042409020a0503210c10060303030b03100e1c14030106030c080c030f061002030c1f0e07080a080a02030c0d0302040f0b 73
    0x42484c00218456040341c070300d00c1488100c0c0f0b01000c0540c00c07070700702901d20300041f0400451901e00040b014140e580c10801d071081a101c8000900002c2d0150007502c1c2c0c00140014545080d007410081554080e0180f00804c810500c0002090f072140a0310340c12031001341d11855440194209101c010004003000d400500c1d480c0b440501c51451200303000000c5100207400188000c814504200400c826002d8200400005560313140140003054980c0800c2e000780605440e10800e12040d10420341c005125101605845240740c07a42e10040e80200808400c6c8809610f2450004c407140f00518080c18181e10001484001e0740405414200001c0075903030030305010010481091109140e281d04030400f81da038000101394001069086004154200045114070040b01c5690502054217044444004204228001314035041d16143c82190042c04e07541c3d4821038800340080c00c018000c1084820f688103503824030044a10380342c1466003011005001a8000c9400e104206d030b000c124100a0000c01c80071440c1c8107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 894320854 1250 894319604 894319631
    0x30507110f070909020111011a04050109090b010e071101060e0601080f010609062003123909150307031a0409020112050c0f040b2104151a131a04 64
    0x80c000d0007a244404c2d110b101600469020310494020070541000a03c8141c10b01c64010144040b0004520700c07039401d000002411180500c1100e40641e08542c04441036800d102c0e180440c40c00c0902610100f00441c40d468200803000c0c46802c0c0a0114400009401e091000004211820281514005e0340e14440104541c6811403e0301c2d048406a00f1300d920300f140d5400d410419040c002c941d040c160b0000040c00d91001d102141410302c00d03038480100f03400c0c1e80591a0036034402c4002c0e0f013541402140f0600345803003180343c603030242112400c018211040b0090030b400a0500e608107484040c0480d482e402007400400b0090116440e010702a03908010514907030300000c001030200b141c4503144070341c4d540208241142c2107040f00d2260301d0301e610340d80d5560b50f20a6660b100c2d40c00b0007240405850701400000b994858203800600454000d180418074003013003070f04040280f500600b604810052001200c000e9200c00408507441940401c000941d4103070005110060030850490601c158980415240c156 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 894322104 1250 894320854 894320863
    0x301091508070e0406150b0a090b0a090b0904020f040b1c1b0f0e0616030201050105040c081f08060403031d070f140a05060c030a020d0c21050d0507030507110f 70
    0x45890f0300e10240c4648481c10300d40c0050003070040f00161711038144808690425040c0041c2080151a40c56130b444954a407609546405a02c4000c40081c100640411032980003030301900c40c26900401c0113150144080c103240e20303a40b040d440800c800e0b0000c5440d509482459100301c1521804841c10b000c01e200d01c2941d00b900b0352054615405103c8101c0b680300308039200322010092030340094049070f914684404001d05c034406010b4100c0041d1700703110001c9402d0400340514080c0d4102a240e0780e2681d207070141107214404c022214800c92082c120b90010351014100701c032901860007600e00040314410750000c80b0080c017514410600c60762045070100034103d805c01418085400c12403c60000000701d8000030b1110f20b02c0d622642c1d20142c003103500040c451300072000b45010700040c0c089500b441082c030420340d0b400403441c0d005040510003da501d450108000c10301c8150013601e1928030f00e04110700c1441021a03806a40000011380d40d03400f04844c460708030f5408510303420000000c1585109500549640c0e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 894323354 1250 894322104 894322109
    0x17031f0f0302130e031219200928060c0c12150c022b08070c121805061603031d0319110307060509010b0f030c0108041403070602030109150807 63
    0x15907903c3c000100203020510070b8410024105d0306c200f010781002c040302400b45501e40e4000381000e1902d0404c1308440d4068100c4842c14840c188114245420740041212805110101a0b07611500c0e801c40310b49200411025005040c4a441e5840c5c46403142c280034040ac0b441c1d030048290b004c00015800c001c903200c180d400d0303141265404085028020920100d003001d10000b1135561914281802036454030f0020038017100314145a6800c4c0107503555610440e0904003040307001e01040410350b040c54090f03200344022032002203d2402441466601c0c1d020aa0583c00007a103001098414040e0504140d85405903440c0460703503a5040900b6514042c0c5540c99201d825030702040141000303113082009008060644000071319500780d03901d0703030740a0401724040c000071110815954a4626002034503e00080e0b19a485030001d401490103188107070040d1000c0c0f802500c2580c5039880c844a90100b034004000801c80c01d84140350268407940b41061040a840c401a400103c8a806078820310205000242403000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 894324604 1250 894323354 894323389
    0xf0f170f041e03030509121e030c0c0103050c0d11161103060601032009030a171306090e16180602010f0f020301050616030c0b010e01140415090917031f0f0302 70
    0x141703015a5400545421051003801d04980788583d040c00036030802000ad04000781d05581540d24400c1030100442c216041250342d000c00e14003c1c010001400881c2d4880040881c040c80524940300582c07040c0740d140301d80e040f002c454020b6801032403000b038141403000c2034020000313003803d01042c200d0100b22010300100b4440120020400328072440c07940c1e4100650b00c84141c012008034588603030804000060f40c040c07016248a55000100042c0491151065034111a04840c6050b29612041000600f0140311044c0000b0003461003048000e108010750f440d4003c003010380001960b041282021f03801c0d40c640d10043e003006441030004000903100c860465200080121034000505e00b240350039542d8080c08040074003803110001c0040b800100c001035031816200560b9403940100c10250800c030995219403641c1c0c0e01e82d00b121030104101c0c48150403540d003003803040e241544480401e001024280e0402c4552000014021100c0072501c1e09141448001d0304494030072034002170540d00070542c0412010041072 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 894325854 1250 894324604 894324619
    0x3140613060f03060506030f0604021e01171825030f020102120304060203040309152708100f05070f0207030f03091203090e0705070f0f170f041e03030509 68
    0x50180c0c100d5071000d0054554034070000c0351607071207040c01c000524040b643d060103845021020a0800000100d040c41258020300d5030314560790001c0780101000032000281d060150174005d0101008001c60072a100748541e40452010000d1245e03a1440c013402d10024180314090900d040340c4040b04080080f06582d04241a5143e6200920040740b80c001c0b45901210015404428801080355680086000c1c9000f503449100c440e4481001ca03d2505d00782503402d010540015640c0a100d420703c501c1d01d42070070640410303084a0f03503900341c00317080a010311240410340d6920300700e0a080d100c151207010b03082100740c68080018140d4503c080e54861300c600010380852072071000801050f115510032405031901103030a8000002c9850301500050150264603854000d002c0001c0e045486141079500d0b040d00074040100010680d180c8421035100c140302903601032000d1402d041105041001800f004102c100c506940b51b02d80039290030f1024404510200caa407150004002003580907003a40c41c2c4603000c03240349 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 894327104 1250 894325854 894325879
    0x5040917030919050f06010b27210703060c2f030712020d030b010e060909090a140a11010314060906040b040507020c0a0b030609071103210115031406 66
    0x750b01c3e110b03c1e064040c1c98014210851001c200022900032420301d04142150f05590301e5661400b000e000e85100c4002490041064140c1402d908019005401c0d0141100f00c1f0802541d01c0e140d181a00031002040d940e0006508000304600c1e881012588a014505404500d080c110b00c2c90500644000c1480c102c12680c0000e00035400a0040380c40c419400340c3c9442140c20030a8011f03407640d8103d0344600c0400e1900c440d51107554010004207001120080556103010100010000e01070805020305080c2c3c826507101100103402c04809010181e0407100030003201c0d04600c1c00c40030100b150a0041d04050914400503402c6000700322080d040041180c507080282e0b6a000410b0003010307180c503400d5101d800d040a000305140c0224000c802c400c026103152140306d0304c032802451280700565036250041815400036403282c0c4200e2800309800c600034240c80c6032212504603400c102780c0951450704d032290500300400c158520f40f20b46841002d001e003400c4c8500b03002001600c4402000400303c034000c40154400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 894328354 1250 894327104 894327121
    0x1401060e060618181807051513030804031a15030c010f05070b01090204180b0604060f091208030123184203120f1309090312060504091703 61
    0x440c0e90a80043c041e100c01c54184c6940304080b081c00d0390300ca00401508110f019035440046a40c0c1e082c0c0714050b10b0b440034070302a8281e441d0790b94052800d007082c00c01c000101000058000c80100300550154040d81c40c0c10a18409900d00500050401501030000c400c100788d540c0c902068803074a1b0300c02401c0090071811403003c1511244150100204114000000411094030643c060300c1031701c5900045102c6000122101011a280d103c01180c0c886402d0004004844c441e600c1d09403030f00b1003442d154140355901c00c171001a02d10384203004c6454040c0880144405400c3d410200081c400c1400c12081c008210004206651580d503820a03c25624100084075002801c0e210072044a40c0d00000103040109103840d12400c3d02c880e840401000041500ca520b464002501c103043d000403c4c00c035103003040361401c0020700c1d408294040c15001081700300040c07031000e030f1040703500d41070098684800300c1c5c1c00c842c00c0c0c4040303c00e50b8001c0b521661900301c00381c1c0401c0d050024005100c031011100e555a0b111400e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 894329604 1250 894328354 894328387
    0x9091107020603100303032301030b0c0708040e0f0a090f031101110406020a11030303160503130804081e030a090504051009110a03050a0c050906161e1401060e0606 72
    0x40a900700b18000140240c0314400008601100e00a81e01005803814810b405d00e8034000c41d1301e2004802ca661001800480c80380e00300c454000700c00080302e0740b03020f507581d81d00b1000e90465840140c03022000400c105c0d40c004040d9072581d104007240d04c10000d074040ca5564002802d4140c2c006801c02c4941050b18451140940c41880010400c050b0303192036903507c44000b5580c4002c800122408801002601e425040020549029001d440c899041000c08980221230795000240440702c0300b5600000400070400050051000d4240000034110041500c3c000094010484184070800d43c020094543c03a580d00c070b082c1600f41c4000325000310f01c50315081c1c00782c0841d600980203004410310f407a10101803150310708001c0044a03a01e44090200342e551805042c2101d02c40c2c0040408a01c0c1001030740510301e0010010504000e4806003120341018075220184622610328515458030281e000070f0040c081c90003a5284242419002817040c50308001d41c998403050041c00c514010500420b42ca0b01503813103e603 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 894330854 1250 894329604 894329617
    0x1e060d02120c121b09070c0c0b04141005030a1e05011413051b0912150703060905012d12050307060b09040f080a032405010f0906090911 60
    0x34101d5500c41081d4480781e03100c91070300112522401540d4010100d00f0340100b404d01841e00390351007003200307244640c060101000d401000c403c100100e1000060003d0b800694a030301409482918549940c1403500901d91202412041c500c00c070414a91508a181d00804403039202c1320507900072900040714071200c042c5244044250003814101800425001ca51490902c640501102c49030300266507050004100c5605031051f03810400b04824043d0b540405200038800100081d040c0b030041c1000c0c00980c4c0c1000800016050440740c40001d00443c00d50501070f902c050304c080102000a545041042045032400340103200e610160712080181c1c0c481070680d582c0091454484811066805203041901c940c0021412500c1c945001102d640b2030410201003031040e68400c0313011064100c640c070340042c9900300d054084101074481840545007208280901510101c80c052481182e0500c00050051003400312200e04100d80032900300400d641c000f0403c0100c2e804c9403400103080d500000341d51842e1013641c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 894332104 1250 894330854 894330859
    0x3030b060d0f09300c021c03080612031201090c030204030b0a09020112050408160206090a0e010e0714030703020d02040b0a08060a1a07020906030115061e05031e060d02 74
    0x551501d20902d80d003054545078400c80380d03000060680250503a01020fa000e03c101000000200c2c81d500a018032180f015490000f8000c00740460180d03411940c0541c01003044001500440920540e400d08228002c402c00b40c4a0207541840c11940e09030800080512500a0351a01c0fa1007240c02030f0700990441c0d01464004c10510f06074900361803054040c0403030f910100c1c000740c064031440100744182e1080c14003d075400700e00c06140c03916000000214010f442c400303992112042042503100e503160075684000b0f0040e803684039075540c0341075401c000b1502c005003410144280080301c0b070140b0300000101c0341e0003a001c1c20016200c00044903004002d002d180c200c03031205900055a100000d400491041c46944115a20403540740c9401803001800c014100c0c0b043c0d0404140320803001460310000030b0f44c0c40403000d030000845000080004251241da503029201240c000a850121001e0700ea0607030801c251113080c0035246041000d00040c3c40035200075040d813201c1e169004201550345442d03d80d07640741d400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 894333354 1250 894332104 894332111
    0x1a03010606090e0108032b0b0a060e01030b0d0c0b0721090504180201020d03110904060e1f05090708150a4a0903071704030201141603030b060d 63
    0x16400040c00c00b0b041401242404041c80d0700009074004000b0481e00616a6414407000d00916800d900138038041d031405051855403144550180e644481d40c002000740340558404148901ca24005070850716485485400380313005141000118041c52460030031074040b403450300e44d640d00328100392035204034044441a440355400310480b5115801429003050301d2084600700143ca05c06100d0711400c01c1c0d00c0300001e0158108e590245000c031f0103035000806800902211610b00403a00d0001011684a5000b044032025040180103d41161030103030316090a000782c03c50310440c20600020b900c4032004200c50300f0031090800143c01454449804402d40702c0c00b03004030a00c5529884400003400142d14641084d151001d1a01074003034060100305016446989480c1c803921700061072000e5054000e150900c40d01c0708005520008a060750b109404416000303440f41c440d0f080d40b0005008204100101c60003510510400300c8512511002415003941800c001401c2c9604c500400d001c0d009840d2485c0c6407928 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 894334604 1250 894333354 894333359
    0x1d070b09130f09110d0c1a040503070b0a140f0919150c05010f0204120204020a050705031303120801351002031806041a090a080304060213080c060d1a030106 69
    0x102c80d005100030070f1295101c04c0d0f031850490280403802018410203000801310110030420001c14602041580121420841c134050320340010920380b170860b174400780341e180c030000b0302e80d03010ad0b4408011040b0010f0410860314254080d0700c00074007405246105441032a140740c0002009000602002c0104a1942d203070b028407503034100c060200070644006503031950801d95403000c108494400c0b601a101d11503100c0403455407980074800250000030080003409800c03c030881c04144100046e004400300c03000181910b5041d0700c0e16000c0e100c0392268280034007071a03130014130500d840100c403210360400010600d04484491520780b8920118400e600041d4000d00515141c0100030390000c0d84a4013182d100003100c41c1900c4089942c1e007800b168098900d80c2103c4494a07461132030480385401840c483c04594907118140c594490a500c10b5904442990b4009041001049001c0e1128010f1580c02c018160040c080c0000c168280705240301c9070b07401c03991030805190942a8440306819000301400821403280c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 894335854 1250 894334604 894334631
    0xb24122104300c151403071b0c080609060414060c03060405040c172a01080402130f0c030c020c180c07050709141e010302100503090c0d06050a1d070b0913 68
    0x5404000c40d0006844007a84240d2201783e0310071280250840d0740c864202c1c008040860b071707155000041c21140f042c140c000000d030445007040a503000701c0e600b0000e400c0798101442c082c180743c204949011000d400840c00c12140c814440182c036805241560082021b43c0c2d60300e071070b10308500c05810501c0c10b00c544503000a500b0703c00103000e030b010603d000f4000c1041024050422a8900e42c5801940044c1e6260005001800e0102c680020761000d00030202d1a00f14005a9006a880c813042e810006a0b40303806661555504002c81c0c04003401c1600e00c051007416840381014014030047c1582103400300081c0710410004200001030050040712420448055a0804900c0425068850000194202800428848410030014122a4001c0c1000880380803040f00f80c80c141c200800c10401402002a000d2840d00c0705164112010710503000040c151a01d401084110342000034480b031610030b2803c43c80740b40e00c000151030058514041c4180c2c2c40381800000a40840903500001d0308440c00c015050340100b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 894337104 1250 894335854 894335879
    0x71d071124060f060909010b2805120c121501091e0503010c170f0403030b030a060906050c0406051c1d03070209060d0b24122104300c 59
    0x40104480d68418600c02200b0058140114003107291b0100d1310b14010080c101241e0014104035070b4803585000c4021032105141d4907030104040702e10110700700007a1200e01000001c1c0c0d40da400f00b42d1405403800c003500b14900d8000040010305681c0b4028516656100c1607000c0c40801c0020580d80d4088040e000fa4030a0341c85690741203200e828003c0d828110b00810701400b88112030480c00440307603240e40c1e6949100180104c0d41c00070b04240d0606554056a4000752010b1003250b440c580a001c000c00d042a00d454098200c07200102002803050090109012a5601c0700031144620341c0c6107500000300003040070810040008110211a5500c103440d06013440c02d011019001190003102c000701280c1ea10390600010303103110540181400c011a0000d14254000c03e41d90040c1030741d00440781d00644540011490010720710540f080940c0c0600245007091040c80680340101d4408401c060800b441d2070f50351090100c030280710ba502e0381d40e08422611001c0f0305c00c215014054000c100241c19666802e03195090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 894338354 1250 894337104 894337111
    0x6160207080f1608030a02251205010207020a060e060d050408161b09050c1209010908131a040e040b090313030609020405070309080301060507140d020f071d071124 72
    0x3d0003010100081d16642c04420340e468071019401074840c40386407440d080f1900b907007601c0fa042c0d9102c4079400410b00a40e6100761440c00b51268000680d02c42d240d004102440300140d00190400134000c1240d03107031f074540106803030030f00d29004804103180d00c480c503000f040741c01039031200701d811000014210240311280c9101450001b13000252002203880f0709011083e1101191501200c26041021811024000c0d26203039020400360000a01c0d203001750b440d101594083c0c002c48d4500461824180800038a01d0300c0501007101c42c04046107041d14114000000200003400502030080b03d00021b042d421050088030564080c031110280c029440b4500170001304542c040c103a01440c44c140000d19070300d00a00c140282c0381e0f0810726180c11a840d0210031291588040ba049942c0c1c08286500e01002e00100304030780403441a44c010704112036028001c5480e1500c5070f03000c082118916030030bc0c901c1c0c0204102c41d58004440c2e1034110b01c580c5002407180c5c6071401c811481020000301610822403c804040b20600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 894339604 1250 894338354 894338383
    0x30e1c0e0a0501021e0c150913420b1305120c01080603072114030a0c110307050406030605010312052107050c06040c060206060f060d0b210f150906160207080f 70
    0x3000c2c024451102d0858429440148800c420307512b1001050100c8450104c60100c0f0b55210f0244e0f811031700340702168055541c4040010074010944009244681c030340c0d440541801c0c0c84100c0c410f8000e01001d03a4445441c4207081c140049c0501284079903d0030f03c81c850140c00742c6c0000f074002c6e400a8015030300540507414140ca0600e00b84415071217480b8040100c03503080c043c035a44c0c0740c0b44070815265a21410114640c0d2581031180200006841d115801030b04000c41c000c0d400082c0a40c510f04000351442e00030a42c040811208100c0c000c149599018004440c22501a5500d410b5803100420b07900d6220b003c5c111042ca1040a04100421400d0315403002a5103155095444c1521032006000c031604410000d154844005c2c459441e00006907848814442d4004103142108400c44010070b5203a1003001400203160041801a01c8a03101000400c0c2914800001c41785540b51090300070381c881d103026046120302c10b4008804581d0030702c04c11105003e0481c410030350b401030342250304040d595400800d6128 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 894340854 1250 894339604 894339619
    0xd05071509090b01050d0e030d0e01090507080a080f070201121d070503060106051c02130e090706050f0702060309010b0916081f060f030e1c0e0a0501021e0c1509 71
    0x59842c61400b80c1030022206031100c07030070b20034401c8503140602454421751181e44820300c1006c501e0019070180380c80421800b000050b03c86541d0400030705001003074010440e15800030488000090340301e422190308401400d002901c45115200480e84008024645800b0906208400440141590407002841100c074102c95a5566480526032544c03000d00c90900401c2003803102c0302d10341107840c07200c0503207400007240103107070485115198580084940000c0e6161030755204005504c0410000c210180071a414010b04160600346003184600c61588024007581c0003002090000d03030b003500451486a8024005881c3c2d142c280740420168455181040000c0c3e4488085401000380340140548074404510548005003080d905549445826035039004050f618140620032400501035190840c0c0c81000c4001c0803500c8a100030080043c24803414428001d000302001160f800050540b0f00180c00c1c5900042001815203042c04d080c010126984c0000c00300b442d04c209454240c0c01042d540400302c0c0c061 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 894342104 1250 894340854 894340859
    0x10f0c1506291603110d02060121021c030e040f0e01140906060d030c0c03060c030f2a0521010501080907030b0402220f0b011d0603010b090d05071509 66
    0x8201c0318022070742203481c03000420064100c10f12401c40d083d070741d03402410149403c40b1a071504038078240c000c804403001a084040107000c00148000840303c004141e119000c40c0e85402e4001a0105000d128424000d13907110410b10708060040c5008640508028410400000e8129005c8040c05088103101500d500e400c4484505000040895000d03800701401001150b54850902644400c9480190140304860460f41300040c42070300510003540c498040403503441d501c59009419141e6120141d01f030581091018280c5030f04201d03020030008188030180030002030083d416503440c494028007022411841100380350a9403080103881c100d500070383c0c4e44902945d851501544504c50341c00020314002c041404100940f5000d048282550030844500c0b02101d040280f1104680c050804901c099495030303920b10185d0303004511401402000004801181e114100003051880f050052100c82c6201040c40030644d10382e04d01140000c0d03409030445204e00c0d1205a00309106001401c094001505154003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 894343354 1250 894342104 894342149
    0x20a02010b0a080d0e1014070305041d0c070b0c090d0803100b1e0a051c0b1302030106050a12090f050703170a080f09010e011a0a0806070806010f0c1506 67
    0x1d10050f2a07540d01c040c5e5030090010480300c5e03031054181030100908103c000d011a0100c50040c659039100b91521a0389503e824288600755104a464105a002803000c0203044100e0200711014103610154404450380c440513006003902501c034003079801c1904407403140c08210440c4004d40c01a5521840b5520180d9902c0b02d91180d4480d5001200c41c081d407010048032950f920700040e2a8507031403800d0143c1440030000460150b0704507800980d503407684072107620345942011074016240305405801585158101100641340b40b00300c050910400054521251145910350321109410390b12000c001c54041d050b0401036611203082c0411f842d038081916440c01e40c1c0c002a02150040421a1280c0b0318070341c0c034129100606c96004129040b60354844d20f4a9004500a05c80d110001e5103c000a03000007a440f018011200010341001c0749a911036000c2c03201781500218640d034410001d180c010b0f2202c0c101c40b800c90f003030105d060006149100e45d4180510340e4800d0341140e000d41e0000700d08074070140300700e0a1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 894344604 1250 894343354 894343363
    0x14190c23130902090a180b091603050a14060d080405030a08040806010f0338181501051c080f04080705011209020a0303030509010608070e0a0506010903110121020a02010b0a08 77
    0x300c00e80d001010041c1044048102c18144420310703031b0341301d0015035070b100040841d1014130225580c90003004103960340004550144034031500301021800400404803082c1d404803031030001410340e030320907000108802c2c00c2000348812503010300b401405841401015241600d90b80e0000c3c06101002e025840000c60b0540b420103011080700d4000e894800d040191044180d0b016104064052400f01041d240c0030b0350000808419009034140580265080c4c0303804c500320704159080b0282901000c085004210a6039800301c1f58024070707540d4807015120449480c00001d5842022103142000d5404580001c40e40000b003075110450b20207803501201c6000014420003200c2d544040290300c107213900c8c418008248254441684402510f0001498980303032070807940703001190b44c4180284c00001042102118990007180d07081502801c0c00481d031411941d6203c915055202d1203810403121100315500a41030140b801200199200210750728440444000d020300701404030707079000f041c0549000450850000707 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 894345854 1250 894344604 894344617
    0x20309120c060f0115210204030206070506101706270d0305070215010e0f0403090807080a211b080909040807020a2403090c03020301061814190c23130902 68
    0x94450140c0b1b09000340340d0307038003449050303108140035424000400161a81c200400c04940168001c2c56203140c0303c90a10702e03085c480d41011629060b450440001d000c00010754030340003403030b0400d60240700030104000090000981d4526545204080c00c040303290b6056408103009400d16402c1d181104202c0d081c030130f9408003c0c402c450f068461134001035820907608180a402c18441d140c009000e035620000c00d844c000c2c00b40c2041d5000d810503040c03d401c1140004403040d4a0980804601102100110251603c02021901070920240e15120410048400e04650300d0700d00007020300f0424142410714a5003900300c1e10341240299510075000c01d0341f00300ca40820581c455100541d40348105a07420131809440f1903c811105960321b0a4080010382d800c0c01742801074500403e04408024040c12010141c1c1c010907240b0b001d2400c00024014000801000360325002c41c0540c02050300562030004503649000025010300c0180140008490084103100510079110118130203843e850300d80501d40102e12030203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 894347104 1250 894345854 894345857
    0xf14010305070b03101e05030601060e040b0a1a03180109030903020108061e060702031c0809070b13030b06030a0506090f0f06060a03061e05090102041802070f06020309120c060f0115 80
    0x407101b08102d880c0001d001a14089556100c00455a1000441c1c5000d20a80020012900c5010003501c1424948526246440700301d481d219030a2070000151808031405041c0d41036078400000045224074a60004242441c1c0b42000300068051420001e040302100d0000700d0001e000200810017519003240e00b12080b94824110118a005e50b404000040d44041c0080380c050240d18044410f503000c10508090b07281d07440d2248031440c03405668143c186447d64006003c6080144002d04010414645c01820f4943c0301c00c41c805243c840100003441d028007804010902d210752010482c4800d40030841081d00e00031001220740303036103800095039211201202c0058100070064420400b04015400c0711240c80c40c4822500444030b110840c10082c3c0d40103d94029607031390002410050f9404000d011132809440c1c40342142452016071f561282c2003805000540541e40100109003416004c2c0031585d04162024080d0390b65031102510270303407141400c40b2003400c2d400e03c19000141003180024440352a2015 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 894348354 1250 894347104 894347131
    0x1b050d121b0f1209050105060a0e01030c09150b030a14010801020c030702100302120903070c09180624120c0501090803120703060e0f0a0e1b0111010f14010305070b03 73
    0x1004001c5036004010b44060080000640c3e000c070300c40000780706500503203000d0030000c070700c0e45032204c18403000d9586540700f2110ba041d100010400b00340c0c031201503003da40341101c0100e2010750401070021444081e41082c9483c030000070170700c1116800740e4003421400d0710703026450000c0d07a661070a5600303c0c050034910480a400810281005150055124442d0307401410018180440c1084c0b207042010104c8401115500004001c0c05000c42408810018a802c140900807a14503003240341111105440c01450152100c0c0314055141c000541c1c1c01c20715821105108035181d40e5400d41ca6a03200001003580c0e0b41c0c2d503a02010450754031030700d489015101e00c1c4006520700421301d558034060701c030014225410180d48040c08950046800c3c1450b00814122403101440c1c1042840d0034212605100d45500c107a107c00038200d10581c01c4189403030b1144090030009040003410650394050900180c840080c40e1900c6003a43c6442000710702039068a000d42d04075692151142d4a0084c0fa100650310024003025 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 894349604 1250 894348354 894348401
    0x4050307090b0406150c1b05010c03050702030f0102033c04200303030117190c120c05030706020a0b09060f010b03042f010201150b12071b050d12 64
    0x1441d00b05400c50003028000152150b920b48103d807144005080020028507003000040030300c455110b81c2480650007110b081c85075441e250000e05000355680e801001c0c4100070a90105542d01445506031188115009640d46e2a00500301207640d03a00c0c03a03e02c03810705085449800789011104542040d40c600700e4031456079864075120b119050441045c1d408602014261041190700d051000c0c5002f840303140c034a01c0c4a4003400360518203000c0c69894403010381c0f2003036107403a0104a122040c441210714503400c2c01c100c0c00c203c2c2850b00c1100316507006540c0610888500084542c0d00040704802680070702144c0b11503413103250000d03843e04000c1c0c40c00711148405d0350040c441001031800568100744a401c0341c521181c10001414560f09851500500c104400c0c2c461542c5540c0a00445038802d1380b000381e04880034100314041c0441c0c0201250300745070f07502c14000541100e010b20030310000c14858084414031f0800a00c0c26941c1d49031080002e400041141511123810355050081e02100030000321100072546 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 894350854 1250 894349604 894349619
    0x19080405010e0a0b0427090203150705130f0602011b02100f09240f02090d111c0b090c1f0309030210090b010e0906130b0c1306051306030204050307 65
    0x100c01c02450755000004010011389540302c00000e100501c95074618a0500000c0300005016440c10301c111203c003030628940b0030040c3c0d27000ca190f4100c03500c22010074000d6229000b08440c41e01440c12242c0e03002ca1410000308400c80c0388505602102c80a80c003c0c0f1411400010752035621013030811420169100d480d5a610b08400390304183c20200c00c13000005868002600c8058005a14441d145449030810040a0a075049401524402c010204083d0701e80760000e800302c2c1042034100703800341070420b6000c18464240d0354001c54010791004006000f0341c4200f13074202503409100986101d02c0c5032203080031041c498201038102d840c005104101d6403004441c5102c06402408043c01d04504500405030300c0201c0301c4042c403640003a24010041c807811036050600340f84c000036000c0c0c2628041e40c4040100600304900b03d1504110640c80801410743d526020740d0f500d868058820003004003041102d02181030f584c44400b178100102c001c50f15600e0942c0c1c5100c1a130403440303280901600364100c04801d00540 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 894352104 1250 894350854 894350867
    0x20102091c0609060c0f030c02071809020d0203032208070b0d022a01020703110102090603060d0302070e0a0b0102060f09120906091302120a0204081902061207020f1908040501 77
    0x507010b5a00801d40300900d503181d1003114468040a80801d2042c024020442c2e17261241020201c00790008141c80b50030b005512230300f0200c8403000615107480c1e010031021501d43c401e0080c1c00c10340c00342c11607403120141d554038002000078140310130b8003822880002561308400030b00340d001c850024070702628102c000724044003e9840340c400d400300004440f40e40313031031403a607081c80d008100c90f81400161203901a01d001000100c070030020805170ba00600c81800c0a03901c000859411000031500718858840c2881c090f818040d4541c01802c80c1c0c294002042106000fa420456200400368244d400a50b9101041c030504801a5032001003680103d040b0b4032044604801482c900d600240005d04250342800022640d680c1d0089640d4100e40110741c20241016001c2400e42014240e4003d60800381401801e956410f601700400a0341e1020001c0a0700799158681142e1889a80c1101800c0b54642500069502e030070a4417884910b20402d28030910f10a50900c09040680d4480d11252519141c9001191403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 894353354 1250 894352104 894352159
    0x90616051501080313090e030d0e160e06090a0e1b0406030b250912030507020f04090b070207062610080607020c09010609141e0d060506030d02010209 66
    0x4a01c078629042000062a1428074001c00a0390000c50f6155404107030140420200d43c48420210b041c40c800c0740360030300b01005950170204561800a0b400c407940310618035004180c08400c0407520820030200d180d00300c0078483c1d44500780c16502000742ba224144110b007101d112054030491034001c941c405108200c0e100110181d488001c10124400340c481d101d00c40504025142c14140c1c0940380100300d0311340419940a600d003c41828440c100c24900348000100503a0070000a0800c8030020752542150303202d80301181010300282081011548620703100074841000d1303401a01600c18004000b501030b02c219000c09030382a2002c81c065a40300400a5080124030150000d0340c0201080c1c0c003c18401010003280e4484c40c0203500800d250802c000a0012808d4182c010608008503c4030503c141074000c802406044030940c2c101050007080311140c40342d0034400c022a944030200e0301c152030501c03806d03422050065804034243c400c004030b42070017a8200d1040aa880c3d030440200915982022500e0b02c03281c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 894354604 1250 894353354 894353363
    0x31306120b150720180406051518100f0b0c010e061012060b060712031a0a0b16170a020114010e061002030f0403031d010923010203070204110a080c090616 68
    0x403d00e2410018822440c02040107000d0b444850806c000e000c441e0003400e030404420b1070040500340e000781c0458419490303407180b00050051100402d40b008010101c43e001003080d000510704c0b180d101c11070003038980e1042951004540c00c11110040908000c0b4500f40a0340c0324201209000b403034007481c24041c07410740d50240d942e1950b56211000a07140c01e0f005000491050382c046014014140740234044070b028a25401d010185140b03117114640303400e0781c2c00e01900e000b000c40c01e8450709130a04100300014981c9005182c1e8945e001c0303180c1c00f810a24003a10240d144c0350024040a8011282d00000260900c1081c00c0c1c0460300c00031600b1810080021419080c407403042e03902d402c8003a004040103a00907402200007554204203042243c04102c8a840500800d280c42c0020901d0030000300e58070f898400f00d00c4c072901401072410055a00820403100703c01d502400a000c07032050a21983c00d59009003101c075002c01e1014000480503c10082101c888050003001541040d0080340c01080d245e980550495 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 894355854 1250 894354604 894354653
    0xf05010e2803112e0b01141b0a12170408071b1a12010e24030a020406260708032a0318132a02031306120b1507 49
    0xa0012105001c4014801011484c1200c0310306010000c9410344002d42c506008a807030480040c0303203a80e000d000b040d0703408090180252214550303103812004410512142c10113219556007001042a411a044501003654492414080500110b0121088102c400806102c410030400c030005090f000c04a1180c803171001d005e081e072038858400440f585402c50384000c1d0310b400032404440124140f0203040c094410500c581c240c03400c020341c500d011850225080641c020b211558084187c50810503500308940083c020302c6141c2d44d607141d6580000c0701c807449280d5000304a850009802c000520700f41110040001540381c10303443d10346200d41c1100b46100044403540d4904010025408100ad01078065060f0f4400a420b00003008101c41804500d441c3d51010381071810104200b0300e01a1100d01c404040441c4001480c14803200720305510500300d0710240d103401554003049a0340d12030085030b40581e080070200507419010701080303041c2c4540d21903ca420303602080b00784000340d416803601c4040f041c0d41c403080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 894357104 1250 894355854 894355877
    0x61e0603032304120f060c0e0d150b04110c0111070203030328020d1a01031a0405060d0c030308150a03150902010c0605091f06050108040308130c030f05010e2803 71
    0xd514510708025140204c04002080034070000b40b01f08001c804c250304201800c8400900400d000307001b5244007404001d20050800c05c10800c3c1d40007501002ca0007001004010810800c201c99a004031003113518542c6048903d8421900c21011600c0940d0010000e40c01d541c0c030815054008281000340010540080086804038691030020309500b04480002107011044031660b60300142d844100030781014200031900c603c00c2800c80c9203c1109005031004600c0e0ba441c1c50105080014406004115425202001044c50b41c445041401941d5610600d10514010410005140c40c4ca000141209040c66444101460395510007400345206050800c0c1e911000e40703944e800c644003100c2c420300580001000d580440c031141c800b04c00c405005402080030a040c800000c0c0072120083c001801c0c8005d28010820308441213104044655010703121840881e103d02d0038440401501d0b13030440e415820f001c2d906400d0100441e8580c1d86010300302070859040100824501c1e440140031041c3d0038008881d23141d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 894358354 1250 894357104 894357119
    0xc0f151e0316022506031503150510090c02190f120513060302040f0302060702220b040b0102060f0601080c0f030a0e15040803010b07020a0b07061e0603032304 70
    0x9144107001c0161420700b4801200000381c00c000119810710350201c240c103040041110082c0e24681a078500d0320300083c08070442061518025042d810140a2244203c031078030080013560000c0e0b2040800000f1b2140c12076440708480e0a40c0c1d40c8105400160301b0031815401d20b42e40001d00c03245030340c0c050f401da603000480648525501820450074040010b03000117403000c00c1e1644010140090280d450b0451401d80b0704032500e10840380e903001c028071407200001d40e0001d56580100400ba0b06070780c041070b029404083d80c4480024402a4030880c000d9003043c030403203069800440d80c03610644d01209000510380d1903500446a0850051070401800300034880c1200050b860406540300d180c01c031000040c2c91110348036051810310507800c0305441525020070040040d10803c150307411280f0364148161034060910000b400b0076000c2d00075200c402c10102c2d01303400f440b050341c001e00c80a020058400208007191841001580c145000140c08640c40c4103030101c10102c040c60804100d140c0c00151410b05448440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 894359604 1250 894358354 894358357
    0x21e0d050114060d05070b1602030d02030a030605120d030e1c0206150d030f0e010e06070605100812041e0e0f1801020a1b0201030e030d0e0c0f151e 65
    0x400340c425a55034a00d542c241032a034032910703030003110885081c80e05421540da0107984214602941d4092030380071030300540f20120500d0301e00c08640e0040c26030b0050503841400a54a40121300364000007401d00c1400a05d03410040101d0407204c120001401c0c007802c5046007940604440d03180c4038968400c0480030800600202100151800945c0c003070b2080b4100303400da5025182211036581d00c10039403000507800094201c84042c018a2031824200d01c18000303c0e0068500c8440f009419800030000144075040122a0b44114840d41c481075402c005191034024243c1e9410710f258400180000c200024451600d02d064a100031440c0c2094041100c3d0300c5078145a00c01000b0382d40501e086001070305000411481d0500346420500c80310085041c185034041c001c00c070000c60450740918042e440c104905692280d04003580365950300044030781d1956a134254200070800190003900c3ca020303549007000c0e24909000005410b1000400851140804103403206a56102900341105103000700003421034941c4000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 894360854 1250 894359604 894359629
    0x1a04030507082208010b120d08070c0f02130501050913110f040b0409030f12140c030a1401150e041503080f041211040b190303210f0b0a120807021e 65
    0x84c004521100c01301d0910011146202c107561541c1c00040c0e00d001e9031540004017543c40542482c08410a2040307041040d4483e4440d200a50003e00700c11b04c00c071034840305400990403510169900d0940707642c1d40540540068180f60001e040280c1c24030b00144d189442c0c1c00c00ca010543c02440003450107145000101198090300b07084010603503524200c0040b940040380d80301d2140300d08806002c2c17079800038051400445c006010305180840403000c900e901c0e12680c0403406940a0300c4a243c081d5840721031441140c41e41800000009106501009a03420107000e4804401c1080c000c0502550469507000150b400490000013021014440000d104d6040e1102045603402001c40c2002e920300941440203a81d2003480c82c2c1d0151510402440044806015281c2120b815207000c0d0384003002d0320105400c5580a0490384405802c0841035143c012803544041d1741c000085a4152100c1d0b690710502184819003003014000810130710128026017800901030a8039800183d21819140010001414412112 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 894362104 1250 894360854 894360869
    0x50301020d090512030c0403020d031b0c15021f02031506070b0f010509060d020409020406050307060504080d0e010f03020a0513031a010e16050d0b03030f071a040305070822 76
    0xba80380d207060000030703c058203a40b90b2001000f40355207443d15032944c0c0c40c411807000a0048100c1d20b4001e00707041c8501e02400c060f441c45002c402e004051414200e800041c58021001d6100c5116010f0212500004912408406210018080404c000c03c4d000c003d41008260041151400000b60b260390380381001442000d1052241030070905190201d00d04450050f000180140784803002e201003980c5029514808940c1190040345501c8944040b501604160344038540520901c600440c0c03140d00301000d04155088241140c400e031010f101e0495064203034000b050301140d04146030080440c800c2d00141480c0000342007080c6418080c0e441281440100c2d8800d60395014684080155403141010550060480c660030300007074148040412090a035605003c1c050000014400705607802035001649400802800d80351141d20655824045510200040310000c2c06030005000385072541001c2402150160b0300d003400c00c0380d50394805040364013031650a00d03013a5030340d03500c0d0b07a40408400307080c0d004d400741 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 894363354 1250 894362104 894362111
    0x60c080405152511100905150a260105100302210412080c090103180f0f140708060f0903161203061a070f0825140303070f0f09050301020d 61
    0x110303e810b032649a201803250811007100110000400d00040c410310300c0440445c1c080010501c103250a58611007103a2055401c8190b507020812501d0b00d803030150040309099150068038900880900a03600008202c0c2d62481102a00500a03401c0040708400e600006050040c80c040c00381c1c10b51042044503201c41c10080c140d81c3e04200401c0282001008140d4050500391a03e0804003084036981c001c10590030304040c0d0700d4010818400e500c003c9401c20702d41003c0c4c40140941c60341000030a203a02c1c00c6096400807040c800410380d90400103019800c40c6d685034040d1600f07445801891455800181608803988024007640c8081028040410340107845002ca10f03c3d08603500f0700c0034066504036440510900c4902503d004146550000c40d2030480d0301c040c080c02000d1907403400418a0043c9071526244414806902d121034010124040075940038400790351710300d07101c60469556840304582c0027000a02143d90318182c28000c54042e40f103550305080080b512511500841d0890b080883e402503010348 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 894364604 1250 894363354 894363367
    0xc020118050a060203060d15060330050a0e1203070b220809010c050607020c10090f0308070602040f0b091906120506030f0d091806060203160f0803130b01050415060c08040515 77
    0xa0040912f104000c01103418420380e10940318141044682d6080000f032140008a880c49584209862448804c000f0f0000c002d00700910b224079640d4002181c204c44092040b004a040d504001510b0070069407040c5030402c502c2c5860742c0d03200d10703078100b203100340d06016a6285100010b00180041c900c507544680c000c08107032008608020200d900341e407081c001e10041e01003e0010318080d20b40034080d6030704040358660301c0c0c29610f4000000d204551001044003c80b01d00480c0600c0054000c3c030280030f00710354a40036031003442d10000003c0300511443c004907040c0c080300c0700d03504c5440c1c00c4641d00101c02800e8900340c08420000600b040b8400800e100000d4403840e00344141f44004441e01d988030040d001c2004030070304000003e9a24441c1c2000a00340c0d8041d807030360b0010804544c82e094103850388080000d49038202002c9500710102c2094049806240c0380e8000703e55803e142c40303103a00d80c012105521a50b1407400d0400c0d102c44611030020343d502d100401000c5219246d8400c4482010180d0a40503507c40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 894365854 1250 894364604 894364613
    0x11070602120912210903190807090608010e04030c0c05031b0103060e070f110f07181b05180102030412080703021b0d0b0c0903100c020118050a060203060d150603 71
    0x105a1401d02d44080c05102404c402804640900c90360388040e20361584076200c1030000c510318090450001020401144040c016030762002c2c2c240c0c041e99860715041681e0341c40e04d0082e01c03800e1003401203015006d40000024042071240103504409800742c00b2a101842c0c48801007410642e440c170340c0120000405100625a50b070600c5080014004031039007480a0030a250020407501d000344a800801c85601d8220108200500c0103151401c4110304035608a41c1d50380500b280034480c13480c60b600003440c04942c4401c000300c0440e04000c2c1440c0d517a90510f401c0c4002d1540c2c0301048002c01160451005120100b10302c0350b41648100303007038096000c098881b841d61400030b00d0881f0512032000c0c586481d44000078035458130350a401c9802d5110b048003000380c0c1c030703d4207008160042d886034690510603894051600203059014030450b0036168000c3c416a010190700c0c06003e80e000c00e0003001da13800038800798007051550f0f001c0c5811513802494450250550b4890200d06034800c5490610207507240002c10410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 894367104 1250 894365854 894365863
    0x6080c100507021003270b070503040203190302071d070906120b1816020a05060f130b0403080a0b0607150903022e0614030307020d050c030f030d06060e0a09110706021209 75
    0x104c451b1100c01d440c0c056a80c1d14020803014201d40e05018010000c541150b40900c00c3c130162410b2005ca1480f52002410001d50790341a0b4441c1c0007104481c60344c1c400c2911042001c41d40f180085484503030007030b4644003044501845148042e00b1326603982c15005038a40c2cbe03501b0f082c0d03521354817100004110309020001030403441e611216001550701086401c0005040801e00316070098131880b90300200d41d01d0000c4011b5002000c0380003004076405604010816400c80d08c29400342d03206180c00c00071541c0080c2800140c0c0300328a0040c1c07400080011850b5250003d4100c1c1c00040e11a01c1a05c061082c1500002044c2c80300c154145031070740310f4043d8440781e9405403141400510380120704015070753717130b00d400b003503d0740310342c610107406000702007513220502c4010401000041005400c40d0080180a1b00c0c15484c2d4201050150980741400c1e4001000380c400e4905010504000f02955511880c006250006000c032444c00c1c01401418010440452428030141a0300b101d58491502149400c003511410f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 894368354 1250 894367104 894367151
    0x9100e0109020f0603011508040503120a050702070905011223070303050c10060b190e0312180303030903030106181802091c05210708031003021306080c100507021003 73
    0x1241c017840108044e07032100038548410491800c0c000050789403800c100341144203012030a00b01e0f01050061000244c0c050380310320310900f1325500f50f4400340e40718695003060f100d0a02c500c0104000e1181e401c0040740c0424406800c03a0300d00221001e41550790036400b405c00f40c1e154010340100308082200c444e686c4090100c4582c040041c076040244604090610007030340920001c214040c0d5500b521650100e00641600c450003400070100c030312008143c4c240001c66445070040303080c10490480d150445003000815a07009142480180d4116802e020040301d0800c1020110302c0020000c15000940c00b2050502d04c18000703905c0c00c0507135289000818816403042580c1c2000401d03220b1018000812004600e81042c0d50304943c0e0000e4812012412003614000c520007c0d00b640342c0007013448402407500d4083d04c204c0c0d00c00e0f1954521010100e4000045688907c00c041d00c542182c030010409141c80105084004401d042080c1000c2036500800c810104118904003c2942c41031074140008490012400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 894369604 1250 894368354 894368359
    0x20127121b0902090a090b031006230a121b030b04080703031d071502100203010f1403030309030711060708070b0108071a071e080f0a030f0902031509100e0109020f 72
    0x904070200c40400c5d0b1103411841105041517882540010390f40c1c061141400c0204207a00a01c41c240e140d03d0813054240d612905000f801c860004901d0a40c200503d03600101c0c1c8184629000c2d480a5495900d00a10328814070441081c2c101c001000041506002038042c9024010080c3c07142c5451801404403111908038030f8030841d1020300d200380380c0d40001d03c90041c2c1d400ba08413a842c1c80c1c0d0144069140803444000d607070a45001100101c0c242c00c000001c60204c8842842480c5981c581109040e22848180d0300903907250070400502d40481c0d445c1c90399840208010341007500e4201e0640703503000315401042c02204c00b1425040100000b00d0108078140181c40c10000403000c031a40e07102d0720074851050041c002d029900b000c0344100c0d8043d0340101203038480d8202406c3d903620410042d003840c4680c003e04103400030a02e08940c1c80c81e4081248a200e01d02940600189001d80ca60501c81200724002801e00040d032040d140d43c003001840601811007070904000003c50b010580c0e02c100004030207100e08450 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 894370854 1250 894369604 894369607
    0x1a0c060a09111003060b1c050c1213020310142707030b090a020d0b10060e0604031115300c0306240f1213020127121b0902 54
    0x207011070040d004015040900f22022001c0c0d641076a010b40c05400c280c0e00070702c181c11003c00c5200003110307011260f41e0840400e040400007641c500d050030b150303405070b4000b541c0b0030424400050184e0343c8003511032026600080480b14510306005004058414148500700c40c003410000f4040110403036820400d4489542102e60859844d52001ca84c4d1822030b403001070101d101c1c02011034000081401101101c0350003500ca01000101420854101e28055400514901c03041000242e400d1040a840d40c4098004001c649000e1942e2901c21040f40c5212210703501c0100000c01d2820191080700078a124244401d10205020743d407100403802c401007002c040031f829001c0703007084140340354202100c2e0703c03000882e440801c801002444016100c0e1024040c01d0100b00010071450308032081020708103c10b07500400000c0e42c3e031f0b0050104c08000910788003d0106049a84580743c0c1601c01d04c20007460103074036143e20f942d0707542c5030078142010807035520548030010039003c08107650484107055405801412001d6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 894372104 1250 894370854 894370871
    0x408070210090b0a0509180a09030206010608091509010f0f0507110102120703110708040f1403030c100b06090a0e070201050610080c0d1d07080f07030503041e1a0c060a 74
    0x460f42c4504441c980070414000b6805007a9585e03401440051205c07466901d48620702a46179000030040c1d1b00050380036101e00c07400040c1c010311404205101c2c00c4a00041d01602240d841100c0709500040c00c1c44c101c035500c03004070284807101e0f403081716100e00c08400301003510b080240010b41a03a0810003410b54903401002034542000700004400e810805074600025105141048001d00d405100350081a1100c00100011048061800c4409030343d001c85050703410b22019001c0513600d1140c0d01c05c0803800d4002086180040700141c3c400d202100015001034540b0618400040c402140c940100c5501c90302c41d014041049e81c24442c007075008006452102c035040b070b03054000d806604d009080302c0190308002907a61030851039400c20340d540e9046103017050f00f40e00304d0302c1c210340c41f5003003400b8019683c4a40918140e050781c00103402001c43e50050061031805041812849003034007010103044215145080001e0004640040e4182c03810100b00a42c1c0c4401e50040224240702c00501100c0d4043e0800390b05 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 894373354 1250 894372104 894372119
    0xc020a03080c0a0e03030d0c0806090421020c04060603062306040e06042703270501050304060e070b0d0f141915140301141003141203040807021009 65
    0x180c202e00340915183e00c5441c81101204d00c20300c1c2d02c0710b8070b800d4040810420001e181540140d428030390b80782c41f00c0038255038820911000040c00c840190060b00c02c00e000780c0e001e00c1c0c00e8808062036021441039403030031150000424150380d02548904002940d80c0700c100300a018680340124604180030304901c20341180400100280220300401d141000f440004c11010b94071540092180c510403003040280c50141d44a0495030310071300c201540460040920359440b08500c0c18030000d5480c0300c3e490074981c90706020044400e9040107004440482c2c0e06d04640b0010b18003003017140d0003860701411072a512180b400c51601a2040c84460980c0c840c01d01c280c3d81d100c00c1da03100000c2d62111882c4010313040d400050207001c010307000496002e580c03804170702c6001c545000e0020403040001019002400f41442011550b92001c0045409032a80a5000005d00010311040542d13032404040344e0484841c010788501020641d8004c0d0b408072591040016810210f05004502c032603406240c0c10510380ba641f6021a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 894374604 1250 894373354 894373367
    0x10f0e060a030f0b0c040f12030e0117010911040f081c030b030a020409030e0d080409111206010f110304080c0109140102060105060306130f0515030d090902030406110313060c020a03 80
    0x20000c1c800c82c0021300181e2601070038000d89008000302450700b580a07545c0d4a40317041c458040041a07000a07001140004654041c0b00c412841c1d1203d1149914aa031900c01c001c40200344842c01c0c1540048204070000c0d0300c3d0a0440600080c09506001d8400811102e940b071440074011020341c0c042c941094031003040d9940100d412550b594064602080e40c0903180342c110f403070080103d0190b0307000203882c0112090002d07000242080c1c1c0c54218040150046500c2014040d002d8002c1d031445c2d81c0071020006080d540b1450a15031640c1903030801c413100c0d0300c42c414a1030450300a60010b0b61254442244d140c4c2075a440200b1034001d103090003204d0b00600000e80000d490780414012240188130010110764140c0b11528280d0100c203030814200035141c10500c4050146c0390030b072780c80094090303500f201038400d00d80854442c2c01b40030b164440e845814a000050300c0a50001001900c0d03240d500c0080c0b03524414402e0045100380503001c5101001e28085c1303482021208140940001c6501c018010070000c0e80002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 894375854 1250 894374604 894374633
    0xc020a150b04020f1206090601030b0a03060e010b1206072c010c02060912100b0a180b010504051203070b160c0221011415010503070507021e09010f0e060a03 69
    0x54001ca20a10302002240c068451440c1592a02d0400500300020101d16003c00b8011041100e03080411b807690401141910300061106901031080c180810004040d584072a0500c003116001082018840c2e000030b211410035204114980c0102080160031030781302d555025202c114066000010f00560f0210140190031410300b414032100b801303494250340c0c912040e209202c0005000a044100c21000183c46122110080d003003a81030034980c4c882460910502c90660b2000d0407409041d2580c100301d14040d0024410741810f010041102080c02e032181301043c41d82c20300284c0215540c20780c07842d118a00345401044e030400d42c421240c1c131034102ca40c8103810000544c0c0466650000300111a5811600c1c408100010201c2d0f02e401072240c071068810b501c0c144211049000042c00d0240c48005440340d00c03003111414000746080003100c0042c81c1c4005241441228001c2100050824001107012480c0a0300004124190011b0422511900b000e070954072100a0740d40d100c1052460380d61641031010340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 894377104 1250 894375854 894375893
    0xc08210913092d08040621060f06090515030c030a020403060228030b0f012003040f0602210406030e0a020306270a080d02030405150c1306080f01090203090f0a050106090c020a 77
    0x1140c3c9034030001d04e0b5501247c010b50500b401000510f40e6003503540203d034001e201c0e842c045a2020350003c0c043c03a1915494403c3d030b1049002c01d19554aa28290398035610040c481000307140d00b400003202164007403001c0c0100c00c1783c100d21a86940e40f40380b0882801c201d45008082018200000b00503035841d404502e6110000a08100a40701d00c0d01e80741ca8800301104100d0700309880007040000310445c0d1031000390221180e035000e446a40c2101582c1411001d0820110740d01ea11040004112880c401ea000020000c3d0450a4804943c400c0c1c1c0000d050500607548000c1c4a00d0030544001400c1843c1112180003615100402001c0c9580e83d40114a01070083c07048070f07282e40800002c080c45000e000d40e90710101e0b882001c02040c5000f510811084c0c002d19104454010128004200f080c014100c8900525020700c02c001d00341e10b0704004030040e50004140000501416068242a0004010a0051030b12600000c280c13141031290100072203031503400c01e90440d4062007400d00825041a416109070220 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 894378354 1250 894377104 894377117
    0x206010e0f040f020f03031204050c1504140906130504050105040308011409060f0307150203270f10022103092404080702040908040308070c08210913092d080406 71
    0x45c1c0e40007900b1070050034a116401c24100f0104030402c10045080d0411200485149080380345400211800380502c0c040d81c0e02401021804807001d2400d02446a0701030001044c842640c1185205d00054402c207030743c1101c1030382d1281c06200c01c01d9004801140502024400080600e415000093f000b060282009001d01c4202911068a0714140f040e48003500d07005040040411307100c43d00075500d80c0030075001e2180c4610601c5441007003014a45000c608140200350044040e011130401050850207100b03201540b04c0c1a28400e90480c114040c840b140102501c1c003910f17850030f4404542404410447d00c2d040b68204445621140c8410700d0341074106400c1240582c40b0105403010400030455008040d14074a0b01040020400200c50001d0001d14030400001d83d0306a582c00100383d441103281c0310440d01c06002c80f04e40f00c1c02d202d9280980700c0e140d001040040e1080c081070071350080703c10004040c1c0b50115406650342e14010407100c00079910701000584400000c440e21040102c0c040d6010f80010080c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 894379604 1250 894378354 894378379
    0x30304060513050a06110f03030f010b0307020a0506010603020a120605030a030804052a030f0d090501050d0b09130b1303090b030c0705011a0312070b011a0d09030206010e0f040f02 79
    0x16030200b800b0281c00094400c81400b03440340360142c81d004444030862050300c9004030506000c0070100643c0e000d080943d02400f050390800644240075040280410210311a101c03015004c20f47c1000310350300074441074a0041c0d039a4004040185900321030141c01540504100e0200855103000603408061600741c5044485d640303561501c241042140c005400445504041c0043c0030301380281360300c1101100b1400c441481e0560703036000e41c47d0303801c2580e041c01203440804104001c2d40141c0041107000071aa200040c80c1201d80d0004005101c2034a120800b0040410703600304001c09a19031640004254410403013002003654001c042210303900030f100c81e49001001041c241c0d0200340c00d03119980e6214000340300170006c10740004140b44482100301d110f03129190702c00742048401e1040b52110f80e00008800f4480c1c5c02c0c01075180510350b102c4411140c0b44401c00403182501660710556007141d100354090440d9500d03112f100c01c42c0000c040e103000a003001a00600000035850901c4082280e07054a50314182c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 894380854 1250 894379604 894379627
    0xd1d1516020a0801050106021006150207180603020d0f050d300605030a0f02100314060402090111120a0f0e0112050415090f0b091f05061c052a0303040605 68
    0x40c441d80801d14079800d0100105080c4e0700441c2c2c0508270740310844208511a0380795500c00c5516480006c00015030405142030007803400884100601e410b0100000c15502d82d01da010690030481035205583d02d510003100c0e03400304001401104004445841c1c00c100b10084ca10288696000050300a050308040882c0004000c1c01034006000070140102580d182000034140f0b45003402440c3e400b2481070041542d1110b00a0003407250000005060102c83d441c1c1e9580301c184802980500d10850500c64040e20700030042c0410041c4ea03400300741a21085d5241c01c089140034100100903c080d20030300c521801a646d481c0d0340b0121012501c0c0d03407510049502c0d00c4a040c60141c0229011075011540e0501691406101d0300c40040200c6a200d40300c07600c00d80d594402c20984620f6600015400019403507a401703007498880e08030b60717007040000300510507031031600d0045116480b03969003c8550343c000700d101111048030782c4002000410310440d01001c16241c0c8000980b41c1c40b4a000e80002e2290100e207007111403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 894382104 1250 894380854 894380869
    0x204060b041211090126101a03010b0909150c0d0612050106051816031b020102040608011e0b03070e030a2f060a0f1407030206090709020403020a15110d1d151602 71
    0x7c8040e0001c0040c0004500440720861542c8403490103503081130403442480c28080b0813035203d41510300107054a03451188501090010207071188050f180c0500150a0100b00c0748603880040151140d90700c004041880c0c81400d6501d41c0e444603200705d002207410f11041d606282c009070704c8104225103541c024040f20040e802040405154004c407024241c4001146805500410543d401512064100e0383e80b1103031102d00c070140711840004a07101c884c0800601d00013101954001d034075403e000300c0c160310403008640f500c514024140d40500c20301000004045a1800801000031904190581083c082020030a24030802d88030701c3c10400f401e28000c0155110b003031054070300300d12014503030340d610001d08000307690302002d90343c424860290031400a040324103807080720100d80c0e000d4070115009140019140300d50040540040600c0345d40408001c100d03d0a100d088142007068540324603a0820441200c0b86110320560140a42c8030301500c0001510f440701600c2c1503071182a039000c00c11901d0f20214001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 894383354 1250 894382104 894382123
    0x30403080301260d050c15010b0a0f05070f0c0e060105070308160903080301030f06054f0c080c01020a021c170f030901270f0204060b041211090126 65
    0x180a1300382100c15045d8004018244240c0202c200c9115000c40102e40001100c2071240c0c03402000d04101c0c1d8014075002d511a00381c5c102c0d0a080c15400c0c4a62900d60814100e8403520880f08030802d501d084c02042900c040b0650000003c5c81c15a091002036503001d003a442014082c4a04400e00d40107a10a0900c01c00320749019681c0704a0054403541d41b442d2000303240c814804c0480390315003480002456014402c0c0c400d112002d01e5440c01c8035a81080d1200400c0150122a4407900345000d9019104103103007582d00c00c40144100401c402e003900c0c280c0f480c0d040c2440d046c8041c0c1150040d480c5d10004d030f43c6410080d91080148520320010143c01c4c0351140398000c90911007c002000440c1c90007034035401c000990300c5070345244001d00c001b110f081901541c42ca100c003044001c064039103044001090340640e40350b06641c070140c00000c1840e01c4881503c250303002a844450010b0303a09036490108080c15110310364002094510080c43d504010305022000d4030302d0070403005182007100031140e036102081000035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 894384604 1250 894383354 894383429
    0x3030318010e010e06061f021207110d03050703030b060f09130b1206040b011202010507081305041b0311040807051c1a0411010207080c040f112109030403080301 71
    0x3400c2d81040c40c2e16510221406880f0f482a034151300808166604a900c20703144a80c0a04220310080100c010b10350003e0ad030558207904c07001d00d8201c0c01d0b191140482200b6001e512001d80340c1e01c2e0b524004081d1032480c40c0e828000e0202b8400308080000752025107a0202044503850401806522400014055182c005900403905d002c01c20000201148141c080c902035660300000b0b81c0c9911050010a001100c000d001540411000300070130006030151000042a041424540350746030001070950f84405500d1990700000c0008903110390301803041000719004e0f0740c140b034181846c14601c1c80d19546140b2803180202ca0484c1e20354500c41101c0c4004440aa04c0901c0d0740c1c106025030103240102108903011681d03154840380103c00b40d800000e02001b140c016000800045d00180144005444031802c08910203480390100480203a001d006801e031005041c03120608080085007100b0451001340502504d908101300034404609140f003201e0545449841140406211203240104025842550302 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 894385854 1250 894384604 894384611
    0xf1207200a120f050111120c07050c0f0102160303201603030e240301030201030f1404060c02030c010221060a0311040c05090409030c05061602070e0a020f0309061b040503030318010e01 81
    0x407071910b0500090000d03041c507105040c40688d107201d001c0103031b8816841c0140c010341c0002d500048a29080c1c0781e452074901c061040ea89005224050300c0c00e4003407650011004180f10980c2881e16164004c03003000743c074440d080200070380201c59598240c004003d01014040081c401da959156844a43c8816500c6034005600a801b2081c0c045850190304203000807030019090103456045140540256418003444081e040710ba51550313900c110040c80790a5626095020a000b1000c1404081c405481c00c88054031f1071800074035240880d04590f1800074402c2d481951a1182880421030445803042610803c0d203000844480c59407007660303079010b0a034025510a0404003400c007016403080720f4006040c032030700441e0400c0e15528220840c01d00304ca040400141d020b110204005042a018940c100c00c90550042c90090b0899100005600468100d51a0744c041e4040c400701ca180018940f01c031080b03000701e0500b09801d040000380c03203100103403018984442c044818100c00400390300a0042c1d2030004000c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 894387104 1250 894385854 894385871
    0x405060304050307050705041a0d03030617010e070509100303030b0613080a11062704140117060c040b0f09010314091e0f060103030807020f1207200a120f0501 70
    0x850f0740b039015038011100d50180800c006180c2c2081d024410150002070940c064100341c18081c0b040a00d0a28419010075480300c02c000b0388805601148030801403460004602c0c1d109100e0b1130703807405004c0c0d030040b40225810010890f0a8009840340c07002c3d40d50625000c19070b126000000307040c50046403040c4030301e40c59101000840d90b60000c0d0a01e07003244504108622682031070f08210882c09550010151480c0c100c9079001540c1c0074500e946501100104009441d0b0065101a645501d003604184035841e000308250300380032010405107034009a00748500e841d240c202108820312303000c0c09500300e031030b1700020030004540e078000e4100d126071191f0700c004c80b60145000d0351400c0c2d403001040c0c8031070700c1d11307020030590a03c403603001c15074a0080461000030302459203155801c0320404070080862003140155141003400c51801e2040c0c1c01d60988182c5102c0d01c0d0f049500702046407289407080c1c00c080103c0030700c0018498803804600380407a00d200344590350418690400501032120054010801e51070300001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 894388354 1250 894387104 894387113
    0x1060f05010e130e07240305010b04140d0602040e0601170c2b05090304090b01020309240d0c020d032318160b1e16020d080403060507170615030f09030405060304 71
    0x102c09550306c00940c101c0c0041c10900b43d04885080c0100389800000b00018000c03665500c6107a440c0100242884083e629207848402c2281c0143d00100c01594095060058a607849100340c440c200440c1480945410883d140c4071441c4640801e1042c0d0452804030103a213a01c1985010704000c0481600340018605080c41c2611703580302d8026648221f00c0c0034040d00700d0394130000c03d488001d07134050214101d5a5148400100c15491310b0b5009101c02c408000c1c90040070700394094a0071840941c4c0003095420000100502030319510ba4580007004001071806c11141d0411012a4200410301c52090096a842d21038a040010240360900c045000301800a00c01417020b000341100c082004e150501114803007034516152141c0307443d90380301d245c40510744e03005444c204511001062040300300a2a0907541d40d10003094035804c580602c0400c2000003400300800030403c415500503001c440400203c1e054602d180c0d400d010141041413003082020000b1003066040048501820008291070b40302c0c42d09181 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 894389604 1250 894388354 894388379
    0xc063c050904141b0a0903061d0706030c0206010504090b07030507020f1e060906070203030a0f0f090f0221070b090d0c030c03141b010c020415140301060f05010e130e07 74
    0x204001d013a40035803650002111104140d43c83d0f55081c0c1d681d4a8020b166440b0007000e4846003582c0031840b60030140c901340e0f00760200a05801001130351404034035058110700c0030f0700340041603124034065428000108005654144d40d540c1c03180702410001a00c0d1a516806c030b1810b900061a00103921035040300e80c5420841d01d031014001002103040f120385030345850324161211800d45800d005a07000b880072a002644903080442c51b85182d00c0005400c1070210542c405480d40e851040d41c130103803d00201000e50800c5c80300040810100040701213548030001c0c0c030694034401445481483ca5012841c040b0702e9071202c0f50304a180b40c00c14074200f0551b07120b09180c89203a1481c130089405180020f06001090300114840120804003090a400c0f81c03007841c01541c401c1e49910b4100d034041e540c2c01c000a2100c01204614006e00a162001e8425103005810325007100d43c19081202804d200b61700800141c0ea00018003400c50000fa42d110f092547c089400c58007400140c011000c0324004c020022a18004005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 894390854 1250 894389604 894389611
    0xe030715210e1e0c0604060f0212120105030f120406051c0504050f0d08091f140708090c03010e0604021918090209070804050d051c0501030c063c05090414 68
    0x1151007038943d00d1411180c0da40c400c000f404940041c1c0610081088a02a5249480c40503e50042e2854044e04085952840c0c1c4503004260380303040c40000500060808000140306524020024128020b401c8070003c520701880c492102000000101020000e014902100203000200020700982c101440c10300c1d200e18400ca013180552244154a00000b4821965140035480360006091004101c1d651070040042c3c04207403004031078076405025052500b560796580701e514180d46006550078660241401c01d000801d05034403130b0307061654844210b0340c04280c0c15000340e03044403980d080906140c050b00800c072803175108006c5820b42400084501c031240e00102181c902c00c4510344956515600d05582988003990050100d038400c034903c400c8103020758000c01f81301c2d034400030b031080d00b80240c43c0c20010740d030b0241c004a8100320800381c00c000300c6070005400709070681c4160180b00c180d00d0018603c110455040034911002080790201d124030f40c0620121801c4050252051180c0f05c0024265020000250b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 894392104 1250 894390854 894390883
    0x10f0e0a05120415080a1e0b09070c030503180a0b01030b0a05060907081b0912071d01050913030e090112230a0602090a051207060e030715210e 63
    0x802c00000400800c02c01c039800c1d00c8070995552503415898404036107464005011506c5d541e17070b80788421041e91440b044002480f807150f9011400c2c0717140c001070095090b80940604140003c501c12240080d402405481e41b00d001e00700c90303143d07198100c0d608920346004800d001e0004840f40001000380104018440d10a051000007403050b61500401e0000d0030348200e404800150116010510140001300750301b004a1207456078a00780300c85031340001c000d038600d00e100303144680c01407100704051001d150103900d9484c44116a00e40303c0d0315040118800040c01003004c0c59a100c0b0b0803015003090b0103028490103000001d8110b00c1c032581c640c00c24600c01c40c01c0560a54040300d01041107105000031224480324030a440015181400c5182e4420000c0d41002c05002e6128038841c4000c40c103a11050844100108000000c15100340781c0701000e800034100c070302c00a009420002044c0701032544591805180c0d50075241940801c0045c50002e502c02c205c440c0b0900035907040510032801d200b80080c41c0c04241510 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 894393354 1250 894392104 894392113
    0x506180f24190507031e110d0309060e15130516060e0f090c09010e060c121b06060a053c030118110415080f03121303081503010f0e0a05 60
    0x2d050041e12036026101004000821440c0d02c26002c200100811400350264200a012452030300492401d05000c59061000a40c0e201584010710038203008080112600070090450000014980c100d41e1030000d1488164a00c1c810a06042050811a5018018800348101c06281e241c140003040450700700200ca2289008444a41e00c520f004e2040c54040c2a00308901894844e0300401954400781644519622400901c900c00c0c0c07592041c0b10140482001d402c0140c1c2d14201c0c224554410700c956072002010b40d11840400c02c132916100d01c901c0540704201c9220702200040100083c81c3c4610741a1043c2c2c00b00741c1151004042001e500103081c030407085000b40800c190329982c64111040e508030142141c14003580d01029410039a110705c6210851509044580c0e0b1540301c0303245480c4104491100759840083c42d10701020a143c01141c100001d2170052100640c26103005080318030152902e18907000c2c8080212a42c2d40962100000906858050244503081000d1945904001c501901d80740603 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 894394604 1250 894393354 894393397
    0x203010f0513151a0c1204030605010b070f170d0911040e030c100207030201180f050105070e0d03120617060a05060904050a1b0518060102070506180f24 67
    0x1864010040991525035000903464601011203c1a0307003a0040c40013a0301c010844c22a0480c0107100c00189040081384150360b640c9540703003100c12108164480f02c070300752080c004100001c4202440d111100e0301b000884949100c18400000184940300c0c00000c40b52a02c80301e4002c1161a01500c1c20803078048800308a14843c0010240d1a8131540c6032442e0940c20140c03480106003c00d50260003400d00a200000340b1005451040c68000500c030400d98a00b910b0380e03501c0c001c000d001d000c4d8039400303040352a14101580620f000304e40e42c002e41c0076004003030040000400d200d109103544200001e0030444102c01d4032079043c0421301d8603001c0a0b00c2c4901d0301c50a1000060340340c1010020180620380c001d0044c80c0c803900765141ca05c15424240405485101e180c07800040c00ea6811140050362031180500c113010742001c40000e0f140c1a144e6000a000d003009000d515460031403109030509011060f50344041028550001030464034101c0800d00e254640e01a503003d0456104010344039851003142e44002211 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 894395854 1250 894394604 894394639
    0x60b12010506010c290712111207051b0303010b09091003080304080703110318010206060405071d01050706021306090e0c1b030c01060b0c1b1f120203010f05 69
    0x7481281c03881d0101d9134442c1c40c1000560600d54010f01440803880000c1d06030304c640c0941c00024810703a060000106450352040340a601072103090f43d82074183d8200b0b403a0450028041030f100100501c10f200380400030800c0c05965884000d00007003a508203055a90300d607142d509a2005400003510140506894030015054000e00c04118040da030304030081d6819680d603556110b42c1030307021030710480401ca504a913144090354100090498070a030310750342e00404c840082c002803803e1030080003e441a030410040c01855900882ca84180000700c14a0504107a070400059401c1c0c8240d1000070070392031001604489444800c0303801401d41d1507540c2c5003101c0d541d0340c4140500c80c3d001030740d90a046840400014400c0135801068032600f0200009580c1000d103071903039a50071203400e94003c5010080006000686c031409000c002550100800080c290448840100d0649070000800041d00054060134a003650700401c05940c0c188001201999070b9038503071021b5080760303a943c4510f501400200b0450f00190 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 894397104 1250 894395854 894395861
    0x623040203070302040902210a0611031927110301200a0305060a050607050703060c0302270f090a0b0f1516110a08030423060304151503060b1201 64
    0x464005005240b03060450302004000c010248080303078802000480203a0300c8081e900c1e4007600c205000d0107000b48040c1802c00000ba038034941c064031700d40603082040040002d00c103d10340038024500c20001545d42d200008452441e0301222a400e032407424449248100300f44080d1507050848154020b1100e00072992501c3c070075004d0ba0f8400d9200310814001341c00080c5c481d51145903c00f4000303002145042d511400b0a4040c0d0001600369115008a0340038001e0011038010b0120040741803804500d8102e518402d94091200100b030701d04000d4400c14280c02542d548800d9005821008001319020300749510190018205c60700d1042c018403000f10403104a1800003840285035595030b03051886c11941c0d281d054464213a010341122034203095002c490080c1c035804000f401520058000310f545da402d017009035064410480404445082102c5021a5901c0304402d41e40c0056020744000c0700d0720010f160f105d02a20200101e110420a0150000144240741c0c204840d408801c0e01c05003180d04030f0041c6203003603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 894398354 1250 894397104 894397111
    0x10e0303090a0f0c03020a03050d0e0a2117030c0406020613031b02030109121107050913080d091203021903050f160203131706010e1608060f0a030623 66
    0x201c0d0810102c00011a8981c0744040410388207060700804503499600091180b8160b400907501c2e54404000101d280c0c0c1c005205502c2c59108a0f4684400e034541900c0401c00101d04040001030815031500720200030f1014050a00e41103085005a03c03850710200900c0d80b40c009214400c014401d40b00401d040ba0b105007550300421383c26540e203001c6508000050014131f5081d80040360907641e1036001c40045080329104a9207041d80b9a1034021126429146500d4105540c0040e44103040c00c17024844908000344c0402e003441e034480411511620740c495440003c041c403200140007403d030301502132002d070b0703169000b03040010100d802c0c020722040e084011400c5030800c41c0c2c00c029540004010450100610507034034104881441102c0c0360092904129900c0d824a42c02004842510303002c0f1901d58006200d95405032107d110101c05d80d00e40301142c1d40c102412921303048213021595000c500c0c6500c1c0c041c0c440080c040041c0030062542d07628640f02009103080c660041d140d03007600740314a000c1170103004010301 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 894399604 1250 894398354 894398371
    0x50906040303110307050601090e0c0114301e07110d12021e040602060106080f0708070905032505042306011b060b01140901021c0306081e010e0303 65
    0x105030030741c0d600b50342207990381c5500040d40c80244180c0380041c008200c000c1c042c02c15200c0109417511102000e03450072500c640801d052014a052803a03120560310190307074030307543c01d21441840d0305622032454402c0c00144a02c0030060307400c0000c0010303040ca000e000805011010307002c82c14554907440122190314100c81441e03142d80140503041080d5100d4255401c110500c08001071030302072003440c0362604e9541c074a80134402c404045002c01003a501804501c0c010549030414411501e40420081d0100d400203044105220124000c210010702c0350780080050403010303084540c400d2010508071050814400c90b02c21600c001c0c000860141003034095003c000032a88070340c055404007090741e0242140700500007030400000d040808101c040c2800450f00150060701d0000b50b402e6542c00050181c0c0001c2c0c4890b12007041000000382e16603000400780142e01d003c5e0190414171800c070b14100c0280074542e2150742e052040318808030055404580c16051000994001c00a10040720080c5441c2d0004941000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 894400854 1250 894399604 894399607
    0x16030c02031615020a030902040507090315020f4006090b0903190b1509010e0703020a02010f0f150e0c0406051b060106030605180603060a09050309090c0910050906 72
    0x50011229103424000391180f416101c01002480c0000d00320b0700911005c10001e40c5880001040d8100fa1060341d803c9041888e062800b10b0668960301c5110a182040244443e0b00180071244c0d4200c4000fa10241c001034180e08031081032801f694401d20380e0007207a1025000c902d268070040404000c0c001d40c00c44140344c42c0c4001071460030700341d0324403070300243c4426030980140040300c40640c2d180c0550f501c1c1e080c4039038000e0045042514400d000b1104000d481409420244c006000f01b104100c0e2195020240d4900076a41f0507020000320f014104040c030401c00507090010072105401560040209481103805910980d0b40e250102264010180c540101e4001d08100501c011440741004140700b4607203c0d070710041c240c48081007502d001000d03401100002c0e82c0321000d10941c91b0a205141002c0d11594107d15641010b0300003944407c0d0141282072416035885520041100038070560300c0c411401414644149400001d042155022143c070510460b140842141b00c580103200b642e609407806041207 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 894402104 1250 894400854 894400867
    0x5090a0e150f030c13090807030206041209050102030708070812010b0d0c032703022b0f030b0342180f06041b080610030204150501080a020904060e01030b16030c0203 73
    0x70000303803d00405c5450303e48613942c40000c290440000c1040c984654001c054914140c145901e400a020104401b0030903511000c000d5607170300105a0300b4030390700700568070340c0c80c4440e1600307030218841c040345103910304241c50000401300039103000f0f01038007140180140035200e911082142107031352122010280d14090020172041580500e20920354522070b0040380c020550583c20f051580c03403044404103800e0b02e011050914540d020b8401030007001d180c00c0910480f0b6200001a442e001208002d41c021400c2025004860034000c000c290b4105503400c00c044c01e0090a0740d5000040c008039002c0609040d40c00001041e0100091403240400c420b1f0080d141545655446100c0311101408032030340c04803810408121881e05101090080d407084c500012501e2031403042c0020342c1d0744031903100042511100c08102c0c0d643c010002a6010000700d00044e52401102d00180041c9541e410150030030250344004010494164a03490040b142d14031800715241590303004030107440e50040d20a00580003440344 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 894403354 1250 894402104 894402109
    0x210902010f141b0309121006060e090f0a1104030308060901050a03050d230a030b0f061905030901060306021912060b1b0f010c180e07090b0a05090a0e150f030c 70
    0x119410040f504244d9150001e0f410000354450116040300f02c080d046000b030450484c69512982000700301e141460780070914070341e00148240d80c000f000da8040358218400284d42c5409507104140032014040304a407215241d04004254410449040d402000c18200100750351031b194001108aa41c0880140022449158115820040103600030185d501c9540d415802056000c05411142015500085c0c5c01a0500c100711808003400b034074600a00c4104007501c81e083d80740c003000308d03480c6840c1403881da6920380e13031000b60041050740c0c40500f0491010840d00110032901d0035042c150181030f41d448070f507500313003001100845c2d2852141c0c0001c1c10040214401520050111a80c901341200c00d948502d0784500f426429110b44128400000d22400b05144440422482490242c005641d03a50214a001000a07141c5d0040d0f010304c2003500c0000c60005210ba103e801218450400038200000c2207a440031006540301e4151484100b80f480c112440c541414208100300031200000c0007400020407800a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 894404604 1250 894403354 894403387
    0x6010b040314030f04121e0203030d0e030903251a0a0c02010e0d141203060913050a060606030b04140f150d06110a080709030302060610210902010f14 66
    0x9201c80e8003003400380d6404ca01c62800a40000d180086c00360851000518010010300952003402c1c007030311226200f060142c1c400000740c2d001c10b1640e04d8000742e00760010000500d14020b0b0350a035035142c411130401124030203401d00f99203062071601800380343c80381e1206401030384000c201104400b907030310a005411400f8460079040b0b40c00c80c0103040c4000211124008034010183d40d007029104400a8003940280e00f604001c112200200e0410450031810040c0001c2d148070000b40800d981c1303907150100c40d802d100c0c044c02040f20040d031001b020070417180d80b01406006482664a00c6206034a0520110b03400840c144000380b061000c16141e0406d9940d6100050303801c410000c1a9820800d411074500000c2c54503c200030359080c0004503181c541c0c1d0254001001c0040013081201044050401040042d0b0001622604160221041803500d84008812140a03105c50000c0c035071091036080c2d002100b05503a00c243d07802d81c000c1c2c1e102d00e8401240303041a561b16414a0441c20400d40030424119140105030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 894405854 1250 894404604 894404633
    0x80d2d0203190c1107050103110306090405012301081e0c0108071b0f11060423011e0c0b09010204120303110d020f0423100e0114040f060201050906010b0403 69
    0xc946500318480c00c6241000c8501c0c00c2d0080d070101c0c01840783c084c500081008410000d000900e070a0140b01c4040e0399201d06400302900d814000e003800408941046000e4101400f1b45c0c5275207640c911810f02c0110200380a101c284a840c0c030502402150b1a4200303903c4504060300c984403402030409c11410740045580b40c00003400030080001d1904a4140e0740f603c01a1020342501581d5003508007041c6003020f0110f0003034004024400c1c003007040f0800078600003080460303000c051032507242495071034000142c0c4c4100041d5030303040417544400f11a40070380360486030903c88240500d644856035a110002d0500301c1c0704a001d8420b804409800d60030001c0d1094000154501d01c907401d050900c0032a880b0107007a0380001c0d000d4075002c1d01c0807070184410580407055072410802c54041007040004140070a103105000040003080150022061105034090503250901e22020b131010360b581e0380c1d07801d5500c5000e1118020301006500380b00c00f043e060f800000f50141a55038811801c1d25003491355651190040b40310 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 894407104 1250 894405854 894405871
    0x31a011d0a0b18030706140708040504020a170a0e120a02071806180908030105040209030a0b0c03150909070b0703021203041b0602010c140a030612080d2d0203 70
    0x10600500c2621a1501c1d10014045038403000d480d880d1480020074208011500c8502960080800b0808280e0050700940190700140c619039a4001c1070404107421701c03a64000076041400010171000c10b591084107001125800c00d4600c4560f191001120305542381d0480344205940140700c001c170410358840c010012030040380103c0d02800c2c1d03a544603e25503000b001a0b9000c469580d94100042c8440d260000860401c5913010050b00a45944100380b90006000d1b0034050341e80800d41106a0710100f0007050840d401090200f51803400c0d6005480d55071017100e582401c0f00e10849215024182100b1460003130300000d0181100380d0400c24290040e03003108030243e046114442d03400002000360300c011400380e4015004c0303080b0541d00040440b0403004540c40b440440e85031410b40103440f07602c0482c600c00c0c164551a5035a4031503280c0011006030400390001c1a40301c440300d0b2141c040001490003001e101c0d04620090118843c001e0b1003444200030b1503c0d80e00c5008003503500301101c015940c011684600607 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 894408354 1250 894407104 894407147
    0x528050d0504050d02070605030f13060b1206071103070c0911090a12050601061d15090612040c0b120a0c1b060c03050903160209090a08131401031a01 66
    0x18808080c0680e40140c40550310f075000309512143e9143d0503c00c050245c081030030130529608058203182030400c80105410000d61051450504008260b0000700f00350800810704c1201065014103141c40d100142e8044020030f40c4a01c50800e0f4610220544807031a0b003142000c40078034604041603018024801c08118a40401c020442e960358500421401402c040304503d556040c089c50294508501a00305505204010340d407004200350032148003400d0201a40c2c9801e20183d000d03404801409030580503603200c0800706080d8051169030501c248540d00030580b0100740e13030b544c1000803014400d8903147c982510312100015103600268200d144429818941f03120760701c0d2015a9070302c0e21a201d00c001c60704507442c3c42140300038035418028a9000304010002d0f5191481804600c03a144800d0031000f4081d124003000203140748801d1101c0100c0d9504a03038100e5031280c18041012442519010b0059850b819010446195110344101e40001c4440390058000415460054401121021100c06800384 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 894409604 1250 894408354 894408367
    0x801060b09210f1005060d0b13060603120507110f36070f020c180a0e150c1908060105030a02310801180210030b0109090e071401052805 60
    0x10400c800d0040c3c001e4440130b442ea14600e036a4010660300c02a042c00e00c2101c0c41040303007020076480102035800002100048100c0001c918181c40540107640c8003901100303220648001e925000f400619803540300b810855a5003c0003820031111750b00490205810940a100032140984030801c04000010758103100a05100400040310b26102c0894403030340060140d000100170540c0400200c82c62140c21039846180488008204003a0a4001c022040309034542c0300c1e48514200c2441030318003e0300a5190039102d0705c1d1040c200d4105500100d60010310b034040704181808107125811241c06014140d54280c6507464084692029422010011000314140704210512101c0300007081a0f0b50100011149054640100142100c1d030054091065a008211020040c0d480d07035001150080c00b4140000c3c1e881503000100c0300e0004a4200c4913200349054032a02042c2e0000400c1c0088408401c40c04540f441e03000c00449440c000c0000e01c7d540103010900e98190084141010320101d821450203504141 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 894410854 1250 894409604 894409669
    0xb0f03122b06030609060f051302010e1206130302150f0c070204020f0d0603050609031809070201110d060312090b0d050910230109090b011202130c0503070305010801060b09 76
    0xb4142c2d4821580117a694004100300082805840c40a01d505130b800c114514116142c0000da485d0610007d041200110703c1d4141682d5658643e5644a8020100c0d552480c0c40340c00303105958510042074003d449600c446c0d181e00441c4c030240030301c203c5100d0540c0401d40c55050866a030b503003208600301c0c1d00a400344954915484a00082c08420f90715540104905145007011400c0020103030504c1c40340d070410014401203200f07051452080001c02d480100700c2d030751010790480c0180607411214500c01e0380050b400e40f80c1600b41e00014242c9004070702650f10300c812035100b03540003255449003424054050240301d01801c05980020b903c00b88020076680b11444d080004422500e9101c0440880c50901001400b09002001c1443c05014a0302c400c101407140c0703450744c2404080520400c4085584903a0050440d150350b0115816421620024410018500030140c455041114100c00080c5040000035003800140620000ca030340c01c0e548075207400400c400340111803184092a4a01c4c1507548202c09191 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 894412104 1250 894410854 894410861
    0x30c02010302270f060c1209060903070305160906050d140c0307080d091a0702100e030d030501030201080601140a0f0302091c02100c0b060405040f0c0303030b0f03122b 74
    0x40b16143c681e0b2400441d203030800c00e03001e01181c8194050315061005004140b0001204055076244000a6403a8000000000d9042c03154801d040c3d0036001d952400810001d00041802e101c42d016180d01c0302c0706071514420001c48140b403003102c1d40009140c400f5004540700c0808c4100500c1c1003019030f00340842c41d102280c07600e81e040c0e119469982c0701f0b1104e82c90f1140e20001c0038015006400c2c211407000243c00700c41405014001000c1c5c0b04078444c0c83c1e0391011030b0085042421010f8080c050f0fa01d00968140b000d0000c120900c0264040344880001a01561003621550002c00003055504c1c10090100002c550410302010705100341503081200641c1559222180c08540100520741080703215140305016075990841ca0f0501804000d84114000078511600280d10407004d50300000d681d61103051032a580c0940c0a03015200481c090b10100a25a05400ca003503102c00940d00d24100d01404400d0566076204821507160300002840b41c14015902c0034800242030394001d0341c0c80c180c0032030080e9001c00c0b03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 894413354 1250 894412104 894412147
    0xe03120c0901090f0503070b0a09030c09021e0313080a09170109060612120c0c0b07050604030f0e090f06030304030515190e100c091503051b1303030c02010302 70
    0x68003000308101c002980d002c002c890144c0722070302c010b4219505e4503000c43e070f48514030701440c40342c540007082c0b140c6020310480c0d68600031504003440440720b035034541c801002980010501c1d40c1fa2009403161402c08240c01007268055001d00408550102c16625240c1e03480d00030440c12020052032040000c5c103100c060700b649800042607400041c40011514010044a01301d500003a0b00110340c01000020605c1a59003024204c500c1c240304500c40c041d480c1080401410b070308502c07800e25020548109100e0b00240711489184203032070f02d10000c009100140c03804051240c095a01800000000e111510b1002803980c201c03c0c0a801c032800d00b516962514185045e550682082050120400050300300740401c2000462000004211107136924101c06c0d2500e61042c40c41904030f88a08000c40210303c15040c40c4001c054040c62611017407458000100a42f205407101c2c5000007078101200200a110011505100b0035011114001485c0d036030300f96404807030650140c4c145a401c3c00405000c55910564694 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 894414604 1250 894413354 894413371
    0xd02011d030f0a050f0f01110a1d06040303050a020c010207260319111501050d0816080c0c0406051c021201090b010e1f030b01210c030305120a0c020c040e0312 70
    0x5041788620180d42c505002103180c0700c103587c1041c612001c80581d03c411254100c05901d850b9510a6a0314004200c8440048441d034000c07400003800001d05900ca0050444441c1550a84520b031900c500126030710281805410002070f01c2502e18410701c000408911000b0b6460400d40e82058450842003180c00e44d148401e01c0400d56001c813000503c10f013844005656a03151804446950615000c10380726011968000e2850000040405240100104416640b0b07031004545560305100c1c1c41c0c040d11554040e00040c000c5003050400300d82c2d0300e0240742001100d00a920b400f241c1e545a502000b14030701000c82e02ca8090f55850b14079034089014010f415010b41404078000075581480403984003000d01035001c4181c0561480c170b0034400503510485650440b1117101d500800500107030719149207201c0207400104510303084000002019000405084c0312004610000d0701d41d81c1d42820442070700e02d10b58440b001030300490111503142c5891f90000d0402500002183e040c030404c007007004920700083d1a80113 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 894415854 1250 894414604 894414613
    0x21305041d16061e02010b030a031806140a080723070209010e16030c090b0301090509010b1c0305070f0602030f16020307051c0311180406050d02011d030f0a05 70
    0x1c50000800100c00d00c000004200c0440c00d00c0c1120080020300c5a5040950750703e10001044040e510175001a0384200d8010f0555040c1f09941c64083c1c80c41c80746144440b10701c8480c500014085004209a80413030b20800c48007458040c2c5c8100446100200800c00010710031959004d4840c0001e541801242048519005c0e1303a8000c540108084040c0503131000b181ea2503c4410410417020621814448000c4d40c180800c150031003003c2610405601e4121611a80000c070001400d2409900500d02450401c1c1c000c0000d0740d20700e824480280112000d024000d00c9070382580c00003034850001401d1981c09004141da201e0029034820f4207a0b40155412090280107506000081c17007504440d00101c9140e0004500c2c0070025030340e01e501c41d02410348402c0001034440030f48021030f000e0f4200340c941204071400e403503461f040c1c00c03821210741e0252054075028600e06540454203081c9040d92010183c2c05031030308041414450503080980340855030458050050b00540c020304902004120300882c410300c05003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 894417104 1250 894415854 894415901
    0x90302031b0313083d111608130b0a05030115090902040b0a09170a0b04022e021c0905040207061d0a0318050904080a03140c03160305100902130504 65
    0x100b00b80752803045d262041d800d03800d8255140545084503041c1c01484000c080389000d2503440c0d00a1074002c0400801880d1a164010320402c410600203000c1241040a02c00a05840d441e416000c0d00a1040f0500802c17001c00c010300010020464040640c1d403945840100341d5160521002030741c001c1c0e4007030082c00c000403038960141904130b004540a0060b01400808540c66540d0070350b80d80180384006032240004201080941d11000b132040210f034450245504842e00031904182e490700014078003070050054400c03803c80a10038959240021000c0da40f06280d880c109820407009600c01001210302c245e540304425180e240044800501058800c060b00b8019501e04000d01400c0003074802c1414441944000d00444d603d51500c0703074010360800030702d940714401da480941c024014042d031060104142420040035084090045100700c40c4841c4144c0300158081c3c054041e11001e65900c1d90392000200b060014101c7c0c0d81c00713416540c175048140d03001582c0d6400824102c4820020600440b0380440300c5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 894418354 1250 894417104 894417133
    0x110613021c14070e180a15020702040209040e03092707030b0f10050d0b010912060510030b09100b0108040c030803060a090e010b01181d060402070506180709090302031b031308 77
    0x2092003100095015003050003155131144000d00003400345030354240c0c1c040340c09d10940d25254150359030728038090f02c10002c07096004082c0d5600d4111b09030941c8a01100642180c88440e84816546540d0300000e03820411307241d100d0309502034a40c948403a0f0300449451540007640c0c1e01d07030fa01882000480d4980e51b588800751180702e01074851050a4905100301e60004100e6040b41010140b0016004680043c1a45070203070904a10015a4005011840c50009001c3e5068011600700b2521403800d00421400c41450b0041d0350240046070054400043c41d281013021540403802160f01000042c0158040e83d22030086d0803c4071080400380c000381e9034402c848820303540c006e07110401280c07100010090303240c5416040200c041345900d10001810000340406d269480d00d0301610f900ca0b6025050b60078a1030074072044c9107026601c00b0500700501c24030030000303080147d0744200030400e03030507602461811020038000a0584280c0c0b004000c103101c10480c0a144801c0703101a54080d18082c4050080f600c0724010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 894419604 1250 894418354 894418381
    0x1c0503031006140f0715150902030108010510122627041e020a0c08030903090123041e0f0e01090c0503060f01030b0d020301020307110613021c14070e 66
    0x788104030f14001c101c00100e03450380d00d00f55166240e100c10240b00c0301c40100b181501410358404040c00380ca501c0c07000481c40f100140c019606070b42c455402081a5620040e40c00c1411a451254941600c502104540403a8194104600103101c2d03801c2c9007103011100d00006c105900c11140e141c100d00c200903001d004042e0329080c0701d0201d04111028040d07040052004030701c41e1005806403940590020b0007400007405505d0130303c292500501e5064032460850760380d03510b990000c461280002d0400514012101c0124140d0795034501408a1078142410003140c4040f26122080544201003014000940c000f00301480e4405000707004211740c21545403000420650301d80703020f0710040c00070500c00c020031a06c0380d03800204401c0c030900e00418450711890108907075405c80000070303416500000030800c100d50041030b03000300180d101044030314541d120a4501d0200c081414020743c80b0ba0291402107241402c81038080c50b2500a000d2800e82003000c0b81a6460201aa0300c13101d03100d6102420003000d21545c13103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 894420854 1250 894419604 894419627
    0xc231803010504020a05010f0c051509060a09210302130312080907080d210c030c090501050f030a051b0403030305060f0d0302060c0d0b190e01050307060e1c0503031006 74
    0x14020b20250030150300081c1c000c80c1d2400b40904105201441414462165220a11454120f0f0543c0c4181c80000141c6481c5032040764541107134410392010032481000d5100307070100242c2050803071030b5a0501a48031403030103084103541410180c0030f00903624405941c40c5524000c6210300c0003240c4894803210040c105100041c03695000b80c1124504100004001c180c3c2c00700001c10f03240a42856500491400c04540f03800d1400300c20f036141c12008910503030541d000d40c07144810b50b212403141c19651001191213208085841d08544014400300f89908515000386030070a00e03040b500e041250b40302d242c1c80c1142c0c026900550000c1d03160001d0100c641425081d44940030000c0e034409904a040f500c1c0039695007070180c004c1300e079041c0025115681e44600e03804011400030040c4a508004458016003149401500807494001c110200001d140c0c900000c55908581e00c0d505e800550a800f02c080140440341c203104c00c445501100141d20005d042400114410f40745006101e07522814144010412180c11 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 894422104 1250 894420854 894420859
    0x280207020406240302070204110313050606100905060c030f0c030403030314270f0a0b090127030c020109030c0303110606060a1722120806100c03030c2318 68
    0x10f041d910042c0c070011285010a0032541000b6941d0610f610205006080701d591080c900131000c4184074205250b240e078001a00e02400403501c0c25110321741040030440c415030000c070100391030303910400c144c3c1082c801070240b00da8010140d81c02d1580760f44c03441081d544803100402c026040010103204060309841000403800403542c01e01480d00d4440c6220400d0150b4007412003042e0003807c19a02d11100c104007185804080605883c0161400e14100c2549175090704c180754554202a00940c032110f049003010298140600012604801500c0c1aa150146420181d040042c400000302c0824130b81c902c6480103510a036500f111a155603c40c0a080003005000c03030344280b00402c2080c0e0b10507030000000315050910010413107180c54000c032507020306500002e131501441c0d171101c00500307014000301c484680f22242d4480b9801c80d13960b40b0401c50003011003103c03070380442c0c1e0950440300401d01c00ea01c424244030890a00440f140d4411541045684003e0040002520000303403101c41c030890400741c0000c0c40d00a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 894423354 1250 894422104 894422129
    0x8030c19110d15060f0302270705220b0a0f020d020714040b0907020102091207030812090f010e0d030b0103140a020322030206041a060d0b280207020406 67
    0xc940d00d2068480704078910502c1007052900c03000500c005000c90301c1c042440a102080f103d0764030007a24440c80414803080c1c1c441e04000c03480c079401c0b0028000c0c41c03081010024814030f0559480d6000d640076004107a5203400e040e04021351001494504039880007070050751080c03d403a46c82000c0c000f440d01024141a0781150409580c0c113804030340000b10042916a400ad501021354980d5020030014445c69220603030013100d140510000319019030003400312250503510106030141884681c7d5441701180310051210b0820000c03480309081c4041d00740d130021850401e0380c2c0f2a010b051500c1d030940700b030407034015401c1c1c10480b50381010540621900c84601c000303003803c1c002d080e140011000c0c2c00f03400901c01402141c001001405d142010600540c80b071405655030181d011241c1002075440340d08803421038069001507003100645a0010344079200e201c0040c200b980041d42030741c9a10103c03002406010701c14166820186800f51035178100b40c0e403655480401070f20342403a1f00410041d582145c0c000b0034007594 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 894424460 1106 894423354 894423403
    0xa050d11070b090f071a04030b0f0f07031401031205040e040809460b1c0f0902060706050606130902090406060302030603030a110a050708030c 63
    0x10b00e140051642c0e0391164903036511806100d240045c2d20044c0c08104a0481c0e07200c00e030039036681c0007586080550740c0e6652020107205850113004a0004000c110300c030031a240032650300582a00e814000c5c1c00190000d10240781c41070101400c1300c60001003d0400601400840e402441d120711102600c1c50581001d600307a030021955903200c4c200b02003452140c0c20080c03038040d12151580c80070441601c2100c07000d4444102c1e254031307810003d1074401c0006219910f08c014009a0b201c0d075050310303101d047c0c1d28a0441201c848001c1c45000c50720f0118481c026844900580c0c6030258440e2000a65440700d00000c0c00f135002e0a0517044542400000203d01411550054801068192000c1c44078944400040c3e082c1d0104940303081d010345c0306210007905144110320760045c210b9000140c452030061912014180440380d0030001990b40001031014150000b004113184007610381e100c6001c0c160 = true := by decide +kernel

theorem cover : BRFrame.Cov 894244604 894424460 := by
  have h0 := BRFrame.cov_init 894244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 894244604 ≤ n) (h2 : n < 894424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
