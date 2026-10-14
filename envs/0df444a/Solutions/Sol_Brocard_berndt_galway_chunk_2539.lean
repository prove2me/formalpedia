-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2539
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:00:54.130866+00:00
-- url     : https://prove2.me/submissions/2ba07a18-8356-4d9d-b3f1-9c8370b3be0d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 456474820 ≤ n < 456654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 456476070 1250 456474820 456474827
    0x40305040b0f0910031a010c030c0f0204060b0304030908070b09031b01120c080f0a060b030f09030d09030c02010e0a1404020304020307050a0308030a0515011d0301090c3b07 76
    0xa01e090352079814180843c40c404660b4203107081007500c00290351580d2031140098101608a40e101e030a00e003150b082c0c01103a50182c1152900c01010f400506075410b10001c5503034a4004601030000c80007519100d061614016210b0500340c0124843c50103080c1000c91319850070f8040c0c4624180c0180280400d01c100020b8800600c80d0b0307c01c9078100040c1065014107007409008400c040388032651000c080346048800c804a29402404001c01141881d9040048080031010740ea08400301440b1460146c4516462600d503120309c807901d40d0b0780d07401c1c0700c0c04905064201044805990003a00d400d4501c10181c400c0000c00001c0780101c0e003d003da03509003140c1505203540516441440a4100e85140d9114000520700600d03507401100c5c001d500008110a50b00f070b5000b29904448094401c0000009100c0040c00c001610118040603030320707190140c000ca54003500903801880c0c10811010800d40c5440600f4110a4503810401403400704122072407041103542a01c1945510400554000e510342400c04c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 456477320 1250 456476070 456476077
    0x706050304081204030e0901060c03030510080307031d09010e0a050901051006110705040203100807090902090a0506210d0f080411060a051210030c0806100306150e0a0c0e0306040305040b 82
    0x1790200650b050030f600e0700340c0355091003501820060302e4444100c5ea1a1030b0040c280c034002010084c031502d1150041084000003c155600a81e2506081441003081e210900540d858900981e0740701014100004100000c1900d03e03004409418050255588103a402c80c00c0e9001682c1c40768803080e06c40020803000c0d226411a0780c1100e103400c00d607000c0a9540c07000030140c0c0c00603140d070130790402c3c0a10300300036400b400c1000a0040c00f160800740410300c01a000a0402c02e80200490360136601c40300015031503594901c090041e0340d20305100503100ea581008659076034480411840218103140e910814507030117a0301c503c0c455036000712241e0303202041005004184c1c0003106c10b40103001044c005804480c0b40101d00e58428904500340c02d2120b4610308201606000c658407220207074120320140100d140030a140030302a03071380041010404440c0146d600405821640c0b024809080c050b0520402c0d940d59000811180c01540d01c0c20500c9a4450030540c450710269402400b040b801c1000b00705100c15030029 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 456478570 1250 456477320 456477323
    0x105040b03030d140702072408061c03080402100c082d0c0619060b0a0c1424150a120201020109020a170f0303220606081e0706050304081204 62
    0x256400d10000441250503a46a540d00c50740b0000c084d4100305029034108504001407030900f080d071495803c641520100000c5141c00c050030031002030b00060168441f41d0400828012100514041b1129805c00808089054408901c90400342041c0d81e14284203141c4503c1b015080760342a45480508500c2c2d844080c50440940280c0041040048403c4007581c0a000070541d44000b61003039141c0303900740d00f001100c07150749480c0f401c1ca08102400782070340200903554035000c6411b190b081d9140700d0500740d030b0088103412001458410b802c2e4141d001e11842c8403a0760f10480d0b80c04074003400c0d101c00c41d04032100c0c84a41707241500003804100c2003051171000e184d68129030380180000540c0c0207032a008038075103841a0300403811001c01b140c19140444400c2040a1107800148091403e500f0200c4080c00f501c000224161050039081590703000340302c1150302130780060000b03001f00c519802000c04031001401c0c0d0b081c6100d10a004441c0c000030000e01510445c0d201c5c582c0941c3c081d02d0901380752000c0c400008080c10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 456479820 1250 456478570 456478573
    0xd0e0a020603160306050324130501051005130603050a020d0c0812030f10030308060d02040e07260105010e040f06020c0703140f0a08030c0703051204030e090a090b0105040b03 77
    0x1104009615070300000e5000e00104281c5480c9140006006010303030720701ea44440d0007070703000c914002c103030856408100c61100d082c2d91240b4003d4490380016115500300c0740700504107500e41000e0200146000001204495084d280141c203000e41c01214011950140304c09002c41d0800b00b80040140340c02154041098030a4010429054507202082c1c5080110b00440741c042500106008410340e414114683c07209820440c0082701d03003550784c014103803000504103030f001e02c0d4030103603000466a49810921382d00c4428001c4400c2195a40d50144604a08034070900c200784184e414581101810701500c1d05840c40b07141400c540d42c59039540d0510041c1c14400c2681c14503828041c040a070b500c28882c020045006100c40301242e0000e41c24241412200170031a18150b100c0e0842d6400030342e2103416268010903c4c503072907413500a94182920a80311b40c140000c0c10562101c1003000b0103800c11303035020a0f140d0030342d00e440c0c450751105620000c0300c407044005490b091500004000b43c1c5066081980e01000c00b40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 456481070 1250 456479820 456479833
    0x16150903080406020102030402010e040b0f06161407150c17030a06050603040b01051201020403110d0f020a121518060c110114040605250302031b0301030311010501060509060d0e 78
    0x111004071a400070740280005035000410310042d0741c1d10811500200c6070464003040088019000070754841030060681d40220b801240c006648440780c1c10b052500354000400918541da80c0c01010b8448241e80034451107912602c4540c0d42180c03241000c440400d500c12a80e0148526a80314480c680d0802803049240f0b60729220302060316141c100c0654011446402d10306800d50420040000b030041744c5080381101da00c10300c41003010600420302104c0703003902940c0e4002006524100015804090707400a50040345071040010050701140c4140540750261241d0342109084089a209981141e0a99984016402c2000020420580c020014220309003441843c180b2225031032401c2d036055001d4580b194a0b0b410800040c0800e50103000e03488611060400d04187e240400c21518020160300d80d800c00d580400069042500541d000c412134140c80041903c030340e03407403800a042c1004070551503555400c0900004200340594203607007141100520b59801d10812268120051040c0d016800c5144a0364 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 456482320 1250 456481070 456481073
    0x30304030c0f02150a020607050c0c060f090603090a11041a010e13050c07031b08160f0b0a05061801030809060d060905101a0301050a050d050c03120d0e16150903 71
    0x1071850008005011340e07002d0b2210381000020b41010001480c0e401803100400c119940f044000c1904002400101c4038035071100007180c140715640c0110241c25411290000600280b0b613000100f2011091054400003c007100c40814413060307c1c2e005513040049a101504500c096004030328000b0519409013140c005403040b60325010a81d074041e1a605800c900c001080346c203040c5d00005488120010300b800c0d4071081f109070b55820092040e031080022420704802c10f03000b006004a4200075443d040382c0401c4c4071b810502d8144005090540d007903803140686c480790580c213000903240141200d070000580b0381084005000e100c0a54881c1c3c0e40d4030481c0d5501c00000c180c0b0007841c8940c501400b00e00c43c0c074890725810031000160016040d0030785401c03d1410700041240d603881c1c2c00d03018190381060b80e1020340c41c610303480e0042ca0071001c50392542d454080c6481c0564032140c40310141005030828101400458801c254664407407400316880703042c1c0d041062040c404503d02800f074a10080e080d29104115035940e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 456483570 1250 456482320 456482329
    0x3040b091f1a0108010e01060302030c0705070617090c09010311010c0218060102010e1c0e1314040203010606050405031506030c06070b0f010b040605090f03030d020408061602010905030304030c0f02 87
    0x44030681400e540d103102c2e05110040c1c01c069407041503802e0034111342c40d5040c0034030001a1101486420101500000010360b403d02c1e003820344107001c0e03002080b1100b564450030007030501c5803e96505d609001c10744000031007414001401500d95000070f040701c012a42540c6035407061900700400281800702a841c0700006858075002c40745d100031090003200d01428110002401d480c2100c0711440c040c1d02034928804034000304428900c2c450001d04044086814110100352000e10b4007101008140c0390003050901d840e03903113440c40c0c81988228020010a901e80ca01501c95001e14000c40b505540481c2030380000c1001d80d068150801001002c5600100341c910010305541e00520048400889020a001c100d04a081041d8094400e0f81d0805040c10f0401400a00b039005242010b449920f4000d00b902d11904c0134030480300c00b8041000c040d55110707203461000795200e000755400d1070890b5903450500b4104d481889020001540703c00618a1a215030300c0481c1c1d5190300b01000d681c4841008102001682d8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 456484820 1250 456483570 456483613
    0x303061519231206030c0a0305150726040501060803030c041206090512070c05091501120e010f0614100c08280305070f080403050307030e01021c0b0a061403040b09 72
    0x14042c140e440c0914214045c5414656400c81c0703980a60307174560043c40002d0000c20443c0b01c82960044110503a41c0e07140c01160345001442c42482c20b64614545825201c000300841445240500000e2100640d140150341d034a20007121007111800d02031105020700a034000f60181c500c2d008000202c0c80c0d80150b1980c5082005620080007034200002c3d020080203248482c1c8001803a040b10524081d00d007d0b1a60703929901940421170421031114100910b100c85075210140410149000b0411452681c040e94010f10260241d42180050800e0500151804400f1900d100c6025560701700c4403407960761114600d42024100e042c0250072100c9071028201c511410800001d120794011442d4140030b100504180050440300d03041288140030400800c5c1c020003129000802d0b8a00015a660280005402402141c80d4940183d541d060300040d2041c1681000072403010407500400c1c0d180d0748810a40e0002c00d03159240448404c2480054003185c0042c002c40d0344003400707a080d0703000e04408810051740885c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 456486070 1250 456484820 456484837
    0x20714010212010e01090207120302070807120503071701230612040614011508042d0614011707030308070e0612040c060e0a15090302060408030306151923 68
    0x20310b2001000f13083e60000b0468010214858110310b0004240c40b06001c4c0c081d0010a0f0080c550006407000400c40b483c402c45018039002140c1e66403403030355150024181e5000340d4980c2c000440441c8540c1214401030700680c101c6940c80d4005001e104c1c81e01d4000003a00e10210504c3e17201d0028013444800704410700c0e4461040e889072500140528404800c1000081c060b007001107100840c6006e01d1b04a80c001844940150700100d00c10700c080750032a850f5070b03810004034240720b401c80d18104080800c080c0ea0440044814001d030282c1c210f0f80c850400f42070b0185505411700003035000403400c001207402030340114ac0140c00ca29008280007100d6000c0b9482e075102041c444c55541d180c10820082c80742c1c1d00c6601c80605814a404800e00004d21f00003105010300d402411003859035052100d18040c014441c1d10001c59028080584803a07480341103a4483d0803c580203030113114a00045044807402d201281e01a0f0304400c000310020204d05012a070a0000060349505040001b900740c100d460500050702c07019 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 456487320 1250 456486070 456486097
    0x13051002031902032505030d090c150e0901082b0509060a180602060c0d0506062101030303141b0a0e060c030c01180b01180b04020d0504210906030207140102 69
    0x2101060886105c41100806205030081c502c02a0000104040110b64040405082c00305e48001c0d1402c0c40b00d80c601c02540700700c4107400d089002e00c2000340c1043c08034a600c1d104035040300460b0707a07d000c00ca4a814426018009081c0c03c0f80c01c101d40d02c0d004070354500314039100d80341207030504c0200404a201c5a00c04100c40020512407207210401015209451011340280c1c40909030500306448140142d000e1601b000c002203444100046480e00d4160135140740c001c1c10318401507000300201840c01406001e01007980000c1c2090450300d40081010001401000840e030300050183c0b0440000740035030802c0f09502d0030802c004072092200d40c0c03410064100f0000004c041c50341e650803c07411508462a40c01500030314040400444049400724000c030741100e09820a0f94a030010741c582440003068000d043c19845803000c9021009007049038001881148140030036030b0b016100200305214a8032440381400013412000d010720900c1c1c46030300607202030b0b481124a60b20300c0c10032040003400d80c1c00022541208 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 456488570 1250 456487320 456487327
    0x20c1c0b10090507030e0c01050703140301121718062107111b030c010f020a140a06051302130b03030702030303340c0204020a090902030a1a061305100203190203 71
    0x60b803298810f940c0c000e00242400c012515945124588450818000034148040864501305150058045401c1c0041140d103540d900d6844100680c0b048400c040107035000a90080305000e88601e01c1c08440201c1e408035812640204110200a00ea500c56507a0012596208042240d00803101400500802a58a6007241980c46020103071406811100c0c00b404490785d169041500d0710045400352074038100b03292645400400100a0349030443c83d1400070030740d0440088440109030081014040300344204001d0150361036000641c114440c0c2c580010391b0009005000d9102084943c0c028580c04da07000d03050b2410844e441c0c00203407e6820459500400b102e02c0071300160741e20b00241d840c10b5620952400d1035080300300c188004000c84c4c551a40203000c0e039400903202e803680b4059850200141000171056640340740007117410020300308100d01e6a504442550700411a46041010390b00d146400207110310007a440c2401b00b1202019842d286420b5000420020b030003400000303200342805441d41c009507074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 456489820 1250 456488570 456488579
    0x110f0d150e010b10140a020f1b1302040b2a0d0e03010e06070504140d120203091e030a03141b060106022a011214011e090b01020c1c0b10 60
    0x940721a180075620403061043c43c0c030b01e01600170085c1041100310706003264a0703e05881c0d0907442c005400d07100342100d02c1030700f0203c5011207001c01200b80441d015034100d803902e2040b400340010b074001e03400394614400b4203129041c0500704001c1e100c0d507a0300e90702c08910800e0702a100024201383c4058490000241400c188075103c2c102402440d03695084070f4010220391824450051950280c0c0c00360f01c000c010701290481ca10750320385501c50200c40d0000c0084c400420040c2e406950703a407000701c850780108142c441c2d103103c0c800302100c0c000d48660090302500c440f080c1681d04035801c0d841d8140c0d102c82c3c0c120070f201351040d02d654103d5100c02e28a000000300046d5051480107480c24074540c561000740c1c540c8030011445030383e9421241c9a10502820401d150500645028025002001c40042d50301801000050400d445e814206408201804074400c01a1995011001c3d103e032920700b240540c1c040c070420003035802c0c404290714004000050340c00d0450015034034180a0f01e41075941d1044181600340601 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 456491070 1250 456489820 456489823
    0xf020a0b12010e010509041b0b0a030203040b0f01240207120807020306160f0f11060702010b0120190309080d0801030209091c21060902040306060b07110f0d150e 71
    0x50150403582c03d0402d06600d0100010705507030380184028030300e807040840089504103110f1124058821841300d04d44a44450031700030003d400880e82074905d036100380c2c00724001100c08503009040c2d0310700400c1d0307034140303414102d1a94245031842c0032081184111040001c0c0c0c00001d101031036440d4814a036183d51050a8010185002e1003c0c000c02039100d00c3d0364644208540201c60380324250380b01c0c1400840365041400642d0807080c0c1a01c00c100b180104c1c000c10440c43e90640c400c20b8400002d8996424803034401c404512512150f0381d07204001c0e4001d0009c00e039400c06000c1c01154280c424034000c0122a19500301c01e0400303042e0090700011030b0b5a8030042c0114640829410ba00040010007001c00c030500307044c0b0301d00a44540c218102804269440703071850346c00400d002d403940903501000f40030255a90340020025445440251095440c0010106200c1181d50460f01d2454010000010903910001088000d082c0d903000107601c008044220000907000701c0230007401c2c00c5001c800180300c03496408100e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 456492320 1250 456491070 456491107
    0x11805030709092f040c0516030e030105071b151e091709060306041d03042306030106020d08100905040803060a3501060e0903210105090c070f020a0b 66
    0x8500321301c41101000f00b0320300380525514920350407507021415004682c815901071040c1801c01501404d451169418941c000800c80e410a806600801c41652440c0048920038414040318449200d10b180d03d0010030039a0502c43c5040c4c00c840c00004e541280c401c10703500340c5100b0003a40580240c0714240701d07080c4a9051880318a0b00e800018007841d228168000135028400100b48910855884484091188407000c00c0c507001c00180003229903440d191542d61798031441d01e80c02110030352002c800080391800c0c8103054038100c0e0300607001807210030a41c10054600002c010040c1c071003854158800079081c81c0d540138881c05140a070300001d03503d0a02109100360058540c101e16207001080303141a6034926200710840700c082d54180c1c4805038441c408441805000340d580020b819040741e00501516840100041881c1d0b507140e5891041107480701c1c0d180c1281c92003481095030001c502c0000038003520501005000013840b8120700c0c40d8040c007550000d40340404542142607e86408148803c2c112030b00d02c00c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 456493570 1250 456492320 456492353
    0x218040c030c0807120209040611211b07030813050a030e090718090c2106050111010605370b0d06050a030503032a0d05040218070e01180503070909 65
    0x107000303214144030f400c82179410303920f000901500b540700c00035042c032565600040202d01c0780c41c01a9620004c104000790b10110507480027413020444000320301c90140404504000348481c0d142c160604216803807e891424004120002c8040c0304011030700054010b01090340c2861090f112510707809011070500829150090040c8140708161900710700100c1e07401d00c1c0b90215000442c003c615034590060032030300000d50543c3c1c0c0032102c0a01003a00f400500d150440015140281e880e6107040e0503091065080c1d03035180c4a07107070700322600c10455002e106025032408482041000d009035486002c0e08000e2007040f040d17108820008001c50001c000d600d2900410004080c00c5503040c13226401c41d200c8544a101c040c26440c040c90f0403500001070002da00030400410020841141d403035803e40f0a91002a05c0200d03400c81c0b1407000704151400c0c401040fa100d030b000314615503c51a07144849001511041c01440b45a40b040700741e0000042e5a80d4100455005072946c101d000c980c6c01c40901d4543c01581480c040e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 456494820 1250 456493570 456493573
    0x4140303091209030309040e0a1a0c1606110705150702011a0f01090f060e042018012010060902091e010c0c0e090601050102010501050f0d0218040c030c08 68
    0x51040410000422042c6580c1e0802c84594030114000080d00d18495040400d8002d030600c0694800d1410218904004a01404228040307420b009a040000103045802c1800c1200620252034142210400360704402c0c45000c0000d65852500044070103600452003c503581c1c1c0c0712403030082c003502003001400c3c1c210640d80000e0181c024420444070000f044595501e004642c0003403d07040580c414503050005100441d41c0c50322044e01d4802c014072007071820207090b0050303040001001c11504c90708000c400c685000c020003405e0600c0440408508a0b0814090717040000e0914003800803011003020039101c6111100800150140d800560152103641c1d000144c0d01d0310501c0149001e072074041c15804542290700c80c2d0201e4225403001038922a02150015041d020a050007017118100c2080071401102003038200d07095a0390f682c00490980e0402d0064941041520585094504040c04400c4c510b92009015880d0741c99044c66403006079008079000e54440c2e05d40d010070400c2c803901120320070140c20000c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 456496070 1250 456494820 456494827
    0xd110408011b0e010507030c0f02040207031d01140703050307180b0903010e060601021c0309080a030e0c040519090c0801020a210b0303160311160504060e13060509120d05041403 78
    0x240085e10340d0049a10140900001c2c0c0141d804003c4c0c00c802001c816035008004644402031820020001c9001044101c1d20441424071058950301078861482c2c010f80032610545840762070713601103d00e600081c1100080c08031072542c0e24103881d0f031260b4075005022a0200943c40b58190001c2600355009a0700c08000ca400a80a010f0b42c0d981c041079090203c0c0581c0411520301461160840080c0700b1303100301812945001c230301007a5156254000200580441080b24107240c612810001102c800b5030790346904800318404001d2320310302500300d6110310f070245610030700b5a503603220040d0986e030190210800045003d46c11030103140c50181d441d040400c80c060104840c0078684042540d0348a09098610780300025403411041510504200030906001e038250f60f03a0006410380400c0c41c0072180100c03803041e4144000802c009401e1440c40348038041e10400f1820342a09500c0310401800081c055162a0080c10700070380c1000d52400080008500c208030020307481c07a15081c840007500d54540000c1e4a03030000c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 456497320 1250 456496070 456496097
    0x1305010e130905030c1605010809030316030507050f030a09030305090601120809060702180106110d2007030c0611010c1b020108061908030301090c0c05030f0d110408011b 75
    0x80241001078000450700041e81c4106082443c514000c505000741c0903c9410144945401810407030780845800382c0b00d6200c00c0d103d00c101d07152030b070200300d4a0000314440c1d0103031404254865004260403d080742060352800c117a143c411140d035403046035402d8104c0d44a044490030035506104980d4000400303000b50242e541040b155450052403036001800011010135422619515041160807245c0e000700302c0e489185165202d0241c07403200348a0702c8041400c8400a0842c0b10011558601c40c4030b10ba501c008484c2c0102e10b070017450008405c2d0070000f034441c460f030100006001a10715805812640c580c5003503000c4904d083c80c2907400300240700701001090600445004240c1a801300111360908090740030766510305c04543c0010f6614002684075003400d00c0001c481d41e01000079816691010428421114071280c117a58031284528002c000d035104014208103244107001405140224200101c1c1545d050701051400c2d4100c0d80024000307035500c1c0b40d0726181030400c01d0480100d11550420351509d04c5034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 456498570 1250 456497320 456497329
    0x51305060c0d2106080a02090711070302010c06020c060c03040606210201201207050f0c0612090c0a03080a0201050a110d090f050a052406091503030d060b1305010e 72
    0x4a02120140f00d0403001c64031981425840d40d249140a04200308403031580d40031950b0f44c0b80880c5000368040c0082e040456441c1c0d02c070b94040316071100c1041c0100603180c5181d004640d0b1030310b0850140c4807117074244950001008203110827406540f02201030380e02ca080c2420500300303c4040d0750080102200c80200300722161400002220321540900b0810040c104441604484072030018800c103050180003451a140750354800a032190f00c0c06402203401a24200031450f076201c1510300081da2181c030501508802c0b840742125507621401040642d1084081003021400c20b040541017201e00701408034400c062554241308042d4020800001480f06000d000301c0c1d66980e104074041d030f0312400d842e950704000b404400c0f10390744010390307120302140c000d841c5038141541c5919101c4c3c8007484150440c240c22020400035106617000700c4004140040c3e54540400410300003c20000040c0c0600081c0141242c030300c2684038900052500e02c0f5010f42c0c8041450b18a04110060b8001505001700f520030701c0301c581c58 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 456499820 1250 456498570 456498583
    0x2070b04060e06090d050f01050117060105030a120c05060c091516080904060f1404060e0f0c0d06120303150501020106120f020d080f0c010b0607120315050d03051305060c 75
    0xc00743c8160b943c1e0190000801c00d1000030240182c03407482000410000b106055100b41d0403118510040d84081c25500900c5448007800c1c485e280e4594014000345020034040c00084a584440d8105211900c080d030343d40f9400c203402181c40030400380340800c2225890900302c10f00c8400103040d064940ca0501c2201ca0341d0384c020230403032001c2c180980c086140501a01c1d1580030341e0207000301e000c92040d0150354000d003501c1e605581414a00039400c0c45000500072444c40307081c074012041c20135001407950700c200c05044190041b40712450100d0b04c0c0d100000d6107020891a4608181c000d540100c0e01f50642410010409040d50150381160f15000c801c001c140d10b038040c45900140c0c08062000056024000202442100d000180680100081510125100d40002c00c0c180c00070a00034130958031190200301d810f014036032003c0c000205171075000c00c007644070354020024011784645495038647c071240492180e11a80800310080380340020900595000030349e405005041c1200c0313040c038242441040c1340c0c41d80c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 456501070 1250 456499820 456499847
    0x20a08070809031309050603010606020304210204021b0309040605011b081e0a0507050111040b07020906210f0105092113080d0801050405060108010302030613050a0606060c0302070b0406 82
    0x41e004a6039040082c01111210100d10310140e00080e1980b034020000c000c1500c115106c0c0d8a440d500107080350021041c0c40c00c440c4940611803050742102040c0c041d0380e90208080341e000b64200848019031031042000324114082500a54442c05809c2c01d000c01c0381c146400582c1070001c449148110082d582e0842e000362680b262840f43c4902d646802c00a22407415070a02d104102c0c081404c20046600c40040e240d15409035000740140d800c03c010101151146005000d05640304200364800350801e84070b100d41240c409813540040036046c41d00b500150214070949401500481b07400c201c41d440034081e8a402209480242001110314100f00d4260b9041c0440d612083c400420000003500803c9030a00040c03c0080550b911100c02200c01411000d00f4080c080c4120300c0c15020507545d500c10f0f07002c54142d80c0d0140082003d511480401401c490750200c041381e4038811411300781d002410700c1c013500c00140b03440d445002140c07616240c040e06282c5590024049010140f00800410341e0003000714421a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 456502320 1250 456501070 456501077
    0x60c02041d100f1d030a0915020d0c020d0b040615090b060318070825091b0e0f0616020a0b030f1b0d02130501080901060b04090b040b1003051504020a0807 68
    0x7840f180320780070301a1406a14040303980c80708550043d49044088000e00c134503140303030362003980c60398583d8403a0034076046a8614a0046c0d20916107244560700403402c101c01c0a0000b400c5141c070381090791741d00041240807241140c44a40f40c2c6600200100083d10a0001d401c080c0014099184020081000d900008144401010090002d01660f040130b1020002400105003920500803074081c094001420402d00c030400114001c0300013400b1105807017020001420a450200b12090441044407101543c0e41c1507948403508001040317140d0703650402842d012540100c400c50348503040c010031640789416841000428010000c0181031050f0901c2558403448040084604031840302002049008160030400240c0c03001484d4849100640c444008844090741d4020259803503021403402c2c1e9415220301403c0042c1888240284d40007a0003000301000d010f0000200155907800082101d2181c00c0b00d103000c60750f10020301041c071440040030380b0390042c10f44065141c03803050718005040030001800301042 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 456503570 1250 456502320 456502331
    0x60507020910030f0303020a08060d030503040b0c130f08060f01030305030a38040b0f010c030809030915030a0c08040218330a05031203160908030301060c02041d10 72
    0x42c0015a100034051608141068500c64080c5070240003540210200000b00f0103120014800c1c0c90300d0031050103a664503640c1c0c507082d070300c07103603100003801fa000351002c04a02c1c0d081c8812000e0542100c03400004100100d000b280b4146040d8641d0704040025202040d01180100148086a001030440f600481440c070001640c2c0074881c030301c41182c000d006240c142000100941c03448040e0040c0c0701c0c1510307401194200560400c1600700080b144c0340e00001e0703002c942c2003000100800e02034204d0542c003110400507286400c10700d1000643c500c0d0301c0301c00c4109224012060090782e86240c82036030103996103410401000e06207a0001203002d024020700440d80e90607600060310101001d68191024400c08445032804603040e50354407807100200c6d40c068010718140c039002a40345800501d00d60504090610103141d6102d007100d03660b00700e841b10a03400074028002e4000a40c030a041000b14001c18665440d132246002e10f00c100802d0f1044031049107070f00da000d03000c140c0e03010001080c0000600030340080040d5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 456504820 1250 456503570 456503581
    0x9030307110a1e0b06030a0201020d0c05010603080304120207120c0302060f090405010e0a0b2d0d05101a030c10050d0b04110318060108190c03150902030d090605070209 74
    0x34000078648000c01111071009031041407001e0003c0001414810440784259990b400c00745a5181c10011002c3d0041e480003090017142801860310b000c10600441c0041010303038aa880700001544280c6046500404100524030060760600514020f442c3d803c01d03090003940d568855103503401950002a20800000030b204a04800a808071204014040d10a0040c0d40e5036005010b0f003031b44200d030b64a58060031301c040341c00f00d440c0040c0b0b001001c540100b04071200342000b03111003140c0415840d03140d8109200003851004140b040051280b0466410f0000c54101d80030802c2d251a2540000761502981c0301c05104042a07440aa0340d40b04498646803d58644d58070454003000351088608190300070785810340c070100ea0b80440000b180b0540460360b18401405035003501544e507920034421100a46c01c01c510520328060310304051091107000d040004d10700c0ba1651100c3c9a500d80d103000b80c2c0d07800c540e610091030440c01c040c0310700c00b026056400c040100e107103083c00281c13a510802c440280f003281907900244 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 456506070 1250 456504820 456504823
    0x21e070b0a051c0e07060e01090e090316050307060c05090607031101020f0424080c0703120f020a0f0806010816080406110f030114030c0607031107170705090a050903030711 76
    0x10b1a1012421048020481050503200106000c070345140131406800c10110701a401101d00048007401a95221000380c900300540450200c0030744580e545020801041c0462990040002c50f4540904061599003189113842c904440f20b0010104c1400070a0014444c141da840041e65103941d01410030300b4011507002070490080c401c08521681100c0f02040109030030305141c62807041c00400b031001161100c026031040c2c4e071003001224285030559017004174200182c404c80c0c0302612809911004115032104c1d01700b8405a0708003842c20000160210900300c00c05901a60442e000300003800c281140381000103003208052800f002000502405101040c08c11405602c26810700d10b16011081d1202000314010440f54001c2c4901c0410201c00c05212140b483c0c04103580d2200700e0b00500040c600b100c940e45c1a151014100b4103c4001d01031860700042d04080118038802c02010301d806404d80c682032400f000445403020b4150030300e8034682020080e0410300041103c2e0804100d04020b02209003020006 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 456507320 1250 456506070 456506077
    0x5010312110726010b0d020f06131d09010516020d0f0207030f0c0f0603060b07030807120905100f0b0306060d0507091b030608010b03070506091302070b0403021e070b0a05 75
    0x52207081243d056a80c1c100d280f5005034800034400b6000303000740082c3c001040241200f074400a5480040c03000b0140305890560000c1c0380c824078548684001c680d5510181903000c100c401c8412401d4500e004100d003441c000c0c450799902441c82413484209042d1000001c2d42c4e11003c04012050081846017051641e008110b08001581c0c0803071424400090b074501000f00c0215071040341c402c2d8506000105580f0700a003d00d1b002ea9520303403416801d041803a181110454009440700080c0064000301c403c2c03280d114000c0108840c0244024040400012603800884040421640c0e080e890a030760511903a030040394841c0c112200702d94119a5641c1401c0c003e05101c115448030b403445150000702c07981111841080014811707244c400704011641e50000c1426601002407069068002203010301c003918001000c0e220441000e08551241d6081d20011001c9a01c641002d8882002403001c000416604000b11000c0c0d4420704109441400700503002551140b082c090601d44d804049030081206203d441034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 456508570 1250 456507320 456507329
    0x51302040510080c03120304120905100c051216120e09070c030f0f020c090a0605030111070b06100906050306041b080603011a0a0311040b180910050103121107 70
    0x100118203010342103038402403080c0708a00150160503e005038074175000c164040e1100c0c801c09001c0c5550340e10341d226006e91001d0311401c000d110b000c54003c21035445500c59030300360310215150500b9103006424607519240c0050f800c0042000e04004802d0131400c0c003185086000e0b84144409812599004152030304001c40c51a83d41048401c01008035241c1d01071081e1080c5030090701c80da60642c6000030101d6a080c0105141009a8131034070b800c0350a820301c0594164401080c00c1c0000792561a040000e09669128100407015034000c610b603018003114540d01c640025048906406200180c00f018080304194814407090043c0030000501c181c6440e040b480707400f0b0803a030f12240c0d00c80303082c200542061f030240c41041c0650300c0c00490804140032403010a40202d40103184040c01480d40d40c802c001f807101d0700003080d0400d0b1582c4024940351034000b801180307503030102510403262512210991606c501c0030000e10086051500400c08214074510b001030040c1c85281c00c0041041c40c070070003403410000b54003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 456509820 1250 456508570 456508579
    0x30909130b0903030a050105041416170a020a020f0106060f0c080405032d06012303011d0105010510052505010b13021b07050303030f0403090b0a02010b01090509040f06051302 77
    0x402400c2e01d40880210722a02500d0340810a990302c581c00e2104030f13491042c50700c12181c880008034960a04100b24803000c040b4030728050758520f0300c41c0d1000301000f6095030071121840d0003090840303040d901800341c1d10400d5a9003000700103140c540301c1c004114031303049111081442040308944d02801003440466010f014040c085034000c04140308440045502845c0d0748400405580c0d080420803404500036040758891904603030840c61a80e070b000c0080c1a5522499070665940c0565201c411001e810a903501e80000c000003519803401c4180001d003c2082900ca0411604100181c0c0c4091120701d004010000309400107101c0105282c5a80103140780030a159020400380f00c10300e8100030580040600c051098050703515003c02855007991240b1030b005040e4590402d20001d0300002d009458035034420301911f082e03509036944a24001c44c1c3e40c080041080141d4503400d18160958008000000404003600c0582007458075403a1100842001d2800504061303c400202d9041624003d404803015001132 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 456511070 1250 456509820 456509843
    0x70f06020d140c0706050a0c0b010e010812031605090a050d0b041b030c031514010f150806010206060409030e040f0e120405090c090d080706020c061803090913 70
    0x400295861000390300c1080002e0035460810b400c0c00d504402d0b59038035600b000003000100e06000060301d03543c010844a000b0080840c08000114075180c01c6140200091511022254145020b0904220036001c250000c210100140134540c07407071048400c810b41c514540342d070301ca81a80f000100103e0361544025400300940251006201c24907401e580a40d01c114403c040080c080e1403c14000e1006200280483e0415481000801c2c5400d80485458010100009800700a520044043c010a03045418068025142404445281560a000c02c120b904140d281491700d880002d645000007411603028a858046c024101b6015117241c21058070020030603c0300c0018810600b0003000210b4007401c4521642081400c4414000c00b21025502c01900d490307000e580c0c05050071000d07840b240c28103801c21042c5030f124000c26004009003480a10403c005655421620901490008003800306524410700e035030101d2009034000111501c260050340ca524180d80e552140003078601401c00f02900707140740603 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 456512320 1250 456511070 456511079
    0x503131a1e0a06122603012706051f02010e0715140a140f0d020301060503090c01090503030901030c0e0904080a020607090513020d1b020d0e0d15020c070f 68
    0x5007800ca00c0403101c4007050340c0320303600c0b501200c0a4841603c030340024000194140300c00b00d08501c1460744601c451412005031254515040030050f80261f0200303c48501c5030916000030950101c2800b0ba00b034404005000e800e0070880001c42d01c201501c10b92130f0002c0a18141e000c094000e4225080c198005020354040030360714080285801e07005041d1f00001134101561040ca0f4400c40d0650307801c0e912035550003000c0d0790500002ea5007513014800314100a0024840d107107590b1304074001103001c1e06513a900c154490406940842c80e042c003000055060241029091042c0d40300001038554400003440c0c04110740f0243c05069074180544444146c000f103d00e01000140034000c0000e08100000ba82101d01655821004440310012400352650110b290703403400762420015000703480044a002d030001807940110034400140200c3c03110100261704518400c3d8000da40124806060700303410380f1009e01c60351203551200c0f07001d414084070003240c59021412402c41e51041007040050a030385c204524105445 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 456513570 1250 456512320 456512341
    0xa050d090b0424020f18130c0c020a050d050a060c11010e061e0f060d0305040b03040b0405010605030c030a02060304031713150b060d0c0e150c07060f0503131a 70
    0x3c03c2110701c2140b40d0389040160f00030b6244202d40c480f50403040c41604296452084240030007501e0350a65101030314000782003807103220748a04030300d651160322030a4141d0807903c1803040150700b80d40180d00c100000c41c001404110041040c43c4030b0703a4881e00016021541c6081621608050b4030038400940c03821a54810070900090014003404000142040720f092085490611600c04c84a4403488100c02021442c0303410030502003421a8070034205203081584a0740e150303603180c00032641507a203056110248028098284140800b030402a400b42c5000110140030a50360403000000900480c00000024181440364015400140001000e01818113081d0400846010400340c1640c4059052604803071802a40c0311716142c2c600084d020fa07040031020301001006140480306030017400440d00180724545d507a40400c0105561f82500c0300c3d1034a40859a4a01e01940c58001c501403240c80b01c0c400e85143e400c02d080d281d01201518a45004d003500b07103032005041c0b021010028601002e41e051000e906e15 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 456514820 1250 456513570 456513593
    0x81801110309190f03050a140d0915150302010e12120307030c020105040c0303080406150f08120f0f0a0215040c061b12050904020912010209130209060a050d090b04 72
    0xc000d0308070f8290440504103107020b0382200d0307001441214042081c000007402800981007800141c101b8040701541d02c2c1d6003c010354420440c5164450f940c00030001001900d4400404402c681c840402120000c43c90710300110b080360101034180101802c00c003042d0303074038180c1d0140020240c1003580d00d46512050040c0c0c8541050390840d011038144820400d21a10500c10148280e4110004100c00c626544043e28514005881990450384600b56003101e2039410608000801c801801c8800c0580f810340881e042c1015080d00405021081207982c4403030298006803540d0000d6405400c0d174800d00440305a1a00b41c0151180101c90382c005c0404c420700807404540c00445040303480306c1c45075040940c42c0517400c04040400410002d451074160650501c1030780942145900a0801850000e0500c0015041c0c18034440b0040c95a40000d11140c0c24106130700c04550240828005500b00900d03640000d5050040c006003008201c0c0200d280000c0940680107118100e410111110741ca00301401c0582c101c0e103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 456516070 1250 456514820 456514831
    0x70503041512090b060108060607020907080a0606021b0f0d061517060f0a0b0307080f01150b030c0703030209130513050f0d1707051b07060f09080a02010818011103 72
    0x440042e002c20700d010342c41c0a445001948842c03110340c0c42c0e071960010f40b58420003501c85500304a00307109103c0103840e0700e071495000b06516107a03041e6900d00f8102c00c50030703981c3c035800640c2150024030035441150041c0340c40a459600032254442c07038404800c00710300710000c00700c4003600040c2803006445002d8116190314007655210484e80048003038031085596545070a0310700d00034104100c00081c08440e0103900100080f80c00401f40c510440c3d80b00302c458a003810340800051242d56804400b41d0710440b114444d0001e06454207220705501e41281880404d020b0b6007406000c1c5a000181402d00ba51556405054010000700421141c1000c1d1001c1c0b0b112001900119a039103d940d001306040d43d00020340c29066880b69489414041c005003041101b00006000d10741402401d111100c80e41c40d07603c1c880c469041421009207c1245031072001003405241004040502c000988140500c550221310040314607020300b4100c40d240c0300c3c803520790030501c04400d08145551900500040404080c3d0045002c1d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 456517320 1250 456516070 456516077
    0x3060301091718180f061207081c02010501050612040512070f110102030f040504090206071a0a0b09010501140a0207092409050906040f080706050f01031209061d0301020705030415 79
    0x240a540c00780700440e0a446080103040c10f40c500085c5003524114892548000050002c3c4030b541d800c09511880c040c210b800510703080c0c01002d011201d200e0344000041520181e88020705c01545000c01145191140d001c3e8071342e20041b500c000500707000040107900c41002002011540e540030310f0801c08420082c4030400c5030342c003410341560700d0550300c0081070301d181c2d00550030340c01c0c58541f4003820400200188842240c208100b802601c021460305410803448000702091000c0c00c0c6410300180702124020174159101c0d841c0c00005100c070366804042d14694003040849a41d551420000c143d01d0480310f684a03074501820240e81440c50560b03510641205c0c1001f400e0f0030042030b1512082e40039184121402c2d01180d00000000300030400c07402001c14000c0c01100c40610340303882911240d081d11021903103e907002803001e0040003001600100c1c3c1207000164609650311506003a8000c1031441e0340d900000b040c00e00007640220075607080d4100c0b00d0003907210040301c0d5203582c0d0388500b01c1c1e0480c5441c006d0021 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 456518570 1250 456517320 456517357
    0x903040f0e07023702040e07091d0a0803070503070e03070303030609061a07020d0c0906080c1002160e10050915191404180803090106030203100b01080606030603010917 74
    0x4000000000e4070350081d010540400704c0f00e103409150400f0160380d000d90740191140d807210f41100c0301303000c8000900040f000c007141c2412490240d418183c0d40c148442e02c00d5110642a40c00710780c003001520303007000062030590317a2616640c00032642200300041040d40f501604000000700b54056010070125440350b4000d0254941c0c6007205a40e01c000c1c0c580d54950010200700040c014540506581580743c0300c0e81c4068100d0351035101e050b04460082d000488260302001d20320703405280401c450321002c2d400344000c0c082c002010069008041640c8640b40210481ca004551b00703a0b0161101e50190501800104062800507560303500354080950603030140803410104580d800324030703002005980050780c080c030707013080c3d02018080101401d0b00020f80071914400c042e4000380c402c40c0254015210440041252804c5004242c10401000c8a283c9014030b07241c1c0e008002d0360004222544200226401c503103036610600428003400361500001d010408000301804041e41400c007906a602800149a41 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 456519820 1250 456518570 456518593
    0x304061107061e150e01120318060f120225170f210903070822080d030f02041a0c0a080c1f1401050405071101020a260606040605030903040f0e0702 65
    0x15421900e000b105c465000c40c00040c803140503541d419000642c842d152a500a24807503410300e0000c0d101ea00524000340000214041b103641c0500ca0035504900d07400c045241010003024000c107416081c801003c2c22220321f92031014000d1182004841021a00fa0665180c15030360114109900500204913450369030500318400ba4298410584641c40b0030008518000c0030f502e54004a410490f212240c40307810960207944070a02100ca1401007400d08000d290124800030041d00342c5440102e0030402900c10700c4100a166030200000404081b0008200d9442000c0d0041e113041581d0401c01070805000051854510380300051620603906003007401e0b0040f00c2024503850240c40000340880111500d0740018170407032a140d400030750060f0150a2400c0701c25445101d09007680c000e180c00002146001c4d0400307040350720700c0320308084150041a4805561038180c002035003d005074080c1c2c0d0f080000100005061141c10400c80300a0820f5805a20031030b40e8850b034007062400215a032400501a0720010780 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 456521070 1250 456519820 456519851
    0x2109120607050a1808070b04030b06240f041a030108060109090506040b070e2812082a0109150c02030c120f040f0e01030201030b01080106050304061107061e 69
    0x502414072a55a10301c0e0011096003103807510040848000c0404180c540003907040b1082107424000c201003100d10f5201c031700c0d5040451f84d510300188014020613801c842100c07000f115a41c1304110401600c04c26403214004001036940d4007544e000348608215040c40c180d445040107010314101c805210460312680c0e01c07002d1941c1078030b1400800030074550016010070002211014401c0e40506285000312130016048001091741c040980010318155080005106003d421004100070b000ca41c8203080c0c03600e100d41c3c0e5800c0c6130301c55050305044042101001b49090300c00c80040400140c000c40c000d00c081009420488140014445140e6a051038540d9004180380040b0682c3c02415002c005400d2080d1b81da1120311081e4803c49469040c60420840480c4d0307040e440f00041d0203030800041c007605544c154800941228400310b013050500142d0401040102d41c088100ca5001d030703100b0000314000141010060003402042802002e0504084500c070300e09043c3d6400121001c641039003400780703110a55051 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 456522320 1250 456521070 456521083
    0x120409140631020d14010807080307030804080c010221060109141f021006060c02120102040b031f0e040f0312050c040605070515090a170426210912 65
    0x200d50111551080c00103904120740b10b980a100c0901c02500e08045000c900c82207032002c0204100c840720850042c071054008000310f002510050000f14a09130345501c0103008510300a100401d600d10009614a24042c29015281820083d04102c0c4074034002c0050707480c0c1801d041300c2082c0040e9921500140650318000e852260f0f41c400740014283c0b0201e02c1c5202c292150510f54035040d4852103003d581c482c0054410000140350030f81d5030700c0860100d841000711401005a900742c1a0b8018407050254496400413070ba0801c5090841401d00001d0710307850030050019610000510310382d903040009025421a900b940e2520070b41d6103040301c060b004610000c50f4410b442c3d03184242010720051103007600803802054842e004404a8222404080ca661a0700808a840d0007241d0031000f000410040c1c0903050800b80d10307081d0005802c05060a0303c81c40c0c001000282000100390721640c00040f241c1c00e02c0045205940c002680d034212540020070310641d0700c00c41c030300da0040c10090542140c0ca0343c0030030103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 456523570 1250 456522320 456522349
    0x50a032705100c02010201060b0f041a03040201050927010605030f090106030506060f0d050f24060904030e0409060c0e120f0a08030405030f0703080703050f0f0a0c021204091406 78
    0x2400040c0702c1000441d2030000b40c5100700c0c10343d907940c034012405059580141c030580d50a03028959641d801d017003400c0f02001d0340c2d20160810b82c50a0040c400140c1e0000107803100e07858180d61081e901c90100c103e03408240c0b401104010300c0e00d031001c00440c8050b4070030015881041013040b88081ea881d02046c5c0c0382220703014071014010fa0802000320305185090012441140001001d00b0100c0946440d81d030b060112009101d82241d0009071094060b007078200100f59109a12561302c2240d2074401c001c50300c0380b50001d2008040242c600703c000782559482e440405c010350008401c1042da9141a40941481c01041e156031150540240d14101d007071000410701c240c8007060016001c90462a5900e40641d000600203e50501080c0050380910241c040600031003402079076200c0d00c41c1082d0101030300720b0f08094054440740c60170728101300380e80780c44c2a98944c0210200b000010040100341e0b00302d08200d003500520350f92040c009000038001007240c2010a08140c514010081c0da29a001003042d6980500c0300c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 456524820 1250 456523570 456523579
    0x70b010303110a0c2312030703050307050714010b0a0b07170310030803040602030619051e03100606120e01060509040f1109180f06091513050a032705 66
    0x500010b0310948407890450810381c200c41c5590810742c1e0b041c42455003034000c07964501e00c0c040d91140400c40c889030850580300544900480404940070580c8034429901c010b0306021000010408041c0b040088600c515003041400e10b0000c001c4200d58081c0c10360a1015200e101a448040340512040b001c031040b030b41d441611f10342650400c100703c0c000c640008044c8000d0310181038001022820072401148141d04c25040141c2c3d07480c10000704012108800801442c0858034402881107858070020342d15a0005c444280c045110300f240024a1b06c00c1e80207114031510706142d4005000364104c200460b00e44940c040610032205004446030032a0014800e00390f202c2d11900100780800d4401d54080311541c0115885411030305540042041158144e03a509502041d400d008801030900740080000124000c01800036420994a403694503001d451000c5c0c02086200f0100e40c01024007200c200b065503100f000d0380c1090040c2d0401800540480302400404d0440f00840041c3d0908045240d0135224001c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 456526070 1250 456524820 456524843
    0xf1203092705041106030c0a080108030901120203041506090e010b03030304020906060f071a04140d05180a08011b0801060c050d110c041b180e060d081603050403020f010507 76
    0x40c0380c401801d0302420550300600d41e000070703200c01c0d05e0b100020740c0320b0021143c2d49079551441c400f0041060805030300011041d0820311032000a0b0703a20070003c204844441d017016890303807120b040132444102c600d03c1e0300240918105000921000a401004802108074000c10240840c041815103034401120001d5000c1e210030009042481c2000c060060704000710101410500b05554681201c0741a48952010126000400040201880c4068080d01543c40130303110300d694680010f40700f03004260804600c0c0c00c01d10100c2074180c90b01c00350480103010100c02441040c0200850072660b4034500300c01e4000900319000803906500900c0740003440d5602200410151060600c202e82003212241080300c0c40c0292501400d03155543c0c010f074200558001190001910101f001400f141d01505041c0484800440100985802616070030340c04a01921450003980c3c003403070031901e03910581d10019100803400307441c1d00902d644003000d0001d403442903d100c0d0349440701c2c4005481600690750000d19050300e04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 456527320 1250 456526070 456526139
    0x50402030c0705010212010f06050a17130c0e0601140a0c06090f0210090807150c0f0c0803031003110603010b0702012a060f05070e0a060e0a0f120309 66
    0x95006660000c0d00480d1281040c501e039a960382a41d02003004c18985030402e90050003c0300c3c607007221400600b01411f10610b07025034404050107207044146160100d101c841f001031801403030042650103195010b90f2800b00301e41c40d140e59843c052015103805000990324a0505c000c1c40104040b100c0385511920340ea15059110f5031810003924040306c08440503404a0800300c0180ca0300b180002585059444203000d903030030044854a8007280d9800300c540c4c040c85600c4200307000e40240c9030b50031407904850078852080d00e600300541d0200307050303000840901c400030404c03c500100c000c0c2d40c01642e20a0f0410703088103041504202180c0028015800307541d0081280c0d000660050f180803007143c0a9007045400308008008980b010b906600c000d40301c080d1181e0b82094202824850715900850318200240c60304070020100e0b007401061b004070820b0000c0c0c425204a10356615041600400420880f648020b440704503403c00c4541e055011408103a9014012504100d05030740c0000500040b0107002428a94 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 456528570 1250 456527320 456527329
    0xc1703060604050409050d03050901022d04080303132006090609030109060507021f270309081c02060f0c0f0a0309050609010e07060f170a0b12010b010e180105 70
    0xe000503501c054100b0000450780c03101c1c02182d40f6a402503018002841340c0355406000d6800c0104406030f503902c10481032100c0d41641e981251841c4030303d0b5110f44403c00e10b0b00b00341183d02c1280c000300340f9031102000b0081c001e001922400c0210303114030320440c146000b0081842c85035215045003903000c01e060010b00c4071801c00030003904001d80014004640e0401c5512480101e42d8181c0d40758005800501c0b860508030041c0280709035800818a00308840d901d004220300c2011141d601d8141003240d4040341e4005d062180160318041c040b45020740707040c0802c069130002da0441c00300d0702c20701501501c3e0010350850807401546200e10218000c4d07502c0d1858500004043e90b009e03405850078140e230b811005000c03d404001040c411400440002510010203028a203000c900d035001d10100b0640440b50900558080c0c403544003400444240c4031152250300700003018018900d6519005586a826840c00c11815003143c1050042a2a4500c06c007400344140300e0104c202803003450000c40c00340010803041c200b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 456529820 1250 456528570 456528577
    0x1103010f0303020d1404090f0209130f0e16140d0b130b07020309010f051b0723060c1005041106030906010303080a020a0903020d1b03060c0201060e090d0806030309040c02060a0c0c17 80
    0x9088100524203403031107001507511908005902406940d070510780014443318810109110700042c0200814030310000406500725560060740703150891391400320a00e44441c0c505480b146d5000e6a450344901e041c1b0191036598110190170b64802c15000d012514460012007104d07100d460607903800c11041d05903075041d901070b4000b142d00f00000e0355507648452901000c0c00030801401068000c240d8144a0b00403d03442e421052410358842c08041160a070381101c0012000c69011000001240966a40c2031903100b400900d14146c0d01320000004204120202052107030581c0d01c242c80d18921520381200c08400c0340152400c0f0004645d14503800e01c058a404820401d030300e4443c0001c0c001c5224400200c2280465950086814680300e040c80800d0350707028001c65000d050400004c40d120314042204580e22212503c2e8003046c40824004510b00340c03018800c13540c07a00c401a005004602c250030b0002d690350ba040b1280350a89260001d540240c2c1c0c428081d00c25201e80000c00001c0c103401c0048031070031551 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 456531070 1250 456529820 456529841
    0x7030506090630010501050a081617010207020d11030601080c031005090c030102070507090e0a0b01030204091103030a0c0309080f1f1e020a08070e1507061103010f0303020d140409 79
    0x20780143d007500700008680401c000641010011a0319458001407202510f515017184005800010300b0074010305e50030507100e00705c526444501030701c2440044001d00a125000c406500104641c0d0440240a81f02c002183c0041081e81240c1da160b0703a43c036141c2e44035155622001d81c946c00004568170351410340e030092500420b0080c195a014103500c1c000074226444688121101c4e0090a820040407002e4400c80d540d004211018004a8401c0d41d2540741010741400300901c070f1543c0703294103000d00c6908090305d034040b4005000caa03900c402a0401a001c8650040200c00007601d8440114a00401180d8000c072040d140c40149040311404d02d42203d0b01e01a00016030945a0740d040c490005008914041d2407140c0c800401a80c0380040d1500a148030401000701040c00001e135000c800f280c98071070200110805a000b01511160700d4a030800c082d04000014401f201e0020001040b100110000501141e00c65021070740000c0e011a02a10007039072105080100140a1008000e4001a904141e5a46 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 456532320 1250 456531070 456531109
    0x403020d0f1b05072402073605092e05090a050d0302040f050904050a030806030312042001110c0405070905130506040f0e0a0807020114040602030909070305060906 72
    0x21a0103031040c0120081c000f5155584441010010f41d8031310340d28000c0b00fa840d0304d9142c2e80c0c88040b040103035a80400c0d01c078110030194148842c0d81c035070a02140140340c032001c80300c42000740c0c5910201c05026203400d4a0f100140e000b248441401e007000e05140365480103162050744001075030304510340000c0c2001015000b02d0702590b050000028005e02c0404c0c81030519480041e252424038083c2041450140c00040c006c40340c141c280008205c00064081100c1c2e814688184195900d0340802c0c25802800042c4048211140510081003683e0703421101d03415004540380031160034007004440801110503400303520b4200ca101c0b03e0203810180c01460744001e0904254400d565601c2c0401d41c40c08504615010565441c4248601c51415005101e16240000c0d030612100c001c100c0c041d5110611003100a044180c0041c0140071a4040d822429000c5031180582d41c540c0d80e00c04000c3e46940c0400c40740352151041c88d0000311071600a201d100d0180e840070b016610316517900381c14001c0152042004c840f19 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 456533570 1250 456532320 456532337
    0x1204080d110708130603050c03190b060408070302030105070305061f170f0709050118060809190b1006090f0b1606050709030209130809091b07060605180403020d0f 72
    0x4581c852002810110700c00c04003141c2d980c06001030480f00704d01d0b41e00b040040608100901a18500e00000d070f907042128559811103615008400c10000c00c106510540c03c01000b140010304801d02141020072680240c0c005d0040b6612000124101c503000c994480d84414803c079071491552440c0540d2000606506100c0544910140c0c0b0445a620884500030854044410000543da01514143c000c12080c04c2589147c00812407a040c4000302d80540d004101d07100001901740790040051495042480c6e0140da01040b5a0034100080b120440d1a00c56604003e43c4c00101103108034040c404462090740c052840324207000805c206641700f110100ea00c02d54034110b01021071064030070580900103a032100c1c1049455481132112140c0020812041031442e03941010120308071b1012074003024012200d85825903100c40b518115550b801d8a08401803101251680800a4a62048051b9182203030354609000c042c2d1074010104504a030700070010703081040d040c01e282d03000e42c0c81c0340020440703400c05951 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 456534820 1250 456533570 456533591
    0x908060f2e090203010b0306030114010803182e110606010915020c1e2b020409030c0501090501050709090218190504020c0a030810032a080609010b01141204080d 71
    0x182d130000e0704410140d480000030b003c800d00e42446a50781c014031401002c829985400b00586e04c0e0701400320b2481000003400a41138541d994030410a0385e9040c17004401104241d089004501010605503060104e280c2415030f031420761000892a1040e00c0513542d514100c1c1c24001e02c4c2009400c540c840340194801d039500d60710180c3d60107940c102c050000724910924040170f10100514074900894034003059840c038001403100407610550882223501542c0209008400f85000c2f580000c12000150240d481c0200f501e01b00132064102d5409401c141d0b0301e602c4902d0b214401a000ca1040150050701d03000070403005810b90031f280caa10342641141003070410362295540c0200c1d00740e07400006690303020b803c10544981091b0b0042c58150f0005008070310303848100d08543e601e071000c0c0e0104041c400e011500c02d03132207940c0c1c910808190307014250480540d8a9030601c84000e9029268800d03543c1d02180380f01a8551032400031609076220668800c0d940320003a140c540303800da02c1e640103200c034101c1c041c0c48110061 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 456536070 1250 456534820 456534839
    0x7060506220f180f03030c090f1a0c1002030405011d0a060f1116121704081612020c01080f070905060702131e06050d11040b1f0908060f2e 61
    0x103c40c00c1c01001340d240d120081d85002400c60f030041c0724600600c081ea40e0244000ba90283e101c0056910b40c0c4110851194210300340d200e07a01078024018880c0c86141244038080c0410f0b0040d50069200c0c0e802804000c00c00742c40c124002c0c4085c54212815800103500e1008a0742541100014002c454000540c038042242d00c1030b055072046001f000101100d0b96601c3c1082001102c1c080c9400b902d1410a8640c085098080e603200005040680303142c4010801030490b071000000032544980c040350b401c07080c4001d0708000c1c2d05c8040030303003c11740840c401400041020a9080a07548100490b64440764080d007021b04101850f04079050507a0410b08130682c0d8007490a40b0710505601e80c3d80e02444683c00c011400c5604260342c4160400d43c080e4000542c00800120010303409481c0b24400c640108956054402003081c00200d001d005a54108c1d500c1402401c1f900090301400b0381d0425030541d000c0c2d43d1102c84101c074030407041c2d88950410700c24040b80314215440e0110702034101d604000088240790b0b01c2d42c004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 456537320 1250 456536070 456536111
    0x20c0108130f151e020301030507060f050f03014220030301030b090609010b060409021605010c050c0115140105090a0f060513050d03090b030c0c01050c07060506220f 73
    0x2d0040544c0e414040030301028450700d145906410721010762540d070460341c559403295064481c0205102c4c2003d104002c1034065001e0ba100b5249003071031243c5a6039110040000c4211400c20500e00c4072a0110210b80524030142c069140c054441613001e07107040c02003040f91000d40e008240080d508000300407146000d018001540218010fa4000095007029650281042406445400a689400010303502038480205507411561561001621400360021004a81c1403242000f0459440d007040c0216041d0410082c1041060301c40007004031801f812045c0c1100d18081c02007000025182000088640c410b0004282d860800791900802031b41d2844000c902d0310058101d903000c0b400110340564203d14420551000382012a44c81c1201c416903180540010701e1401036500340400040001e09022441d8226803030100010002c2100f450010342e1507186070405601196000d0034100480c40c146069010410a00e00300c00440209008901540005000e150b03a24800d4640310800c030600c019072007840 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 456538570 1250 456537320 456537353
    0x180c0605090a03080c0c19061103040e04080a0905040c0201050a0b12211309060531050916260718020703201006060203041202190305071e06020c0108130f 68
    0x8003101c1f40d00300107000d4402c413090281c1041070b038001d000400c0384400340e403003494006400030a07141d660403006030b003103034a6156074210b02d0b009814100036580d0a58150700891041d11102d13800c0100c8131206007085480300f020101c20000307512030701070701e0741100c8240c115020414091011500d429a24185400c62204940c4101802a5101000c00103410300ca0040e009440241e2041d040a03464014151803100f02540c240b490160358400181442c0030070451102c0d400840480c41e841607544030110400b003c11241c3d420741e00070501320761b10b4818400040c56010791b144560000c07148125000b01e04c0007504211402d90822105400b016421214250400500c0709500041d24170080402c1d9804281c95040d4020b004640c401c00c82008403803040c0241103d07a650495820200d083d4400390300181c43d44507080036140d40609180000c10940b0803103108021a00001d4424003140c2d28007059840d0107480d891640480c128030002440d08509405042c2002e1042c0c600c018021103071b841c0c2e03060138000500c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 456539820 1250 456538570 456538609
    0xb09040906060f060206090c0108040b040c08070b090109080f0d050307120c0e04054b070f020f120319090c03030e0a0f0f060c0510180c0605090a03080c0c 68
    0x1428812140e040c02010350081e47e03a4018003821001500090440f0f10081c4080c15204895011408001021042c00000c0007054100c2e5642c030b4540035003004541c00a014240800c0781881d0015144101148910b10f0080603c0941070301c0c0008801036455510041041c0c0400000e84030104500d0342ca8880c403c2c1c074a580303070742d6045155800c60a02c41103e401038a00c0710b550980c1c54055150710b40b00c0841d030000c210201d6140ca0144c3c6680c08003d0407900a03010b905401508c00c00b080030b01503110803020110100e944c00c039905c000c403405419480d03400b5000d0200050008000087c0c1e42118071208001c0980f0702c01001402e601d0907240d241064143d5001200010140041c041551420509100c090600808030641c100e14000800b0380e0041c0c584192014022a042c140061250901050309488844002848017603444a1644a015440e14045600302074005012a031544207805860180d40b02401901d030050964640c43e40c541c000d4080c43d5014800c0740351801c0141c4a582c40c0a6188c0320402c03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 456541070 1250 456539820 456539849
    0xf06010314120a180e0603070312021e0607020c0d0c230907021f1103180705090f04021f0f0c05010e0a03080105030106050d03020d0f180608090f030301050a0b0904090606 75
    0xa44c2c102c00c02c46a50b000040803015941401800e543c041945001c9a03400706c3c80b55481c1d0f400078000c0c1d080c200f10000e910380854078200c03002d00403c00030480030300c107520310713400e0782da52700000001c0102512004038094060454017600307001c5c01501a545010300340a00c1c404110200c2d1450015642150032102400181c1001c0440e0000501b001e0304002c22a020080520000d00403410113980c40c00300511610081c00c06544903883c503802400a48090000500740c00a1403034040c15038070708080196801c034019240d0180c03380c1c1c0c990030101e9800303004845580d100070503048160126070080c158141661030b9583e07a0f10406035200c0402c2400d640b01d2184d203c09000c0e602d4141010300311100d03584003600402d00078007140e000940c0401c28402d416460b007002d610810081e04200c0b040c0024001c0da2045a894020208a0341d40101007240b040103444220740c1c0040560282680783e001c28800c071a0040c650620a0010441000103405d0300f030800381000a040207140c981c3ca007aa4000d0703102c400a60200b9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 456542320 1250 456541070 456541097
    0x60a150b040b120a021617070f1a0c040f03080a092105070906081510080604060915060302240d0501260106051804150905010b0a05030f06010314120a 66
    0x501c0c3c181d42c803080b054800c43c1484034449448000c16681a00102261030001c0900c5811340d5036408c0c1c7c2d10361604000c0342201d030b50240c9818900715041ca54500050300900c0c0006110140400454041d12103281541510520390740d911110f68004400c0c56060010162022036920350404441c07100070501303051800059041c0c100a424a81c0d160060714145081c0702090003507110004000c81084040460202196100700304204a520359412904450046000303100c10700c6000d8110032034044c0220301c60180044480c1165040700e02600c0001c1d0080501b12440a6800c0a40c040029203145040c01a25051041c9081000c03140300340c00c040c104810031419954201c1c041d0102d03403a4118000000c02c1907604000c0052181c4984686415007040300710300180801000c86000e45a41850300800c0c010b04420f450002d003c0d10407484250700540389044009082e18000503e460304034030503009401130b030342035032500c2d04007038400102030300103114441480c0300081d0f1a030014030144900307641b01c44404c1d021 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 456543570 1250 456542320 456542347
    0x7031d0f01050f1224030304080c010c021c1a060f0a0e0c130308030708010b130b090d060f1d03040501120207050c090103030f02060601050703021005060a1206051e09060a150b040b 79
    0x5c50309110b000c0d52051000b480078040000d03503280080801d007450000d1107128400030f02c500c0300940d03500c1d071a00960580031080100c09815030100c00c60300300d80385446a541d07006000c05040c0c040c0600d0382c881111917080041c00f58078690760703400152801c509450031091521015207051aa4812204400000200113007554000e441d140034141c0040c295140c00090b180e000d20840c030764090441c0d401d90000340c1001703c3d560195602c2c0c88552140090000d407440483d09030003404d0302d1043e80f07104a400c14002814000100885050300e034161207221030301c021000d580c0003e42054030122024810a0700341c3c00f080d66100442070007984a80e41d074101303102c8210002030074248050940c078140403003030150000190b0082203007102c0f0103085000141503a1000b002605924131640712280020303601c2130b03580078048a5001603100e0814038064519284a00c3c040c841030000072141502e01c0e4020001041c0d01c43d000303400600701c484540b43d44e01d20307140d20740e02081e5403540f140c1d108002c026000109074041000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 456544820 1250 456543570 456543631
    0x9120303060f040e061501031b030c09060906022a12060703140c04030b100b0301140307050a05010c0b10180c0f2d0507080a030207031d0f01050f12 65
    0x1019a400d000400c0d04007013065503150050980624241c400f0032455403a40302e41d025510190000140565013041550003500511280c0019400100301000124105008034400000c840540d8014241e4195552000d4501040781010004020703220f0029001903803008180340011913218050302c0e10342000310001d004c8404036103d13181c603001c40f4010440700245040646049030b401038544482581c40b070310300711240354a9400c0000300d50008400171690350340440704000c00e002c054048502642e1104104007a103901c501c613250000b110403c4d0038001414095249402040142e011498540c030f80c002209440c03041e00c21100219a540803200030564410034010341d20307540e401c1603016032920780040450b00c08015000d14001d0351002001d07424030312030812112941d42141c00151144000400103010b1340c0b089600f45d0004541c20080d001440690703680040d880c20007040b402000b20800c1c0103540c00e0b00b002081a101202c280203142d54440c0030801c2e94403a00c601c0510275030350940c8000035015141c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 456546070 1250 456544820 456544849
    0x405040f0e03030915150105030f0a14100906060519050906042304050c03061011210c07051009030b270c0109060c08030105040518030f090418030e0d06020912030306 73
    0x41d80c15031100901e90700001125006500401c001c0b0315035480b41402d40280040e4038158140c90300250400c040d0040301c0d9055004d07108658ee00744a03040d07550740120307503500440202c1c1001000f68030480444d68015002040c03885405042981415580c20071102c0b003a407400300d0b41001c45241c00b14a219403800d0320a00c0c2c1e002c02d24070500f50641c249075001c503502e044440058010f0101000003003041c0e03d42001401800c2d840c80e6001c001580c0d800341c1203540ca42107140203804510a051022a481c9412101d88100c0000342c0d07100308000345181c48072010008060b180211401c52054a100c81030074444074200300f0300701100144480100b1034001000c40701c0c0e50b40004104021014400000f520850490341107075411140407946440d001e9002441d10071024495140d031000003681c545640c3c10202400241320f003120200102e0b0107449240191340440d02006001070820b001c145002c0c42c0400e06217601d00e0207100c005092080640105072040e11410480c4080d0380040100400c1c0c2c0703812400d002103413 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 456547320 1250 456546070 456546091
    0xe010813030e032d28151b0f0212031012171308010b0a03030f210e01090209060a211104061203020d020d050405040f0e03030915 57
    0x385801010010124000d800080800809046400ca259410052807a00d1281034001011101e040702c2e08820018540d4081c0c1924000c501c1910404421034642115182e044541110b0a014503514061620301c1080000c2050381d455a184400c1c080144403d124680300d9140c500307071007054980107461710031448100381840c002001000711200c112400c0500311410074250800c030304403d1521140a003000c0c103400c2d10094011880c018185514801503003150900402045901141c0b8140b0491004900003c0e000c6485c80b0000d03402244125608100c1030421400450104a5040410300340c41140e0045543d981d1158054429460418280c907040070f42294003100851505041c002d40d1800b03109443d00c4a84e00c1140c101c02d0181c1c051400c0c40c074010043c0200695626000c80070180440a4400c1d00180708522459480b240005124048110280ca6040c1094500300130400540001c40000c41c0c1036441701441c02040c01c04202a5004d01402c030080c00000200090070341d903004000300741c1c01d080c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 456548570 1250 456547320 456547337
    0x305072306090706200a060213030b090d1b02010c14030c0f011a09070c0b0a050a0c1107050f0105040305030706020a03150e0c0310030816030f021605090417030a050103030e01 77
    0x4a504050314240f201c4011840031141000c103d07105d4240300c64014054401070002500003c280d030381e070310744200360780c800c200000c441c0d02c8031407140d903071604001c0d040c42c04184d40e81000d0302a0103060f10701c0d841d542d1051502d194650b81e15a11401d804610640e150159400810031090074401800580d5041104100070005082c260510032401c4a44c0e0390100d000f10040d0300402c1040d03105d944503104068001c110003426040140e2014020320003150132030001442d03c144950324503c10300080550110b00303801000b03058100b104005000b50340c107080905208003000004000b030400c1c0013411704da500410380103850b10701c281005000e40d08580351904e81564041e2041c409801850841a0029203a031011031300d960b10105940b00c55905504058040d9501080103100e1003c21540701c1400da1107656030f20384a1240d00c40585e40e0390b1100852090354041c0980c2171029041c10410990f1040c01403154a1522142100000c0e069005589080c0340d692104014000d041e004285080010028030b0950342 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 456549820 1250 456548570 456548579
    0xb0102031b010216030c15060e1807050d030305060f0f03031b030409060803090a140616050115030506101a09040213080607120e0a0503030c0703050723060907 70
    0x44070700c80c00311289071034184203035020403001d4250305a88143c51070021380c0754903040d2402c019024004503002250000d6188181c0c0040b42c1d1280211421034105040005154032040381c0185581071694070107400e445209000540703992410582001180641c80004007420014103001aa540380c4110600501c1000c001ca007090318000216483e1a2105488401d05e1002426140c11803055501c0000f003a400c0c984041021305c00400141090501190003003203aa5903130747d1141c14105c0500716039a10517403d20005c0e5808690103074100c0300354420f000000304600084407648070403443c2d8000b036505038042410009800c200700a03090140c092070b003140c01064890030240400c0d10a20480c0d6009540203e0014040c0c4c03420b42e101e030041c0401c0c80c00d685061921200040040b1107085988884606000d01c9107003401c000f0880780055900f1502840c07840e51f03900300c0c1d10220360120008504100041011602103070703880290002c0350b000d10340c1c4418503071a450f00086c94000050842030383c0f5000b0160400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 456551070 1250 456549820 456549823
    0xc050d08031f0506121e16050c0c090c04050a06080610030903050c120a090f050f1513030f1103030a0801060e010c0c0b2d0a03050a0603020607240b0102 67
    0x29030140e80391101e07110b07502203215030706821a06640304940064012960403400021003042e10710031005500d2030312413049140581412660305550f06100440404111a4040c0c89000100b1284008070215051107036088040344a0708801c4074003808051010400b0b200c21314241c500d180041005191020007420b100d000a010000318202c003c003413580c0c1c1c249010800d8020815215044c081805860002d885650f0080c8254070100c859000954100b0300440c108082143c2d0301c054460140112040480036000d00040030740d990340401c02403070300348200301d04010340505030310155204034100403c0010614140d003540c0841d4000a1081e0020310022881a6020b00e80c036044403501d140c00601d01d81e199006890050003010050001c001480011403501d2200303004110714465114481d00c140c2d00f0041040c90f030085044003aa031403204100840d0024030981000f80c00080e01280000c000d0b90702e50000e001c6500030502214440c0782e407d201c4d1541ca00702d0201c0f10115101d03c03030a1091845082c0001d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 456552320 1250 456551070 456551077
    0x30e040203071713050115060801050910030203030a080414070b0d0e0102070c080a02130219030903050904060603050103172b02090d111815120c0d03020a0611161104090503040f030c050d08 83
    0x503401180050001b45154dd004002100150380103402d40f40d5428540100a14a5900310340c160348102ca20982c5500b40880003400d0030464109158290815202c903035500090070890304118803543d003e2181304040741d4031400c841c004011010040c04492443c3c41440780b1b0101030382004403640c0c0305000c1c0d1844501c00740c1e0380122003c614070f00060f65034041c6c0b9007900c03c1e0042000f0340350002c0c0f03807000c00305002d900341e40428140d0340a0682d0846001d051141c0d50100d11402c9081442e09030401700c00807034460050701c803d00c44030013154054201402c400101d039086050403070640b084007a45500b410b003030811450481c1c1c00314030300c55405050300c0d20b0010a000e10310441c801c1e50040c03155002c100c82e504d505124800745842c008024042e09515810001c1d62902400750a0343c03013601c2c2000251002c0300d02c0c01120154042859071000c02407440c0c0718088006440d42c4080c1d0403c0d207910303034040090300610041000c0c010045110dc0d549040d8145605910401e0b0006030080180c01590b0010a00002c10b4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 456553570 1250 456552320 456552329
    0x100207170702031204150210020c0717070801020a09180603120f03090615031208010302152209020a090b0304020330030108010506010807030504030e040203071713050115060801 78
    0x950390700e101a1010900d00084c1550f01c50410300b0100b0003040d000d514010307108032040c3c5942110303a1700100c410000124030400402d140d480e845040d0411000f07003103913409505039000074281c0d8204c9980d0b560150070399010411300c50009000c071200740501c0010101700315100500e0b50341000020b0455440c0541910507541150520544030003104005101c0e4000b860400e81c031a81c288091070300c0c505581d48903c1280000c8038081070350000000003a00c2441d1003030403241c0040c004004102c1404038440564000b0380c80c0040800300a0744e1000b40c075030405036000100401c4000513039562948900614040d40c0350824040240c08200348005a600015201050840136040c08482e00034001c3d1038101400c01d01c01071f2a0090040700000d074007031042d07110510510003030720b9050309956000021402c4540450700200424880d5409800b40d0401e0350143d0340c010000d050036000840030f02d40582d07145c0305c22510450040e120800c0501049820302480c4019030340300700c2078400340e070600b071015003214414001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 456554820 1250 456553570 456553613
    0xa0e130b0606070c0306050601030b060f03151c03110c060f0409020a051303060614090702100902040b0409050606120105010e010303050c0127110102030f09040b0a0e0f0702100207 79
    0x70400c00c0c0d499504581299078041c601c144019a40d20b1300e000a41403c41d0943d01103440c04092013414100f520458152078407101c940c3d4690341d141d140c036a500d43c4041d82d4182d00a8100c014603264224605a0310310517a0081e01d5990002000c41040c1e89854001c1d1070541c041c10003448050644e5095501351029036104650158903050b480f030f421111401400403c401141040348000107001d41640010240c407072029024071203400d1074003480440313217040d140c070341c01039000c1042e85e8140e580e180d026000700d1744014004140050180005801d40b48064425a1150081010310800d0b01d05254144e440b031000c3d500078042c1d50314011a200c01084144000f5050050020f60741c02da814081d40301031072865000c14883d00036403008038144000e01c0b100f84101c55280404e00f4144283d03000001ba55074003903000c2a80391602101506100103005107150150f00507010b0fa03008100e030340c240c2d1020b0744078024010f440311440ca4040002407a2407481c0e43c2d8090114410000c40002c29103503010f42d03d41c2050000d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 456556070 1250 456554820 456554843
    0x18030c0f0919050403090602160510050a180f0608090601050f090a11030a09031214180a0501020309030c06070f05070308090f0d021c090509040f030504090903020c0a0e13 75
    0xc0c203070000182c003495244121440c00040000301a08000040c0c15a091a800c44113065100c0740c80d00e03d00b010034010264422481021408098868001000325000c940f41c8009981d0903c03a03503400404540c0c20010782032502500c14010243d0122130311b41c0c0101040000c1030194540008038203112a0b10703210360300901c0d6440018100b0f4a454000100001200b04070b01d55910306244500c008060300c001c03c0b000070311070988039880d5402c14042e554801c10030b9a0f6244440e01c0e0800d02c0c0c5c643e011103036280d020900482c100000492800e1000c1d610403e0300202642d0b0381c400d03002089003001c600800c0901417141080e8500c40c425400000d071074660380c1c10704003200203486009110f03150000b0b5503004650b904c00c0360200c48145502054001a51441c0140803074200b03c0c1c00025210f01c041805265008111007000034003107404080b000c05024001e080042ca02501c440c1854251004d01200f0340c0036030301c41c2c0c1c03159a5500b003080304003004000000a0310064142031024203040c0b030a1040140103040f506d07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 456557320 1250 456556070 456556081
    0x30c010512151f230304110405130204020f0403030809030a02030706050a02250302160e040f0c0e0c0309060106030b0906010c030e280e040c062a0818030c0f09 70
    0x403c1e84000d20b1085040103200e8841800000b01142055005aa40d6440207550039074580b1014095a0040d036000c0c4034522043c03059070603c0300134503004207a4202a10792030710032005602c81c0c7c8010f101e03c4ea0000e030701565075402d60602401c1000080d00c040300942c03003000445001c40d80802521003241d80004007155a07140c1303008200182c010110000c0d01c1d11505550390240106c092081c102c01031107902512a200340c1c040820f00500303060f01c03610139900c180310700040000b10a50825000e046c46004407108490325081061050130048588140560000081c4078030240c040041c240189074515040c40100124008500c6807034000c0d1000b0305005243e4007013020180240c20b900103c0303a020300180c0c404844441d099022019035400031768184468240070650610f041d0106114503001031220344817a2070048111080c541080035031680c10445003125151101d100002a111401400803d03180c25202ca0004070110000102510981c0001501100d03503c445a007540940011038009010b40d968 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 456558570 1250 456557320 456557329
    0x50312072604060f110606011b02031c0f020c030109030906030b040b04050a0b12070b040320030102130303110c1e06090d1407080a02060d0b01020a05010e0606030c01051215 76
    0xd010700e5241d03414000c40c020420550040000b0050040c2d9035940ca210104200010f40341c5405030341c02c88c0003c3c0c0708082120058001c00c68120250701c082d0454a0030031910782c0b04040080d11000050008800607044120290304104a09800200318020069294940d9024004010714401c001c00e07d515118040c0c143c0da00ca51144082c150054418089468103034941001040f10394039032072141d95040b006003000c40000038203409440b41418418502411503c03140c1e842000750010310351294049403c1040c0b80c8007070000e06408184031310400041819442c000d0100c1c41c0e02c0a80d14482c2c1d1090310308082c5641c8503c000542c0c0f03a40c41226a4111740308001065040c418444420b8203c8002c1c0005800c104420140f00c20f0140c810003070324440d64451240039200d20031000041c0d440002071000c07203400025580600014001401160140f039015074405007034805da035003a0319258020004200c0581010302000c00c00c002c0034038002d450240b100503912180e08004c2c1400411995421251500751107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 456559820 1250 456558570 456558623
    0x1b03060b250611031f14061c0912031406030c040c0c1b031a071202160b04120306050f150c01020f0c010e0106050402090102150c0405060a090e0105031207 68
    0x40054040c4201e0200030101c0f20b80b503005a681d0000c040104c00b1409a0174400800c40c0705a80003a11504440b0748580100081034102e0010752208101d19044000c03006014030420420b54401c210b00001410110005001c5a2110082c0400f00b42c0c07000421006580c0800c544541c0d90b41200c0004046140501c1220302600b00c020040c08649c88a0701641581c0260b903101d0700b200d20030840d40d404804240c600c00d0700128143c1d07580c2e020071100c3c905020032000540180000d20350204488901c81020380710820b0100c41034805070307444041080b5288003245d06014030405407400741c0e255902c038012413001c9161105492030149a404012404201100003174044400e107080468669440342045100307140249541540c03040150b18080e40002d55082c40e000382c804069058014207200d00e240e10f464403020708000d1000c010b15500300404143c0ea65080060308070548950f03280c40c00581804600481d09006030171071031080e8013042c0b010700c80c200c039401103d6036640e01103141020311444201c000e92404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 456561070 1250 456559820 456559823
    0x81801020a050403170f07030503041e03050c060a06050a0e1e01080706020c1005091c14010902030c0a260102210406051b0406030e190302011b03060b25 67
    0x140001030300744501c0c1d8800003030030640e0b00403907030701614241414800009114444000d40c03251028449080071034051307030140d070b07000c3e001d503e001d940c800c004941c0300014101c1004c210007003000400d2481300500304200f2580e0045814034104200c5060000140929a540c4104404079942100150800c144410110400090745103500c0d80c40d41c444540039100c4501d4003861005210f00c1d030b22301140303240031160640c0f04102034075064a0f048900781800240c51540c1509500c150390b000c40c1c40c0c00109407403200300585814030000207050a01741304240c14140c1e1440040c1c07003150f0310389050280ca801c8080c0c20030f108070190000365420850500182c0a0b000350a20344a03100c240c800d01826800781c03a445240308a119500c108119611304110040c0c0404040c1d0001c00210144403d1119502950103048800184022a18503071250850b070b130841c501c0b40b00e0850050351100701c145a03008462000321030000d19800d00f807224505200c04129540500d560202201141c0d9038146000607000000080c141e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 456562320 1250 456561070 456561073
    0x9060a15090e030c0f060c0f0a0519030e01060602010209060a08071107120308160207060e220207050106080316060510080a12080105010f0e041d030a0c050115030b06010818 76
    0x4030614602503102e4110380c0c0043d119000b60711792000c00260105100384248a080496824000c240030f041c0100e41044002d030082c4807040082a00c50070138002080c2000d08540c0c0c0c00300f100b030206100d25094920039400b01c2c00307680c0184051a03965503031406440c142640b074a4041c2c80355072030170421115025055103407002c0740506900844e101c490100100b150900036215003200740c84203405644210048485800141c10080050184030321034000d402e40c200008017100a503060300d030400703c5030710030100c0003c00141e8001880d01c2000000e000c0c4000606112000d1402c2075400c0400460b4146049402003144e036a4400040041c041c94030304c480580019801c40c2c030380003e41c2c039084840b06c01030b090003804100316030b000040c603600c0392131401d00030580d83e175842c11090050018080a000170240e842008519403121141c4a10100003070704024603c4e03550b9001c00b400d5170412908641c80b601026604c0c00b2000000d20114121090701d58004c242840c001950740c0d641d03154030b00c02a11031101d8001c0b5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 456563570 1250 456562320 456562331
    0x10b090103060c021b011b170c0a060c170a05040f1a0a0608070f0e13080a0203040e070302030103110f040902030715080a0204211506060c03030506030609060a1509 72
    0x144401030f400951a03682a030216003e0b101030341051552400306080441c00203928800440c001401018891211485000d100d100304405000c221100c0e00320300c0e202ca006a110716102000e001003401117580b007200e0b070300f00150f03641540844400805401407107603a441d92540d01203400c0280c903264800232a5004400c0000c01c1310400003001007600c0603101202c074107060010205a280300440d00d03204558080c0c0140007241e1800d070107615031007c01040b50050030121000400810142c134014039582c00d80e6405190b586040c100c0051358154042c04910402d0304c10310040c000107a122075513035800306003159000101610100010090040d0100094140c095604009144040c22040b031030401c039a0f40b29400e2540e00c22842d141240500d1207504610613041c0070900201184005081240b801481109400007001e80ba1106031070b81988061f00140c000100d0700107141e49841041c0e0401070841c09480181410207059607200030251007000710340c1c2c5e98040a0b0143c1039a6034100020b11a04009208 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 456564820 1250 456563570 456563573
    0x1505090a12060506150a0f090b04151e020c0f060d0e0105060112140f0408160b060a080115150306080106121a070813020a090e0f0c22020c010b090103 66
    0x7200514907080707031854149400300e407052628084030751002c0320002026040100d0303000304807980140d89038a081807004080c07000c2149a02d400080c005852040c044000003180600f000309501a031080344242a40300240103c00541d0200e41d074010321340110740a104c18525240001c002e48034040079480c805140200340850190103401c0746203c1c990980310100c2860920750071406a40e01c11150181c14148031000bd0b01c503240400b0501d41150086c3c20b01401e016004104c15a00804004240c6221400a00b0060070745008580c01011b8043c220080c840c4680480383d02c0e034585180d005a00f4000c12003160104460310030380c0030000402086000344040b07961070a07440b01c0303002e05503001e175041c105d8041030406400d42c02c80c05501850070380c0d5400c001c603a1051681c0b4030305107912000b2a070003542c15800017200006801401d20440e15203001c0c011441034515000e00c0d04d0a04d011a0b030143c130340030101ca10800504180c000601c0c40742c08002d83d032030085117039150051410552190340616904004030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 456566070 1250 456564820 456564839
    0x302040e07021f0b090103020910210605280e03190507060501050414010303140f0a02160501031e0b04060510121526010f0516080f09071505090a 64
    0x80c20403c1c0481010000e2803011000b001d40d0395150303c09400074074000040006040c42100700e035002c041f10001c64020303a1141d918407030780940744c0b0070b44031081c400d1311800051010a101d8150001001c1801000b600034016030100e0003084003180380c1d8070a544401814140e2824401c81e0011103650768014900b50392040090000e41021a00b955403d00d08000443d940c1030500c1040404003201c07400603110b030300c1c0d5a8119136030a0340c041600072100081c405001d943d44484094a005202900500405004c0e06184943c070750180e80858101410801905c2020b2005030b07054110200010001c02c425810002141c050017184e8800e0750000c03c841c041504203a404074851000c080b40500078091480660b006a1648889002d00c41e030f0a821406102030700f000d04150381d0000c2c0700a0001080450b103c250b09411a1011a16101c40000300d01341c40341c0c2c040d0301c41c0c1076540c0301410400c402c07840d0030100d107860741e40c00300d80c050509001d40d04202c0700d060f24010004e0306d01c0b80718010107203415503407155200c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 456567320 1250 456566070 456566083
    0x90803030a2a02030405060d06241704110f030c03030a051209011a10260106020c1f050714011a0f1c06230c0901081308070f030302040e0702 62
    0x78240300c2206041c04641d162141d442d1034901c00c282e07000b1400d060510082240d580d000e842c0002c01c15956000000c0c1500f06070340003d60108441d482d0f225a13040b1032002401e03082e039071024a00e0f20340c030340c0040100203a1300580d1841030503800c2d18040b60207850b03040030a14220800c2503055051001040303502c07150340c2c03101c0107060040003d400e15002c1d4507000070840c00d0b00d0000303400ba03420190443c9034050a0424030b0000c2d00c01041032402000c119480d00c00d00b811620800c0d02824410b0140c0c0040c011907804115205818901f590004010b202c4540fa10701414403885040b0100300c000520b0303200f40003e00e2818504000214004c00800107583c0244a65103038910905002e03151030b45100c42a85015030b001700c4d00401c0307c405612912281d030790b01c000601940801e18001c0702142c03c1030950202c0d42c0c034650701c1602c0800e580c0f66248d5920300054803240006002144801d944000d0328000b403242010f0f5074900348e20450481580f582445c00703601a006540008400030300c84001c1107000c1b40d001541c0d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 456568570 1250 456567320 456567341
    0x50103022d04082d06040317070c06020a1124040b06030307120309021305151203130914100f030f060219020610080304081f0e0a0c031109160f090803030a 68
    0x1504200c0490074013107844400c01c56018021590580c06191301243c0b10144642c414a6407404406410003540d502007240c0007981040c00081015a8000c00c850080000040030501544002403000d2060724211908400070001001c03107a015000c20140e4500304252002c25074005019455008405d03001801480b04010507442954030000340000258540b01d218096103950b0064807003041c6080900908075514503010f1168032041007482c48203c1051004d00180c003460710301103040c00030715096440b68007015003541c40c0c1154402c2c0801c90642d60a45500032203a020700000416100e908206d402800b07074094040c850b035007195074400081e5010504612840c010418014903c0d110b60141d5664001c600400e1843d1384080302c00160181490501c0b00e5042c1c1d44072005c14140703e003200b85401c0560ba444101d921003218007042c0200300000c40b410321201811b658090052600601040d02d2894814100050040c110500068244070f85201d45c094440c2c001120340ea800c00d518802e000b00400e005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 456569820 1250 456568570 456568633
    0x130314030a0815010f0309051006090c020606030c0a0302150f0d05061206010e011205010f0c030c0f05030f04030804021804120f0e150307210c0801050103022d0408 72
    0xb5000348003c0409015a0006940d1002c2e191030709002076005090006080c0c4140c407500b140365100c90000c3c01b50801800c208000890103452142001c2d1038040058042407183d0004055940b035521080500d40c2103d070105c81540203810000ca2000940c42806012031520300e0005808000c40c00b41c1d0007050044030107840c1b50312102c110284d0540c0700c00c000c0c014983d035090084010002c2071600b0108111003405580002007100c07a191210303040ba540e110303241c1c020a80380e159500039143c00005020100589080c250700c0c41c43e00c8078085d89082c1d0010320040900001c0070100c0c05541f01c007285d00301416051041d0031480d007080c0c18007913072a540d009150b00010b500d0700506501d4034442c203901d4495034005412410241100080c0c0407842c1c000409610802c08203040c042f04418198181c101107098005d400283c44588000090210105800c0030307040c14010020040c04901255044002a070101c400790780980d0404220011407003654030031500381c0300d601c612849444140c42030745004039506c00c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 456571070 1250 456569820 456569837
    0x150e10031806113a0c03150905010515070302150a06050618040f020901020304030f02010c0f081e270103061805091506280e09060406050a020405031002130314030a 72
    0x3644001030580c0248041c3d8907a2044c4024030b1541c580b5040846025018100031403c0b5500c21303003c04104031282d00c115480c0c1d4a9100400080c01e088540c44203400c10940510328100702910081c0d80c40c1c203030000e490300c0b038030303500001918045650344190050400107040654034002d000c540c0301e1540490f0401d03032080b1b242c2501c440d950700d140d01c211010000180c014604003480c50301c401c840400243d00590510044c0340c40000002d0b100907145507014810740a0030733203600d5011007020318811841200700300300340e04000030028100051600a0340b8098050341e08640009280101c0180541d684805001d100700d000000529500742c00c12071244521404607031806030700610380c0181c0003095400e00d030012044211043d1200f03074481030051022841d03140c2c440e51a1742d1380581c900680100c81d51602500100144410000180501074220b0740d1948254102410040042e0f214030b00500d1291001d64005402d40d68900030710b108000464006010441d502500da0019032603a0000c0100000900c826 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 456572320 1250 456571070 456571117
    0xa06050c090f1009120c0803070305040e0f100311040f0c11010f09020108071b1718010c050601061815050a110106060e060306040902040504050304150e1003180611 72
    0xa111462200107076a241190344d4903140c02c0040320741d4010420348141174450000f044d051020030041003554401e0759081e035681d1901c4280300c1180d8000d850040459494003e2244030319800c482001074a81040b418102d100c0c1101c0090010160700c015070b4006800c02140120380b5410a000401140c6100c00a01c01a403007000f510302103c441100080c007062a210118081c1482040c8045081016040116050a0036117962000301c40e00b111a14043c50300041101000c00380c2081521001c02c2030801c14014003031903a915483d00707014002ca02c20010441403c05171000d16004200050107008858600001d81c1d090003005540b0041904001c034040c4101c40302c0d00b00c070501c522003c80b040c0344d558803004035804080158cd82c2c4050700c025480b070380359129000981d541b446440c0c007980c400d07001140d803589021007640d000f032804aa50f400b40140490a010962119034070054810300e2807800148048040540d00140a81e0200141c0500d140c09480e03a8100e440100924a0003c15601e14000400e217 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 456573570 1250 456572320 456572329
    0x2101b0f09030b0a02070c2301090503030a021f09021c03090609060504050f0f061c050c0c030f0705160b041a09030318061b1b030a1a0601020a06050c090f 68
    0xd038400105100710f98000100e00d00003a502510aa1388203620100d4041d43d6905844440002d40b1001c41950007a6050800650f07003080c049401844140d01031810800003440c0030b510382841d264149000700c0074400789520040345504c040c0d5603035401001042c1e0b43c00c808901d19080d00140c80c0450101b00c54440200b0320600640b070103800c0703414a9030740a1801e030400003440320301031400d141e180e0031021620900405640d01d2000c3c10500110300201c644e2075854452080603034101805083c0c0b4100100601034680c0300c08801c4030411007102c151107981e40250f01d44245443c00000340040220350300a400b2a9a0f60b0f02c9000340300300c0312400d0308402d00c0142075880340554403c8002681d81944100f105140f840045c80d010255644001d000714107181011080c1d0031240c4200481c000150010902c03e51743d4020040710800442c8207038010010101c01f03035184c000850f00711b910315402c5410b08000411030380c0700300304004586034080360070311490500800e03622158000b901d03d2441004840c030140c041c0c0c01c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 456574820 1250 456573570 456573587
    0x40f02090a03030e01090905070503060f090c0a0c0203070302090c1809010609030f05120f130e070c0807170a030f1b081909060207080306270606030702101b0f 70
    0x500070030400320285140d03425229845004801030501c0300110f000100c64000b44600b6108032016200c4d40e0303491912408019045900d440000e120307000a40c01c1c82905001c090075207141c04034500f0311061181403400000c3c84d10520b9803009501c01d89a808012005881e4005051001708032081071030380d00e14001c200041030b207090198000003030740b1980130004100c014100700c50382c038010f1041e5114503042140140003075100003500d43c205074000410349400100c4d2400180204001404481c81e410b0019004041e6843d840c03016055000c0401c180d0241f00d1984c4505c0881d002c95800280d4441c0143e02c09005032400301c2e2605052441c00c1400c41c6070720400401e000c070320300c01c540d5156125983c104400d545801d041c1130300c0f14416503e00400001a80501c010841c1174000c4031003903101d281500801010350101c4109000c1c0c48188000c010f00f602803003603002e030400c20032249581c0300c0d40c1d081d408929003480c1c00c0000c0c84103070074a29010a0f80d8088441d0b005000425501c46c40c41d0480405d050345d0010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 456576070 1250 456574820 456574837
    0xc09020a1e030e010c0e030d0806062d070b0f0919060e0a020d0b1008280201031e0b0102100e0a0204050403020f0d0215060a21020402091509040f02 65
    0x8030395560910004040c4208048000c0407402c000464a00300926a070031070f29250302010100d51107807920003080c40c0c1002128440102840c1a00d450710f40100031458038018a100707044220750410306411103075000c0040307c0500c0c690b400074a444408a0504122880d02a64002c14608144010074451240403886941548040141007850b40aa50f1034800500c00d170032514210b40641c41003080140c6d10508100911401210241d1060600062044001000c0d50180400ea072208001401a40340740f100300d0700c4510044100402083c583c001a40946007070301c4542c4907441d000180c038280020a40c00301c00c09070780a17809c4682d07810040303081c107081f070754400b00c03001840e40a206881c005103015040130b540580700c3c1c815204200140c441c1e244c0381120440d6410050b800c101244d04880d5024280755902410881d40041c03850b10b0300842818401e01e0380194102c01129200c3e0000351740791a012100000800313004080508030403100000903030420b04480348608e040c040900c0c0c01650034001c2d01c0c00b80 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 456577320 1250 456576070 456576077
    0x302060306210d020a1a0702060f09031303080a08371b200303010f03060f1e02040e0f010b09010f1812020112060e1501090f0f030c09020a 61
    0x60725208100440940b880800c4051a100d481850003240c20910551001091540003030a8640003458030028102e42d00c206054036440380800c102040e5400243c054220f82c0802113000c05899449026046101e0180a2101ca9503480c5000003080400c5000389001100b95480000780e0710740070716009641003c0c00344d61182f003a04410b2584172000032115845503403218400040c00e00300c4c01c3c0514400e40c07000000c0102058040d07420440702422012000400c24114000d5451581400f0343c00c982411075010141240355100c1c3d400b92085110740c4542030340100d000c0c0c0300008104601c50b61010758170502849580300c10601c042b034002d2480907401416500200d091030b007406858001110b240704a0000201000300307441e100085100c0002904001d4002e2040000e00c501d010300015026070092600300d05000e1414038100002ea0600c41042d40210502502c010700300500d400403203001e03032a500030310300381d0320408000a001c0d0003e10540e807c9074400c11800000942e203140c0f680c02c9000768011180031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 456578570 1250 456577320 456577327
    0x50f011511031e04030209160503161808060115030912030504170304050c0405070804050c100c0204140a050c1e0904090501050a0c2a02090606190903020a0f030206 72
    0x88038059162060000400710499081c10120025880703105040c0044520b400c07030015044c01076060841105a01055108040303036140325080e00105644001840303003038070310311051091111340d104181c3d44119000200e02d54810645850b01c941e01d6240c2841025903240c07484070700090190003800341206042e0480300c2e074080840600b0098001e0040204110350941d00850a1352114a90001440c0907501640c01050a10841001c1c44101c42000c0e01c3c0c101403200036403c00c40000c1c40041d0b08161004c06948034039020091040c01c0c1c40c100b06001e8001d51190800c0c182c0464100460102ca103d046034080500240d00d0303034a9004150301c15844403805e030328041150b2403801c0444000514007003102034000100d50300c840e03c40e0340c21110240c844d00c00d06920b030102c21781c0007503100380d0900101c8983c2c54100d40c00c400c0c0c41c40079414600759440080c000d04a1900003000d568031075055817400d01c03005c0c030044a0300f10035580c01003800c0400d02013203100d1140d680c404102d20322a1039022040c0d83d4040c004915 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 456579820 1250 456578570 456578609
    0x30301090c09050907020f07061407020f040e120d0b060a0212032203030504050105010b0322050a05030a0f020f0102040614090a08030c0705011101022109190f0303050f01 75
    0x260481c98044814400b40b0b8a0003e003c0d25120555403113800d0f035501a1154100304074400d03040c00419444001003001d03051580c07002840c86021140c01aa040b501d0301c1d141e1803a50b0100d0050446a40d428002d0302440300c2d040045400c01c4001c101181454104011242200382004400c0c06450311010041e442241c0c00b1501e221030200540c0c210080f210000070260380c518411520001000040740080c0e102c400f0300c070410009000e524050030501403001d00b9454a0509916213341103600030f2520100c4540c500103005d0700340100782c04180c110060701d0351031214030000380469000441c41c1005100f0380c0d014a80b07003401032099030251a401d0359400d8403015000078080d00d0750404559554002c20716400042d43c4207040004264101c4404060050503251100240c41249500902c49240c3d0041045412000d0348290004540094402c04080c503203400340ba07186045010503529200c0c0c03c42444002c240803500c0716000074648665402e01c00b42d6240b02021a10203801c0c8145209030b10b03003882840 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 456581070 1250 456579820 456579839
    0x71104050f13030c0f060606230d090303060506040e10080606060d09020609120601090f0e0a021c140601092910032c07060c0c051905220e0708030301 66
    0x14083d000c0d242c4038243c10095141c0d0407410512807011a407030b0b40e41e03030410440c06403c0002d081031801c104400321410f40c0250310740d400c1c6100d02d251b542045541d031058841018042d0380600302410b0090015901c6e1621040c850b900301100351520040440c071145d0004001d5800560103110f402d003d04003e00b4107407610000c0010b480c40070401c99002300d040c000d018107501c41001d441401103141c4010301c00c55142c90003140c00c0b104002d10b15400d050070261418803040002950500c1203034192401d40c1c49114403400280802e50340382000305680030391240466000d90008501c3c0c143e80414a080100c0010340c03080380e10003411a10312002008442804201d24540810429148070f15800c020414090313038000e4115043c0701d1900c10040b0700c046061501059000c01c043c0c0d000d070845090900c02104192510011030300c0c0340c410b962282140e801c21000d08428007481030000e25015011080325440910b400c0564034803201d000c1c14486c41c00c5100c101003c00010054101c1c2c00d00005145141d00780040380 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 456582320 1250 456581070 456581101
    0x10e120d0902060c060f04060c0512011a04050604030b04050706090e060108070210230112030518010516030c0213020412080c070f2c01060801060509030c060f071104050f 75
    0x42c1d030301078020300443c03403941c0051041030b00c1034044034000d010524080c070b01081114000b51580341007150a00c020b21101d0903c00c41c1d1419126807221000c806001700c00c45113a1841950005500701c503010900000304900b400507180903d102d0380564041640381c44045602524911445c43c00158441c04204c0e5035001d05500ca800400c203205640e01502c5c0402204159094150706c90308074041070a00c42e48030882c41c1005400f5000d00381c6c8214440c034030360b200103000d401900081d094041203001c41e2012030b8080d0013101e00603204c1c00107140180540b400c000d0f00c03c80e090007050340254122091500c042200c2d02c00c44041c4d0b11103011184000285032956907041d04840b00d00c034420b00c6501000300d50040c0045061008144100201c410f0354100401e000a00002800250703c000600c0c0050045a40181040781950120715140d074858180703400182c42c100e0307e148400c0d0403210000340030421420001c0100302e40c0d03005022490070f490303a4034288400c0760002c0f071301540c40072661808610001e803800d002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 456583570 1250 456582320 456582323
    0x10c0302010b22241707031b0602012003071202040914061509010c02060c031b0105091b030a03030e1507050a0e0d0312021c0e010e010e120d09 63
    0x860941e1580801d2060701c2c0c0601004241e180c3c0003200b1210645409071101c9240c45050706a07203a41c000601c40000c10b2580a1940400c0664016074101e000401111000b560052000169110310a02190031101a802018015420040391815108182110301c0740d000303803100d440785952365040007116414442c0d01031210702602000000f074401030a00818908142c0304100d80c9460404004020926404031001d4204020503c428400c5a810068000001e0b8040d20603d940b5484400250b0461007202c544000314010205004140c0f0015072009124038007010031540c00f101c001a842d901c20502582d4651306601c002020780c002071080c0c000c0340604007044215100120400309118550500321401000900d02142c0c022800794881c030610381d400d0060314880505101524018242c4100c1480c08100c00d400003510105504503690340b0790b000404500410101c5034040c8058042c242010388942e0a608111852101441c04548268a2112a05d2a41c5032030f28a1f4407103006000302000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 456584820 1250 456583570 456583573
    0x2f0d060503030f2d07390305070512030d02070807020a060f0909060b0304021207170604020405010807060504090c050409020d050a05070318021207030f03020d090b090d02010c0302 79
    0x400088644081014106002003c00a25150300e2034401c400c1c8800a8a0b000c60420b2070008007482c80020020110b03201290896548a080c1405070100140300800c00e00c4d079060b4682000841c0304802c0510350b15030580788505c0c20345181940d60305c10803c600c01880399044c944e80081241e58045a41a4010008036100d820401d0410b821500010717005080c9510480201c0e01d50700c404103040d03501c04042c1d4007402c2e03215002c1003030a0802d011580d803800b00500081c060004807080c966021403c0052000030121800740a5024408508664440d081618100d000e141420004291090085090801e0b66110340e01c1e84c2c01c161601003210003418005d9a010203202d010172002c40e40d41c1e00c41c0000c150400c56a0070101d42c07401d04418840481b507009240300101840c140804a01668600d03000600c07030f404031441461030504500803403c004c4540d00c020404559628980201500803a9290400903252140480300340c0e41c030603a80c1310b8441e030040ca690007003800105000640c015002441c007503000340b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 456586070 1250 456584820 456584831
    0x105070905040213050d3206250513031509110a0602061b0d0f0e0c040605010f030e030d0501080a150c021203041a010902040f0504090f020d0203030f070b0a2f0d 71
    0x904040020b85d0918142d4108003c05207004031001f08000d81c0c2d4010604a03602e0440b13440445031800c050041c003210b80708109001032941c001c900d02070310a40295400c45131901141103203915950040049417400c8032801c2c41d4000f82c14652174403040040807913400340c0260403580d4030030500085036060180c2a80f4280e00c188600d07a050701c44c0f0300c21090758080d001d900241044084d2406843d210b0a00601e41c4140d0034240300344156680000d4040410001341400f282c21074160004a06500501558203110741c584000046c10580004100300024000c0e40c0002115086010b48402e5502e240641405640440c070001a00748441c0000c507807260080b40000a06201410a0120f003002a8010399038160041002c1c44090191300f000d01c020003040702e04101000450751288150802e009001c1d1043c00e02c01c01c0310040d5102441103d0444014100d0303076903140368a181003001000c05481d4420b80e6890b0801c04d405040d49503000248101a174481c82860203210055030b141c0741d000210340c40e462600c42 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 456587320 1250 456586070 456586103
    0xe100203040c060905041a06160512040f08160312030207050d0905121906020703020c060a050301080607030203011d04022107080c030705100c0809120105070905040213050d 76
    0x610285001c0c1d8480c410302c1d102c00d8a481c030300500381e0100f034010720f2286241c02603080004002803880512400d064070a42d40715100807170140d0500915400c003800e64000c1c040748021003405c2000410580c0d074186102611151680a0300b659041c050001180c0e240400d4402e102090b41130450b50302800b501d14000d49001803564920b070900c5001922113022900b46d8206011701c0c5401040e41c0340303045400c1c3c01000c800c021081c0e48183d03503909001c0a007181d0350010700207060510900121403c1440548550799030305841c60001c00715070091023821264000c0d500401c006900c43d0007224100c0b40c002e19607a17950001804a0980c0c0385000d40221f070f004a00c1174007815401290300310701c1e00710314844003e800c02a141859150821960840c20f503c00d420024003407003243e0f80d142c03c0c000f580c4098502495011843e103804200e41c4079260103540e000c405114a040c80309015084640b284046540343da40725070380c482c240700503401403002035101800514001d0200c0e0070160040d0203102d02800983da07000c6082c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 456588570 1250 456587320 456587353
    0xc1b03051e0405060706090807230615010c0807060609060e04050c0303130e06040f180221031c060519231302070213020c0a0b0f01151b12020f1005010b0307030e 71
    0x340c1120480071100742d103e00750ad40e00c0503c4026442103d40b00048403007600d600000f00842241a4014448000420034000b40440c95001402030455000c080000c41d0721845014021359048a080703526208200030300b0064107010090f030340c010f84404071480382c407410f20f00725842500e001081c0c10380090b84c505a900c14091980120500c0d0403802c01d0402411340c040c018001c119802c51096160f04070018101c0202c0c01002040300c0149103003084090744c109242007520050900e640c040c99100c00700f034040011000e11171003072800304c4d080010410b400030110782e074010b046580001055403100c0b0b070350800300500b89a500103080051000704a2034801a022100908a13004400400c495510a40d100e408200c1712840254001d081c0301005d940a6142243c40043c011000041108210384400c0041d0040e04003000044440d0b400104002c2041464030000d56464003090811460b12031000f65801200d410300c1100d069400488403d0301c0e41c0e542c1d844c194040c1445030343c0b66410f8070074403901c1e4155a00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 456589820 1250 456588570 456588593
    0xc0703020118080310050a030c0e070c140d08010e070801030303180203072d14130605060a020a06151202043201060e1002060a0c1b03051e0405060706090807 69
    0x8a101c84036241d01300840105001304098101c6e03070207000701410034000301d060032140d6001c5072100407805180d562111402c031240481c1360001040040c2c0740d03e011601c008081903840a0b11200e40d6110380982c2d0318041c4511604041e5a5100403800c21801403021a1094110b500309000001e01440c031071040343d001ca0700d480c64035405440d05004c0341e225030700e00c02d80ca0302100414903c1103d4103c1c0c400e0030141641c940d84005040144a245042040b401c621515003044c80101001442c00e0346600ea500006512083c041c5400c458480c9441c588910824034909071409075003948001d19000002c40e401e01000340461880c7ca41d98071035070b00c0c50010a20700311042005a6540b0018002154902400500740d8010b01040520903003401d04240800e40d8000781065000d401500003090540d101903055410342d841e580c95a0400078003019030403c0c5500b1100800018103c49484028030300011581c106038044c41c081c41d64460400c0100d500032403039a1b007285042c20b006480b461318082890303481801190 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 456591070 1250 456589820 456589823
    0x31b0303041202062403011b030b0906010207080c0103050a0b04090c06022e0504020d02101716020303012709030c031205091009060e0a0501061a0a080c0703020118 72
    0x500010421040101074042000c21203210f0000740400c1c1481d441003103201c000140380762200450b001c1201c80d5940e00750400c600c1e801c10441c140c4e03c45000300c10000d001e402c00c51802400760004901040b46075100080c1c04c000c81e85210041d01c8201361070750044002d0304014007030707220890f00c03240780401ca541c0380d1051100c0706202e844003201d85803134900003904282d80800111100019100000916a1400c08500005c40039807400201030b0745910008086040c1400080d400c40d0804d0709144956030051365041042c01c54010250803a0307901d060b2004803002e11b040100050b081803004000107140d0a1064043c0000e020b8006c0d048414401e0000407510300e01030a0703000030545032001c002d064119900003480002640240075601c0c00b1070301903030780e0400750b6161048c055a52a084080c0b004c10b50140c0b800000e60300641d2800d104904045028011a0080d11180110f0341072030366400705541c0031600c0c0c41440c0e84034440184d40f4900c0d29611500690700680c150754aa0100c1c9207200c0031032825035940c1d0b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 456592320 1250 456591070 456591073
    0x10902120c2b120219030302041a0702030c010807090b07051e03090102151003060f020a11150f180109140c01090803030c0306150f040306050a060e0414031b 69
    0x4a0380040100250403402081600000721590b50040c0708a01c0500d4061604580c40200014409a00301d1a01c1c501000d0000d4030550110036904165050b00104100c0e0090220b1925506081040741154419620000d40c50f612900341c4601550043c42001e521801504007409125680c101c00390302030b40021411a0541c02001c144003500b051200c1d012544100b0074003c40c14540c0500000c0e5031809445078040c04080d0300c000003203003421101c5a000145a21070740c140601d8581040c444061341107503e0005c0800c901040e62540f441001950950500c0d800e02900401d0f11104900396000202510818071035012070381a005000c024041c5402040c8250070b540d510710310581c103550400b544a00042c0c10418400750800050400000b623a4011800c4c204440d9251103040000e944d0404454400c01d031502c020440c0e4003890320200c0584100ca01444c0300723014035602d807141c0300d0440341180a0712180100c80b00104001c28450481c80500569a508480c9403001064031100001c1040420285a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 456593570 1250 456592320 456592333
    0xb0a08070803030f0f0115030e0f0106080703050705030a1707050a061a030607110703200a0e041704030206070f0f080c010b0f0a0f18020d05070302280f0e0301090212 73
    0x20852468111340d489551201d4020701541400100d4510080e0b03804100200342e03c0c1c0d03035004003480e018082100c10314a520020098180d5444115846096a10098a460040e203e000800341400305002e95055030240214505010a1070030304410f4005510039145403007901c040300000b030303114807407941e1402e03d0120316982440c405d402c162801d42c008041c1420422050010440d2400025004003541d5021210201202540444652282c210480c9039440043c4c4080092400040d15945001c4c0d40142241c0d01c1c59080a4035071845071103180b00c0290404000c0242c2008110142c506840c154450801c84604614030b07254813880c0d8008041c0300203240d40d92004003180b41b4101c91111203864003a1940020541340c16a01c0c4040d980520a540e0100b001d05804207503400c290303046581c20400118200001d0400c40c800a000350801044a1351507180348942d40100303a184040008910b40079a140058003d501c14101c1d07245080360021034142d9261031000c4011f0b6120b0821082130680180140030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 456594820 1250 456593570 456593581
    0x803030c1b0304030f111002010c0e0402090f0603010b120703110a030e0c040f05010609080604020d030c0503040909060204230907030c090806010806090d0c0b0f070507081b0115180b0a0807080303 86
    0x8103007c50041d400291380c0f42a080c50003a80c3c10268400079488100c80058030396110501051403032032070b104550741c00440000082408144000903101004220b100204d05035903585095013101e13048540600c3c081170602507403050b180300c2c0e044012650f0441d41921400303018100422305803000b444401c1031041e2654014401241d0001c0144010503510340204224205030700030034840002d02030b000e010880b10f40c1190b030600ca010000c840080010200c20058000d01d0704041c0000e401074001c01d940c1594103402c4642c90b00300e106012013010300080001c042500e40200540007009000364230350900080da000058003040912a0500802c110000341103140741c40340c0b450b81050003040c0c030b42d401c0c845103480c2c1c1c40201e003c40038413590241c105060040e140c0c50b0304c0c400b5a0305014046005240d19000102f00c80d02051141d10414103440002c000d01c85400f04400030410606940111209000b0402200c00100402e0308003d840b040003400302c0e01b09079254441142003108640080035907520001c2880f0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 456596070 1250 456594820 456594829
    0x20c090a0216061e09020a0302040e1c020703060c08160e03010b0d05100c11120307030906020403060e0d02030301060e040b040609090b0103110d380709050306010803030c1b0304030f11 81
    0x1000104c00c800800c146a0542e0019424a41600019010b140c0e181001801c1c40000c002c0c0b07203604030503100503c4040c0c2d69420002d54501c114002140c61604105102c0c03451801540c50302d0044504684914106140e81c0c0c040310411084440c042d415900c3c0c00b01403059440e2803020b00c00c018000e030040d040140020a69030700340c9044c04510000c00c000c2c500c040804e01d2001c550300501e1072207000c00c82c1d0b4986179100704401501c2c0300303070313025120610024001080003800c0d840100104003c0e41513800344100024140d869020900c61103000c5a2015031032131051070954850400c52078018400645980c40709009000c540601d2821103541c800a4018001c4c45101004031656060444920703c040903d503584401000d2180e0a2048500352600d40300151000211007124070280721303c2001051408140050070f00350103202b01c60003030091a001003040c2c0b5002c0202c038805e4003030301c1295180c012841c01c0d80c07550b020103003200d2819000030300c00070002400d004503104425018000d0b003e1100242e00410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 456597320 1250 456596070 456596111
    0x8030a021305090403090b030901020409020f0a08150901090902030a063603050d0507050702180105040b19030206070203160e01061704030c0201030e1504060e060601020d020c090a021606 82
    0x15449482e100d82000300286c3d111500e482694000520315031240c031791081c100e02a00880c0c00c07580000b0300104843c00c0c5400000040c0103505d00c180d0310a5410784611041d542d0f55103603400b9041d0040c0c00386005205401094214110641c070141c100c828607100e6407038135800c45005012000d04003074030048500b124001e40040c404004401c80a130f0101403034940d0702070500e2140d00e00f205441c60f02c40e80003642d4280110281c0d8100c64001e420940c2034207680808039429202406418802c80c9000b01c1c05a150401c1a4003a400d040c2a04c039286440f804c640800809800182c1c0c100e03498401c100c040f00c81c031104202034038001c1182c112807102c1035050500c007a2501e0041c0030382240d403080550800000c6507001401100d05d176020700b00051000b448050030b41c1003803e009030041d0010740c084240020000fa941c06241c1e00055a825070720b02ea03d41030b004a0701c03480009403480c016172046840e14407510f01b60342d4068005c0391005006150041c20340e5001034070303003814105646582d40e90f416900c08130f4000159 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 456598570 1250 456597320 456597329
    0xf04142701090804170708101e02130501090b0c03030415150e0106020606041b081902070302070302040510030503041413090503070201020d030209011b14072c06010c0204020a0c08030a0213 83
    0x40c21b0a82e0604407203a0f41c4034811850404580e448541c1c140700742d070b0b11130304c20115192002d40655507103061441c60200d081803441007900003091188001010403580301a2489003441101451035902c030f0707456080f060003015002604055a825031410031003070000c0003400a00090320201003d6142000c081c3c00c24070014445800707507044c20015940c1c0c1d0306042d0081540c1d00a0306000710030f519405000310500050300440020030340b0024650b0b05142d00003a4950450344211003d100c00d649455408070004a1480001c10f0741d0300600083c8020040000d42c100394400281624140e414445000b106450940d01c1c19540750304009400c50955906000000c0113204604040d031504503a100000c009100070000303210f0090ba009211002c000042c00030392080030041045400194813518032060307060300a880700e07111001d45103034004910001840c1e5481804141c50b44040d480d01d94007404080d610035141075041060780d0710010001017030300024500a540300b50700140c9516071064240d0008066400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 456599820 1250 456598570 456598573
    0xb0c061506070308071b171215060f0a030908070f021e030c011b060c02030301060210050108030304111c080306040608010608070902071506140f0414270109080417 72
    0x507001184c2c2204a07183c01500a2038070b5104800c0c04c40401c5050002d4400041c200b586004400039152070620240c00f1046003950401d40c183c451107000100342e00b001c01500d8003d4028403d140e08141c0c43d6024243c00d410380d04003c5080307965903403298220f51015200312034041725070083c1f40c1582010380e010070b0490580003817112501e0000001980d40c20342484101d0401c881220300c0385d074610b8448040012980c0c045000c1c0554011501e019403283c00034014100144070708441175504920a0091904803100701d4040d515580302d42e111140d059000105854003c2141c91024a03100c00203080d520303c541c01740100c1d41d2281803100810041d204540d1200030243e05001303060011031004150007045a07100d450040c3d482c04945000d00002409081098a42e450a04006070885103c80074581c1444112003405948495500300012140145000c02e141d82e100704c0024001c0c3d800300c0b40522680010080d22140c40a0000c0d260309650441104440a12010408214200c20f095140a002d00e0000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 456601070 1250 456599820 456599827
    0x18240703050402031c03020f040e060f091e0a1d010b010305010b04051302072a0504060e0c03130204020f0a12060501030c05190e0a0b070b070203041401030b0303040b0c061506 77
    0x200000d43d5550190034585d201310fa580d8010300543e000b07a0440c8e41c4014448102c0e030312580e07192050555020212210f60145900e031081030030300e00c1c004261500c2043e540c18030340303983c03050224a0265031900030800308a10f81c1c0c4400041d120b07002d010040318140c00c844000b0940741c01a0000405440060313004880b02d00f0140010302040e59000300099610840ea840103884591904200d0221160914040c00381035640c5942250388010b404020141c03042642d050000320782d00d6030f0149000108a60304001c6240c2840400d1501e01003550301400640000c0025081022070ba0400342140d101c80d0b4108007149a0085403d0051580d01030b010042009080801001c88031002c090030502c691402c444c1c0000000305001d00040c024495500419005020704190903260700c400325603940030300800e0328680040c6001a00c824400400c4601b0356100c60000ca81d0200b8901c015006055002c08083d03040c00184404180f030a0a030001e02051540000241044d0400703482000c0001084a2010302503070041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 456602320 1250 456601070 456601073
    0xf06040e060a050618060f040e01030803180307320303010f05011b0507050d0c0308040b1206221104080d05070c08070f052110020901020705030609060f182407030504 73
    0x11a140a03115098486c07555403030000c80c10454034804e41c0c110a0350f080a01c8004420f01c0403540c059803081904807080412450321040f070382c0d6280264040240b455801150310100507c1c4051101d5180c208a118542c11040e003a101d1400c2d038000740c0103420588501c00080042d5031b071101c141d4a546e45181041c07060075043e511400d442d010117004a60084060001140420500c000c11400654000510544441c2c8031200c400c0d941e070105041402c69425200131492a150840b00e500c01c000b42d2940e10b95505040041d46000303010881c1c21126220010b000010b0301c4135051200034040c2c4040d030f860656070142c91605060301c040340e4020031003551045005024030b90004404509852080350070007560021111a854404018a0b040c0c659004500c560103e11025030068001c000b001d13000d5524282e142d506055803948200d41454083d40400080781f101d0803840c0e44c0940050884050071000015011894600340b414080c6800303002005030380c442542c1c5250415904811079280512450806 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 456603570 1250 456602320 456602347
    0x3291207030303201e0903070f060509040b040b030c040b01091d0f011a030106390506070f0c020f2107180501060f0828050a0e03030402130b0f06040e060a0506 70
    0x49503282110b005000680c1b07401c503a0300304502002021001c031001302c0d0a032100802491600240d400e50b00440c2021100e00b42481d2a0103240061a8054018895150640300f04405400e5101641d810300444080c04201600304050f50852515000c001d0040c0f0b04040c500b140c541070301640016040c5800400c10b6842c40e03890b1040300e0443e00350381703005051a4108800b04541e40031840d20980140c1d00111082c001040403103c1c0e155690040d400e1301d040781c1e5800c10544000a49400800000d81041000300040c43d090008640b44000640005110002000c100103000304a1406d011035501c00300003040400b00c000003034054285c1c142010311155250410180010400020407401d1110100008001c0e482440074000c1000841c05403141100c501041203000300029659401001e003050500e0085120000c100c90085070f01800d001d0000c903010110380700610040c5407065020080d0090300f081a56139074040c0024100b08a46000b43d41031003801c102d026821940310501560046c802072525a49 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 456604820 1250 456603570 456603607
    0x1002030c0d0503040501020f0c01050a0b011b060f02040807121506061e031113030506010b160f0512030406060e16050f09060f040303020607020d0329120703030320 72
    0x755050050b120780361403030154060700030600d0b11010700e400400e5044141d41c1c1500424010617100401304030120b002d030011034041c050b10034a02046524141c040b40081c6050303100040503101d8070b1005040584601b10542000110740c0100c8ca00742c07206201c041032141c507040040744980c02f0002004450714040e40a0050304440c4003100612513101d000d03006180c045d42000c10f1403e04407181d12b0343d03401c1e03903020f030940c41100303000565091003400000b0030404c41802c100c8411503814a2000d4000c40303143e40b500c00c5500c40400485640c081c200040484516900c0558052845a9400301d0030604240315249503a1004001c60001003092414285036504101250401c0c0b81c40e9000360303600c186060104900e4405d011703080c001d5070b4002900200b490340c0030400300e00441e903aa00b5184882d440c3d4000314180c0340942c10540d0903800e840b001c2d20030a22210100844013902502d18002d030228000c20270305106640e4001e0f03000c0380d260288401881d055811403103d0001e4400c0f058107080c85c80001c0046900c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 456606070 1250 456604820 456604843
    0xa1409060f0d0203061f0b0f040b0a020708060f04060b010512190e071503050903071218030209090105151504050d020f060f0408060127050a0b0307030602091002030c 73
    0xd4001c6680d5295884012146000c1e0b6005000c0710302c503080c03001d4568144074030350441d000e00600300074000c120641501d0840b41c00c0303064401e106041600307100f050f031555803103000803005500ca06e08000500780d03004d0200502c0345025117903990840c501400c164050300d0400803a907040001c00c1000c070359416185c80d41c0341d81007205032507031a4108000140321300c020504d17000c51001900c950140003e00c0006c80405036140340b01990144200c0e00e810358069038a010302d02004005041c84204c1410b014480d1210300c0b00c10b500d4087c2002002c1d500e80100c0d014080c00d4418502c141d44600401122110036455800c1049054841d0401d445400760221428056070040521400c4444031480a5642d040380f1214540c800408842e5503880840340403160303602500c2400e04601440000041841c1c1d264400381540001000303103101425040000c1c001018024822903500d5030307411000385907440800c54400038501c00c41006075175100c000104100800c040741d100c002c540c4200180100d181001c6031486004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 456607320 1250 456606070 456606079
    0x5090f070810050d0605041a0601080103030809070f12120e01120213031a09162319060908070b2115180708100e0c09130507020c0a140906 61
    0xe8465541d60010300b14194412980800d40425000510420384e000034001d0f40b103499892054141018040c8101030201d8446010440e20001000480c0c012a40140c2c4000f680040d203080c030fa101c0e00c0c5010b84440c0380d00640c1c88106140ca41c501001400c040030059040c1d2070900060481d0390400092001c0e1400c0300344010709402064070b10103040c521340b058010307580c000c0305103903400b01c0c0e21228600e10b00c040751030032443d00c103114107440d6030005c00305032109440c8014070480404000f082d022241305142107200d5004480c8040b448048002d103030f040406403285030f403100c0c0d0b8289803034200c0d071038940ca50304845d4009908001e01c02c000c00d0004101c1500b510741c4110780c82255601b0f211801c06a8400074816048a0943c0c40341105101d001415440342076503481d105400d46680d04090178550050003220080c0b810500801e80592103c4003404c0c40c000014082101440d121545e0800d4980c16600e000c0540c1c0440c10b00c510070701d440c0c160030300030786a04260b409030320038800300180c034807000500380c203004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 456608570 1250 456607320 456607337
    0x4050d020a030213021c0605031e0c090106020708010e0f0d18090f0207060522021210290d0506040b060103020d0203160e0a260109120e030705090f07 66
    0x215201c48a403040115002402000682c0c0700e028480069444020200100006048070b24042c24480c41008203a0f2405002025841c0c5c85802102030041c240c40ea0344450300c40d0500c4144035550340b0314054080c0c0f00b0382d40540a00e0b0725011401e82540c0c0488503240b20f0b03030000110650300e800e00191154201c4058a0003480c0030700300ba840c0e000100390700d410040c0c905040c0f40c42034000d2100da800900c1d04911a5500300a0f580c1c0d90480314030013180141c484502403100801200241c42e0005600b000c180b007801c00e8a6408140c00216811a42401400c00400742c80b28658140844820003855a081c001d64201200503058cd072441c4e140c44004200070002054840440c280380d1090b41628400c000c0441c1c21581c0b030a003601c82c440c0c0d10b104a81440002101d0018085032820450354a03421035111410095040f00301250217015640381481d000742d690368411801010580780104e4010080d066200c0c5000c2c28031702c0d1305260500d0368580202d801400660b0500407440300b0b080800ea88075000c0c3c9804070741c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 456609820 1250 456608570 456608573
    0x1a0115020303190e0a060c090906060509040506011e0804020f0603010315050c1902030c160503030a140c190b06010c030f030b1f0327020906090a1407090302090702010e0304050d 78
    0x82c91060200104c51145500d50020041142e100345491012519405544d0b544d03485400280ca1580c05a0000500d017408248200d0409800c800d0704440141040e020540b07085000b2032030b420000a003203001480e070009002c15820008140d01101405482d02403071981181c070360001003071407584001105965100041e92050949040c0c0d646090800c03010407144051a20081d5079801c1080101228001c00b080444044a815020340403240041c0140d0b041400240043e2440a1004200540d400003000080d0075070400380030845440780f019000c0351810704282460300000c480100340740d061000c07400c84600465004084419082d81c41d103808901440721401107280211204140c1e11141e103c08012003440d6010b030841c90034001d003a00307500e004e524110300d4841030b501ea10001035040741c0110003190715410082481c0780e0000410341c3c0415101100041d0710910101140c1d800002107981005104603e4890b200341d800118a10080c400303041040360b2541c40388920f1084611a5560300c01260 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 456611070 1250 456609820 456609871
    0x609020405010c121806050d050703050103050c0402070201050d0905061801090c051c0b010e01050102010b0303070f030806060f030705040303260c0a200106151404030b04020f0402071a0115020303 86
    0x29070910b05c1c501c0ca07000c15070307481d0090126000919009802414040024070583c8244603460490b0f420200511007541682d05020003903000001c00d82c10080f0401202042c9042802940c9620b8803035002441c8a103402e039030040f90b050f00f0340504040c03039041040e4003012a0041c0860820742d0001c60f25501144910390342c802401025040040030802920000a1940704440e683c0741201c01c01c0c2c000f0f01022030301303004243e02c91040e88401070007209400212030200388100031455010202410310392621001c03100ca01d0702600125298400108000b40a00c20560f01c01001501102e4000c0340d600303881c007034414880048c0002070600301050000304030880460301c01e0040c82d001001c2c0d40d03c40f4180e10620f16035180030b001c0300d0041400f440040f0145040340c40c8501200c01c0c01042c00090b5504040c03c543e681d1070005000b402c2030307034020b00c44405c0c20707819903e0b03200501a192180070f141407515284950703100040701c1680301a4001c0d41c440c4086058580220403a0383c01408528031020100180300380c038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 456612320 1250 456611070 456611087
    0x30a0b15040b040e0c030106081207170c0a050f010606110307060506190f2c01140112111e030c040b0f04080105100f0e060114090f040c050702040609020405010c12 72
    0x1d83e031041c00c280e08407409090210b1141d4090505500905c00c5648800070999940d074540b4041008010410449011034010030700c6d004a103003128103135464401c010700300340c0ca0209014010703900ca40100b0240100c4000910818009080700e0918039a0140500070654680c0242c08014250070340306e4002600e1a80c078545107668140c2c450b00c01c00442a1200c1044043c5216030082c1c00b140e5061103100481c4c801e118004000800d011400c81d0030703903800c003504840d408440046080c1840062140c082c150419402101c3d40460048230880c1c507441500a00020054120130024280301b0800900c8441c50804084409440402c04090b903103840308001c01e10184210392080c0404d5103000c0c140282d1001e081254000c6030308407c1d182c07a8054030348203900d444540547e0f6880c0442d8203a01a8250305d1502e00207409802c000410056109031000040b409541da10b030020000644005011011882c203803180c07401400803070500b1403d21341410006000d940d103071100035241000c2031003840d125034400c8404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 456613570 1250 456612320 456612341
    0xe010318140c04050a0908090d050a020402040b0a020d0c020108061e04060b0a020d02011505011b0b010e01050a0b0717031b360901030312060506040b0a020c030a0b1504 74
    0xa0100039251030060716180d149190416110701e003084003042c0c1c518850300941d1541034100b41c20510740301264081040d0b1101c43d410072100c9001c0c2108400c00f5a64a1029100400c03031130f0f010940c1c520818000909100d043e000b00030501850b4400d04025036480300071598001c4050f5000c080d0b101003644400d124a0a4045440d4841e040680105003868580080d00c580b554580031030300d000c0704903070080c0c2c281c8583d1003220080c00c1d0312550400003588150000702e070004000c80c52a0820b2125100c00c181d03c1d2098010748000500e200042090342490340064000785242c150071401c2201c0d940e10340d1603540f201203829084401c00b01c041948103114020940c41182c10315000c03956624048120040e01038102e41c007181c40c5d8900c031000f044440840c3c8451088440080c4003c03034a80c01c40d642600c0c00000fa10200d0461039540002180c5601d45500030006080354008094494040f080020b10349821192550301076049440f848000032182014035030400f1200c01001545e81d8400003007002082c01022 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 456614820 1250 456613570 456613583
    0xf0806091c1808030a032307030b0d06020a0915020f10050402060408060108070303030b0d0b06130b151c020c1f15140a060e060a11150408031909030e010318 69
    0x6000502d040004010441721105072010301541401c204102e41000031003501e80588000c2400148156100f82c0c41024405002080040251003a4035080c0880e00007081040110700114418032807001d80001c5400d1002d0144028902c4c82e010a001e503803140d241c5a400740146443d80302040c00c554460301550301070840e4108860340b541e5184c0c070003a981d504500c002c2e00402d203031501245c1541071908141e40340b10703080038104400b03864420601c01a8001d5090390384480e69210440302150391741d103548800b904e58840a013507ca50011a6000b6940584400b503400948100004964030030045000000701000d440802450041c041d101405016114104035070f20000704008208800d02201d04614039000740e510403511521500c1c10394801c000461041e52148003809441203d5204a01e40078400b400395007901c4140d2410038140f40d1010040e90110340b0742c500070040003803a0a110302c6a03600b041c100d0006011000450f1006040f060080745a1810162030302c070f010307558221600040c15260381c042c2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 456616070 1250 456614820 456614867
    0x9011104051e04020a120507020703030504060f0306260f060f060d030210050a021812101808040303020f2e0e0f0a031e090b0f070c080f06010f0806091c 67
    0x31350061110318140648041c3c140b03401f01041000e0310003e103000c25254552940307403615007400c8040c1c4d000001d401541d003c0507104d110100d601440d00980002d041e100000d82040001c1808801e410150a1140d00081d035120000708034040742d40400d0541c106000f5a4200001c4000d42801c0303090280e960300b01e55404d401c0c001403048450035503009102c0704002c04801907884250b1001c1002d146800380000c496a40728110030240c00980d944048120a0880310015040c1a19550790406d40c200b90300560150b00815440c1820030303000d0001d42008901140200494490310211140c001a01c0039110205175403080c00d110f600401300312020084108804032002d0350458a0000c21035000780d42034001820840c6614582d0b68002c6510405850160704018204031040030680d22680040f001503943c0d2142e12800111903034103100510684c43c4032000390061b50305002c1500b80000c5654050185548540d003009400c600200c2d5182840301c1d07841d03114008a020600c2107891507450301001c1e540d200801c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 456617320 1250 456616070 456616087
    0xe18010608040b131a0c04030605100e0c04031208040201030b03010921051206130204050603070c02040c1d1212040f0311010206091906060314010b0909011104051e0402 74
    0x10740414401c038843c0d428249969107944240c000000c001c070f001016507003060440c5034401d6460b69010303407060100100a04080e82c9417a46002d0340c0c000d4030030801c12140d0042c14025001413860b501d134441c4901009626003803960365046100184080524104041c050109046a100b5000080352810050081c0501170f454201458810051000f10410314100001c0740340c85802071040c0d0741d0032074100c00c00400c0e66491409209441407090b9920303826035400c010103c2c0303a586201c05107004125568a01d00000014070620040f21000310007203050118402c002c04401e103182c59144a40e4070140d40150741c151040b40303d14030301540001c03035203c0352401050109040c0180307051907085a000b051354501c942c015900580e29840182c4020421f904a101e0000c1c4100a040d21041c40c64483c1c140042c002c0d903242c03039440f180140945c0401700c2c2d94451885c1c5e00145400f8204a4004081c00001c000f02007484010715082d2059210b0903000d4000c01340c82003120508034221080c08100904195a110200c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 456618570 1250 456617320 456617327
    0x12030504150f0f09060c081b0106060801140609311d010f0903090501140d0f020d05241215090106060f0e031002090301092a120b01060e180106 63
    0x1450310040000f55500000c1c00e8041c49041200100c4100392985080c0400c0c85d01c1d40341072903110351882055203050502a030811003091140000501c02d5581d20440c88d41441c2158500626048419104003024003626415944d003401d0614041034810f1490721b608112403030788202511064003542c210f03140c2041056540403030340040941c5802200208040003000b80aa01210500c0b080a030000b10900818440c65000d5461455102d500c00507140c1410a98550081511040c002102141d500401e039441540741d00e01031036412507007140c0513021350a102040c00c205131491003016449501c40c1c07022001c032140240111450f8240403040882c041c80d045890324080c11041c450301c00065540110b02841511801d8150802040240078140f1034803904042d0020350060a96603606542c2c401e9200c0002d50510b04c900b140e1b0313144800c3c480480705079030050311040c441c0da171200c40c01003a044141800141c100490b036040d01d9080c140032081224100101302c0080b21540241d50544000c00080b541d60780 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 456619820 1250 456618570 456618587
    0xa030e0703051b0405090a03030e070f060c0308070e24040302090c09030c0612041b0b0d060e010906050d1209031a0415020702010203090d0809060d020306040501060302040f1203050415 81
    0xf000060103825000810620049030340454103107101d50441500240042d21075001048840164001c441b500c0d43c0310800d0b40c06408803a489100880c0301c840c2ea0504140e000030500d507014900c2d04220183c086035001240020140b0f2543c0003140000c0d19044418002c000c09560103182c01a1003401149000351002426901c41e40d44144030344113001034409980341c20340413240710210310b08042c00e6580302c640e0740765000c641030b011003803400c0150a03001c29060000303030203006840300b9000b0224005140000b020101401a0404c1122504025050050381c464040ca507409507401803640e1100701c410201120100303000c0e00300a02e211030320244212400c810306c603480e000d503010b04110040368055000c41800c82c0308000000340036820234049400f462130070355030301d000d900d004102c2c15241601d00c900040c1150300c03010392840c2c1c4607404401d02156041612400d4007510f890300701149401e061038080346048580788100c100a001c3c04e9000d801b0144a8070a40e00101160100f0800311282240041c00b20b83d03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 456621070 1250 456619820 456619843
    0x212032203050c0906010c0b22080d0617030901230304121404030b011707030602031602190b1612020f0712030510060c030c08070f020306010e1603020a030e070305 72
    0x301c0c074440008075151031268a4012081611f516240c50215610200800f0006000c0381e602e00705070304040c081c140041103c0c0541446800c0b21a0740302c54140751002150b0980e04a040840502980002481c0c0000112100e640c4242807100c4400b00c00000e00301004d03100800010076680c00b00501c0100306078241280740c10030765521524151100001c00c1c101c680030702d1002611041c3e031000100103941c1d0034400f008100482105aa1a464403902ca0b41c00340d80c4240c40c00b5139248000340052042543c184054a60a10264000c01c4800020707102c028045030040c1204828041d850800d00240e4001e074584071041d05070903c1592a4203022085e4030450300144000d4070105808a40050124420b1040351320a1010414937407140c1d040480480300c00002070021028007150840440100e5081409000c1c21807065076010b280c08494810305040c4107040e4050b800304e298880900490011b00c1003c1c0c0071a00c894500103880d101d240c64100d016250a041c0903805000d8204088240507000c1500818403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 456622320 1250 456621070 456621073
    0x20a0e0106081503030a0c14150901062c061c080409050a0216111507060204080f0d050d110415020105060301230c0d020f030a02030106020606040204050d021203220305 74
    0x10fa81e4240f8035211540500d00f1107034990010004a84518000d03074014140740d02420001c00780c444042540340c507040c0a01850710300f0490b02010020945800d02400002e0080c03400d41c2201078200704d00003410803001034642006c43c000b20f00016043c0d2030b40b480d080700d890070640c000c1c02c242503981814207581c0c2c460b024440301d40f401d000014250760359034000c51f609204410034601101840752200b800e204140d02005600c43c00d40c640e48400f40ca6042c0240101074011500180c1d26440c203820300c2d24051403002040126013004540d01d4005410100780c800c4560760740c00200b48103040715078403800c5200d650098058280c10358458001d440e030540c00780c1e00c80c000c164003c11200c0b03051000f8400c6005924050030101100100240010405001800ca905181440941008921501c6600c250411142410a2540440100400c45d030402285d0340082c3d007514214509801c0c000455406480448041c3c01000340024401201710108211500142000c64074003402c01e6602da40c4020b040544030503a001d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 456623570 1250 456622320 456622337
    0xf090f0311061305030d09031206080c0f0405010b04030809150309030a02060c04050303041403120a02060a1811090402030a08040602150108060f01060c06060519051e03030a03020c0a020a0e0106 85
    0x1a5203060381d2000c910340c0c0002c000c50500c0802c500c6c032405000401c0c411070420a001403c0b03c1a001640100400740825101400e6002e20242c188140ca03050030014510403410040100900500941214140c1e500702040641e50403c5501150203c0d2500c00c807485040400010025801c80100240c00d204540b84d0903202d0b2034884500d10340e001e000b9409901d515410421041205146a9901c9060041d01038181d44c2003480c11040e80364a42c120000341c00140c2c01450811005003d40d214401d0701d01c2100c06030141039601c81e159443e28103035408445000d000302d20f001c1410355408103c6104283e6004198030ba4880d110b250007502d480c05002c2c07049140c0300c00c0c400443c0203070000c95254818100d0407600580c0341e180c080b08954002c00e040d800d4039065034440380480c0720b480300c21120b41d4103103406c0d08204805140030300307200383d65991a00c040e862010840c10b6000c25500801211519046894056103039031150140c075080c018400310096200a031400001400080895038038100c0d075080d00c0d074000c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 456624820 1250 456623570 456623581
    0x3152702090a0b010e060d1d1c021605040e0c040608030c0d0809060a09080f0c1e011b082701050f0f071e05070501051003170a080a0f090f031106 64
    0x250f0f4102e041c0d00b40410100d0707a541121381010030182080c0451003002007609039459002e24140181ca5209000b15040b100100100c00b50010f1400c101c1a014070003400c02040d441c14039840e849190044030712a80e280c400c6e406240804201000d5845801002080661303a10b1b102a90b495028850700c04440c05000703480040c050044400510420000f0007402840d03541c942e88000410700301004031050f0f00d05022440090074120050701c4502c4606000b01030102d805074504107450310b802621040c1e43e040c0741c88803076030300184080500c0c03000300d42c10311181030f03103805c008030604490038511207042c0300f034a40006100b060150801070240300d6910140d1100d44411584603006d40088845201140303000780006881c001c038000e8006c07506040d00c1e2450901c0300958038603017968815070b401403240c6000c000600030b100c030400000810584042c10070b4600030410030081c0200600602c064069551404052880500c603000204440d46c04031640d0100140383c540500500c10055100c41544282c0300003e4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 456626070 1250 456624820 456624841
    0xb0310050307140a0902090d0b0403050406080c0405310e15101508040312060311030f1c14040801110a170103030c2003060c07031205010f0315270209 66
    0x10f103c0d81c80913008020580c1020b800318041e511005015400c4a8041084804204204140c40c029031195031915079441c542100206403100261842d109280704010400c51503680d02070600283d11089400c0030902000b4a51180c150250002071301154281000000d00c80c0020809040440f8004681041c03911070240700760400481d8042c0401c407101c0d01c040c0c4009580034003440f60b4040c0c440d1070580c083c0006030700c005044d9081940100c40000c164404a40740386414441002c007080c141c0000d24a0a0390008040f800c400f030304203600103002e145c0c030f424050041010100d402a07d030640c020305c203038181840b8541e0107a01144a2400081652071110848003440c502a81200d8265842c8405000d1940307071084e010488191010a10000005941d5551400d0040e184117540000d030349a00c5104a007405402d00020401d800350040c42c10005201425910b00ca845c180da8008194100340d50350031001d6401040d54008481e010210b803d442410031950711000c0c00312a100b038406942a880722015071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 456627320 1250 456626070 456626099
    0xe10230603030405011b06090b15041a010c030c080c0312010602030c12090607020406060504140427020a0306020d050402041413060e100203011e0531060b0310050307 73
    0x890380741d082003004003d10340c8503500707098a42c19180c040503070510031a50358104031500d08104440c0f11b140742080010010302c400c6180560a42a14141306024150086501071806000c080b814020174054060925100b83c4140038030a038070024466880c21800c03a040e03640d1304214108880342010400200f1040c0c408015140c000600e03000800080e0b03129441e1540c10341064090300c4d002070b4240401c9026903103d0207460001c15540d1111980e841c14007001256160201c2c81150040b41044145610241425a120329115120540e840020110310001c0c86000081e8000f5045600225810364002800d0380214040c500c01c58040059200c2c1c01e0804e00c80a404031741a0b200800700e00484004108903400c4500d5001401040d100240700052416040760230a80115000515104840c040c900c084400d880281804541c8440682d80c140080419105080503c8020311100c00d551005100150000c0740a4004c0484241d00d034604a0842c1d904084503201d0300f413003807240000004c0c0040c10140c49 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 456628570 1250 456627320 456627331
    0x91210050612070902280f0801050f090604020d0912031a12031801180806041a0103020a1a040504060303080f0f090c1207030503070f060606080112020f01030e1023 72
    0x1d070400c1c3e403900404c40001d41044000c4032085480c02c840d603000300b0b03210085403682c002503100c0341c82d07140c8142d500a140341e1058101c03e0160912008840d401c1d5144000c035544500d040760096030728400c030580312020f8210000010070621004116603d125015000120740010303011824585044a43c01c00080540501d0b01e0f0000d900100030141c40000001103240d00e048060500d6000c680080040c1303281d0281a922035941e94000300144010400031001200e002c54014400400c2d47d4110b4000031280340c6244103141e0860040344c20b01107034881040584008050062040103d03540d0703410080c3c05000c0c03c0f0380302144001e094000032100c020040599000c6c0004074020a100c122803404d00c03808640300c243d440c0c43e070720601c000080002d0013040105a06849081d501060380481d03d068000c0e5041508410280200031005100340c1c141c00052034400781e01240d0159a08020701c005038000c2c031045101c80840d0143c0c10001c0103651881c0c00c41c17101e845411440010000c00340000c0403070340398203691 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 456629820 1250 456628570 456628573
    0x1808120a18031808160603050903090102190303060f06030b01080a1506121d0d090803030603060c0f1611010e0f0f01030c120204080d0314040308040803070203091210050612 76
    0x141c400424410b0203940715212180c4840603405480b813201502d0011500b0300380d600c1400616050240591500820350440c020b02c004504254070400040d44808a144050030f07900c3c80d80e41e400c1c0503d40b00c1c0c0c0001e001415800d500300000c4d40c03075400040242040300da0140c042210304020030a18005440307082103c0300c1c009240038055091600413203495038201c401c0d500c0f6548600740c0346030090741c103a0644d0002c0a000000c1054144000014000444641c081000c640052040180507200820380641c0601460f00329640c41151541c0d02005000d031458000e180c5007274420711820407202c200c0c1c142c030042003600e850400d074030140c0030041559401e04130150080800c402d403451a5000307030062404c92200e400e0240c080820014075004907000390344202801d5200c1a11980044d40604c1900c0c00b411424281340301d21300d46a20045e001500142000b4250800000000c41da0b91003031066444040000b058800203881294086990310b030a140034066041c90f0002051103031800c0d4144207a08680c010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 456631070 1250 456629820 456629861
    0x902180f06090606130f060e01050a020303010b0d1d060a111804020a0207030515041a01050102061b0f0a0512060406030b040f02010e10020105040c0801180b0a1808120a 74
    0x70520481e51400303090300e038001e0350501840c1c80004400007181d01601c1c07800c0296a1032860b20304014025031a090005050090801841d030a0b181d001c4103c80c191017081ea06075a9417280c01c0b142200600c0084c1e55081004c440e024024030318900464181e0150a01d000207009d1139001d040c2c403440070312a200807854040740382e00c203400a500b0250050168403445005030340e1543c2d565140c8030304204040d81c0380c0b9148a10042080100000102064180205159084603660400c40080d640340409440c1c20107010166403680555880c290494906040d201004d41d114a60b03110007034205e401030000004030f04050310004020303040078405c4a040700c0e000701d0701c2461601d0f00d03213454010706070f0890180d0410000d40440d000c25200c0300c2d8071400100103540009aa80751600305809038421a400c10045070341005e000c144200400c4421420702c0360060a600c00350b031120320544c0c004140160b68003c8540300b00b14904103220440001d4008001c0e12018611b6560b2403020340341c00c03904180048100c040300c46 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 456632320 1250 456631070 456631081
    0xc19060f031503060501032402030708150a0f1e05040b060406050c2a030f0105090607030c0509030f07030b0127050c070215040503070617010611070b0d0902180f 71
    0xa410110442c00d01d0588000c40380c0c0c49807149419103c00744c1054407000d2808888a000c84a401244555038040480447c02d5041c1154010b0011001512541e40c83e0182d1017410199a0b030692a60002c00d004803180d034007140e41d981903403100440441141460183d698000170300e41041d00039000c101c1e8004050f81d00e4103003024020790b6603401803948024544101c0b10700c039403040300c000f07a1508d11809403603440504c44a00f000b0103140805000c08021264140010700080303007400120755812207000d08001c216824980e0040b19280500802e240c0d040c40340004100302002c011650a09036400b544001c010750b0b0322070a03240c2c050b01074000c0700c0b4004542500c0d200418130450788560313000104210715a24020712038001440d481010142c4126004000408100c3c6140400a02c0c004102500300340740d007220284044450780c0414800d0200780300320301010214008090100c00040e2070004842c03515216010b401900400403040c0403030107640100ca030712506c2c260000301680300d0b0303641d60303081d0a403035980c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 456633570 1250 456632320 456632327
    0x114040603090f1e060b031f0b0105160b01050a150503010308071106030403030f0e0d0507020d02040e10050109060e16030e0c1e031b130903140c0c19060f 68
    0x1c00c54162001c0000c02010800070b042a010304601c072240c01c4d5840480c0000703042203412902c16000c2c1501c82d40c058020400620102100129a01612580090340c500750800590345841804040b0240c0d4410030b4074102007011124030181614001d441c0100c16584910401c000e142c0384818100110320103000400c00201803500034903020744180000740303000c00800c000c2511604150b40031000300f5164014030040c00e00c0c5211b1100580444001000070030401403002c2c1c6184121000a8010b04080e001d000964030360342c002914002940381264400401d800c4010001c0074280548c010881c01c04900140e00c40010b00340501605011912038500c1d2030511094009081120401005020301141100180d44d120700c0b200c045c07039621000e00d41d610a14010182810359460392050300c04030606e05d00503603899031000084220948100010540380c0c1c3e00701a540d51059200044c3d080c0300018000340d40e0700011030408450301044d915501000d2151103124039220050003468002245c081c07030524110310 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 456634820 1250 456633570 456633581
    0x509010311010c12051803070513020d0e0703080307020706140d0c020c030607170a09080f0c01020c012306030c010807050f07150c0f0516020904230610050114040603 73
    0x905040143c100c8060750384403c00c288134400000081413001ca000321298901311b200d448066400c8000c0d01100d41481c00007401d03c0c80d4030600c50303903081e408180010b02010562280514464001c12100c44a5480c5000c2c120765100b210080018002c450300059010f00582aa960800c1d801742d026041500305000a0010b10078588030b41c04500c0740441244140d1010310155014203116035507440d45000400001300400c0019081d81d403854980001d0001250442081c1d403449088c47d2240740c5e1394484d00c0c81043c0640580c0a50110725481e00c00c220f100543d4030110545d03400f03c6004c1101d01941c903041059107a640605440380401d035083c0004506c2c900c62001401040d03c0700901070f060000395100c1e15404451819005891642e90413101361840d00840407441c044e101d440d1440c41c04d00040040d440045c2440300082c0a41c003004041401c010703500f4140c02d00c0084c08414602814403040c40150b0300c10b02070b0b61031901034403640d4010400354402c0c035138401c482029002d61440d085c60138004800408 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 456636070 1250 456634820 456634853
    0x201020a06090c1d0c040501030c0507060c170915040305130b19032409111c41100e0405010b0307050a06120b040e0d2003030105090103 60
    0x103411412030014101d48100c0500c075000c1c04002d0361441c02e0920680414085004042c0b0011410003000b10881104007100d0590b003007848c002c40c070404843c0c03041d030785030151200040800d81401c0000c205070b130740608035100803071010365005400d44407800007a494258580c034410000440e0400207011030702a00040c610007200c2d02c0e482568650710010140b02d42c02a011046401c507600b08407958180d8540101644203081a5400100c068030f0640711103000b83c00e102e0802c2c856103d4084442102c0d040c07055a015400c41f5510901000f101801318004003082c840e6512414a28490003100043c4042070500940307440071482554048403170114010000203000f1209d02c1441440031030039400d60031045000703910410020440c0302c605002c260a00030a0740020b405881805010410305901010b10080d241e0070600000d01c0301061004100034100e810301081891003003c400100881d407102c00c0342900780c44039960807110190705090036181c2c4801e10070b084e031100e407010040c0085552242d81c0810f28 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 456637320 1250 456636070 456636073
    0x71e05150a38090c1606020c060a05091e010615021e1f1107020d050a06050105030a030503180a0203070b0702030c0a08070513020c06010e06030618062d0c040501111501030b04020102 80
    0x4480c2003003003405c24440060484005030045218800c505081122a8020300d028905000750724000b100580d5849426a851601032044000c0e458100d41c01e5010744081d00d2014841d034403140c01d441c00a1b540d40c525050080030049640716201d40340501140302c113980171440340301510120343c40720b101c009000b007040c1e8840c922004100040060b0b40e5001100e55040c13007080a0001d03070101d410040100c0c3e605034084e03030003030304030614802c0000d51020849030f00c00940045040c07400d036004402440c0c4005e83c17030025018858400c02189581846d4013a201c102e00c21400c0315600f06801040c01b110b808a071003007034031aa0004105110701d00d4501c0b004003249400580050070542c420061174a008000c0e400380c00c6030014003041c4082c1c1e04040c8002030303000c1e526031126403041200c2c0ea06070341d82d83c00007000517400a0348030142d408002ca080c00300c40d0840c10400b40022860038411b503e41115405440b9950100b0381c60281100c005401081c00c129a16000c000d000450b841e50b2103c030301ca404024001c9046 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 456638570 1250 456637320 456637327
    0x1e070b0a02010e07140a090606201504150b0609031b010516080a0e011106061507080301240c050c130609050901050601030f02071e05150a38090c 64
    0x940404224044c000c1c4440041130103803c41850600038642c04a070400004242482c0301409825002034a50340c0d061040c002503115480e648408506002c0c5140f40900103000303d90500c400e10808202e011500c00540c1001c001c03802142041064501c0381c3e40c600303034064204100c121246654148544a00c03030040c108a032620590941d104518600040f00701d070340f803801107146c941c8250302c6000710590f0442030078080048180d00c1280c07031341c40344000c01c0907115160031100041070180250549402c02d61041045417256124801d4002041007014480303040a010844100c20320300c117103075010641d500440030b4001c61254000340400e52401041d0080166190340300011001214030600d807190204c90000242e43c140340000500340e0382c6045040d088103005104140100c0c41801d903c2c24503008004144d000c0d0040c4e4a00241860040d5055074480209102004004070716904003000c09114803d9400c006425644225004440c4000240000d1904e5a551620b81040141300ba006904403140c2810b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 456639820 1250 456638570 456638591
    0x30c0b0f0c07090606030506090705180a050301090303020301030618031e0207030c060c0201020114271c1d10080c090406080607020703150908030c07030c0f0804081e070b0a0201 78
    0x10b00700407070307020b2141a90380709800c0041c2d990510410360414000c5510480c01c1c242258020300b140100c2e401100e2a030340c01d6485035401e45e5401e10072001088060002c1c08100c6c05800d001d0025002440f05648140c1411640103000362101249000c107a41900c1c5c40380d4002008150180110003d04400c00350f00c581080400840c03800c4006a009182070740e00d00c4640ca11a00c00203094503001c07100106000d0b01c600030305ca410000c2510000002e903c0340d44110551503014101858101401291b07044800f400c8030590042da40810a2110b0380c0300e80188500d0700e00700c6000c1c884c0400804e103801000540b41c001150341c0360745e10001420f000718000c0000c2441c80e2a0100507003044010748220016a1007800c0c104104490510641c0c040c200300b4100704140c08107900c801100c0e110003484040e9141e00050050200343c0159541482190007581c10400b00500d031400da04180e129000e00e01542c0705100304203214814034a230428000103000c000d020302174a4a142d0b0244d9400245e0024103554881d640c00c407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 456641070 1250 456639820 456639823
    0x1b331e021e210a090317060303340804060906020a05061b27040e0f030f13030506130b090109021e06070b0f06120303073c1107050109030c0b0f0c 64
    0x5005900340800051844c11500d4080c000303080ca4a0040d40740d01144d07081001654021099800441243c600840c1d021201700346080e004403402d031030f043c100070622480400d110311031000d40142e03201b0b610b64ec500031f07071500b900b640e5510010800800a600c510001000c0c4080c0b4900307140d043c80c003610b40c641402c1c00940c185100c0750444003100780307050050419403482d203010b000750301c0404400f0700601220107403144d03c2c545074802c12402d0200200b0001e800743d085130340d44500c4402103801009030b030081d00308410030b40044c0040f54800d039000101c920116190003010722541100e81e030700034103004040d60262085d1401f10b01035502e032544010140b00c8000071650850107548116035028552006140850402c00320300d4010840d504a907009000700180d441d088164080c49001341c04070030311000304c0c0603500c0182130807080746000c41d540038001100805801862030b11100e10390307006580486071128011103190b0602c1c8000f03130180d981140e082110f1341d04500140307140b80d0310030802c1b80b801c001035a580d07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 456642320 1250 456641070 456641137
    0x30c16080c06100f0b0301031412040303020c0301050708060d0b04150f150905040302070b0d0b04060e04020f03240c070b1905071b331e021e 62
    0x1c480a4200b0020001d00c0444020b644001d4110b445120410360305050000880b400305000080c90001410010310140710200800840c138071207000c442d03681769201c4c074000703403107803514400300b40650b0a00380451911401449040d10810001c1d00d560f020a02c50740701c1c80104c61001c1d005996034522640d03000000040c0380141d03400107941e2500460382004407440e05211406c241d001c0c241c8180340406000020358003042c8042202c1411404980f1550141900001051381c00b40d500d6102e49880310024070300070030800061041d8021601c0a83c06415203040c5921810455486003200c070422000710304084041c0240c1f600305d00c00e03c000fa800c2907841c0d0f944405c41c46c3c040d00c400120764820200300065000d44d01509a00a00724500407200d40c40002045070354402c06440181a200815031548850031a440f00828036511125070320303000c002c0c104100c0010809240d20f00700101901e40b08040d04690350080314905404074810110611405070300b615103400101601200300d0380e02147c03008515006010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 456643570 1250 456642320 456642337
    0xe0d031808010614090708010e2e18060605161104090302070519031101050304030c05150603010c020708120310090903030b040612050c04020c0132010602060408030c1608 75
    0x43e07080c245205450802d00004000340306415000400c40b007a0344c80314100741180c075510241c0d441d0b42c50380d0b401007521200024801d514011051007001000b22202d403030724201d03083d04064400015016900c0744c184c030218080c5801042c004c002803a00102580d003500390840c0110580040c1540c00700004050f075004103020740040e4082c450031301c81440c01500c8801490340c940c1c403001601b40746a580581d0b030800c1c44102d038103100e8044001810306000343d40d80755006a20409407004059170f2200c07803500050503246980a0b61030030810b603a0711400000c05030f0a562062005021607100013189845503403005000b00540140d011002440401f50b0080014180c4039860214200d003401c0203002c200d690325032291500702003690881c2c01050740424412032860302a140541d131403088010103400b40c0f40c0800a1202c01e100c8440074840040c0800098000810100c54810310346d03a185d030200d9490b5020788002d0040034080000c074182a147c0343c010008410010035200c0008107030344500c0c2d40c54208a86 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 456644820 1250 456643570 456643573
    0x1020616020c15120f091207060e060702060f07050723030f030c0315090f070f031803020f0601080f03180f060d0b090105030609031c2406080604020301060e0d031808 73
    0x700c0095040713100fa401580b011000c10403071038918107400026651080d400880c1c04000d0700252000a1100341c0d0050a00c1007035420490f00e043c200304000035038a01c001c1300e400c110460410f0116890610a20403a0400c60300300400c03100c00c8680d02c44203544c81e41d6081c5240402d220421803000945d0a41002c3c0d0b1180101841041e1a45440d00041d00200070392458944130724078030b10800060b40b909807002a0410701501c0d00c0300ca04640b8200c00d0f801020544100c604960090805a08150740040c10100c030055070b4081d03c00c44d0766544079541d615201290781d1b4a954100340414400401d84c076210600d40c2070001d12420a09551002040c015402401100e0b00d460b114960740b046400c01e064840e0041c20203900804103817429450306600c034000ca04a070307030b400d595800c1c0d01ca00707582e61900070051042d0b40e000869000038421100301c0c11480c2a100f01008640c150b40003842030728252080c0c0e8126400ca448480041e10760504201e00c0b2541c03510b0403010301c1015a0000021050300d034410b00600007100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 456646070 1250 456644820 456644827
    0x501030b120d09080607020c0d11040617030405040f061d0406020d050c0c0d09210213060b28050304020d08120403020d0e090103022110020316031a01020616020c15 72
    0x249018141103005203a030003594404011040e05847e010125514107812403203242440e694000002c0182c4000c1e03220b37a614410a0307002200c4500003000910840710700321410011044451001c20a54a441c13140b0400c0204840c000007090380e070451722030351003071003450b00500d0000141c03081802c440060318105220040402c0503548000c0030003040724441658113180b00b8452038408040001e10100301c18600c07550941c21fa0304d0131500d0740c03e6100303d0f00c0390150b41403001030303240c001341030543e0000040c8504400d240707244000c20722458805030b000d6082956500e840d503a11130f024411050710045045550900c108003107901904140c3c801d9020f2031181e0b0140081518100000340703049465404684111603c03001000140d075165080d611103800102e20440aa11900f402c50620350702e0214651803070700000403c10000750720442d02c403c8040ca51020401411705641048520030000c01d2103015034007400100721141c1ca603046015050540c1d00c111245200564045042d06070350680e0703052500e1012 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 456647320 1250 456646070 456646079
    0x306010501140c061609080f070b0a020c0306040b0604180c0b0331020111012a0c05030f090a0e0123031c1d010c05030708070c030602040b0d0605060a05040501030b120d09 75
    0xc4021b801404846d0003800204900381c038041e100c24043c072401456006c00600e0601003030090000301100a0001d0664042d40341c5801c00d00b00716902160400d103d58505034040080d00c906514801e083c58005201046041c10f10781c5401c29544080c060a84c900d00318652001000205450381c44200b0b60000741ca400c1d0b601900c0090801604115040c5950341058030707120004c5044500342c0c1c0c40101940c2925651040500d06680074901244003400380d000010325045800c2440d0024003c00740f0984004607041c1c0d07190b400c49030101080c020035841d412000d004460b51030307800d43c855002200040580303c1c81c100d0044503480400744c607001500403d071040d02c0c0c403028085807051840301c00000c0c00c054880e07500d2a0744082e100e214207803000380100804503201042c0001c2d13046901c00f85a201504559458441e2407041668000d10401c5440c9420402c02040c60305000c81990940201032b2034003806c06051000540140c07001c0402c0d190062103864819818140400818a0702c00007038503420446c9050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 456648570 1250 456647320 456647327
    0x5061c050702030301080a03180306050f011d0609040204020d15120b0108060c270d06090209060118140105160609050609151909051006140d020306010501140c0616 72
    0x7024582503400034001000108400706916402caa030524013901c5605400f107003404000c0013504040d101b6440c040400040051a10343c00707060301c81601c682102a40c80090701146c2c200112910380d00007142c10b01003001814a80c014108104045c00081001c003040c880c150400202940200450b4415440c8041408101d5040f035000d0f00100020301010300c2c003090850301900c204440141b44002e13076900041c0e8481c40d5203840c140100e004080c40840c4a050900e0005460301100503403040c80c00c50040380c06580a040314404084840d80720f15003503490b0000c5042e400504018140c10300c542008030000d46150f840c07113556424841c0c2c40000d142c0d40785003810340c544503009045088590005443d18002721440040547c807940c202a821041c03102100e00070050a03030b50400500c903106a80c401c000b0121a60000c1041e640660100040e5010160401c0240300c10b10602a42540003c1d00521083d4459071a052910220540749864504615040e80ca003440c02c452504061081014140a10f41e2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 456649820 1250 456648570 456648581
    0xf0905060619050a061407060509060f07031505040c0521040b13111e0907200d09141c050102123102011e361a0405061c 53
    0x441415000c1000c0c101004564404640d001e042c09004003044020340c85082d01b8100c4d54441c0c0c0c40407042c403003400e1810449940d64001da980b14104402c400000d5201407292060410498012005582c0c051509080c000103003c034001040400c04104005160b06031007a1001e00071218041e01422280703002d0410450f10000a024501403100b206118008205900c58420203010111030b0014039500c2c56400c1c0c6c6024099000d517580000f40f4900300055a50400c200e40419040c10400b600740d0300c21503100503252040040081c4c0850308011040c090319220003034020002c00c02074004a8229400a629412a8582c0000300c409a4000134610826840c000006401888105044007200c2400980c04c4da50011001e00e45079018448075108156031040d1081241d61140f24048086110840c800030883d01049456482400014030a0200440011a10004180e18001c080c0d141c0d03082a100040c1c1250401c3ca0305d9940609100100d11682d90760020700c01464081e9a0075500245a041c1c0801e945 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 456651070 1250 456649820 456649849
    0x8010503010627020c0a0c030b06040c0327050705120d030e070e060402090f09070c030801120201050307081504060603090317010b0904270b01081c020c0906040f09050606 75
    0x800d04165100301e40e070003041c000086070700101503110220300e05d000d1315042d4101009080800c400d000001030001071040507000701d6082d10180714440321500140c0983d40c1034620700b100414a041c4800c1010f03403907901e488a0340d101d0030543d19840d540c5c20004807001c515180c80329a03508510350700413003990036218020b0100d18541c043d0007070300c2c601000303074248900040420703020f07a80000c0c0da20740035a43c140240c1024000100b615400e410208401000c40c01c9501c07048000c40c507aa000406c0451110449400c010f03416540c46255a440e03c0003100d088501800040001500306103004071079466000b0341001e010941c0d00041c00d12180d003402080040d0300e164600d82c69100d20010b0100390281b0085405021702564040f481c420720b07804080b0001c0b114011b10030502400c1c0910780821a8a108a80c1281c00d10310448a50140030100f2607203080c543c20704800540e01903480c056490400c11100d51344070000500010318031000b14080300590b04003410884894020b103080102d549411031078904d008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 456652320 1250 456651070 456651089
    0x5030106121a01111501030b0114060408030f07030c050304180b0906030d111f0c0f0807170712050906010816030b360703062a08100b0a080105030106 66
    0x14a202c0c4540002801010301c181007001e101c00401e03503040104030950610342c840d500c00c1919079490500c0c181d505420700074113860317400f40c0001c20814a484810f80781510102c2029524190301c0325216a400d60003040c3c21024840d02882140104800344050b100804810b9440007107508c00c0020001110044140c880c0304d9040c00050100c0f0351400113010f2051402c604100203001148000c492038200310464803101000c0314004018198501e8200380711116540c1c844001c82d004171401a40c00d00e00485501e00014003144c00c9007804080d043c41c00741c002025080c0403001c2011000c09105480c01140c6280180d800f41c00100a1400104005101841210388440c0c1080c00c0d41c0c0e4454141401914072019aa856a40c0b0800426840c0c40510b11000e1005110b2480300c1061000780c0741d1601d44802e4074011f00e000b1800c0007481810790f9003c049070811305500b2241441c4034040e43c0307140d0046c080c5985a0041200400c00c149140010000c002c0701340c0301c40c201c662400b002c01d1b0950b0195000440c82 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 456653570 1250 456652320 456652331
    0x1b0312030b0a080c01120605100e03120405061804060314060f010608010f03110a090c17070806180a1104090b1201020a0e06160203060f06040e0a110d020402190503010612 75
    0x43c0300c0442d811548000c00d2801060b494001d80080000d84801d81101c6d030302055254200d600b05030800511002c0d207800b0790503a24440c0403040003e144d406a48070303164204d541004070000d01614403100e2508000000c01c0022030644a03100c82d249001107030000540350b4000780c20301591188110302107004014500d8542a50740c100141e05216400c0741c80f005004524013000e40e140756803101c035407001902c0030030001c003c2004402e00c01413427002e51424180c5032000074004502454891700d0300c40d11604001e4001e82107411603a1282c61303120002403c0b421b03006d943d031010740d01050001009000074030f10100c02042e01c1a03030804000182000c2020120107a1042210411403504040c0d08103104500b100d0303594884110985400d000300c80044025414012001040700c0203028070031517401800103490401c5502c140704400f65840b01c00840c00b03090082c80f00c155030094586658402e1000344064000350500c0820303d6400310075041e82d05400c2c045207000c001031266a60020301d40c407a808035004140076 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 456654676 1106 456653570 456653579
    0x2a030312010e010801020a0906080601020c090115090b091011162603122805090604051903090506070204020c030a020d0909090803131b0312030b0a 65
    0x41c02c5829000454024414400d0b1104180b4680302d002080b403c040050f02c5841d070080500341148202c80302043c00351512a0410300070075124008501034910002d010b40100c041d0381003100300f02424006251a0b60350300d000002c0701078007418142801d203032450140741030040e0700030004650230303200c84000f910440300d440307900100d900404c2c0501480c0d140c0c5c80403501c910810003400c40b150700712400b140303403000203032641010368124007202e1413013640070512903096800441d075074640c079080003081005205040c00306d10201200404410241c0c2810741e4050030030b020f24003c550080300041001811502c940d03044610020204c01146c1c1c0360303092070b84002d503240b00c0ca090f40000115110000100603000380030f2606010f601460040c21a88d52402d00000300115075401e480c40320b101e00c080c000c0304e44280d418a0243d800b50070041049040c100010301030320481d00d040e0f801120300d00030811 = true := by decide +kernel

theorem cover : BRFrame.Cov 456474820 456654676 := by
  have h0 := BRFrame.cov_init 456474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 456474820 ≤ n) (h2 : n < 456654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
