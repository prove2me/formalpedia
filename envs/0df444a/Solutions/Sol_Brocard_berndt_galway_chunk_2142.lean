-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2142
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:46:23.313102+00:00
-- url     : https://prove2.me/submissions/4adabf7a-fe91-4d90-a135-fb9fc6f11454

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 385071942 ≤ n < 385251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 385073192 1250 385071942 385071983
    0x806041203050903180301060504091b1a12040615060507020a15050304260d0e0d080609150f0d030e01021509031912060602010510050d11010302070f0c0b07 69
    0x50b401043c00501450400080c4144106041e4500e04c03015031664076000000390a4980d0b10940460a028005c1d0700103500d003011030102940b41d59071111a6850401540741030141c00c240580c1d000c200d00948180440d240c0b81040400f0301501150364600356800540000c444d60403500500409109640c0ca82c0c00c6661484804040d110001507180401c90030030004000a83c0c5040440b0354015440300c0e00003141d07884152a0072904809060362800e0307035911600e030f0081420000304007800d980707260084841c60400d0105001030000f810300b40407220003110300401641d607210403218811001d81182454009424014559800100400d009d4007440e0306a070035541c1900c210510510400c0011894840c440d10500c0d61040985070380c008010150544070051480d500410307000b05020f03400410242017194951044000300e0380818881c0c2001c4011400146e0700e043e0703000426009081c0141c407100c01c0d00388629030b010118002014043d111308041171001841004c0c0c048503010b40c500b1301242513a0801d2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 385074442 1250 385073192 385073201
    0x15090106141f021911090c09031507020c12100c0810031212090c030507050303070c1214120307080a060608130c08030c071503050f070c0c0f0806041203 67
    0x940303801c5180e4109880701d4900b0303042d400009481c1841260783c0c1850b01c00c07600014080050048130354005100c41403010b8030301510302980200703070900c1c40e81c5001e03d07000020381e48d10301d44020710317a0401c10760002031a0540203201c2c803118000040c10300c2c0220f91041090544511038000000b8550345440810142c2d58801d0591074450500e00c2d42c480901425a1900150001032110440400007002c540900c070200f203016501d00184103100306030069055241040c1000180e4201e01d000f680140301c000007140c40c03221040d0443c1e00040b03519000304003d0800c440e040c075440c0d604812038428072280e6091b100c0c1c030300019442100305035901a07132902e50343d1820054803514452040054070703440129021000c004803508646114902c2014034655411586082d9000b0421908054015641c1003000e611003010707040480f070031450104003d10b400c51901050b0500030f401c2d40b007080016030441d410800c090600d840500300b1071002040c03840d0340d003c407103607034200c00c4400300c40142d24480303103450590081c020b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 385075692 1250 385074442 385074479
    0xa05060a051921050a0b1201141f260a0305030115090b040b0c07030204180b060f06070312090204020d1a12060a020a020a0c060906090f08070605070303090515090106 73
    0x110084442c0081d043c01510001e0325000085030b543c140c04d0307000c2d13580e0020351408903004400403031694800d25030010703003a80042c6041b01c090190b20030081c0890940b20900d0580350184086c924501401020f0035201c4003600c8540c2443c80b891465405041d00100694121441c11080320075110a04004895004c245e104424007100244811306c80d22502e40040d00200f036160f421500c04580d40d800090565012070001240c112441b85200140f01c000070300e0b25400038042d6029584030807800041022807050b0f103400340401c00100d803180181c2c1f200c0c1d00200151500200259142c0d590341e030300003000341118118110092403c0c50000380509010500089001d0594080d02c85540c4290200010350b01c1000301404501880c0052000150503280440140801d656250f56180c142040941000360a410400321210140d000f0090b0400000700541580c1c0b007890010303181c1c504c91400703801401c90590028030070b016004802c02e54071220501b00e841508050001d2100b180c1c0d40d405001880d0341e064 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 385076942 1250 385075692 385075727
    0x10080109050c0d0f020a0e0a0f060b041202060708180913112101050a0e06010501141c1103040b042108130c0810060303121107030804020a05060a0519 66
    0x8480a074a1825031202400d46005130680550a6459800110721900581042010f4142d000078040c54503000d20030080c02101788042048904e0802400003140d008d148600c01120303074202c1d00a4210f484a0041d83d8280f40d000050603283e40d007074030510341e4140690a00600561008000640c4c102200741003070200c0c2c2d00840401c0c08000300106201d0803441c0d5249a15524085240f1440310101c2407044d1032003807035490000545184417071145802c041069000604100150320781608082c50344040711511005804c5084281d03a2031040900500108880d4450301e0300007200f0402400b21055085100360300c56007503201303030b41c64007401d8401481d284d4201360300207000e50000800c00b00b82d0340b1403801c100f400340300703480c110741d40c2c03940d06a2800d45040d20845115403902010410503800c13240201c0201108481405038581c1517070301180d24001d03c10302070f00b08020030000c07600f5034039510805805883c0107040305546110b039000240403a4031000201c241003c0e09091070460900c1001550300d1680f228 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 385078192 1250 385076942 385076953
    0x70b0a0c05120703180605010f0e0402100e0d0c09050a05100807140f031e0f0a08032d01090c09080309030c060a09091a010206180d050c03130902031008010905 70
    0x21041d100400320081643c0241966130716400d051000481c08019410b100da40007260940c10500380d02d841d2101940b02400d030030015018030006a441b10007040c9484003926200c2d545259a02c006524030032690000382c10140354640115652445801c12407152145440a00440d1684400b5100d0f10125101c2c143d0300b030300990030500c00150040e10101c0b000e500144640410020700740040d007015801c42c05070180d9107440e01c91404610080c080c1111280c02d001c0039100c51201c9403640340c0c2510000340b40410013006c84002e803003c9841e40b2904422100c00c44164186581c42e600740a00414000700000042903000788001040c400001c02c80d00342a4002c1c0250108240070024030005400084841c024406282c001081500042c0301d442c0045011f0b02058034181d1400c400a07003030034006002148000301d0203c28103150074000541d07101103404c0e403403d15680c10440c0040ca0035400b0701441b00d140d480c030100ac0000c12079500d40146001d80d0804e071f03040f04a56602c0c07140b142200c480d004001c0258002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 385079442 1250 385078192 385078207
    0x14120309010e06090414060306070c050a1202100f1a0a030f06110d020f040905060102150105120a0b100503010b06041401120912020a060513020306010504240b070b0a0c05 75
    0x1a840c1d01082c1202034480c6052030500d038005805c0c0c030100381455410b02ca03e03100b001003500d801c00125030041000d0500720140880c0f6141d0584424180c2c1002d000d4800d00c88442020074030800c019200c12149200400020401d1171f14038001d020020400340340080721503c109200e25242c2c1c03240e4100c940c0074075405844040742d50380c0d201609245100074004d2100b1711445400c0549030005140c0c41c40f04a0503c1d5441c1d041c03c5200c01100da015041c03904540c0279411200107509203200785030544000b1503107aa104581020050305d0500d0341d500041c059140c00341404040e808803d41482a107204030000c0c40704104843c20320070740340120b2141500c0c1302d0070310055254550190040745a0015004004134a000d450f8441c41700b22005c1c588440d0044e03100c101c1910901c01d0314803840d60030440070901c0d82d100344160340000c1d80d00c0c0740600416120310ba8407000c90202c450746100120111030202c400c1d0382c03200c0d9150100007140c5c01c040f0095400c22141000511005414441e03025490b115450f07042c1031140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 385080692 1250 385079442 385079447
    0x7080601090f06051c060503070b0403031409330a0915080f0a05040510110901030f1104030b09070e090a05070b1204140a0506180114040b060d0314070c1412030901 72
    0x443d26212400c05d0345d640300129160b10140303d4107003d04009010b282c0e5462641c0f80c02402145903800040070103005000d40c440d00d075a800714114405d4820791001d000c00120000010345034240e803500080c64800019500111500040301c2c0040b0342010740d0803032454148850642c2d80a9088440d80d580308500c07000100da8004c503500c03c6e80c2090240d02202c0c0982c20010411003100d05543d500403000501240a1000c0c1d80d040c040d00c50a41c0c021142031024403502071414415009a001c0200440950300000304500300400c55000103002d00c45181c515800c10703c0310941c03500260b4200b03a503140100000403039080f0101c0304460704000b621040c0d80c095941c680b01e09000310700c0c20300814014060521032801151040240d140075840101c4c485c2d40d403105201100f402c451000008201010405007000082180000019071040007502c404e24080414a000c44920b130b01d8410824643c1303401310348041440074420707a4505951030950910141440002000800b0a034520184080d620400c8203824030752 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 385081942 1250 385080692 385080727
    0x19030c1205070605010306021207170a0914030403060501050913110607021f0806040614060906090a08060403030c0807020c0310020d020405090103260a0912030e0907080601090f0605 80
    0x59480c0703070840c1042e42c19030390032059550030392064901680100d4003d8aa0100c084820f4101400d418510f01000000c12410305082c001808020815510a0110280140b4211001c0f80da14488140c0b9900c1d512490010f00034a028050180102d18180000da6011a44d6019146254010301030701050035100c0104241c940c0041d40032170b0410b50141c0a45201d52800300c092a100c00c0c241c46000051500d0001c2c401281c50030b40c807542c100340b42e002c00903680d80c80300411200110029510523541d01c0030f480100c0c400303c03c961b00a0700305224480801007490307810750020041070943c0d5aa6800d41d101c4040c200c1c1d07200b0802258660541043d07420524000d4194001c008001d4401e00c0982000d80d40d60008030300d10404d80c000e554040c803401c0d81c1904c010350340c0168401c2100c0c12010ba400c10704a1900100b0f0328007240218040320340d03409402d0382030601070640c010900308c004009600d80e103460f000007400e01c041a0b40d001d01107105184045040b1030004030002c1035500035034034582030407001c0d443c48410340c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 385083192 1250 385081942 385081973
    0x1a0118030b0c090d061d070303050904020a051e0a08130209060f011209230607080a0e0a021509031203090c0f0d0b040b07080601030606210f1d19030c 66
    0xd104200003c85500c070200b004c58028001e02c40001c000440c541490902128106120801e400209040c0000784d00035094401d42d200640300107031223400d404000d6819118000c00100404101503191600407181c4009240c4052141c0e42c581c0700b0f8032001c4030002d411031030800080d0b000c0501c80c001900fa0038250100018a0b0051500c028185402e002140459a0340e402c1500c82840b000a01200a45010002d0204c04103010080210b881c190400400c589805410540c580c0d45660300480405006c2100c804100d40081c5808150580d0a241e0001d503031100e44481c1c042c3c0111012140d80f61080c4040d41e100340e56a5019040e201d021008001074042000d0701c00d0b030b0000343c5050310f1012450700303021180f269120b201d01d0304a60618031000740607440c1c000e14480c10142001800e10290780e1000b80c420241154811a08648103131031000d0004e80b4000032410308041c500821400301d07503580008407000341c00f01000c1e502e034403504108500d0100181c00c80540401c40c00c00c1c8001c00181c0301c12400602 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 385084442 1250 385083192 385083211
    0x4060302130302040501060c051501030f0f08070c090902040b0901030c18021309050916080705040e1509010b0f0103060e04020909070b0307021b03031201060827011a0118030b 77
    0x41c0d52641e0003d02295820303080840003807030580c581010000f041090417062809403089201d00d602d55665610401c0744480000c000035034030300d2584100324007442510301c450382c09030301102010345510f11007000340100c0d0800d92186e0705001030741903a4102500c42c141681d03000303144141ea0758148104002d500880c00303030181e01d866080043c103c00c0d4105c80e0b8010040e01c0c18500124a9040000241d485c0104290209851542074071007005403000000782e0740100c0c1d100703440102d8001200b85d14a82004842c01d203034078007180080301304600b50106602101520b1003c449030803001c14880e0046003165014001d9444003107101012a0151508120361503200400b00c0485100603160b80c82030300607810580340f0b0300160b48605841046180100007031031903188281d00840c10b2540031581204070312018801e410a1260b00c0020800240092004140e100001080c120003110b0010046008101c01c0d03081c0ba082c24910011101c0d9076105d4a10955203204080c40506100d0441c1c940b2914800c020300850079 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 385085692 1250 385084442 385084477
    0x1202093d090504080409110a020c01031d0a050f060106020c060d091106040e04050615060a08060102191505090102040b0a050a0c0b0109090501060b0307051e1209071802090604060302 80
    0x3400807aa00038144100c0c481d14006855a10702180c007401e60340110421201c4410034002d07000000d500040000d01a1000d190110700c0c10003101000f14060941070b80e020460040200500901c100003407100d08681d54002101e8040c0c2e603415040f03803203d1140c40141c1c3d2010003003103592030601661b0080240c6078024800c42c01c2c0d1b40d0b52030300040d10903800303a0700410842511504100a0000901034151b00044035880c090000040000103030750740c42540b01c06c009100d64100804c015034401c01c4100744102a0084062215030a81004c003404181203042000d5a420b00c4002140140113000761000c0310034038118a418a01480002d8600b500015209000c01400c440030002081d10002954028112500300060102c01414850700b594140d0704400c014000400600030000d50000444485461000b480050220808450758103813080e46134030b4803028148010b1000341d01003c01c2031021030300042e2400c100c0350030303403948001a8000e0f0760b220303031b88003a050008115135406500200741d41291000c8510 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 385086942 1250 385085692 385085699
    0x70f0c0c08250b0702010912050705060a050d0b030f0c0618040203160e0a210201050d05090f07081212060102010e0f010204080705041802040b030a05071202093d 71
    0x80c40c0c03a0b041d21001c2d82d03441208000c2c081100c08522000080d169a40e140d07071400341e01c0d4001806a0100e403050041440745081180244030060100343d01506004141c15278075282e02c00c0080c0184c010300c0c012601c0520303089102110b8a4005003003076000c1006800f411001c0703103840c1000869005030701d008684058212140d002540c0d1440214414500844000781c80030101000800803c01c0b05442c03401100c40c02c20511004011000110381d010049800301c2c101840f61004a4a81c022011011174031410001071181c204c034089142c7c203c0070748400c22540480d50710440541d80311482e203046514000f0802404c09211246032110381d1110b0107000110307802c040b0700c09c41c1d4907054030703100d160199941c0480c1c03e0101190074880d0348020081260141300d03040100c0d0710401c401102200c001c1c0b265540f065003106680b0107020700030f4056003001c01d660000f9a98406081101d401c008201d104502030320010303000c0310008030315490701380c0e001240344031a8002c0400d6101140205014040c0c1504102000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 385088192 1250 385086942 385086959
    0x50d05010305060103150509120a02150103210219110a05121605010306060e0d020d17030109061d070806060d020c070f08010207080a0e0406090203011401110303070f0c0c 75
    0x100e00841c032481c001c014a62550070700b29041001414800d400074205014040c9450f0005440003203501402102a600c803010703d002e0345050703640116080c4003102e03c80000b040c4070380c405010028002091050302440355034076040380c442905241503c1030000242c10003001c00e2551032481c000c110302501380d22035103480b440005d540245142d0712000030f90020141c0404100d02c800384031300070072003800d041c0b000c41d0500001411146213051454001c4400b05100819581c40e0005070240c55002003048d45e100c0400f0034040d50320b5000f40204982c0034207092002501d07016000e0100085007401080d0340700b40d202e00c074003290740c840003030f1110383d1240c800d00c0702e400f1000c001d00c0146040b6100c24020801107150440c15006010305511041d549e0348107200d104007048800046603403094152600840460310240000c005003665081007079228804000459108401e0504046501c4240c9900c10072000045a250f9648001c50348040061041030b500720503180507000340c400d00b0f0b01c2410031091094481d01032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 385089442 1250 385088192 385088201
    0x16081b01020307020c0f06040504050a020906030705070b070c021810170109030e030f03040b0a18090905060a060b0405150903030315010801060f1b02120f1e010b0d060507050d 77
    0x4014480e5800424880c4142c0c040002c607469620646500090414080000304103001c0c509c00e15025075264000a04954042c2d8100d404010008103100e45030706100390f00402030b23000f0002c121a4010080d0104035802e01071a015850035a004000804054014500350500100a01074442c1c400542102142c04421060050240c1640c84000282e80c032039802d00600d00710000403040d0003600b15141d20710840d40d022040f50107641c0d501d03690036a00e104000044412855a003824080c031a051603000c80c2c3d00740d041e0851100f07039000702c0c00c5510f80e0315044000c401303d038118400d5480100c004c100030029070400b20090b409015207264014184004140030a003164000c80303c91500041c146503419640d82c008804901500c04c625000c1d5040ea134250020f840d8641810008019120f0300d1602d4085640b40c502c500c9000031107006590b0056080a065903458201c4001548042001c40745040c2104051241c0410b04500510947c00218503480344c0000f13003c081e044a04000d4100300f074000c51080c6006 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 385090692 1250 385089442 385089487
    0x50d0807061e0f020909070f11060a050708060f030a030f1211090114030c04290c15150901031716030903021507120f0917100e01060b1608 61
    0x2505850805400180b01c200d581e001440c2c0015807060140703c000351103140c81d00fa03001034242080e007100d540c0b2036010f541d008804024169640700d00010012000082e80041d8054510b03600d40c2c04460b2605020400c1c1c1b155007c844907050380c06a450070020900c00c00780014510018145030f80100c42c1c1c022f858082d565a45d00f409043d420026000215503070207031780e42985a041c05415821410124450800c074415840380303035a86076000c49050313404040d032030b6620080078200020030381e1010340c000e206440380d40043d40c809085038280c0000360040b005030500018840001c200450603070856882601c40340c144860120009014030080304868088414545c410780651030fa00f04d101d20354030400007031018000c2c2401500409128200002d041c07249004082030543c14400740c01d418004040300c0440e803d500604c8030088000c0518103c042c040381d8a4102158503105002106440b100582a242c0c107100b0307040300c010100000c1800c0300d13580c104404034a1251a02d2498110321004480e08c40d14000b4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 385091942 1250 385090692 385090721
    0x1804110a082103040b01090b01030209060a02100c2f0a02100206040507061b030f030908161a040c1509090c121508030901030b03010204030516030b010e01080601050d080706 76
    0xd00000c4166502ca0906460003907040d4a503190540e101a0b00c40018450108080e07101e42074400c030f84c0c0c029019a0414440604025164800c0c0b8000954629090f0246d801d45458003180012a6100c0c5100c12042540290032200f1101d90780301050040f400000c1c1c2443e10700642018400590300c0d0101c0166404c3c86034000c054500306030620303604145d015440305081c407640071419282c0d1210b248010500d01d41500708101500d1070400e0542c0a0f1041000081000364002010034180d641e18862144450048410214946001030118105a0282d40240407200001d50402c212031500500c4d011240151400c1c01649554640c00c0054030f5108403840049a0b40d09458650061103101c1c000c200710461450509140ca001d4959860788034020101e410540c8400384001e158500350112401180c1c4841103580d9184003660984685046020488a01d02e4040c0001000003600040c4c81c1660404009403005918200401040e08041e900844018100f40081c07408035640348280e00e032040640 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 385093192 1250 385091942 385091953
    0x80304080a030f0503100909052401080d0e0315130f050d0f1704030315080303360d0507020d06020d091101050408060f1806070215010906051804110a08 67
    0x40c0b40c0940045188840002045414010810b40d60603107400312044441a00300050000490b0510b00d04048010f041c0c441d2803692074034491240c0e20320760780703031812107039020251800042601d108440c1c3d9481040100d0789a40040d401440d103d4444150b5a040303000f5200d92030224005940351818405103510640320751f01f06154402c1265084903840e240070000e4500f080c0605050204480001780c040c00140400d941c5880b83c1d8240130004100350301502c000d5040b40d85070319001c034160580c00c02e01c903000c654143e035040c04039079541101e4101c070903150b400c0b00c0540031185c14060101c03255040030304282d911280300c0a050012410740c2c4005c110792100c1c00c1002c0740340309060914000141100e1583d034104002004108090360000c00d55503002003d001c138100c42e87d190044100403000e00700042c4541030081d8018005442d80008844581200c5c2205850490fa0b941c9165422a900f44c0710709904144601d218620009104d46040e41c080e108110031142c8031100004503c14040540250384c03550b008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 385094442 1250 385093192 385093213
    0x30905150a14010806040605060301020408122125180e060f101d030307080f03010f0b0f0a0c0510052e0f05010c060b0301051005040e06060609010f030608030408 71
    0xc2c0209032111541c030703030884480d51400503480d07580c0340c0080020f0710349961200442c1c0300766000e40449000b0040328040703ca001614072000c401d1a40840c48082d1121001c04038103401081c4010014450701031600c1e219590500100148050341c88641d424003003111500d2801200840005c002001e0928160019120700c2d0080901600714000f503e003034440c5100306120451103911820381540342210482040700340b07910b440401e00c0d60044450003040820702243d040700700400702d03010358100d0b5410f017080c10312103a03070f4104e1a01d1481030b41c08400b01e105e0100080400540038010003441203204200721120010318100c4442140c81c1075450041c20600960048290100380450500401143c822034094034030704211240c0f0191203100e8941844a601c0d4210144611a4482244000003030f00034055482c181800d602000510702030a480b4900c0c00010010048002500b507104081c081d00302031034006450b0045d200005000392400c10180c542d04041828403050018000809e00000284101c0f05e9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 385095692 1250 385094442 385094461
    0x1140603091f0c020f0a0b07270b090a120b0c0a0c050a080c0c0301060f0608071205090d030e0309100e0d080f0a1b0c1e0b0a090303180b04030b0703090515 68
    0x907203032114101742e031184080f0340129180c0e4010340e82144013401c1c01400d0288881d5080c0c508560580e14900d4039090084c0004c5c100500b200400c1b50314000c9500148441d00c0780e5001c016144280006800410b001c0300081d69074110800421610409041800460402da03482d03514244100c042151241c10100364081c0071340d42044200c81f1444100c1c002e000e4a40bc00d102c141107203002d40700b800c04201c0d810000c110385030b0051001c80003200f04ea400500035490041e5540b40d48007680b0300c0c0c1c080041e280c001c108007804408825102c00d001b0080c80d206a8184c0c5c454101d42c0c91107200502903100020f001041c00180d00e0a009112102111031107940300c0e00c200c00041d1800d0101451030742904000b0741d00c040050003103400c03141a5641342292981d55103641e14400c0280f141a08131903800c01c40098001443c03504017003800c0449101c1c0d981c02011400100b4080f030f106025101d030141c1101c00340400e0002900703c81e08544d12044074500010701031565207d092510002004600d90a03004505000d10b004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 385096942 1250 385095692 385095703
    0x80a2f0c04020403020f040504030e0d20100e012703030e1c0c06050d021201060c0b150102031803010e060f1503060408120a0e0607180e01140603091f0c02 68
    0x8030031a41141058a59000300701080c42c1540c28500c910359490000d01014064101302520325006411861200c409150005c05100404c00944c10203040c03801d40310103441c11400c0c400d8421841d030740e0000074032009401510f418035a410f48041040c8440301d25610009200032010066010340e80b940001c04056040c81100c5106c08000c8080101200400300070503015088102100c02d985805561140d0618405e1300038080e080d080740210b00c50000001e60154404404142e4a01540c9040c2113510380202012510f14002403490250f00148015500540081d000f42210b560142c008034006e054a1151070030540c00301c841e8110405018107004001c7d40510640d214100107400426060500307446500e0140070b0341e046051a401d40c9000220103110035081817200405e01030458402d42802100a02041d06c3c18060130800004a80d001603140d10b103114160403180d03e59000154820b03881d0520069510003004016a84117110484000d2103440c0c019403040030740072000007071030048000001e0809 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 385098192 1250 385096942 385096963
    0x9090204060e090c0720090709050f060c010e010f0c022509051f03110f03011103010b070507230405070513090b0103060518040605130f080a2f 63
    0x14418041407201d641c002400718402d0004607070084841d5610038000e42c252040207001403184040d09a1001c02d144185080d150762401100c0c22800c540e44c00604580d005501c1c030680c1c1c1d001050418404442c148880185902500c000022800714140079506007907d10fa581840102070b42c0e80c0b02c11031030a9050080b10480d50030801c60b13090300c1001030010000340c2803c0c0915000141d86178003081507032102010101c002c92382903540000d8070b5600e08008244070414000e040c000c03003140b0740000451078107204403018a9034816a2a0840e400c240500030240c003c003008503124410603034085000c031065608031042c00501c0c03000c401c12001c098184002c1d10000b030085020721500380010b8022100c640781c2d00f404e4804a00d0009000c079000e1340100d01030201c0d0b901c482d0300003040500714841e14031100309042c403c0b805074000340055158624002c3e004008620040e00030f01460002070300144000700203183c80f03515464600300b00020a0721241c28108030308202249103c54080e84500d41206003e010581c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 385099442 1250 385098192 385098209
    0x15130b0105060f0307210507020c1908071401030603050601031103010c03142406040303090f0e010602030a05030921031005010206010b1804141603200702010c020a0e090d09 76
    0x410716016995402404090012814010285e1ba004490303024184004560900a0320034841c03810f0200020303464503006d1a85600506400202e0b0b074000540c900d0420458940e00c0007803142ca0720700402018200900c84480c0c0c101910380d01c001002c10307020420745018502603d511440720320120200342c2141c00a440d50014181403051951a4004400c45207a000d40101000c00c9100d043d0004d40d800120310b048556404007001c0307804820b042e070000101c015520f44400e04000251031b034885807450b070400d2191800580c02004100d40c000e100d0f002440d082800441254120072031300c1c00310400a8408514231003141808001c00c11fa8405815842c0700a00080c00609825410800c43c80454400d000d01203a0801c0074400804030b035100e5078040c81004a0b00700d900d003298186160342c0f21401c001021010006401e040d07002003021000f100d031603196401120358900d8080158015205002039031400c0e607000400b030900094080300024954403c000d030700b0240108240b2054081e2042295400030001c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 385100692 1250 385099442 385099447
    0x3110d0e01171801020406050414040b0a03150612030c11010f120c0e12070312080105010e1c0b07091a0405030a170d0c030501030201080a05161115130b010506 70
    0x50998000e002c5502800000200580030380d40d441c160702d6101030038080200c40c2c0d0703c000380c00500386a020000c4c00c203582030b040d00f4407111008135041100b40d41700040076a0b0300002c400700400000e061481c16003050001d040020aa42d80da46500d0b038451446010181c0108080348800700400030700c0000c001084e0b0007402c18200140c01001d00801450310302180700c000654400000d05614028507094660f8a0014540b14419111004440d1500b00324402141c0384640b0b05c0720743c2e01c0c803401030320524103135681a51514190761040080110191200c400c44d541c0c0c248403088140030500c1c0c0448688144059260f18240da450a4000364001c2103075210942c243c8400d0106004aa601182441c0110f0b0880080b07207444200700102c44403441040e181e041d101e0b203494414000c2941540109040364000d89034840550b40d006480d6054510844007215402c04281104440c940a0780c24056032070408011980d07121044581503500010035900340c4810b40f20300d03040e40b04000d4480a881e0140100352078a90 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 385101942 1250 385100692 385100717
    0xa0c0914091c0512130b010b040b16321204051c0c0f1d1623160605180f030d0e10021206040c020f1009140a03110d 51
    0x16210000d080e00c0303051000b05512070b251141d100d003040c0c400903200d0032003061050402191660718403458000c1103941c1916407000241000024080d1002c071812182041d1500d03400d551090380c4264614012502104000700c5054002840c0c0500782e104500f0030420303082c0404003074085141c410440c40102c90302504000c14405030b26901c02660364040036603985401586903140440074003015030410b901c80e42c226000040d0542c2c006400008103514901030310310726100c030340c1c0d900002400e480d1844080350311403400d000c0c1c0540710102407400480400d861420460345c6004511005486202990070980341c03000d000e0800740c00445040d0482e5030a00900650700340da124240c90317010306d2040c503c92503076442d90861140c038140040271101c448400c0c1190b1b0b8044000c00308000d40c0c03090314882d00552034030701d03004180c60001641080001220005122820420740c10304080c0c50b0410003101c0405209101c00c1213a001005402801c9100f521544182021441c03403500d0b02c0000302102040054921894 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 385103192 1250 385101942 385101961
    0x30c04050c09060309030724050f060108040311010b1009060201062c07020a05060406020a18051f03090515010305101b11011b0815030a050c04020703020a050a0c0914 73
    0x40300c00d000e0a83d2029140d80c3d4202d4107600f14042e203000503010b102e42d841950815007070160b0403c4030301300380c900400031511030741c01d03240d0040022140e0f05d0100f001000401c000c41c1c0640079141084d035105001090014070100810f0000c02d2110f081000706035521402e100d180d8080c003e410103002d84003048112407055031982401641d0a0b415403032000c1407440420700061003400600203454004007200c5440c14145008402548444075400000d92203140c1e0100004041c070312401280c000800100010111482c44103103400040024820f1603650381d04a40043d005108008030400e001a040300950300d5401c10504000c0c5203d074024400f0301c0d0030f802644108081000310072054040c0303052045a400c0a02060041c46c00398002d91103558550b001d040050340c000c074040d22446500004113041520f982c14903a03031b002102d000406070740010120200c1401d0541c09480014001d204aa055200d00d4071010f05000f244041035511b140c03c0309090221005d81c1c0216440200c100b0500300a07880c0200c4d12 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 385104442 1250 385103192 385103197
    0x3060301020705070e090f030f1b0709020307050912060f0a0b041503050105011a03220309120c0302030705120303040b040203030715060915060c030815130605030610030302060c0f0d0e010b030c04050c 88
    0xe240c07514005500c454100b003800c01542000c1e00745a00c04541d3b9003401d4a000d0140c4c5c01102140d80b090350a8070b0118071000c0041100d60048840d00300ea40c41d251a24250f0b02c0140c01e00100d115002603580c25200300e03002e02c3c5103050303004500600000a66504001c82129030048022207110589c00800a000e4101a00800b5051440c070440800928101c44d24046a4040300380d88000320000d8131a118006015044491008480c400c0701103600842c0e403034007840800003143d840d491803074005000080102c3c0041e42c040303510902c0102070b00d00d03000655444042901c0003540703494003a540c40d0418811051940314000804202100e03201840e45007072030044c100700c15000014100034112010900d0302c890402c0d0840700910041944c510320502c1c121030300040c0f003030340715580c80b0713103e9040840c1b81c1c00c885540080030380e901030f40541119610a00705601c07940c001854504160820042070190074040d100d0f0401814070705001003224813a040405140c80780280a070f070321079480c00c010710420501c0c5904 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 385105692 1250 385104442 385104457
    0x30b060d090302100609020d050a05070e12030d050c03041e0c060e011e020a021302070b06060304030e04060f0e09010e1c020307021f090909080702040203060301020705070e090f030f 80
    0x3152800e440c2c0703412410507500c00d42c0341c05168140000460000340e1034015118080e650b201c04c01181d41c41c4850310045d00d800381c1d13854010900507031000d04581890440901035080e0401203901d02829526028101c5404a4070750303581e100003000f40006c20481001c84001c2c00d2030700032800d00c0707580039441c0e010410b260751280e24180040d0020004141c1d0081c0c029410076403080b40d0750542c8050300c000c065145c44500f40c0c100e11880c4d181c048401d01482d00c2c0b0035510b0083c0c100190382c1a43c2d840200340242c0754005481a810301100d40102c2c01191f5450046401401d19503540344403041c608030b900d600807403024010076074607414810507605803c8002440b080603400204400c41032034110300140e0a600c68100c0294007c00d0081450a495844d03422206410b8100d035100000640d940e07080c1c6c1c08075041048010701e070400402400c0050301d040d40103541c1008008000502e80801a6174891511046a00c09106140f107070081207220f6000348008014201d6001c0a503182400400540c2c0c190f204151 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 385106942 1250 385105692 385105717
    0x1803040e060f18100602070e010807120314040902280c061508030706020a080c0c0d260f070e12120706020c0f07050f06040311090c090d0b06040606030b06 68
    0x10415090b682c40c03010f45240c01c0781c030600e018424241000c16610b4040e00380107070300c098400d01900144034805045c00504035003c050103403a100341000b81c0d13103800d086000c0080e030420100d44d503054180741600004100074100709600507640c03d030051003500d0907044081708003162010032840b034440300d800041c403c0406500820000380031144450896090301c0c030382c000c1d00b000d20001c45c0c09010404141d000b407001f250541c68000559845803d0404030f4030801381480c0150b0803040440841030f014082c803c0703e01c00820840c241c28409040042411402101d00c416805030707180c1401802c0341c01002c0d460102c03a00b9281da4030f0303040026078103694850070001d00600811002401c5018031629506a60341070070350301305a1703020441141c0d0ba213036100c0e40790040364400c040b541d03642d0a15203030a408403811282c0c40220107080540240c02c00c2205100102903600c002010404104242d482589182c0180d1082050080c0e609040c0c0034841200c0194020a050618041130f450071991a4000c0e230f6542c01880 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 385108192 1250 385106942 385106959
    0x60c03130f0311120310080d0215070e180a0b0621130606120302060a1406010c050a0204020c16050a0e0c13031e0203010507030606090b160210081803040e06 69
    0x80c07400701e0f0410341d001100e00b40790040030394255019050000550160b0303403404800a4840e101c14034240c480821084e030101691003800342c00751070303081d038a25280c0c00401414803a00c03803203402d03000c664031543d40101d8940e403040b080304001c0e81c10f0ba50b210300031110700160303103850500c460200d100c0043e2600c0301d0b11046040c01d0b90b0002e0191110304101c0e422030b95120300c2c10b000c03007942c0d185c1070803044c5c1004030202c2c00343c0120000110b01040601c1040d01c10003520040d501140c035148015281e003a01e0850569050151244c034001503102d60004107031021040b401030460b20b1385101d0070400340f900303178000c00e04c90001c02c6ca080113414042c202c0c0d550003440703480c19143d5803a250020581100c5455200030082c0c489124035400c0c0290560000e49001c0c000e40081c416079a902030124101d504901078000821140710052224032900300203800031807580304050301958481d40014542031a00c40141001a02100800044500308240e031101000a40011030516003032242d0500710490091146001d039a04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 385109442 1250 385108192 385108223
    0xc01020717010f021b060a0c123306111f0b0607061104140607020927191a010f030204231f080d020304090518030a0e0102060c0313 58
    0x203500814903c2c1c19000d046640c0c0c40038010708046440101403100716400b5038000111050091b004403800c1610640d40c03008103440510241004008205400c0104507086c0d2000fa49c800c000911035002001d0001d070000042d2920800401c0d0310004c1c518107200350061445031041e01c100801301a0b2680340000e01041d07040041c0c0c0850340d280600d00c0041c0060b400c0c0004a0042c0030003800030416170391801150460030001b4000c1c040f04e0b00c10344000a4001a1881c001210140c0310300b02099643c01e002160006203080840c0c2c0d03494250743c00031160640e1480d058010810940006141c6450b0004c003040c02c04e90300d05440340700c01424070b01c4003a004503101c120440e5441c1080310085c094000121b501ca40c2070409000c040701d00146041196801200105c011400220004400f01c0c14880b039802189841d0815482d43d02508001d082d065003a590031405c3c00d12030301c0c280060900e24120ba902d0351a0744041c20002860030b0780c09481810307005010824000740c00c5c8984010803d040c4c0104124419124 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 385110692 1250 385109442 385109489
    0x50f16020d1b0b0412060c0323010503060a05010b030112060f0e150a0b0303042706270507141b12090a08010507081f031a07030e0c010207 61
    0x2000800a50080200c9584401c020300303000480d24038424558446416902d50800c01d20354491030040b0ba107228010041400000c0b0190001445d0040900d80890140401d88032080c803d80e400610205d5141d0781801884141410041c003a4440e03001c903014007440d49044003074a0507101c18001e00400041518003c403d00650303801a0903040c00031030082015008050102391940341c2004525044e042c100b002ca41014014051164181c6008000e103203004d00c0c04a040001c802e0002c0791505008004040040c005d0041c8100401007198182064080115070340c8044440030761042c1d90703201850941030240c0c0c0c5500c100030315101c03441801c949036180f6000303c07411040c02c681d4004000300d100340d0342507080d01c1003890050000700c0006c0d1071004040d5160700f415402e0302c0b0112945000140c0b170030300090b00345240040040c0c5008507542c80f0809662642c80d941e804640501c1c4408100c04030a00f03000c81141c2c544110743d00070007454060140d000713034000003d488400900c58000d0760710045045141701007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 385111942 1250 385110692 385110727
    0x3080c070b01091b11060a0f0f021206030d0c030e10230c12070b060f060d1103060a0e04020a06080702120c0a060c180510110d0c05010507020706050f 66
    0x681001c4007451542e034a128400c0608400b043d007000902c5824070405280340544c0c1c100c0c0681e0b21010140c0706613503464414000810520b22040c0d030154882c200c0071020000da01c02411254041c1603d0340043c82d000c810705141004903480f100400c07142d148440c000c030703030302c0310311038400410440720210100001c40381241d28150034000c212000003540403804c200c1e120b0600410403560741405490303120000c980103000600800c03101420440106c8002010782c074007031402c0006c0c2c0f20002e01c0e41d418040c01a0040c4200e411f80300d48049141c80c00024801e6604e0031196800c000c001c107401103062450542d003c10701401152107000c0c1070010510114070001d0082c8850040c14031943c4000c0c5d1100e10f060b060640d9425922400d5440c1440c0c000c0403041d02d40320f03000400f210381d1040100c540042c5414144800840070140030010040d26055501140c5828807609c0c5600d0942d566000c0084000d0509600712000900070303009642c00460100f00b00b90f0064252900c0c0b6200e100502e441e6207984001c0b28202 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 385113192 1250 385111942 385111957
    0x18060618060a0305061504030302030306060c030f1c1a01020312040303021605100608030a0912020d02130912030e0d0e040e06090d090801050c090405041a01091a03061303080c 77
    0x408030b014039610341e0591085204507422aa103d41d400d14402c1904c40c24402d900000d0016081080080c0080c00c3c007800415a61280c0380442e45840780c0041d0f08040c5d50040c00e5154090340c3c02c40c2c81048421220b004089412101d200d03440c0003104200e0000c0d40d00e11820140d21032151104000405150099051760a94840c1c0d0704000780b040b042d850001d0710f544810100c8003c29103441c034042005c000000c16034041c0a42c0c1e8903008240380c00e00d07501000700d00c48104200d900c0305010307800b0001a00d075104142440c15900d440890404014604100e2b0a000f0f03010200805107007000c4011000800500005a45200d050004192110a010501504405c800d141080c0f003041c0501012660024408040281c20b942d000744a5440b12426800e8410580e58031840c1102072022401d24a00b0f68032480e003152041c7c44211808600b82030041600409031b108001d00c513030b40d0048962807004d04403191984d0710101c0107040c151412100d407040307010760307100d0107802c0180200011321000e08130421030702c01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 385114442 1250 385113192 385113199
    0x7060804121707030c02010f06140105030c0403080f04060e040e032208030a020c210606060c010f05010b0d06050103050f01030b04050a06112106010f110709060801050603060618060618 81
    0x307501d01003c0c040c2c0a094007995803c010742c44c0400b145210000343c400c51080d00c0d03062029031110032004c401140d060700b0160040c0d9030300070100000070002d81c22500230020080f54000ca01e848a103000c3c0c015000d148040c440d6070186040c0221011030032400f0013100c0c0045440c0c1903210141e40c2214001d800c0d8070b0309400050143c40002442500310380c000401086118040300c80e0014115028841140b113a80140b190b040b84d07011402244651800380c0183c9030901d800b0303000007140381da800d07801020340b0400e0340180000d250008200e8114641d0340a41307400340c0820308090201d403d1040c5400301e00041440081c0c440c541c0710001c030f41003200a01145103800d4220307509200d40904882d41003601e03400403481040621280110340808000d600400e445180142c440075942c5600040503141e05883c1040300903180100320001c10241c50611960025001480000030b5924004046c03619015000e400c40b17106100c241da508408140d920980c5030700203000d50705652507102e0b02e8000021405806225980b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 385115692 1250 385114442 385114487
    0x10305090106080f0a02040510180b01170708040c06142505030f0c01060f05010c0605090c0a170d020a0f1518050105040c051914060d06080304170706080412 69
    0xa1032100081291714280211000c20090701d400304030311480441446003480e0501d4101d5817010b11411a8011550a1010b041200404507040c4485910500c00c448003070103e030074107007031000384480d0020070340181203d400c0041c410150710b8a0071302d1900410349040b5118900c0d504c4a8485030302c412510302c88130b500c04100d030340321401441e00c010290024244c206a030340c81c1120005020100070601400c07102d0684401420340c0c1e072500c410700a098000c245064521800820400c9a11107000350030003044017a80300c6895460f409100c03401c0c14050740c155011580000f0150b40403501c0329003540142075010100b140007141034200307035002e4140a000b03451990650344410081c46019000288594031a2200f209410303107843c2000010401d007000c05103000d02081060280000d282e118480700d52000b042c041c140404100039406490083d04807411b04d41000c9820050240008507064080544d81d0141c0540c5007070050080242d10300400c0a41000d03180c40100c0e2043e409400c5440104441c0d040389003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 385116942 1250 385115692 385115713
    0x20a0c020f13021204030f03020918062e0215040b0105090a06050a0b0405030d020d0e060c030705060a151203211b1d010504030203150403140c060f180c01030509010608 74
    0x44541c002154241c0c040341c1c0c51002c40032600d202707100302da059000060041c80004040302103c940031400424540c1c118a2a59030f010501e0450300009400c8488480409050100f1540c0203003060745041c01d4403851900041800002032072076200c1e0f07044d01d5003510180082d1351280d035200e0180c030b001d61109400007003100c004200d1109220003482a5241502150305074000c140013241d507110164009000107d0366008501d962034044010b141d03040950341202e082c40e03015210b05003068419101c14001c2551400001c1540e505826101d00400109004602c0b0000360344001e0400c0703d034803134fd041b11002c12442140b2030305240d51004820242c031880300f4080d9481150040e0140300940c006940042d9650610725081d0b00ca081110305036540900a009980340c003602c095100c0001600c2141801505c80a1400e132081402c06014902c0c1e43c103004040904002c041444a050064412542c202c5425850084004c000038280c40391131080c6400905941c85a451500420280e00150070f079025203103410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 385118192 1250 385116942 385116967
    0x30a0f0507050405011e031b0504150e0601080103050613170d0504060501050f06040b09010c080f0a120b0108041b050a0803030f010b090d06020d02070204090812070201020a0c020f1302 81
    0x4402c0e150103440402c4142d88420403022000030103003001000000140342031001a6501941d0b440c04140350031140c803a180c40d00000f4040c2c500e240003070180007244e054100150740340103d42540140c1c0a0030003007210350446e1101c41d187e05008040703180c8403410000c52400c1181b040800041c505000c0451501c8150602e60300d8040c003000d45050342d03da0b08040000c24249001c005014442d50003c14091810f1724043e5400c1c8103400142c201410320580118039008146004018800c0203080801c69507141050300c00588003035071400900e0086803405c0042a42d59030850701d1a42c03c15005180f0320701e070b04015420485200f845030015034020200c034200064240002000c0d50040c3c084414045c40d6030703255940029203024405207a54080c0031607811001083e80c1e81e0050038541f541c0400036160060503000b04040d1500c481049502900c002411060302c8507002903160803c010784025072030328880e00d00090603650041c00c007902c21811a802c00b00c013075451104000000c03c4584056440c3c1540b0202c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 385119442 1250 385118192 385118203
    0xf05010504060e010629040902030c041a1c05130816030e0d05150a1808040608060f0307060f020c0306090703050d020303070f05030a0f0515040612080706020306030a0f05 75
    0x881d001400d111008400c3c00042c02404256078072401428261160484417950300150014480e4040b101040003090f07624a0380002c6229a0031b540c810f680d941d15180381c003800c58004002110000400b1b2203614041003140452006641440c4404a030710746a00340d155000016140004000490002d102649541c50000c100700301400f0707403500310440318400148441d803204040001e0207608034a25094404485154254000f0400d070750000c4c48001c44480000120701618042d1030740c20b004141001003540c4181c0710f070381c03040741a2096020040000c01280e5a113082d0f0140006000136005c209409600c2006056250320000b1704036429410603180507500d980035800160b5075406451701c0303c81218000000c4a009068658808250b45101041110320381c202404461149072288151040c2070003500826000ba038248502c2081d100650080104590041c0d00008440d1390038410440410b4034002a640e2640d040040035030360b5a510b00000341481845a001411805030104220600200046 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 385120692 1250 385119442 385119451
    0x1215050414011503080a05030919080322020d0602090d1e02010311030f1605091e04050907050306040206180a08030304020f01080402031905010e100222030816020d0f050105 76
    0x3080010305043d42110b40d410107001c050a503040404c25000e03018131031001568010a0703075080d40c03031042c0b10260f030084c0c030010038506494020010062000500500c0c24008041d090740036101c60845803603000c40c161010407200901880d502181c0400c164030b80c0380390900400d512004d200d030380d100500811031042c41c070701c103050703000901e0042d04140580c80703441180d00611090000c40b00555401000600c0311003e140c2c00010000148960340840d10303101640c100d245596180c0447c0c00e5146001e01045400007000c101c055405000c0c108800d40300400c030260040c1d01641c0c803954440d02c14071481c03050300001080d10741143c0340c00b500081d0090080048d5014078800c40f4110741030721042c1d004407040e0340d0a85001c2d5064202030504583d100303025000c013404134030407400420341755100008036040c0420200d02d0011190009211582110b021103200c90305082200400c0d565411034890b190300c0d004800f11100b0800e002027180c0c0079540e8080500d0083c55004442407010b148a01d02036018040039034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 385121942 1250 385120692 385120733
    0x30d020d0b03010b13020706060302130b0123181c0803011e0b09120c06030a1406041109010f0c050102181f020303130303231f05010912150504 63
    0x20920007600e818010140004401001d1030014495507004000a5112480c212900340c0c1d598070010058030703a08035203000f40009000004488181000140c01c01110f075024814840d503903c1d0840350030241400f80c03034a01011034141000c0384a09070204d504505290440f504c0c038400540e4a9040080310402507040c0c41300c4c0c0c0d04031000309490420505500d1001c0c003440d91282001d00191059040a102a035014036080c0204c0752006206008a100ea50040e1900c035440ca40703848208104410380f01e0306c1e43e00008103803820030540101c401c4064140c025154158100880c2c1c140031000d0611400c1000b20058014008550360b40c1140c10000306008001d1805004038042c1d5a600c0c4030840110092600000c0b5402540c5155504070880707501c4203400c40b00b03c060568407140b040010000c1c10350f0101110304140c2c40503441c1030505042001500107194491100300c01802800143d0703204589d10220345200702c070915000f0390780c505100441e040c1803c0000c2c0600e020100820300c40080d400100741c00991 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 385123192 1250 385121942 385121951
    0x312040b3913050a0e011a0304020303040302092205060a1107052e0e01020d05011706011a0c070305072d030305070213020d0b1005131206110a0c03020106050f030c130e030d020d 78
    0x10600102340001c46000c1c0d8103400510081015050000d0311941c010071034620550300070000d0340c1d03000c0c3c600c402c0b5006640c0740c1c1c00281080704814191003507408030b20307800070f06608141c201e681d41c65440b0300322509040c451260f001c982c0b0369001181054405c0583d10320060195807160001c0358000d410044000c4001e508107000050500c1e4074048060080da82d04002e440760740c2c00c01c1d5030184c050680c0480e07501c200004014040b40d107141801070b800030b1840340015080c4a40303000305499003440d0a8001d20309180070f25162040e07207003404180e4021641d06007071060b02d400711400083d0307180f403620211140c0b080c0001460f5201410540c80164040350860780c0c2c05446d244031078100e455002e80f850410f62004824022701100c4414004108600c2c415030300416201c0301d03600e54418540011400d1404070b40104c1c1c801c0704140d020b01906001d000281d03000c1c80041061800240c0c3c80b1040b0001500480801409a103075031078075000060100061400c0701e90718599500342d00029400b0a81a03014140360 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 385124442 1250 385123192 385123229
    0x20306010e0103020120030f04030602040f0608060d0f110a1508070311040b0d2a030e0c0a05040207050a0c180f050105031c020312040b3913050a0e01 66
    0x34480d007a060b2a010795462200000200b00002107a10182c403105185c8014804652a403000c10014001f80d07203d00c0c405030325103140c10130510041c0c40a40141050141c084101b10355622054003c3c490360f904a5004402c00e8031501707102191151414540da001490b4100c0410700c070110700b12940c1c08800550762035401d9610b1103c01c03030072160111081401c0314030802080040501540151021225083c0300043c03031003020121304078101000e031350b02801c0b0b000703441d0006019030544101c0e11110364003400303042800800000180680103034004e140c0f0a03a400700c1d040c024410208240e00100394800311510040d03485088808a05d43d401740381d446c6550034802d0445178403a0038002da40c1281c00240092406c6034840d0700c4560f00444c8041c0380b1045101c148034000f06c400c001c47c1400d000305d005480c0b148050800c2e041ea800c51240904040d91006164040301e00304002048407052188004503d08bd15022481e00c4010454a242c3c0201c4d48071101c039102060a254140035075040340c01a07900581c05100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 385125692 1250 385124442 385124459
    0x60b030d081603091b0608070212090f150c070b18030a0f030c0f05071412030306360c0d0507020d08011806080a030c021002120409020d230402030601 66
    0x103044030045000300020b035558009038002e801c00a440742c400c0c1049208441502d240c1032221005500060008560703409008241d901803100b4022030890708502031800c02400007240740410300c1c2070018020081544c026140c000d02d40140e410000c0713440c06542c00b0300d07955a001c60442e00400001c03111160301e4400d2560603c0c00003084910560b03c084040300100341303514280c5085520b403806840d103840c010705c2003000a0b8184280e002900b0740d40c0001140480800c141b140c10f0302e11001c2840c20b948100184201175444800e00b02c3c1c1c95000c4184882240b0041903494400390561b034020490f00200c00c248660180301c0c10150070643c5440c04100010b80c2c07140c0040342c0c1e9004003010707540440c007a100140400b075000c0320f00e801d54250282c400b19a2030350368405107203400c806910603000641c2502c044011441d060311421820140b034401070000000d0004294210300c90b078807450a50b180d00040c4403443c020280c120000d851026413108020f2800d00d007012113610421207040b8440d00840c00082610003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 385126942 1250 385125692 385125707
    0xa020f101d1c11012c060904090b010905041a0f0a050702010b0d0804170102031e0402211606030b01050f1e07030c0b011a0f090406030213020a03060504050127020904050103060b030d 80
    0x90200191402160300e000c148100350f0320500e031f80360700142c131020b4050100d8544404179008000a1400184500d450304041e10030303001000064101c0328946c414044610ba42042e0b40741c02800c00e9000040c251540d14003070b4018802e009000760072403c01d08250041c061460094012166004401d120454010941034202e110480303490402807008900420030b0001146459030240c03000e01030706102d213182e0750019118012251401403d42c001040c003c9031001c0d1801c864002c0100781424004030140c90006409070041030041c81400a020902040e03005100680781c50b503c080340c50b03e642e2191203060042250061001c06c1d01c40d00c0756500002860010103031400e000c148401d0b2035905050386540c03804202e41c4051201540a900d0304404009a07079210003203141c02522400041c0d8501c0340200240a503001c80d486075104500d02070040145079012512910b030101100c01c072884181984000300d00034065044050b0300301b8030701400442001659804210881800c504840840f0b034410b20403542c14 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 385128192 1250 385126942 385126997
    0xe0a081b0108060a080703120c02030115090c170106050706110c0105070f080112020108090a020301290a03080d020a050409060f031536060203090a020f101d1c1101 72
    0x1588004d07001c00c0410b0741d400502300c29041e0351038400001101c51700000d0964050044001c4850b50400003041240c80e140302d141810b1150b400c00628184845c100100614014892241401030000e801400c111044d488500f042c0c104080342e54481c0c002c600214000c03c81207032460082455010010602409141510304a448043c0e20140c9552940c0c01100c0d92070026140c4103c900c80c0c1e110100c010399081c003450a08400125480681140740280c544d40c414561214034040c0400f40402c6c804200010104c03109010b80f070002580d0740700313600c904403510320803940520041842d102c004602c0c41e034200c441c441142d00408040340700c2c031080a051021901186240d0100071001c410005408003a1555071403143d00c20010302400c61500d80b160300907640b084840c0d9039543c10125805007189001d851908512a0a80708190240c0050101911507980e0740d000101c4040c0c02140d01c000c507980e03141d1800800f8010110040c6210140c502000c0c2c000e500446540482c64241109111150108002d05003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 385129442 1250 385128192 385128209
    0x501020610080d140c24010506070b011a090d050304032009060d06061802031906081018170c0606040b0105041a07080f0703020607030b09070e0a081b0108060a 70
    0x940565000e6804d00e040c50312038500c02c4ea050215640c0f0910178090031a080a050415108a40d007080744c04280381016004144510f9042c8681c90104a440241e2410f49004000c40d09003410000f00001c03142c018583c5050f4440c3d0500201010020080084c108076417142405404001c0d02c080d030000002070180041350400081c0300010b415141007210280315034021107000400c2900d40d400a1b007407140c00d203201030348943c0000038040c030848803c00742c5401e4040c00301d00300209410682003507115800c0012400ca405c0c2c88200580303514031880807034030026a0010740c62500b4400c0000168550b04a03e2145205006850000d65181854066140000c0050b52513504c0c043c00c0c41a40c000203544d10509641c204003c0c0408000504035600801c00484400c03120781d2510000d24000740350000003000401014140070220301a0703241c0384001a0400c1e01c5081c0542c0c0c68041101041e20001c0507840b0380c820b8415250103800040d481d6000385182c1500781c1c0e400f10705640f54030600840e00214400e080c2c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 385130692 1250 385129442 385129453
    0xf070c02100c05011a1306050907120b10030504120305070818030d0203040c150c1e060209130b04060602150106050a021f0501181b08090307020405040c050102061008 73
    0x1407501c0c081e024080d0100782041c0161616549482e421a440d41c0045403c00410303a4000c0c815280884c1000c0403444800003d0142c03e0820000c1241c1c80009003032802842600d4003c038051614a130070241e10b0308030180880400d000d01e000020080c100681e4191100f600d1000070540702842409454428a9940c880c01115200d25800800c41d002402d0300c4003444c0002c1c000340300c02e0139590000314042c0c0c2c010107981c0c001c1410195180311f207058003801c040501003000c40c18030020300708846a9000180c1044144030590340307400e00402a200f54880c155011880c1c6042c10199169603018881184003034804000054984005a0b62880100100c10101c0440001003003258440d000400d20240d0a1060726030040070300e0500032201522202d5441741c10f84942c0148803140b40450043c0200710400c6081c004040441e07140d10780c5902c50301c0c00c403040040104c00a100d10100300103e611641c1d020b0030810644c0740c40d09203400c5050f4607004150040c0243e1011440580320040044140c510b200c01a00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 385131942 1250 385130692 385130717
    0xe1e04030f02030c061008070e0f0426030a150504090b0402060306010207030b010b030a0c0504140d02190b130603020705100c12020403150e0102191209020916080f07 73
    0x7240403001c0c501c50800c42c4404c025a410f2040144401d6004580c0d5060700c10126080000e2a4280b61494010040b820ba41000300301001c80c2201c51290000d0304103221101002c0b072070603504207085c481119100303480d1001042c032804021980c416050301c51801284401039032a2400c00058581d5200d01a0500d00000c01080c00b620748170000316040841401125030240da2a80c031f504081c1c20907130081c400701030301204000c0c3c8803045000e01c0780651070b81e1030030500e41402c003000105c070f0124424005002d503513000004000c6444e06011281842c1112501e180b01c1566810900141d500000f500010010f110310f0001e1520700034000d481c40558000e002e800e61842038401c40000741020a0150b04105003044d03240d281038400e1008201650140c1e03010f548000c40326181c0c2d02502c5c01e04420750343c07980c0b0412400c88864010b00e1a007001d03034a00e22b4a078030503c0c6694030301e41c05030012013000380d400030b121405d020707040300540008a40d81d03280c0d80b40d414040e920091140c244a81c100e98a1300841c20001034072 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 385133192 1250 385131942 385131947
    0x171906050f030d0813120c0501050a0b0a0303031a04060801090201021204030b01121e111f1e020304090f061a040b1206030f07140102100905190213020d060e1e0403 72
    0xc65011805d00f58101c00d90130a9100d0020301e0a17800c2144002c100031040410901100380606035002020940034800f104400020410051051001a04245e80c0c2c0c244030300c0a5600080602240310014400c4c0185a25545240c0c02001d00307140490141c86109041042002c58109540489410841440c1c881e882d29a03801003480f100502154060103800c2030880d441802403041c09064026602856441c101d8024004401c080040f00001c4034003010118400e2a48100f4000d0711030700301101c00c01d600c00d071742106902d107000b40e030000c03089130341407503601e803412007003a400141102d010312030307500a9072000000704c030003480b56010314a49010108170424072910384000036074000f2406000c4541061ba01d50500d414142c1c00d4001550450a5001c1305040e503030304001e00e0160031000ca404000c04450740d134920b03948001d200348414403510340c800b60ba0150340d9810300030040d800c038202c815951000c080418000810703882c003a4000b140e4403000480c8082242011750128014103810300e61280c6c4450324107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 385134442 1250 385133192 385133207
    0xe060306061017041a0612120a02070f080607171902090d230c27070c0203102c06070c21120b060313030f171906050f030d 54
    0x3038003e20064050041c900326041030254407560042d2489001464110740401c080c0c03c02804051003200c2400c1010322086001c2115070031101c40d401455910150b4080590078151983d018450b05d580d4102c6c00142c2d040e002c5441442003040360356000260740c0c644041030b2003820a540016584182c030400e2184843c031640200400500180156070291943d50b4000721905900c1d01061103101c1143c4a00780031804111000190400321081900c40d044030b074126440640301e009114031003018a020803020b41c0166030128034250080d090355012202891050050b02d69a2000a9901c3c1840310a048281440c00c140b22064040070240c0103e480300c060455442a05000035101c1302d03186120b003a00c030030501003010540700783c684541c00020140601501203038440703071500e400f80408008220100348103080301c5d0202503260070a203c44010742d41c401c8821215401e00d400009000d08140407404042480010100209440030b002c416202d0f003c1c40403900808440a1305984242e880a0f10903000318003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 385135692 1250 385134442 385134469
    0xc0f030302130e070e01020c040c120b1c05060103030e100c08030612010c030603230d0503090307060507091e0e060d02041b0314160c061a040e10060e06030606 70
    0x400b100340d41e00c8031840c01100c0c01c240d84090100701c003505a22075558062056480203d004c070341c10450003503ea0805411501c0d41e1a00810895a5003038149250396a4901c0030900c40b8003058100880342c00c0c1c90700e980d484030203005c00e83c0441c40d9154403420601e0080302560203410955113a1034010450b58502d6060b401c0a002103500c0a0071904000c45880244900004004507550210340b5601e9400c200c003425000708003182121614650341c92008400080036003d94a2a1400b80e50741e42d140100c141c114060910010085800d1600717210119504c25413481c1941c000b080c1d0310501032681084124012064803a030000041c2d9000000e0541c5803100f0a0b0301c03618001b84c000b14480c003240596448240522a020010036aa00b02c0c60700d01b00c03c1203141e240d01180704141c0c520f8115602c2c0000d8105580d00d0300c003c101e5602d9902815185004034601810100040c209000e01298801410b40b217240d846610f00156250480004118500c3c0c400280198001303405840740e522540f00348010346c1c80208 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 385136942 1250 385135692 385135717
    0x319030e06090d1b110f010c0c031b05010201090f061508030c0616020304080a02130f0c120e0a0b01050d0320012007030807110f07080c09070c0f030302 67
    0x400d40510a5018400c0a114000c51030141c22110351140380642182e0a40c1500101e905000c50a4070004002030700d43c0401050880d0703003444c1c40e103401c8012034080410380700041c1030f8103110074000200162282c641d0700841c5150300704640300d520b94004908941e001c4901411000b041c1d115803000c94955400233901600b0a90303614161620b6003080c9195034424000f42c40964425403c02030700d6488140d02420101842c8080c503d00f514008105070386000020000e03200c0d000c0c000c1180303911891030303008003500b0321040300900c11100307003d602070070f10314001210490503800d00010028240c001b0903500a959405103a00550340d08107170501031100c11b004011024840d151000040310303940706a560040b14a500004944410214002c04040702901c5403041c0b07d41c010300c02880000d0300803082d0780d404442440e00316083c0400d84101c03450620000031762481da01034a040800c0d081000b15154014444c295240e02c890b8481c4041290400c402e540c01410780302e42451140c0000344a50000c00c034511610 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 385138192 1250 385136942 385136951
    0x11b020618130e030405030d0507051203070513030503030901050f1e1e270d0503150a150504030611040e0103031d090c03040201030c080606040b1b190c080601050102031903 76
    0x50011104880502d00f01c0c1d01d840d4804a0100044e250810850f01c80ea8114035100741000c1503940d0f2a540c404210441440191300400001c2c03005201d40c095404c1c98083c407084030100c40e6241499a10f903802502d101c40340b5400e080014000414541851780128802c001c1e08180754449440c11141d09405000b904024859100300303240c0c4a0000e1440740502010644420f2000c0898001800d924100000012a80020076030481c41c94012050780d0340880c3e5404540027080413a80081c610030034581209100b60b03d01520b49105943c858041d20641e1312a4104021881300100801c8441c012031080d0740c00b9507003010050000070302c9a1500450207242c500040010002e0070000f850503d0116400310701c901001c81003000b9983c1c14092500b140e0083d0034540003d040c1200460400c0c49280218041490001000f8207441640c1301c8810009074140255040d440c41464490700711071a810060f20041c0c851200492031490214805040700c1c0140c0055191198428600d2030314001c0004100a05555 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 385139442 1250 385138192 385138219
    0x21c0f030e1f0c0f1803030c050a060f06150903080403030509060f030703090b0a0b0a14120f010f110406050304020d06060305060a0f0c0908030306130b03100b011b020618 75
    0x100b008203400c0454040d804128180f03c900c0050200d281c00220070208205051000642680c81241c403081d0307509464200c044010b6400c1640c500301c1d48600041c03100c0d250a00724181981194019026182500c81021510080110443d2a01c0003400090300c2410100070800c0041d00402c02052403d50252065003807200c44295461a900201e5111001ca0380783d41c40700082003100e0b9082503024244800401c40594000c02065074107841d40100c2b07902015040070320b1101c2d56000c00d162140388019040b500ea0103214601c050203085285140500d040c1840c05c010701c45080c4401ba507003610720a50f035217829a6102d400304034003040702041c107030340c3e044c3c0c2ca01010011403001c0c411580b017006080c10102d260038015182d48100c40007881e087c8200030003910203005415010048941216045585031090001403240b5002024050340c8190325115244018216824641012044000036250810035003610002c0d122138107501200207500003410000400e55103032806d00c3c0940710901030150891a00b4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 385140692 1250 385139442 385139473
    0x9090309090a15210b010e160e01030e0703050c0f15030a05040c0b040303030b18132a240203090d081608030a0209030c061602010503070309020310020703021c0f030e 73
    0x51040d4080440302c0441c145810700c80c05005146c014025012500c3c120310f05001801c4c09200310b0340d51541000480180e80400768820380220810001c03040070348090980da0f1810b190380394902c01000f8011402d00391504641e1625510040000c022200420729550f200c3c8601c1c4001c00004004070707031980c4290404102000c003000500040d52190310f001641c0b600c89006c0004088554600c000080c43c41801c019080d011542a840e0381031b401a10658030440c1101c00a2082e26507075607020a440f9007010000d034040d010b4100301200c0801c0c8055804030424002c1c22a180d1041d080c40581004038070403494000b0b1010b0740100401d03419025400341c21242652010f40590040e114050150b40200350480d0a140078429070319850012507105103807000940d04241e8a400b0720101a041c04008400200002d019030000d1004541c02400d46540c2e00001a00e4402034100402c1540103128000d03800c13001198410940d902c0000d15151110303160060f0408501403d2048000c000d44d00032040280d01c500b5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 385141942 1250 385140692 385140719
    0x1170a05030d0e0c1e06090103090501090803160c0201200f010501060f090902400b030708070206040b0402130e01060803040806090a080405090703060b031509090309090a15 76
    0xb105140418103a14118440e0302c1e146010b80400d10881401c103128201003808180c2c4045814203071480b50711880110300503030003440c4600c0060003550070605403000700402134008500c101d502e00c0280c00b4000c1d000d0b00484509103000070003408a0340ea0304000707044503403c131070003000400001d0842c0c160b841d00ca0609400c0d1030081e0300503400300d8800010045d480380c0040b44240540105201141010300500c849400c254108911180d23442c0c0307281704c0f40295410000380c1101c2c03980e02190b560043c2d80d60440d0310f0403548205e17529400034030050f0100e40035600c0428040d008541081c41507003039440345e400304043d100c0032440f840440b590350001030055800a00646008000700c0c1d029584580c1b9045515040100040c2821030b2a0800201000003d0500d8140d41c2921002e46000303507a59074110094008001030b400402004401100700702c1e030207010088144040000751400480c0751264041c60383e4034010610070307641c000c4200e00098031400c03007030303000910108017560fa11500039552a8008800c2c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 385143192 1250 385141942 385141957
    0x10b0f1c0e010b09010803180603060102070f030312050a02040302180907150c050f07050604140d17090a080f0c0d0c0e090a050613030e011b0c0b1209031201170a0503 73
    0xa0f5100e00311101c052801030301e0b040c01410250065860040c844c1e100c802a4015103070703880d214a0f0040f010a130140d2081108001902c0540c1c0154502e948030b04014007003005440f182803002d41002c00103140c543c218000d88080b20350140c035145910400403004209003d000f00710101511500000040d801c000028403001d00340385031203241d0308900b181071040c00c0025404d01d841040d4401e0030100502e41342c003011102103a450107866440c0e0134040303000a1315401803403005452a4120740b40c0c1411460042c0042c0001802190020305e4140c0c1c501005854035040344107030b10180c1100706602103508003a1346070080981310b001404c01c030307036220755641010403402c2d5500c140a03031018ac011020881c0401a80f508082e00000c40007442d407040d41c00419020341d03c00640d04000c070f0002d60684808150100c0560380b50f222031001c52964a503c0c61502e5900311000e01d104c0c0007110000b05000e883c0200440d6414214070404148a82c01c0c6528180c2038814070f00e62044c0d61040c2650351000c0b5409002800d0355 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 385144442 1250 385143192 385143221
    0xa0302090703093c050606092806080d02010b0a2d14180603030403060c05091f09050a0f03060b060c0d0507020907022b12090b091203010b0f1c 63
    0x4041c1c8421071301044000d5090506200008041e1440880d00c0012455031021003181c104649586900c0f02d80c1134400600042c20080c48000c042031a03100e80e0341c020005941d442c00459103081d003804012826182c245503040c0e00011351407000d1140384601513503e0101c04142d49844a00d01e45260b101d00181580d52018070004410006a00c1604c1e28004202034038054025140349420b1504c0000e8480c41248401007030107540c2c0030260489801035040e6040b10310001c20301006460390b040000c1c148040c00701c400e00010060000840c1c11f25202c100c85082c0c1340b40340310110b001419640c810000717090300119698404818080f01840030b604010303c070540b040a94495464649600c1844140c540241c1083d007950000e4803085042e000008800301c11211760700c51032241500c110760540c1d070040300101c0501c900381011040e0040c8030312401010700404c80307502150380c441d8054640c003610f8017080c000e04001d1074040200c0882c0100440190003a901080c0c0c040340120902c14480c4112100641518023 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 385145692 1250 385144442 385144493
    0x200f060f010509090d0915110d021608071404020d15090b041415191a22030f170d0204091e021305010c050309150d06060203090a030209070309 63
    0x10324107080c0c2c0f07059008082c040042290444071500500b0b03055103809213000c000c1e0580d54034100c0c548100d484110000402c4d09848501050700002501d41c3c003201c04000c0355042820300001c103550700290321012500c0300711968281141c0441004043d521820301c00018644030f450103c0d0f03900c40280e042004111540740007603c26011400e00c000e4800c2e4880d400007049910041000003a958201c28406941c1140d07510f400d200030204a60031b8011680181c07580700c10240480005544480c010a82060f000c0c1d1400e5a9145517149119494203034000104102010f5120348001000d007100700c50141c4c0c0c2c0c22445814000c203100c01c08126002a40080a041e849001100007100c03032140c002504d004030034040d840c2c052840c01c240c2c0224080c0c440e950402c9804c107070040a005c0281700b5203050880040800c503020100010300c0c107040c3c000059040c0058900305001400c140000b08450301e4500103004055407500e07640030000d158800a0080007490749440360b40c4009040d003980c0c0ca10074040080c000d903 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 385146942 1250 385145692 385145699
    0x50a120327020f0102030301050a0620032a15070309140708010c0201060806010308040501051c09081b01060b03060d060b1804030f0e0108040605130609030503010f050d020603060906031207030e0f01050307200f060f01 95
    0x400d1003ba00c0c0300b40b1308e50010b050000f030100e00000d425501c2112800e001c21008128038024842290020300080b0380c2c01044c5010622510641007241340000560003404501c0d110000c1c03540700d4a00f0b22005000700c0040100300603c3d40258007038942d02450044041581c02c9110802082e100300040c03c440820300010302d2081c01c07411418441851901a008009070380c00c1400000c520302c4013504261086001c280024100700c01604814445a4094401190005003404110b10840240c60443c04900002c854102c42d0b4400c90303643e103201d6416513400309540c03116110030009000203000e10003415081c01548010450902511a40070310a6460701e0360b07585040320031303a04440d080d0400d40c450415200f2103005651680c040c0c9401020403140040d50b51110740c0080d00d00084560b0011035100042140c03070901d90000202035008200b030799101d0381c048024004451301e10007140c0c0c83e001f04c0c2c1c40740303007628810004502110364029188205c801001690220a20303045085408091105482d001403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 385148192 1250 385146942 385146997
    0x50a14120a1e150e0601090b040e240609090604060207030c050d0c03090f1d070207210605010509090607080c0d02040306020c0106060c050a120327020f0102030301050a062003 77
    0x12071640c0000074200803240035007804ca900ca0718103209644030b1540301d0130510f050341e07580d900036200c4104280403200d41c03080d01000c00d985030030080c000400c00082000010f40c1d9052903800c09100d04002e201070040340c0d68940e101c0b802034000000580c2008400d8401a0014604004c0f000c0c14100035180c04032504070919000b07061201c0c5401c40d10b000100000c0402011101c0c0c11800c405018400b00c0015a80d94107604910303103c01903100c00e81d0841e00e208410190110034400c2000c003030044a060000e83c1c0c0390010f21000d00e80c181d6582c0720550100c4000b41210740f00300d10ba81d4208810b2002030349004407002c107800c1030341c20980013580c0303141c0d00080040300c20009200e801d004103800c1c1400400c403121602c800e80c40d0508044003801030f00c0b40ca01c1200b0300d42d22a500004803010850249006e1a100d60030708550400e00030b4040f80910281101411507600000550b81240e0005040301e5046080c2201110055400b40e448a007110b85ca407620141d4100510192812145840440e424200c2e40c4042 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 385149442 1250 385148192 385148213
    0x9040321020d0902130c020a0609052506110c010903110d081803011a2805180601030b1206180f0604240203011503050c160803060a050a14120a1e 64
    0xb034540c03461b02c0b041d1030b03903c3c1d00403d41d4407d0581002c2c00055883c031505103182041d0541c2540e02c2041e90700ca61f295258070a010500e0180c0c0c1640c3e41310715110507002c45050b582c0144d40c040c140400c0c02510204005403408860003102c0740080c11003040c0044590711501d140d004408903602250706110888881e007424030481c580b1003041c0b0586001070340d059020402450351400001a2440340c1d003043d407612012405010000c080180107800880c44500d6030803440c81055801e180043e0074113818021928150701304042c0d0380660000707040c1c651107103040e00f60100340805e40785205003d8024405c400040c1840b00b01c0c0302e50b004010380c026211040808076480c001000e2000c011520500040c090360020030782c14842214507090005440c3c8501d402c0c40241e0140f0204903c4841284964804101c0c400000c1e41c02050155102e408041c1c544040082c803070142d00442060350300501c041e410038900f4240481c181c0d00310f0415180c0b046026220b255401140c0e04100310040c01e094007007020003508590 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 385150692 1250 385149442 385149469
    0xa030504090c3908070507170d1d010917010603020312070c09110c010504030908010f06060c06020f07020d060e0615010e2e090f050307030209040321020d0902 70
    0x100250202240c8062003020444903201c02040104503d00300040b100c000c41148000340c009407410349030314180c640f03650340380b4460081441400140704c08180f40c150009150510342e100f0f8580f40005c6c3d1580f070007070b070040840a20ba0f40c10003d0310b200005104d0a001c844004440022001049007802c3d4014149445e6100000700100d0000b00004c401181007917038503005031141003c002c200d02034407064000050284106001c407a5180c08184010560404440021280500000c1c03068410038220ba6040360440d01c5503101240c0c1600301940042e1840e8020009840314140640c107150302900860352030340c06050101e9032035507203a40f120382004007040903c1e071203c0f0b103841c8035404000c8440002c180e99620002c1c640614454015042c100103c1f00421901c483d00000480c00c02c19028001010814140318407422401c0444011609040210340e107801d40f80c0140050201d511603550441c3d40718128840c000d480c4082402c1021041c80c1d50008000c100852030020554007042e004000c1e24a2180c10f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 385151942 1250 385150692 385150697
    0x30f0b27010537051302030a0b0604080d030513120f17010b0712120f0b0f060f1603030204080604030c11100f030c020106050916020f010c0e0607080c0a030504090c 72
    0x107940001d5000944090b030000682240d80c40101c00407446540100e100940000e0340c841c5c16500c4107a0900d03420303400b40d8400c1007114014010f00d60324205021051140d8007070701d00c264110362100d00405000e40c1005400a80c03d90808040701e045c2c0d00d68a00810442d0140000603807000850030030294040411403564041103824103031545071003810141c6200f1910004c10248001014988080c003440c1440003298860009004100a040140004000d0900c085105050209c1009c0490801c1c40c181c840641c80318002c64581041e4030b071340141000050800710100340e002c20010504040900425005a20a4071380070100519860300d809030302c10f1124107034000c00c0c0204111440c05d43c041c03010224416541000110501c410307008078054100e41e0042a04000502e05004d002c001500d40401c4841040e401c0c1e0380032149240700c081c284c1e0002548400080c5004407201c409280501c01001c90034803450503240f500c13100e290041d04241c52104207402095001c641040b41034141d0051258201003407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 385153192 1250 385151942 385151959
    0x12601110702040b010c0b011e060c350f04050a0b090f130b0301060e0a0e15010e0c040320030c0109050315090712050c100c05030a030f0b270105 64
    0x3155146806207490181c0f02e5901e400c0c0030000307a40115000041c0f41e0b00401c8404140da107800c081c209004100020f000b0600000b840040c441d4486d049078846250b2010a002030a0214035211014268004078420541005030a07803007207012802c0140282c03085149220b4440741743c1000c000c81d003e402c0d401103904980170030005441d6611048400441001100d9104078001c01d03075031400081950052050b055840c107107020410888995117075200310070740c0c60288000c0e002840c0003500c03441618007140030b8a01c031000610020100d035000c01d901042049560f401e140e40d0b41c6410030036034501a503074201030b80402207003055406d081c070003030345102805c0c20300316541450080482c2d075810390014000c800e42a440c000c113008042c180b1040340240031184a01c611b50b0f01e241441d43d100c040d80c10040e44585143d00501900e03a0003044120000c68021014500f44410003030241c0280c004142091a103c0e079900340402c00d5510070303644650300100d00e80d4115510b8a120640a410501a04924401d500d030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 385154442 1250 385153192 385153211
    0x406140613050703110703050c010b0d0b010311030a06061401081f0509060a0b04182301030318081606020609150c0c070306111206040938012601 64
    0x20307070303800720303882488040002159a5180b000320018205410700a803400d100140600906030b0103405000d150081700020420715100c481004030b9030b40e004100901c0c91200e0b40c01080418040500030142e0325024054a00449140da51441201c410350400f410b841198202c2010035684003020640c004d160065000380440a012180c1c0000024802d10384907450325000610f86071641c1d04075100a00c6038510258556855002101c211221100d0480c1c00c2464214042013030040d81c803c0728064148881e080505900b55101281c80080000349030314040e00c5000c00144d000d004122141c011f440380032605640a041c18402410044003404059480e805650340c2c82800303112100e01600600c840c0f45c030729681e00d0010040e81c1041101d40c00a0015460202c054240d280020018504490f16011107000c941c0d0340c1080000700c610f42800134248a00c2400c2901112444400b941c10503150380c00790360607114034050108040039003600010650100311208548840302c1d01405100ba030b1405000340070402c81c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 385155692 1250 385154442 385154449
    0x170a08070c150c0b060409051f0501050118030f0f0305070c09020d140108071403150a1d01051303120905030313020306180303040623090d0e0105121302060f070b04061406 75
    0xd083e05100f995601f41300410000e040010f540e0050800580e2850b81204024500c01000300348665400b240e080d20001400e902418150800d0707980c031042d00000f1145a0303e800f0b2203000c100c2402c400348802004494046003840d49058014034650001503690700107401004255a15028410b11130444200188401c1c0c0010840c0c0050f9502500040130a01d103183c00680381419604c0b000c140907400c9024003810741c41981080803441503c4c007038040700050118980e800c89504440760311100c09200004800070388120b04110140202d07442c04126030790300743c0b1024115402a1800c4816002602c01902142420301000d58441c1c40840919880039010031090b0704d80c44000e1000701040c2d51016072503540b03a0383d407650603860021141e2038805441c0c901d16555960355010425004140c10481c0e03185250700c5101151040024028030040c81d032540c0014894009081c0b1089a1245045c0845032000c020400034000e41030007401c19444a08040c10b0840460342401c40e403010040400081110585 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 385156942 1250 385155692 385155713
    0x60a0609020f0d0506041d0a02030c010c12080603010e070909060b06030c0a0f02030714030c100605030a08160b1306060501032a030e030406020a060b06090307170a08070c150c 77
    0x40d0f038403800b04031aa69440040d0090510f18150324407170b00141164006840c000464000c0c070361083e030842d200c2e00b0700b940c01502e940740040b038011b0958078080111540740e88954010394000d04060008542d511000000c1030a00c007698002c0e5000c640d4840c5424280300309070083c4a0690800c0d82c0443c03541c285a5500700c02445a08100c005100b140208082080e02c00c2048443c01d58028496880d032689815030a40c80340d11140200c4500d100d21015070020403030900c02c920803114024020101c0a8050307440440c203400c1034180c3d0f0400d01000841d0004074040e030094601c648040140352441c41040c0c5090400c5403a640c01241c101450141e500020b0405a10100d0b84058030425400840d8061300d0201c020f000c085902ca1683c0c0004100064815000140d003200c2c00c0c4034920600507000d0078428050140640c10301107034180d00003401000082a8803201202c040b40001c00d5030340c0e880c1c45866810341544442400c45542c040c10350f0411444840c80c4807100024418038103403082d40d0300d84c0ca604c80e141e0b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 385158192 1250 385156942 385156957
    0xa150f1b03050306150c01091a0a060602071206060f0e07020708071401030209060d110c0c0d08070f0302160b040e16080a0c11060c07060e03071a06150c060a0609020f 73
    0x180c42c5460000c0203880c1c19400e03107046d140040000d2100075190b00d80340104e030f9036503e4050000d410440100d10020b000d4003611055500c594020060700d45001da16004050040000741c2d48150380d00b8022407000c000f01d07121400340400300051600d9040c00ca80091501c5102d034400111504000c6040c0308a1a410001e159668024a07000d61903040010020301b1900c00c0e200400181c5280900030420309991070007800c24148114196915114800e0070b00581000244000300a1902080314000090100312100c4002e03011f44121028007107801c0b48461000c65640001c40c1c003000204003042110802e1000640c4101c00300d200f0710419a801c003028060100181c00c404550341c455420500d0103220b4000c154400c0c2b03144d81151241d0810200d078003459404071000380c1d0403504101002c0d10083e07000084175a09640160080f0b1039048030048002c0d10080980700070703800300940805a100510003009000d8625602c4090040d606121030850200e601c02d50040341290300600c4804241884003082d540304 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 385159442 1250 385158192 385158199
    0x5042609060d061728060209060a02061008010e0319091205031210150e0f0a17060a1112100b0a05030901060602070b070212010209061c0f110304060b0a150f1b03050306 74
    0x103600031850900c6c06070081c100c00942080011035405441503000880c540076040b551740b61074508d501c40d6002801ea0355943e64a1301e09130700400070308102e4207a540503c1ea8600e090b00e40907003025252902034041401d56842a038560340042903d181c551245204140c2021540d07080c03080e076a28200f09401a140b6400c1803406011301c11030f00c01341c552070348142c1c3e414402c8010480b103001c0d034480311004481d0b420003034090402d00c43c03400010404081e81c4210510410050071346424854104c4136440311b0000200809180b08803d1000910051614041e00102d40d85481d060344034a007000c5c1c4035003110083d5110b18215440360000f00311424181e811181240c3d019a4480c15080400b401c0c980648154070300d480e000040004c20030b11003001c51100010035411904240500c164010140c000c1c0e030b40f036002c940302403581000403800240450384154440c04002e009003102c181d44442e0300c90066400c11080001c01da030070800c200010707805000d01c207204550740c1d481001c2400d1510300800310b00004021901 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 385160692 1250 385159442 385159513
    0xa0c050a17040c03061803110102040311061308060a0515010201051501030e15010b0702130605012c0d110103140c0304080310030503220905042609060d0617 69
    0x50145070040f0502841e002001401000700d0309580312005510500c0c1600016904100002c1c05a41030013102c040700d40003d40409003056480412a1907482506080c0c0c0140b00058009100101480b20320700c1045540c1d00010103150106541c50070090544007641164541000c0112021204032845040d450a180016600f062034003824609080c0c0030040c3c171a181c0100000841140c0b8400814125100707441020629030641c2ca29810b0702d40364040c55011503100a0780e01144000b0b68140340200d03410100e04e00d40c1c5002400414010219140240e5104100c80019000355826025030100b80c040038502f204945072074a0401c03403e00010340028406d040010110b16541c420210180c05140c1040903070f5941c4075490040c5002d920030304041c15180d10490320010300c030801c0b40b180c40d204030b800c81101c198000c60101c0c80c1540308880c11511280c0501400300000700c3d00c6280140ca2081409000010140d09180210000070030595a080c059801040400c00c50340020740340e690100e840c00c6041d0b5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 385161942 1250 385160692 385160701
    0x9040608190b0709050a142803110d02060a0809060903070f06150b030705070303111c0b01051e04081504020a0e04020609040c020616091518030506010b030a0c050a17 73
    0xd90079051540324031ba00143c00f40c0d001c140b2680094040d0000c07030007114060408401d01030034022074800c1002e11000074003c00c0b01040403500e40c5003841c1411400900c0301000c4003259000410760380140407c00001005503003008070b46c0004014403900000d103d0002d500300082540e40b10b19905103a2030003448152100c2006030800601c003400c0380500340310940035480e8038101754000c0480d0030030031042c2d002074100702049222507469421a4025a074156112200075005c40c0c607180a001030010342d41c1080010000c02116184050580111459582c0348942da103141c0200107240c06016034030402c000e1003010a002c0166030300640c90049405030880120320342e440d030000551724042d03000e15070703041400c2c81c0242d0412680860032a101300503460220309217001e400d500700e501c4d52060180000c940d4003c0041c0d8516402482650a00c4420050a20100e500c958803642803800c00c2c0c6c00909103190100038000300341402d00840954900a162041c100749845400822880e00c1c240b8024540d40b003540403a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 385163192 1250 385161942 385161947
    0x100203011a09040902090421090f09020c0f01020a0e01031406210f060a0923030f0d0b060c0a050709020f040302011209020d03020c0f060c060a0e030d1109040608190b07 74
    0x20182d80c00800446c020700c2e0504003115104145080458030100407040220924000d0b43c3c1c1c8016a400e001115500c0c60420109a0080d8844001d01d25180300c1c00340d001e4082c42c402d00040c20348031816a01d180d440b010070380002d01070320300000e1301900b20400002004035a031188003101060341808128143c800660f100c08a080103a0580350302d00501684080080700031241d0010f01c460340c403a0350300c0104181c0d4000010020b10003889900010781040140d40c00b00721094002e003403009903c0344005080c800180024001303501060070401c89410601e41001070140c180400402030800d00419464880c00c6005a00c083c03045000c02410301c0f501d0041a01c03900400e40c0401345c3c0b03a030b0180c4941d041388101d08010b5604c40710244a41e10501c03440c920403001e82448025074a01c1840300008110503180c0454030f4018208040c01c0c883c00340b0003404943d00307014680c0113490801c40440f00c480d0740c4818030010701c030940c0c115030000d103402d07441412520449640b260051140e2030700049842e09584803020308 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 385164442 1250 385163192 385163201
    0xc08010e1618060503041202030c1020031e061207060f0309080309160501111504080f07140c0d0b0a110d1a042a0c02010c0b0a0e100203011a0904 64
    0x40807201c1941d2030000c143d20390010000c5008a02601c1c3c418580426200120f1780ca00c2072100d515600d0700303c2c00326440c1d0710307440d5040780795421280c00060610310040d80d030082c0540c10445159070046109150b00d65081c4030344449541203141035686611a5208080c010b96401251207100e0400002122500d0407034403a60164042070361042d95a9603074149210703020b035104a00910080407040c0e0701d100003010360090401c5a008141e42029050600c2d0150840880040c024000d07039131268204648509415040000d000292007086103c1d0382001c402a010b01d005044c05c14a4001e490b2000311070045505403025640c846615000801c000c0302c48180354005000300074410080340c2c1085200800041010005483d80f4001c0c0d608124101c0c203078a02d0030307482070107216000c101c0d00802d00500105120b0228614a1030060404940c1d4038a07580e20300040a1080b00c01019043e614030614441000911510008140c02d00065040d941009001e410401c000c500220140c9030000305680c80b0b803100c1d0403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 385165692 1250 385164442 385164467
    0x601030b091204061206050405061503130b070f08010e07091e05060f0711040b221e1d06160c031107090501050a08070317160501060303020d030c08010e16 68
    0x405545550f51395402501c181d40c3c82130710340c80680c2030200105181c2030034803441d8400c0c04002c0164246d5007406c400180e203540042c105184150040880501184800340128055042950790795560056224024001001a0003281e28101c2400920005075448030303400050703e0079010b000802d48800b10240b0180c3c034141c1d00454102ca0007241c400d0541900d040a03140311400340040c1102140d03008100f104840921004a81c01141441141c0d4010442007540c20114861540003440741603044500e03108503240103415521544070200c48407001c1900300c162840350451402401c007428001d41d8682c2031605103650b0740403c5900321503501854071900c1804003510000041d200c00680b51440c4401500d024050030780a0400d03c94001108840043d2000c05c232a0004031142e0340c8000d224280000c0c0d44091341e1422041004001013012030000c0c41144029446034000f001030020140014042d1035032400c8403410b11003e074004100c06030b042250964001014010701080b11181941a61014101c41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 385166942 1250 385165692 385165723
    0x203070212160312030e06010b250b0901050114180a05070912050d0e010f05030a1a09130b070e031b0105040b040605030405010b0418020f0307090207030305180606030601030b09 78
    0x2c10010500c06401e098100d4100c0541d000d000c03800400301d09a0ba500c0d002c0c41525000002004110610f406020b0103280321068250008440d103011380301d240001000740c481d8001650759600406c09902c84044100c1031035401d03500103075001c0c0040b500310b0b8801001000c1d4030781c41d5120400114003d1049c0740700b00160407030103d6201d9402d07490401642e0782d4000380e105008114840591042d541c0181c0c081c640340c0c203c59465510f1642c0b489580c50182400b0000d801d40c6103181004200141e50381940320b4822152121003002020b01c504100c0303900040609080103101d20b1001080326601c01144040039410703642006100c500b070000c0126010b116035405281005400306001c248194081d0086000e203000340000c0c0405005d0030b0400c01111504e601da50202c54420b4586401410640750700b20810350020140e8894503542c250407410b9038000102200001da4590030410300b218440e1119040306a21801081f00d880d081003c2552400f040c0000707800d00744010000740b032401e010013103540b00c1c91544 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 385168192 1250 385166942 385166983
    0x12090204060b1c06060215160e040908070201030f1107030804050c06030f070e0a0b09120106080d020102300f04062306091614070303090c0b0c06160203070212 70
    0xa8040c115203401480712405560508400003140c070300c001071401d1001e4150003a00301c1130b160382c64030a840300384048c0280306115180c51005025695445042c04050007090120340d202c00e83d10005080b5001f03030703020840a13440c0c44002c0170040c1403602500c00b01b0394141420b20080d01d840c1021807600074040380c5142d2100300041003100005148040602805490300c40004500b10a006c1012840442c041d0b407000f828140030f14621841c01090912003000741c0400011002e817100d0500d82404030f080c100d2800b607900050785408a08411601c1c0c40c0082c3e4800c0301641e985101c070035413403500d04064800510b02500101040901c03400b94082c070304442142180201d4400b05080c620007081c001c50703403103104000e0003000810288201040c1000032105941e1101501000d0307000c03a4071508205000d80425565100744400104809082405000d10100160b100d26807a40041d02e440801448040710b50b44c410140300c03546130004282c90b410b9904030703200000141058541884e04d058010f040c501403141 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 385169442 1250 385168192 385168207
    0x60d03120c0e04090f02120a021e0f1201020a12110703082203030b120102091008070201060807090b04180c050f1f030507020c010e0d0206030a020c0f15130312090204060b 75
    0x100c800d96092031b0310035100c14007040783c0c101f8140e441c0c403c00b1101035081550b1524401280410071051088840300401c4400c040380202c000c0340d107104040280441a82d40050210051a0044c900080f201400361062002c50700004203880240141e4000902740100040421450401140468480c40c85031252900c03030700300e50400601502107210618060b012070b848003003440b907060007150f820b03c0015001c0c1480c071809490403261458001d240c80215540e074040454480700c14071410f802803240540200e1480403450400c011074401c8501080c83d51a412040b0000402c4a540001103d008503400c509000d00c5078003043d4208195081000c504110101030b00e00d1a40640c04207014040603401c8890301103180c4019200714464244450703104004200e4000103190640045600c1020f588025003402202d0089074030f001c04201c1c800c1126008640b490301011581d583c242e03441100c45000c1b10514030716407005414039000c248040001919014080306545680e000b58005013002c0204640c0c4504 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 385170692 1250 385169442 385169453
    0x3020415090609060c02030d0e150406030905120310090f06030b240907020304050d1b08030307140307052d21060a0303021e0f0d0306060206060d03120c0e0409 70
    0x1036074060030b000f10f640e084011407403d10840340b0302103966000d0003c1280d0003140308140d400401c440d004070f0380b0181041d03031070407031011000280000b0701580d100894004403d14009040c14220400000f00c04414001c021001c103100c00b01c202141c0324410001420103900703007003102401b0190009801692010300340210745e81c00c100200c00030b209161200c4000411343c0100b100c0601c007a00e241d070040c2e00a001c18007049c41c10702da2800b001840b91488007100856640c200100a02c4c80e031203034002c0e803c04001c11450760707080200c0312146078041a031640345203800e0b01c0150040c054180c4c010450f08000303415220100800744c034000c20604030780d880380d166500da000d51101d144605d801790f01014000000310345e05040146811045e02e038960007810000700800c0203180b400d281268000c1d514803903c1600e410002051041c601d0102e5a654040b55403400c001000e454440c002d0600e81c01690b041a4000c04250311480280549074200c0e40810000101d0500729138210320301c40987da100e450952000c04010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 385171942 1250 385170692 385170707
    0x230a0504180b01050d38010f09030b150102150a02180307080c0d0215040909141b130204080708010e0712030c17040801050403030b0301050c04061e03020415 69
    0x2071111031102107006010402409a03840c20340124003159090248444076007590b000030200800440b007010341d20401c450250022041c0c2100c2c2c80c480c1c00140350350140b959000c40071903508101420045551072940e9a071031081030000b13044900d0852050103065aa84c82440320783c002c50b460307c1c903c20382400c1000000b0b0003580501c60f0704040e02d400f00c1c03020015040105038101241c00030005040503424003010311800c40d88c864800c03a80702d0301c82c80c0c001c41070480038406080a04103040c400102642689003150426601141d03100d81a8071000e81041c040540050841440a09546045415a240e880c1da000380c001c68000035070b103000340200490882d01c151320045444954030100e84c036095894140c01d5841183ca41c010713000401c0740540c000403461202039103046403030710880d581c60542e60b00801c0b421a18241d4003100041e84402c01d00000e8a030034014203030407100c5601041d191038a094405032013141600c20002d06035141c94003500f8081e029906032002010a122801c80050f10640001e00c82e4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 385173192 1250 385171942 385171949
    0xa020d0906030c0207140f13020d18080702150d1a1e01090911160b060406090c050a030b041103010303091a090a060810050a08030c01180302060403230a0504 69
    0x4110800000704207100740a24400780300d0a0700503010042c2810075450045140c0300740242c000b02a0702800b0284d40756100074a00300000c12000580b1200c50900e80800d07500d444591036034000301d1501100c0803078844030071968069030486c0c00d11f01d4052024001505802010a0003404078500302c1d200c068200e02c40c603107106040086072100010894240200c5030075180e080164001495400c0501c081c2c0c0e01c2d0b6001041f1a510000540e0030051442086e51150400e110100d90028001051103020b0030240660f801808941c0d8007440f101580328001080c81c003887e41c0600c2007648440c0860495280c591200c804110300c000c006030382e5038403030801030820082ca10030101d20f0407000d20b440394003220441c1034440040d00180740100030740c030700b040859050401905051512001400c0000c5035500d290010f002420418060f54450488030100c03421100c008003a0030101140505800010f98041081681f21ba40740c02c200c0c030001c0d641140444101c9500074400c3d42da10300010707010b030708079081000340046 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 385174442 1250 385173192 385173197
    0x6130b1611120c01081008010f0b041802010206060d170a05120112150921110d0503040b0112080c121b1f0507120f051f081b060d020a020d 61
    0x11140d0144404042c1002c228242c5820428142080e50300c500c0e91950030903c00b6543e03014958648040c2800c588106904220b1340380d54900aa0542c10103014461a2514448609100f021940c0021b074880100911b181d108440c00c48819040100305c3c800d0211a5030303984001500e40c04010405404c0340d002c290381400030030160000003040c3d4800540c040005504c00d0880b1400401e0381060006040c640101b19503620480304000349801000c0c000082d136209503035640304c5840c607440c0340350b0600403400e00c82001c0150800c03c02c030100e01c00342d800c6070443d60b48030040b10140c1d00364140f6a14070b000700c0071071403254003803c948111803040041c09441c1c0807489079071310b030608001007407030b240c0d40c160000101e86814008201c400300c1102d25400a0344c0f010031414001102001d000c0d40d101146c6194160321615541c4100b8000000d007043d0010302d01c440206071910903141002019695400c12903c44003c4c1d4000c3c6005d8589925010705544a402d040e00c415500d4075280c2601a403a94180c00040c0300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 385175692 1250 385174442 385174463
    0xc0712080301060813120516061a1306050105030c0906090d11150307171018020d0e010501120b0a06050a090e0f01020a09051c3e0a0506130b16 63
    0x1309508151144a40950202c040780e04c120044031b00765000d4100c8152540080c00130000907001c02c81034000c65034032804088034040d03490791200800460b502e000078041481c918111381442540d0300321048070b401c0345001400944802084002461900c5101900c58000c41c0c91340601d03040000d42d140380180c5450441d100f90488201451075002c5000480300350b4005041c002d10600c0c61000180100d0300010f8814603c0310722500d44039842c00c1940503580c3d561300c1d10350024512000700c0a6120f90766400c035500c0c00030701440d40350175808003001c0e50b03003500540102142000b01d10885e019500070402044042c02c0546803541d200c101e0801403081074200001c501540e8072200210700d040c82140c508840c00e45908141c0713810141480181c00c1b030b00124801984030840300c0720101381c03404003ca03501d1044c03184282481002606030344100490540710b4800c01da103c104004e481d500c45229200782c07070701a40e01d6601d403500d070801c19400075150342c008460541d0004d0f030010541d0103000441c04040c0a0010f401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 385176942 1250 385175692 385175701
    0x150c0f0408101415040e0f03041205010b0a0302220b150c2103150a1205010608120c030418090212010c020c180105010311070b0112020a0806040c0b0c07120803010608 73
    0x30307080d8408031000b51070000e0700412918140780541c4568406c0580b03000316030509222841151440c0c3c4240c1103e100707141c1c0700d00b00d00704104007402105030849059915890319031035a4046842007440321894080d0f8240410000c08041007940303c54009030b00207001030f006194610f840d03482544404c1a000b214042d00701e40d10ba200c0d030803603002804010000d10451460380c0b5140d00101c10105424416440610b900e000180c122800f0700414649004e000001001860050102d2414400841481014000307100f100350201011080c1da040762200700d00c0c8400305440502500c0141103540000f54491400c5260740c038804815800f9004201c116000c843c0d84420390420003d1042d4501d80d00c0300e816100c01c0052103554400d030055003540c4446a800da061540b195a265107500c0260003140000728410510015490120104801050008040c14507810f06071903a0420319114003c1c01c0d1001c10005540e18818020004a002064040d07901c4282d00101e18080345164403c0c403c0500044070480442c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 385178192 1250 385176942 385176971
    0xc050607050405012a030e04180c080105070f120c090510020d08010605340c0905041106031e1015030b0a14060a1d060408032a150c0f040810 62
    0x110460081c1c11790050800c0d2041d501166850b040703009264016031103080140c140d1840e0303c2c001034294480c00c080381d9054105044203086520007044401000000780025860541000070035a84000d0890040b9007640c0d0031100381d54052041e88502d401580f0921034880b03030383e40071485800710322641e40d800085990790501254903005003680503c400301d6130644080d0030042c401030004588840713000250042d1540d1218682c2445581c8000b08894940080100f0055086018035411008803811411400c1c41c0442c00741e18401d00e41440920740f441804981c00c41148400c6400030b0030020b8231040c0101c20b0010003405001616481800f4a09080d404190a0700b50650101c0e0000081c09050400000110441e01281c3e0287c5410880350b00041182890b1a01c5008001030500c0d14010b50740d8845003020b40481c402c0c40381041448400c20000318003441c20214500319101c41d051508082600c882104a07407500c644407412400c14000100019031840c085060340030105085404c2150100b269590b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 385179442 1250 385178192 385178237
    0x70e01020606150d05040c12050304090b01020d08010b071a09071706061518030d0305070e04110a05070302150108060403110f070605181e0a0506090901030201030b010c05060705040501 81
    0x40c80c1000c8090044c40c4215101d41e011a81c410b024801c0c03c46040e80c0c50203103140d40f500040050f02c0b240c10014090200e40068092420a90400e1004240384455110010480c41041c00368004444000529005201070800d18140810b41daa941c0704150a1000b81c065079078940303200d44421a444005558407064002c1000c9228541c0a0244c2c160110060a80591944465410000e20321001c0210400f92010028000b40c4006509c0000f00ba0034407141c00303817480e44426070181c400c604094110040b40c40d848181d03541413400b400c000b51500c1041c6801c0e4244409041c42d00c00003140350000060001b00082c81a00903802510389c81d243c0740c101d012030360300d801580e514461580d01103602007101ca8418001000005043c102e840140b03e2504001151200d40690601c41c150405450f00858a4a505460010b10382191001d1805080c02c0200740820014403019040c590b65080f042c0c1e4590003413103801030140d030140640320301d0b25221001a09603005801914002050f003865244890f801c6e155 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 385180692 1250 385179442 385179469
    0x705040207080d091a010e0f0108011b05090423070801080d0203120c19020f0c0301140610050903030a030f0c03022107180e041106160b041a070e01020606 68
    0x18543c0c500140c8070780c010042c210407202164030040001d00d40c40300410901d40b550280600500712a03140c10001c0f02c03002c80800607081448240d00d8203401d508060341079866280e0603241410055281c2e0b002400160051800501401c40d104840300c1c00c0140c02000e420301441400c4580f0789000a0340c0700d800c2d50340d80c0c48602001e40c003d40d100f0007040c07005000001100ea400380ca00100f1a2619400b0281d0080080c201c041c2200980e00c11004128800420702115034816401c1d0020441d40d01826511000408007a01c02e40c0036040011800001a118600b05d410211010b001c07260303a007407480b00c020018503801d0700716012646091069031859210f80219045050303115110a4003d0141d82c0d010040000600988144003d0030710091a075407a2110f00001404004001e04013440c01c0d00381004845411503900303124507401c00601c0c07034013a800800e640101da00041407280b01d03512840c0c0001001c0396401c002c24840c1e2031100700503016602807449520081d0a0f801c2d0f503241d44540e0280b000c005a03480703 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 385181942 1250 385180692 385180703
    0x1e0c03050715180803060915031f15061d042307020a0510061d010b3a1a12100218040e1614060306011d210705040207 52
    0x30000100c0d00c01c1100d40100d00d41031200244000300030700d03804507250000d8011102403001104010300c40c940700d050b007070b400124041c00c00c404150823400a5107801143c0c8000203011120020b005001c1c58540c0240b083e100307c080c1c080080350301c9841c0034003400640e1283e0000c414100d400030b03495080500582e40040e08c028142018419500351000b46600d0042100c4210300c503c070400d00104508001100340034001c003d000900701d0a100300320101d200112240c440700d07450080108121825041111041070040034404e9412205039450a002c81c0e549044580321602c00f80c0c4d414689a15501c404904005c1d080000c0310381300b5400900034121001800215260044500000070b4180da80040040c40406a120584031519030009030440d0240011a64180d2041800c0f4110016000d0560050241740d51240310707400c040d9000844503c002481d03541000080003100108580d02c42d02440e05450080154400144100406030412807030815a0141e1145000004690a044c4210f40d011600712 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 385183192 1250 385181942 385181947
    0x5061605130b09190b03090708030702030c01081f0303020c040c0f090e070c020d0602070317040b011a19020124060203040506160209090604060f0e06130602191e0c0305 74
    0x100080d10706800c01a00d540d081409184c40141100e0a4410074014158640d80e0076101d00340b18041074605038054000c0ca01c1c0b9032080140383c015035000038003409400d40920340114540c1e0f4902600b84100b2016100d040080804031001c400c141d0086004c1611701d41c141e504100ac4840c03501704551201d0b402c910003020901c4a20248640c0544288482e8805880e0074002561016540845d0501c40340c91825a0419800b0802c01c0400d0741c80412000d00382030b521007401c000e061903182c04240d80c40610903aa48503400d10400030070490240241d4040008007061034000070441000680640907460921400302c642c882e00d40b010780700502028042e0340c001c0e8000c500340303030030f26041c010158850441c0c00c103200600212100140e84484841c0c2c400c5030000040d0005003814079110f815601440c006880791407d0505070010001c00080c915480640c06408110311500c60038544001e114400d00c106455040075809601e4540080d00c02a141c034103040030741c507100e50f00d04c01255412140c907001400034204 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 385184442 1250 385183192 385183199
    0x1505090a0507020c0d05060f0a02040806070c1113091502030c09010e0609040e0d0e060405130f14150306010b030f011503020d02030106031a010305071202070f0b01030506160513 78
    0x450703102903032008140c01128682c0103c000011071840e0740380d00495060384010304000d030000010900942203240d0034070541c24541401c00098a81301e0007858001003140e004030310b0042c8207282408058100700a0004034408000c0384000c8041c114a5001741e441d841007500e04169030b68180308403481440d61002a6050540c2d00004451041d09522116070112080c4411200caa860740b240100d10071801d00142022860210050502c0040c0600d42d0310401c4144010803041d140c64141e03804020f9030700320000706070700f00c212544d005081e042c009440002d612820041d09440071010b03201c1c4231008808492003a0b0741c40b000d43d051480304490a10b82440341e10010402c1c03400e91110000601d095090160a11a400d0a018200d810981c4504002500c44400081501c4280403000c00c1e21400c4c44c083c0aa4540088040c1c00c0b0b903001100114007981c0000c80b0001d100300301c00d04552b5103500140059803940d46e41003603603890b0410b68901064071822401c0c45100d0340984101e821926150401e01c0c1134034035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 385185692 1250 385184442 385184461
    0x110a030c1d010e24040501020f010908180111060702010606020c0306091b031c020a060605090f19090f050c010801080d02070b0d1107050a0302060a0c050f070609050607050d150509 79
    0xc243c50440d42100308240c03100200341440c000a2849500c650441707446a181c60002860320601500e07a030400d902d44281200030030140740440c0c1c222040c90401a420742d0300c82004903500f842c0003122503c68001c1c00b060040c21641034000104442003a8226081c0074080c0c401c00d0345800303081c0d0b038000d81da5105401481010400b060450f624210007000c2d100030540c10b8022800007660b004400b801600b01c15014003c0140b0303403107400302911054800c60064a089100e035907810304043d00540220b000303c500b0390390303540e46a0041d80e1241c0d44800c0c088050b04091406641d1606544551404207141000215000c000000c488020310b0301e03a80201389c1d4500d000704e421465400340d5165440c95880d01c5040551403c000c00030b01d03615100700c0051035081e025050003418500003800c2040c02e1030504a0506010f83d0100c10b41d0f04810b901c510007076650241345003840c001c02c9442402000c5002da4020020310341d03004806452144044101070221244201003c40e1787e02c2c00303001300d80d40001c0c6000803400812 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 385186942 1250 385185692 385185707
    0x20c1c0318112b020321120a0f060b0d05060f0604030b040303021608070203070b041203031d06070503041109040308041103071e06120203040c0e0c0409110a030c1d01 73
    0x300050944441d034000100304056400700c0f40a418040030b80c0750084021400c080041010b411009809100b512001603004651446540700c201082c0390700e0400705140d024a9401046d00f00c0102d10100038a070340da902140702d903801248006000e5407901c40019100c0c01e2282481c0078402c00140303850724180c1035aa42240c0e090000e04181c0c2016403c2c0b1240a040048054800c0d0a0307000b5a9030303d4490919104041c82e0085c1034025034034198091100700001840300d4416586030764103040106091326071580c42d910419040c8401c1c5034900ca02c206020354542c02000450069000718150071641c8905418440c3c0b02106a4004001031001c10000e008200880c4800240b400c00400359038109594910030646172411442d680341d000090310082243c1904120000c1c40300c4400c100550542c079090b102c940c842d41c01c81c4a60134041440e078000a902d1408070081300c0c00f40400b01c030704002c6003160780010152500110b21a07004240f40c68424900c0601074040481800c1040ca4903007d40003c0000454959 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 385188192 1250 385186942 385186973
    0x906030a0e0102030c1b0a0c2619020118080607080a09200a050306060d0609050f010203190b031f0c0905040911040b01090e0f1801020c1c0318 63
    0x32955166044000e000038002140a61111280f903500c031442c150400c1c05004070301c210150b0a60020106900154880303039004121100c4021980d80d280100945c292001d15010005a240c020b101c3c0d1340c091510802142036a0714002c0c3d1340c540100c84803211102c0c044446000b640444d501280000c1d92481c401d201055000082650104451383e0741d81e1020185c8621012140c0c040311003614600d40d03810106074580047c41c08500514090400c040030402c0c0e0480251b0107400701e51924200c205206040204203000c40400000310360b00e207001010481010307100e11244c8402e50618461380c0700d0b0715000840081810f051115070074030720b5680c1010402044410040f0050000410f000039480e034a80c800c414200e800b5188400c4084103503003c01040310003524000381400140380c0c06000404c2c20045165100007407400000280d107503282000d071700300140f01d01d0b50020b41c00040c0f500081540416075050500c03411002882c80c040d0140190143d81d0b6401800e42c007003043c0024070300031525001164105 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 385189442 1250 385188192 385188211
    0xb0f06180a0b060c0105040c1701020a0504030f05031207020a15020f0307030b1c0b010e0106020a0b160c020604090f0614100806060909090f0607030908040e181b030f070803090603 79
    0x50603004d002d040d0035a80308450035520b00540d1481040141c2c506101a404d41080300c008510f00a02d542010782940a5400003408240d190f2002c803042103002c000301da80c400c04e8081401c00314945041c0003035946040201c06c80d4402440941c0b1a10000781c0d00907105401030f440056411603455031001c40040095101c0b1651149080c5840540c40070f000701c1c0b1000290060303211100329814104046103860041e4040d50466014018507004104458120307504104003046940018800c08800c4440304101207010750300000004002a02d0701d440e0303000c001e060b482817a003441101c1d80e440303501480c0b050750a1802d4200e1880c03120309000b136105032003080e0303c0fa41c02001c2e01d00f812103035004146240022a03480c107459000c0390004c50300c1c010030132109611100b83d2409001204081d503682c1007038000d9104010301c0480010103d0713200a030340740e2100e201d241c0d810308a403628403680c00100c10780d80c100400c0901034001c0b00c038200310b03083c80401c1c2c200507100d0500085141551032070600106a0008015081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 385190692 1250 385189442 385189447
    0x50705010f0c02010c030b10020a030c082704140c09040c02120706020721090506030603030c0a120f08131101020f0102071104050a020304020d02130b0d0b0f06180a0b06 74
    0xc42003000d104070442c410655000040c14072031039101070202d603241a0a68820129030112020050780011900e20440e0b2615041840000301d10f0442254000c01840c0389072012400140e8560139851000220640c104440900075100307407100c00d0b44a4901624907e4402e4401c0214007084e0800741c1140c040014140b0417030740d00b00c034848040c0e003813500310460480e00203400080203818040c51480b5016008800a20403101e54182c882c0580880e5161107464003c68000c00001d61564040c000d5403010000c5509441000c405450004000c0c0880e222035008501c542416100745131084400610507a400c130054006800c85441c1c461a00d640b0300701c01030451081e04000c41d4012828005002c10500c5070400281c401d141e04100000d6590040112080d24170500c1003002696902c47e03594100341d010f403440410302005410000c050042401034070340000c9001a05410406e20b448091302c03590790603060014075106c80c0d0802120758011072441ea1090b454102103071103812981c1c081401440000d20791032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 385191942 1250 385190692 385190711
    0x30c09070c0f080a080906011404091e0c081905120c1212010312080603030d0f11040305030d0b0306091b0d15050a06080313060e063c030f0705070501 66
    0xb9006260107008481c64140410700788100340d0010001d98100e603a25000c0d0002e503040500300078000340c0c012000307403007240c50303203c600c080c08551100d030001a036140c441c40054010600708003c07211041d00c1211440d1180018803002030519025038420141d100d00508048030320030003546a03070341042040c000b050080248544107030012200800c1e80c0340d860303500c2c1c1003c1d6141d03041c41c0041035001c5a0100900c0f0180081100c02da401008075550000c0501c07000459418110b140d80040070418203805101c1e070001408030501c4000009840460010441400f00d0710000c0189905d500c415210b00201c1d0740401d403075800403451101103100103034001e8141964101035842c3c2e200141001440105015924000d2250705115409003130007401d0800000d5141c101c0c000ca003900c00811a1060000704070204881d40071075030300c4200320341c0700240138083c8034039075101d170080503101b00a1801c01a42c251004900320b168440340c1c4083e00c1c45114100d048074656529001d0039247e5500180382119103558491415 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 385193192 1250 385191942 385191953
    0x906050714010615091a031f150c02090c090a03170918061c02061c0216030f0206130c05040b1306080f07050109080c01031d1b1806030c09070c 63
    0x400040c240102d000482213031038034001d07007001426001040841000c1d110110038000c0d00d400c03240c00102498080321030044040c454461003456400c0f80f5186801d00c50802c00e105d5000d80c242c11518021600b21499468521602c541d6108006485d0303041403140604001040e1310500c0d2402c056330200300289400902c00000321016910000c4611403d03400040c0005804c4c54508142043c9000f22403104032062500050300d00e00590180000e0400300d040740039081c9003160107907400c8042028003e0104029460068000a11150342c140148160f40009003003091440c50850306170f4000c40c103620400c4c1003c2c140406004103012243e00260040b012440088940c40740000400000c00036010704005180310604209141d8001d030b0400040803414001d211000c91005070b80c0c482401d0015074015049020981c010400e407010400340106280d031144000742d0300c08110044c02c211641040c0c0500b100882884100a072181e58044d40403031888002820180c03141504816207041c500000c20169a85 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 385194442 1250 385193192 385193201
    0x60f040201030c0504081615022a2b03020606010f0c03050304020406031a040201030b040207050601050d0f08040f080601050d150b010e13023f0c0706020a0c050715090605071401 78
    0x103048204c00900c108101c0c2c0e2301900c0012020300220301c00380014840072003070340c2000d242d0180360007444e50095108a41c2c41c1e544d1102130a00382070b901c02c8000d0060007181920310003070340c462043d005401241d00007405d5611541c400040c5001c00d44030403181c15041d4408903955040184100e81207556600044042480018021589010040031a186140a200042c1620714205c0f085000da8018804c00e000124041030181c19075005031a0015500c5c810300740880e80c51041c42006c0e040d90f43c00a00412100c0202003941d05640b0b013074045411990381c901c140110108250000b810712900c00f040c0301f00c85922608a0090600140f40100b00c810142000441000a6100440140794000f5442d11514102c05200c1315901c64582c46102840e0b01d404010110701480c100e000c0024620400144080c0c904c20541d2159900208110b4481d001004060103484040e10242d4a40c407809200144108800312081803000c00ba41d0f0b0f1002880c0b80c10415074103500300c881c00701c8070440204880486030600340b16 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 385195692 1250 385194442 385194463
    0x3100507030b060301270b0f1210020f0a02060906040f0b070905040606020313050603010e130602070c061d04290a080109050105011a0405010c080c010f0e1c02060f040201030c050408 80
    0x550312620309040c10300c0c08041b504c0c44482402d420646000002d90711821a9140650151912810f07540c1c403110f03c17824088400b108580340c501c00700d8a8035412044902a0160008a80844c0c140c0d44917100c00c569134150450f4020300f5402102001800646030408007074000d8030b142041520710382c403000041c0503203409400074070050740007182256031103c41d003000070300030300c800d50b034041c03031541058420618004014160035148003601f1240c030420409a048480140c2c11680068480c1c4e1034130780c001c0850381007090b070f00300e913950080c1e4022507890030f03101d8540442c000d084440d2603007650380c03010a03018082401031075000040c1080040d4040c02030107000348080c4110000503056040c015501d04049a040c0ca001c0341400600042c80140d0f0030410110303a10741c000034455281e0602c0c2c0c00785405802480000d40c1c0d01400d01c0e104001200300000c4120a00d00426030400150b0500c4001720f9840f03804a80342c4070f0900d0345102050143d4003941c044469011796240c001d103003644481086103421f000e41c3c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 385196942 1250 385195692 385195709
    0x6090f0d0312061a070f0219080115060f0f08090703020d05060601020610030309090203040206040902120411060702010903150e03040602070807090606200309030709150603090203100507030b060301 87
    0x110842d01e000300701c1c440c1c500038180100b10356003442240c0740f2034042405940f02c010240c6d03201410b84002d56641185400c5011009200c00c414262140c601078040c0c600c152904000c521111800320b040790050544060741c1c40d280e5070324061003a40a0341218114800b0b08480b060303005000000c070258840310001041f0600820003003019042c0640020319000c0020011410b9083c444414000203501291000440349880409602c980313903400051940d10960748800702031840040c900c030821621065580c0b140b805205800c0355910070700140030f101d219224000340007884404042c030010b1824141961700142e5081c000841c1c9100f100b5142c03039680a44c1111000d03a0112404106d0750740208400005400c20744428401d1610740540617200c2a142400074400c0b1001e050079490b190020002c1ea140c8070001011104015540d0603500e0042c55182d2040300c0c01c42401c8800f26945019009030742c049030b0b02134000c126141801c0c0030341c0c00800d4081c014404042c0c60340c038500b01643da41e4002c1d40c0170f03000c1d00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 385198192 1250 385196942 385196957
    0x204030c0b13090c02030409020c1b0f06070602030414031b060c0a0909020a02010902220506030c01050a111c0504050103050f0106210e030a0804200f06090f0d03 71
    0x5060894050205922109080c0c1c02004a421803081c00000e01c0211840c0c1c503000300f00d01c004500142c0c00c6000d55040021081c1c03011880ca10700c0900060040040a9a0601035807811000750502140c141c90100700790300410100303c0440051096402143d20a014801c0700400d816003028103811a07210240c107082203070010040d03190201e828044a07411100041107103103041c000c404040c003008682c0c401c0b91035860b800704020003034500039044a1509907005003280302d03101280d40300404440f0a40f501e00c1e403c0e490800040c1c0d20741000140042220f20503102e8a040c0b0740c02400c01c880140e0b89040907034041c02016064003521940d210704500503d05500c40d2901c030341c24280010205c4d00300a040b00c1002c4030080042101c181c1042a00010300c400b011400041903c0601c80806004905c50141d50362200080800c0081d030320401c09801035115040c42c029501c03008440354086011100d019910011201068085160a000070510b00c903001c0c0204154455201c0050a01c181d20f40c0c0aa0119284 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 385199442 1250 385198192 385198199
    0x90109020a060305040b2419060306060c08040e13080a030212070203070f0b1305060a2a080105040203041703071d030a08030402060a030b0901080705011403071b03090503010f0204 79
    0x28074000500030a207000c202c6803070a51603402d8080405030000b01d016142802c00c02079031f21407040c10304c401000039110301000100780309940b680d60580c1c0b1405000910f04000070807046e205101c214901504103407941e00b014140340d80205400303405016007901400d006007007000545410090304840036661070040c0c540466207849071a55400500a0085410401c60300317001525a45c0341c0c4000715000301c01b04c20390355202c1482d84818901c0c1c0c400074140e841500700300b02c010000c0ea08500302d4607580c0c440c882120181c4484e00c40c030109081900d0400b00311082d0060213507082590103960310a0090000c0070b070700700b0034062680740d5610a03070b014030019070b01000401400001e401c9965540100340c004090b4255280c5a400b0300e8000540b000380700303500000e21114512700ca504408040c1400074400781055a6604800b80d49094500c503540c04201460b003901c4140c030203c03003074034854400c07600c8101c1c400941c440151808101e542d01241406007840000c110b44d00c00748280d51410b5820300005a90340d08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 385200692 1250 385199442 385199449
    0xb0a03181406010512210d0608010b0a05030a03140708090604030303090c1a041208130f03120305060a0302012304140f0a05030a03201615020109020a1401051209010902 74
    0x9050f00114024255090b21009078180019040d800010040088480b030b40e41003405006c9100e607213a03015040d42400300210702c440c410f6110b00040314040b80c0d101c0050760f885041c1074486078075480c081d010890304404005030081403401052400d2142200c6403402a2050001e80300f0340054000341c001076a2130301c4000c2003100c000004400791801b1824161000c154104000307072403089001c0c150b01102d4020501d81017090340030945d401c0b517030058401c00c4105d03200c201b102d0600da107601c000d513070303003040c010810b05502c3c0030b0302c9480e0146001828403800d044c2182c005450642c1d1012003500d44011341841d400125900300b001d000a02100d116030101b0071851010410180c1404015501c11a14060300f04169039001425407106685410050100307c54802038824034244059070b480f41e401043c500b515400140b014080c140d41c0b00b06001c0907031038181c4104900302c03015080025000903450201b8022064403072031808141c2414904503180c140c1c2c0708502030041d032064506400300ea456200e410304516 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 385201942 1250 385200692 385200703
    0x17090f070308040509130c1a0403150221150d05150a0e160b03010909020a210308150d060e010e0a0c14010203031e071124010f0503070b0a031814 64
    0x4c0d1010f0007008840b105451fa110f40d01c07000c0c80b401070201003002d0b50886d40c0340c42c101903600554000d1607040d0001c1803890f604000c2d50042d001610010800c00d01100c0502000740128060141809004180070903035003032100341d4042c1241900e5600c01c10040d80224003d0710003503441008200b9011804182000609240c142c40b00c1030318840310b4816405000031045c038000c1e2411140700c03240114403c1c10b1800401e0a44c48550409030b10380c00c070481c60b04034100400703903150101482541e80a43c95950302c20400c0b804604201486d902a501044200128159402c0300c00c10710360b158000079407500e2010215182819080088580000c4c00c8010099000c2502500840d050300b03002640c95031401c05c41069542c0032070032082038010f810901280348544101070601c1071034101c5040785c207420030050910180c507942440010a01000d5400402c0d00021245120110781c800350043c20394070305003ca030515036005502c0803000c151383c0d214004107012100011212541c010070088460001c449011030500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 385203192 1250 385201942 385201951
    0xd021b0d030e06130206091207050901090209010f030c0315030b09011508060408070f0b071701060e0102100506121207170f0d02030702010f1d010b0405040317090f070308040509 78
    0x25103040b940c050003500c007181450b40400c4c26207400044504901c0010290f01824070070541040c0324100c501c40b0340d90300054100a9541c220b0b0003003916a078802000041e8450003100500048000c040d8401440c000d1b000304055090b02d050110b410540300c07a40c08401f5650754400d80e030140c0840c051103124802845500c001440051442962a04180e10300740e50390340282c4018030780040010501c080c0001c2d0540450300550007000300c49203051680c401008111005000707664481c50b02c000060060040b4402201c400041e0080c1c115203407880c403050010180103041c0340d040070666000038415101840302545c00c0309408041c940321159400c01c0364252082001003495030404011081491540b84140c600d018030303640d005a901c3d61007250807030152820079079038920f5174182200880602c91042e401c01403905404020000ca004050400c07080e41d40983d030107400b082d0a02100640d04039541040c1d607022000b40100e0b130b000000400301524000280c0c2c000d0718281d00216050001d440c0452245401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 385204442 1250 385203192 385203197
    0x4060e070c1109070c0201211a030d020a020108060d14010203040501020c0609010b0604120503130303031d0102030c070803130b0702060a0b0108090d05030a060f0801020702010305060d05030706110d021b0d 90
    0x15241c070010103403920f100803d0290500898003d80c100741c00791094241110114407400303000c450306044001c9c06140903010740c5442030182400d1550340501c0002c0072500c10390141e440b06c0480c1c80304424080151310000d02518034941403a40400d4040003400110b000390b20400005130345040c00c041d00e50401d1009091450f059040684200c066070310f10040c0d8090314848551419140c0046c40c01500c0e42c4100d140c40000680c0b461000030038190154400c043c2e8480305202c01d4402482450b0580c02c0384030172200341106001c20720170280030416003805150711180c01d08002c1104000c581325441090000c8942d070006902c070341704100c02e840c0580282182c0e03050070b00b4481d0036401d04440440e1a040c240d1500010040c0110000e00b05080c213402010091140e4803044d28640e4035a4041c5006c2d51103400182e010074240004940c3c07030b003001072070340007219000000b86007070004564403840540001500220100814041c9482c1410584001c019111540120554010651004a003482000303ca420203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 385205692 1250 385204442 385204459
    0x20c011b08060a060c081c15091109130e0a022d09040809100201061503060906050d02031906020403060501120c060305060105041a0c0717071505040b030604060e070c11 74
    0x4c0140c0009170742c424a54000c1486807904042c03041056216115109006602d041000b40c0003d40c140600f03440079034041802c180400c07800d00e050b2000c940300c1c070321005400c400d454002c40610602e03503209002144500c0240c07a00000690001340000540c0c0c0c010b100e00340c402c4030700d01064281c81c00d810880d0000540e49508186404c1c1c071f80031050300403c01e4180c0110b510000000a0502c00e40c8500007803c82c0e135010b964008600c15004000308000d010f5140320f54075007280400c6074a0b01c01d0704c800c4d270180d00400424001412804101020f103480304200c810580912001c000100c0c24010180a00719004d001f295006550510ba018041981d00103418186410203000c180d990040840702500c1c148990b401d070645500c1c000d03040303d11607110014518058003034041a130600d403941d490700036102d400c11240f40a0b02c0c0c03003405501e40070503410f400225400304410404103541078003541d0310010043c000151107075102c582a0494004884034000a0b05030303241041000064010384904900580f01c411 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 385206942 1250 385205692 385205699
    0x302060a2001050702010e06100e07050c1c030e010c081005060a11010f0209011416030e030a0215190302040b090d0f080a0806011202070308010e070201020c011b08060a 74
    0x620621803650384604212601910036840c65a8041d980c0348004803000801141c40c0c003240080c02000080e08100340741c090361001c43d20007046070100c8003e4a00c40c401007100da4403101c1080d9120740c00b52010986c40d02034004c21035804511082c0303099140700151000301c2e884101071011400c684d07032281c1020501441e50240110300f0000d0f0f12004c280c540076513115650f080d1a000650300c1c113011614400d0150b0030100180d450f88456005030913106030070b0706c3e400300c420503c022141042c0038500700a01d803055890354000100b03204951500040c180039050302e440542a40200d43c0304d49020b0f201d906180000980200f00305806284000c240c0d40c180750850425040c4400010248078809003180f044644800c400107100b201c121007654544d0010550b503444241c02c801810300001115210b0200d0100c082224034140c15000700c0d07108a90560700c03804540c0c20640769403400d070b5000d060201159420f01001a02a509102d40341e2348046105180ca42428040703001410044005d00040c001c400c02042003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 385208192 1250 385206942 385206949
    0x12030c02060a11090306180106060203040b07060c110a0b150303090a12170310081516080714040f0f0f080a030509010e130e1c020a1104090c08071502070302 69
    0x2160828103901c00802d010940d0002c8040138061604203960502500c0188031606030069000004280c0c800c0007404101e03980c11060307840b07000e40d105542c4c810b40200207a10004880760b00c058103452040c2070205042a050400030701c2e042100030121a018018030521107140c200840c00d45108104038015803501c0426004114001410f00c0b46c0783c0a000c990b02201c04111144281e060040f0422507810345900d4400c105122042207407050300624010712884c0108000c0ca180500e02c2604201e0100103c454501d804131060600101102e007000080c69980d101491800c00410090400d85d00c0b102d901400e0044101c084000d50384860010403820b142000003501c04121101e41e2070709410031584460b21040180d0b054810440810303440354900c54100a101c50680c04203180c482e0000444244005240340c1e007001f80d802c2c2c100c00740968000c020400c00101c00300600901944090310101d524807443d41c8000089140da00715100542085000340300c003205c8c0034a459194041e92001300403031803558010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 385209442 1250 385208192 385208203
    0x601050d05100e0c040306110915181504060801050303090904230106060801063c0c0501051503060a1a0126010b0a090f24020a0b040b0412030c02 64
    0x3001554071240001c03254504158504010541d011906550b4680f42c2c088003003503402800200c2d6101d01e080142d002460700c003425079140c10740203811880005842024259660000018018101c510040340740baa6103401601a1041e40c0e13151080d61294100940549109e6050700b02500a0b841404801003c1c1e8911166941240c0c02198184075041003814501d000001e50342d42c4202c640c00d00d20700090050388821140d048840f650b8904004880ca980c6541108440340403011102410541034058601030319000c0c4050400c90510030040380040d80c40900b590000c8520441d200c00100b010041d0b07050501080c1d601406600f410008240600301c2d064004030201c8589041004c05e0040c1c0d161030744240c120190032034904074008075642c2e640740060400d5002080c9000080c044000010390b000e042d02d005425103190111162804420000b2410004c4000c98100214490341d010b24010415005031030340a80d000f144841464501810075244503030142000008040c0f80c50420042c0c7e42e1701040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 385210692 1250 385209442 385209457
    0xc020c0906191a03221511040e010e041109240a120b0105040c090501020601051003230106020d0503012103090f081c020d080109091b030809040f05060105 68
    0x82580890644a11010b409400741e00021401d800520440344102003880180d480780c0564034440e130503154845400b07030516050003130041c0b4034900621000030110703407500070841a10481e0780142c20265211002124514203030b010181c8603601d08284000c0c460410124001c42c401503402004504001807442001c0300424540002c4200d08034038880c156450342c4c1084010710b01c40005083c1403080341007440141e802031180303c0c4540c0ca04180140c00342d000d0032a900843d60140c000e0a40d90303107801c1c1400500180d4243d40800c040d42c031092110b40700900302501d0164940175110302c1441d070404201038034140e0f111800c40c06002e8180300406c03540040844a00300b00c084da0501d89500a030a16064a07680d80c99080340c50640b035402004281c1b07110015407031445581c4010504034004204009907140c04009404500152905006100c0f0354200e03000a01c00e00d105a002c0443c2d159841d5201c0b03942e505680003103641a02c00103051445180900803220783d680c07107600c10042400c01d6000078006105084 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 385211942 1250 385210692 385210699
    0x9030c03060124020c0d03030b0109080c130e0f1e0c010c1707110402040825080d08040305120c12060301050c1905041e0f060f022d070e09010c020c0906 67
    0x103100700d01640300303005080070a400503052441668047c90090701401007202210300040040b800000c0f81b0100144000c40250081c01018002a8410740741d00030b0200204c0e0200c6603c2469251b040c051001c101102e0868002c1c084095100c1d004500c2505180c0c10003140d5042250784a4020040341e040d4408070056441e400307072650754003400e01c1d080e010420b0b4441795550041c80440c3c0080d006202140510441c0d1200150004040f80380202254580140c003a03250b590744145511140e560060001a802600904015083ca0704500215041c65800c6907465100900487c0c1303450703501201c0c880745400c144118000d0020b0703c0c0120f5404520f000381d4800e141c0707041c1100300e64100b860241d0101e80260525a402c0031101291242a101d0390116103c2c3c0d280c10b80082d6000543c003842046d00d001e250300180c0c06809064000440f450f1076000a50107480300d50084003440c0d060600812442d0000d00784e11014075004c0c0360440c486400c40d50380900d443c081d5000170241e942c6d20707030b5400a07440d84000300301c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 385213192 1250 385211942 385211999
    0xb0108030306010e1003140405011b080c03070305070912081b0d0c0803150a0b03180a050712060e0f010c0f0207060804060f02120c0c100e030d0f02160809030c030601 73
    0x9200440c003030407070300c8100c174000f00001c014423041c81410342083c2010410143c8181d807a88141c90b08641003e0106da9500c0d500c072007440400d0141780301707400942e0021058030f41700c0c2020b522a80f0b05140e404580400b183d040c000003444400382c4e0391481d803200144600703034054024800c241c40f0251502e09002170003090b00c000000040c2a4490000c03a04000d00d4018108900309602c1340d407009096807059401d00310300c00780042140b40e200130000d407150115600c580504800c84c43d041d0a4882c441c0c506508440a070b4407001044060310042249400102c1800e001041800e2002c40140180119150140464004950501030907811400140c0c0042d44240e00181c0111121003100084c003400c3c0c107483c40c3c41e00341c905000038000d41202800c80201e4034005d5035403051300740301a44e0443d640b40c0360492035604148056100e040c100c0d8441c0486d00c0b00b142000d850185a508050021002d0000445d10a08045213151841c2410003419091400c1603000f0905541071401c3c6400400406004441900c0234 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 385214442 1250 385213192 385213219
    0x105131a090f070602010b03012007030e0d06020a0221040b09091e0f07110703020108010509070201060f1d0a050105030a020d03140a0e0306130206031302010c0c030308040b0108030306010e 83
    0x400036403411003010b40c16926920b4403490024040d0141e038807040c0c86076080042c4401d8480d0544850200014103185007440c01c2d10658003a00c442440440466001c14012035400100c0c2c16800100780c0311000b540601a103800e0f41d024600c802d18621160a940d0505001c02d200101c0c852044030403120040740d184003241d59070840d6211035108081aa00381c1c8802a0501c04020449c00b00325006010b541c9442400740c9000c40c80640e200014800030340000c2120004200900344410070b143c000400c5d00c00400d041d500d90190529400c0194007110800020350809500700c144071680d5608020394190a102c5940362000290b41c81c0a02c8030040d00c01c00b000003000c402c041c041d00381280603070640e10a443d12110f0400c8041c2586100e403009c50b02034080c40d030000740c1d030464880c4c0400d54076a00070511070468481010f888020040d00404a0500c170003184804040b518000d0180d0045103c2e80d9240010b1500d4900342c00c2e07206044c0d21008072948144240039660303800480c50180c48206903a654001400e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 385215692 1250 385214442 385214461
    0x3140a0f080927061e150a120b030d030b040b0a080c120c1011160b0301140306070906140d0905030c0727020f1615111201030b04030c0212010507020105131a 69
    0x202c0800e0340d4415904d4a40c491b401000c0405490040242d8a4400d0305040d40b60004069038042d00c0d03401d034950080c0d08030b0700e0264020361121040c804080c000192400c0c1c2a40440c01250494025014a9108804094140c0380c240380c603c0e440459200034000e0b11940202017000e005484003944240f03d030048000e070890600b084001fa14500000c0d64031001e9075a094000b00b00d5000b8080c910215a000442030030303071300300064030030300035489540c0d4020420300d00340040340c0038000762113425a40d010030403000151002a0203440903140c0180080c568510685454514043c8103500c00c00030175004407000301100d03410f8100c505821002082c0580c0e00c12000c0014070051007020800e0380240103100c4000c0a11a8900850803031011560040220400413200760210b4060030701051000c01c2032100520000302710030143c94200c0c0c400e050581c01c00d506d690004080451078031044c2c000d070307541d44100100725509003c0c164106000780c040704072110142d21740c0c030166451055194050b404e4100850703058103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 385216942 1250 385215692 385215739
    0x3060c07052a030d1107060c030206190f0204090204050a050a08060106110c04050412020d081b070501060806010b1804050c03240306070203070b06100903140a0f08092706 75
    0x81c1591035035031141078080c2c4040c04a60701c01d802407003a9400071070154081d00b108e000706034244c1c000386141d80c4c0f90a039400215078044031280c42c26860301c0b0301203150b40050000e007016188003c030268035a42060140710b10f01d0007a0340010700c28983c104c020403040c05c01242d0241540ca40d40f8080d005d80012024207454000050302207a0803510740740c10030043c0544205032a41c1e007405603090f0b82c007488000000315124a000c0d5410340a4054441d555003040c0307004e000501038540700b00000700702240d4854000d828100c00368842150b66800046005540340701950303031a40890102c030704020030700381a5400f001d03e000c010310b00c4100180d0f402150307900c010b294000d00001207000341200c6042c034102500075141c0c0c12200045a601903000003040302840c108106104120341c1c1d0395011061417941c0c80c1c4410b59051034210102c280034000c160408a0805403c40c01c006000740f03082e41d5a1000310040c48001a038040c10340d1030042044800103510700e141072405030170040460740c005e8a04518000f114159 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 385218192 1250 385216942 385217023
    0x2130b10030e0c040501150e0d061a01020d0207080705060306030a1202010b01020c040e0606090c04150306060806030607090b0309070b030a060e130b0403030f0f020d0b03060c0705 79
    0x510524110328a40d0780368101903000590b80c81a100f0100c041802e020545000f030003031040105121600b225001d20444004050303200080409641c00a2501d400c02103401d00c154410024610a8500703442c5d503010410451481d9103480142800c40c42e10131180c0e21000603005a61240c600000800c0c169603003000498010340d0040702c0c80054001016000e8001e0900c02c52540c094010340d0f01c0c4140a180511403400c1d00c258000c00b130503482c1d0f120310400c2541c080050500404407000c2c04085990f12100b03042c01d8101070251400100d00707061080140c03203100010700c000d100c0ea000008010003140d00a00b188100c5008400e66512510761020542c01d00d4260341005c130041a001c030404c4801d100300c0e000b900072514250718800c901d0311245052036032548415800703014080c081006c40c00081c46075200383d11101c0c00300d8002a109842c5011102a030303001890f00d060403500d80380000c0130391800303108264110342815401e80c90240c00d6902c0c0d50321003030441d50694010703644900403c5049200960318208 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 385219442 1250 385218192 385218199
    0x80d09060b130b011d031203040f140307030816200106080a03031d03310302060a0f1d03070909020f1207030309051804120e040507030209011d06030402130b 69
    0x812007204a01001070070603d9295000504107002c049655103540d02c2030140c2c1c0c001502609a200c1c030302c002c03041142e10190040354a203054038822400301d521480d003401495044005150341e100c450500800205000e096001101700244c5910b01540d001a03c15034075441554501b501140800308141c01040268010021070080e246210b0825903d03a0100a200c542501416850424055141ea8a0250001c502521401c60107140c000d01c01900309000b455454021226103e41c496000c02c0c69900810000000708005480d401c603115041100414042806055600c40d20100c0700000d0b9118140c1c0b18114140365030300c01c15810b644910202c1c0b40c1c0f10742e020f01501c10070f8115684061340d82e4610710083e0300040354a9070200c3e062a1441e850100041030042560050300c6503101c540300c032101f400c09030082c0404001d079540551650701071248208410b03140180c403440380800140440c0703240c0382c000614413a0244511101d42d60a0700b0340781c0040c2c06840c042c4086213031a14010092011000b4241d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 385220692 1250 385219442 385219459
    0xe0f060409050609031b010603032007092d050424021e07050708060103020a05120a06050702070503160e0a0e0f01020409090606060302031005010518060316020c010804080d09060b 79
    0x8094400001002d4000e8035991072404651b5003001e617403c8854502005000175015260040000624041001c44145107801d1310400c0e651600000c00b1a2221800078a51841c0e03500b020b0032112840440844105403030724140271501e415a2149012485c104440b000c0c54040421058101000d1341034807180381c00010201c81080e00c0401003a01c2d500420800c030380f28840c500c1c0c04101401c01103101b070b040340e6001d0a4495564104030801c401040c000001d100c280c401d0401c00f0000c10002e0148500844060300545a1107013030100341410548901c0198062050289007004100060310700181c4c400340c40f0500142007981209045e003800b110508070f00c03a0b58004a008918040c40b54000700e1442e101b070348104210b56071407500b41c00360300044800404487e800d003030070009940550003d1082c11260340e0007119074012900007421a0b003081e02c4bc07001092884890508082d01004956003903642400e00f4001482c0565640001e48540c2080440e15612110000c007008000d402426330100300074680003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 385221942 1250 385220692 385220701
    0x12010207050118020306100b04030828030b040f1e0b0a0521010f0608030d0b06040902040801060e0a020f03010303030b1c03080709050f0a061404050a0b0c060a060e0f0604090506 78
    0x3c80d0303008565801e904c01d020f400c0c041103a135176600d0304060031174000065050030030380b440c3c6540c08940c0000e034000480f24914441c9229200c0d0326000c9003010b100580b40000c80e46169030a01c000c668807030384034110b03091070f00c0710f040d0350030056000c039140080d000382010851b980a000403a014901d550310481d08151082d0038410300807803000140c1c04009100e0000c12502c118001c0c201c0075200c05102d0001c4940042000c00e881306a1030300030000051000d02014941656103001c9022a403080e401940581d550b89014000039007640b0307142d60041264001541000c0c0d800380602d095100c180320060502d9643d01d805038158941c00c07505100c081c00f001c1d500001c0003507400c0103400315004648440004900c044045013034a0864201410680050103034800b071820b00006a03004501131484003800d4600744400603440d500c015200300907180c1d0f21444c9495034004200340345010405000c1c0b402080c240030003030014003120b0580c55802400406000b4040c1c0b01c560125005103284071014019004e184100b2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 385223192 1250 385221942 385221971
    0x7080f190e15030402100e030d021e07030206091011011e200a05090118030609030206010b0705100507051303140708030408030a0e15130603110306030c120102070501 73
    0x10a0208201d464800580080c103040003855841e03031080c16112030081c400308015003070004109498510b64105882e40e21a07600000386000c140101560041c0d0204141d21240c040700076103c29101d05407401026918259800110742d13008200b03c031806103900002000c0050302c9440c0c03041d9068000e41c000c02400c088040b00502640e656071440c50464100310040b840150020180c0108103000032031181000700000c41110150700074034219040100691801e920011408000c0d00194419140059884801d00d400390801d01c050b07000c22a4101c040c06003501142c8003040c059501040b0035800245681d450006132128002e048101c2c80d480700244001c810004c0c240c56015070020f5810480300c000c0e564100071035603403085000d40856600140b01c5000c0081c025000c507030084000034001031041003030180c40c0b43c0e550805000d0503001002c0c1c04040007a41d405105441c2c10005070002c60340b551070403a0200b036440c0a8206041e002d4401e80705001090301d000c0d4151010268041c0085c08100806080d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 385224442 1250 385223192 385223227
    0x1030207151a100f0e010302090d080f2107020d0804020418111c0c1202011b060501051e01050307140c0a140f0a0515090102040e0109020a031d0a060207080f 69
    0xd0141002e1503000d80141c4c06840300400400003503503482c05a0141e840110041e41051424642002c5140403a0000074400406071402884160319103803110305003000681c0e0136003840c420313111a540d80028440d400e40d0104d1b144803000c615080c210f15079112880400d000b01405070114846417600c0e0b2004040054400320800c0d4a40d04903005102003050107086e036850f0b180031030014500d0483c40d808102d0b20080c90030b401945401410440328104001c0030b00d0040c071480200c1180d8050340c52005020900c1c00068a000c41000e84405c02c0c810203603800068150301c0003a111070240440000740c0c100e1450520111000380480714295a40745145151040c8041090442c407211b03400352480742d0440e150002025910140c004000b42007007508034074103042c0488081c1400c1255502000041414004828082d00030825034400680d01c00700040028101d500a00103d0403108541d01a24201400082c06a6070340390040707001070350b0f2a0107241c815002d100e4480ba11602101c00b250803622031603e04503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 385225692 1250 385224442 385224491
    0xa1b12140606220515041b0206010e07120b0a0915030501060b07211106010303080609060d030503011a0904050702030702120a05030a0311070c0b1b0c0f0103020715 72
    0x8840d415142c503820040c5004607060081902e441c040084100c44a01c2e0300f0054000301d00005a500c1c00c207280000c602514242c0c8607005000080c0c0c6071071020554104646401000c2c000742100c501e00300740200a200d44401302c81000407684690404078150b84480c00d5000034500d0a00422500c1a550b035a543c2c89403540c801641c1c03e500c0d01c40300281190f10703001141c226991007401e5030b0035140e04428006900d00400519410003c5003400d0300781161040110034040d48c040d840e0f03500d6510304070080100c0701d0341c0148054003601000418000080c0c1110070750b0305450400c84c1c000e40004c03000d009600d9a000307d404040d84141050240888270b030300803009098850003a6440c602e2400d0301e00e5a550790b803e0010004006030b00402c195400c55109034400d03681800c86d000290724150b1130340c03120103a022564010303460031480000c0081e01e100104800c0c2d00c0c00c4240f0005400c104205030002031785030141d8400241416000203412080100182e0701700f8940c0305600041000c0c80b11441c00841c4004040d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 385226942 1250 385225692 385225733
    0x110f071401030501030f260301180b0303090a0e090c030619051806040204050a110c071401030606082d09010e0c0d080d09050f031605011503050a1b12 66
    0x2815080194030a002d60f40c140d0f5007152104166403080d5071164079001a0210860410350031500c0c1c02c40350000d4000542c001e11020120b04460f0742c6080d0058100c0300245013151082c4d000308814552629882c1c400c1007240c24201540d02159210b0125905003a03010799101e1381401030b00208480794080c0e40455054012504041205580f07034503460018000d028648040e950107800010014602a00046c0e4440d4402801180c4c26540c0d101c8c008058200103070b020055040700405109042c2d03032008022030001d00340307420310000d8640b450161008a0140c1034101700030083c041a5000d1036800b1700e11628002942105400b03140000c074441c02401002c803060101d009098a40c074140c5004042c00b00d800b034100300218a8401e5520074100106542d0504a440f07010f40c412000c8190700a0014140e0070000d03080034a61a410792401da400c55500241c3c6e99100c5d11101000e0000ca280019520000c40c1e101d02c84191403007448424688071039080d40714044414040c124041080942403454143c0c0c03a15a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 385228192 1250 385226942 385226969
    0x30f13081506010203040308031003020d050f01051f050d0203010207080a080f092e06030b01080d08010b031b0f0712050910080f0c0a03090605040309150503041110110f07 75
    0x40050601d4000c00daa8281c0141d20500060001c10780c120021a04141e10b00c40c5401c00d10742c1d035400b04041e50302e031640c146c6054003c10a0856015020701030030f030f40401041c5190071050218034900004100c0e50040c0d5014020780c241c03407000c64600b58100e448141e04001000e407100c2c10140c0040043d141158032070640d4a0000106428100000b02c079030b9481c410b40040a07505d40d070fa42241800701225070504841c9a02c49e400000890004640c440c041c2080b14068070403440e1502000d00610300c180c2c491f40703c0c084100700b080400d104424141045442c001086542c48256002c40d40303141c058000064000480780d5180500160844018064001c0075201ca07140b9140481d42500e40d14021541c42c05003e5001000444800c0080003d081d00a1310303050001c0c6803881a00c2e1a0100c6404850490114000c1c1105000d4044e0241c0b60004c64009882d00d140b95181aa6500c0242c50320b20b0b0902d4024032091a500b00c0c2c050041080d00310010120b003c03500d10700c4024409580d17507402071040c40c6520994 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 385229442 1250 385228192 385228213
    0x10312030e03070605190e030405030c031614190803070605090a21050705010f0b03013204080c01050f07081303020303010e09150109020901030b062a030f1308 70
    0x81c1c05558200081d12020b542024415100e181c06810000c1204030940c5402058400182551182420100c50100156100c41c01c1005151504041c1d00c0030b60b100b5444080c64020b0010030801440945040003100028038061202141514100b6000c1440e0030301090000704068800002a00700c2901452044c4002d4454081040d11a01c100101421200088800041c81030a01d4841003560000b482c00074502455070301c440b82110800d03441e88102c5921040f40ca001440c00340500081e203036914001010148000541d00c070cc0d07607840382800e51302001c404009400c6c00740c0c6000f61010401080001c2c4010714006140c7d40c001d501c1107421078007140c2840c2c08145074503410722010100640c143c00071423543c0d003070110b409901c0c0402040120244030b4054801c11860340b1000c018020541c01c4c4004d80c8604807200094256422850a58001e010500082e5a2203401c1d40b082c460020110101904030303401d80d2002070a51090040c445450200090448001034100d080103045071483d105403801c0e07090 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 385230692 1250 385229442 385229447
    0x150311091308070209060102030904150e1605180f060f0304170a090611011d0706170606040b07030908010c09050a0503010c050f1303020a03060e0d03050403090605090a0f0e010312 79
    0x24100010344510b00c140424001801e00317001c000d4208005004990511014400142c03e9407a549000140e040c5043c8003005661000003000e5002006a098510306814551005146004000c07000a00c0c41c9460f4011060782c403180710303800c4080c1c00905199500e00c0c0b001c41c1c8030700690042d5401c50b001d07205070000d10034842094096481c2c0c11640e035640f05040f413070445c0c21078441c610480900c0155590b070304001c080110070b010300e940144803240503089041ca404000b40841c0c0525030b000c498544e0380010400103a41d08030488054401010301c20b501d4031601e00701110162243d8108110540ca4044400c681542140b050021280e04888405065444200349400c2c0c4800c4103420000c1601441000c2062100401405482442c684032109a50341d0760005400290325600645030760307a03201d19024500405005020450f45242014003c5003802c3d94010040071140c400d8008001000c20125400c0c0d4401e20740078000c00160310300c5a42035488141550f518a005c1c0f104803030000c10901008440c50 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 385231942 1250 385230692 385230721
    0x1d090c1b0d05030105010e060d0c020106031b03050a08031807090605030c040b090109091502121e1303080907050901090e010c080f04171b0a02030c0303090a150315031109 75
    0x11a140d0b07545086074680f0005481d4000c134500030703982c8001c0601c8802c524044500c03d0038100c00c20340d0700119240c0d18506013002800b0484d00c10f02c0401945aa041c0085400081c800c18000d5000415540d283d03141c6191005000c012a9521654020104c1c0040d202031240c01c50019204101c0a4030394074000e600400c81120700b01c4003141c0d0041400c40c0100910191507019007806405511402d1880152003640004c0f40d1054008500745c0c1f0070502130141c402074800c100e1281f48010104101d0b14144a064180d44e002c816030b0040812500034001218420144503001c01054050810796203561521188409000c0c03544090491f5071030122003000e11480303800703041c1c040c1c3c2d0300312521205038856446e00200803103140010120950104010307440d940d1042e085442d030f0141900900b003188160710416090103011032034503100e68000e120000440d40d40c000306008540b2104004442c8620240c070607000341496090558140c45c0c506800801e2003a450281012070301c0403100b1040c560380c6c0c50713030321070860 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 385233192 1250 385231942 385231963
    0x10212010909020315040308071e02100b060c012c06100b0d0b0d060e06010503120a03021b07030b090f03070c030204050423070315050402010503071d090c1b 69
    0x41401000848080d602c5500e080c0d00140c04e80d041c10300722013103840180006480880014601e14100125a070f4400c03241c0202c60030074400781c8200420035030700070340d110b450b45a03c403c1c042d50b896640080350345040460b81040c40c144020b001007c042088010310029048a00c0c5e680c0c0000f900305d0f07070000008a82c8610604100d21403251990410500d41d0041d0441c1c1d0b18045490754074a5801e80d50b40c0c13280008400c15100c0e900c00304040c00c07a01201030501d031042c2d000074080d5012011401d00b44810303100355031845485290058130707400c1c1007a01e02d0b17403e000014000c929000f40300d00401400307808020b0b0340c41444d09104403940d05084401d0705549125040020740301c0d600b414002e000501d002e410494010b030203181c2c47c0b050090003188118102c0110700c0031240c039510000003041045125041e4a1084c10000400c00c100d02d0190000b800510000780840304110004038840340011001010703003a10400035103040c01524245901c01c0456100e01c041c140c1c0714940354914081c0d00710018203030111 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 385234442 1250 385233192 385233217
    0x609060f1a210a060e25080105030c01031a0603090a0b0123101e1211030f0109090816060b04110304021008070302070f0813210f021c0b04030806030102 67
    0xb624010361640c1401d20043d100c0f00241c1e071200c1000443c0030f40002c19900868001e0b0000d8084a51007150801c811000c12040c4140550b1400410441d0b9001ca0701c2540c4038804e00300810040800701400344003001ca1002103610260120030700c4626800007e000c526940f15142e0344116076200c020740301d10320420302501c0102916110a00000f410320780d0070302c0c3c4c00c1c050038100009440c8041d9800f03614410000414000034100f6143c021012040b40207828807034401041c090f10350305000000c0e0f40d040718140685800e60b921100c0c2c003010803906000f104c00e98049160340016940042c40d014000c1c000c3c802e50148070f1070504624010b016040c5c81203d0103030745e00070542a030303401c0c4a0034265400040201018207044c5d0c24000640840c1000740c140e8139142c0b042d00f00a5481e00380910001302e80301a5004800480c145d444800c0c03041100710f02c004c2030039030440d5180090812510000d800260040c02441c0798548860a01c420004039403241402240310b40c0ba4098240d45440c1814200c3c041ea1454452 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 385235692 1250 385234442 385234477
    0x30070f050703022d0607061416030507030b0303030115050705030f03090c1002060a0b0a0b07030804170703170c1b01020306090c0307020309090613050103031116051e040609060f1a 79
    0x1324544600107000329440348101003640c1f004040d503400c20850880f0240c8010301c1203082c41f04106d81c5882110703400919030804010001c241400b0076a1f0f17010500809620318031803286490780c20b0181003902c03c140d070b03c40c08a90b65070303040200b268441d4000341e0310340f100c0c1d00c01c01c8039130009494015103409110010342d000304001c1c1d4075502ca4601030030488500c80d4003d00c604001080c05e03001200200740c0039004c0c1e00c0350b41044c101403500105501d12441c6031041c200f402d00030130002981c0030004000c2c443d00405014070f01e03126410350000390300c0f41c10380f503014192403251200701380c05064000d903200d0001100d1901c21983d980031514030a200c02c44200006030410004e084c46071601c2c81145030441000303804600c00e80e01c0a0784c503608940017030300300381e02080c00b2900ba482c1198040215a0000302c0e6a8030200e28240380c07a0205010302d046000d04160407401d1221211603403102c0d070010004040c414001d2017299520455080c80040501400140e2980c440d0420152800c0c0c03c100c48001000c1c1c4613811 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 385236942 1250 385235692 385235779
    0x30306010c06090f020307060e0306130f0807030207050405130201030507180b0703110a080909010f1a030a090213020405010e0604030206030f0c0708191130070f05070302 75
    0x61200300c1c0300711902081181c4c030601588080091101802180c0c8030718504000725010940b800c0801000300b09081d00390b19640000421030100c2c01c1280c0c5e4000700c0e084d29400f09180990609090341c200c190020b1030b08082001d4000342d20342d000f2165001707803010001511003480c100c034480d80c5c0007421180070390001020004000d0a1004011060191134104800201812781500344421074100707441007180461030944c94901075195900410603d60609016480c05822401c4584d401240080c1c0d04004000a44000c40750b400803000c00794002c00764184140204a01e01c000d4010340074941c001803505640d1459800e26030304583c242c2e071300200f280341507544809056050307410050481101d94018800c41c4001000c140181803020055040b904004082d440c0c000c11003c04241c90b6501640300380300031090700c0d41035403130000e8040180e281100c0d8103c1009400c101c1d40325104005050940d8044400b09000300410400c055030310854031181140d4900c2c00b03215900c06080c05d41d920010030200c00a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 385238192 1250 385236942 385236953
    0x12c03120103080d0b0d0c031b03112106250914040b040b0d151415010c03020705060406090e0115020601060305060a0512061f15050f040b0406020706020f030306010c 73
    0x1d042e1321810100c04150340c544031001c100300c000d0340b90f822922120f60703031418010040d5000070080b0041440080d01106072550b16001c41c0c02e10351201b45801048009000c0103c0010171403010320703a10300c0404490807070401806103000850340942810080c1c1c400c2200c40740c001d20886032403040b200d01c807000c00140009203003040028a11030b040c195015a880304040000c0e01c1e103806403860680a084120070002541d81d00034181c900900c0003034039003900e0208000d080b981114440180c04d50a04c1c102981c41c1e001d01d401e074604803607500129400711011500098050f44614800b003581c124040c00384499070707135080c1302060100f0b0f80500400368100000511900b482588801e0340a10020103048138180e5480105048079421014024150004010001d1400300800c0501084590005d5011032500e414142130003800210300c03560410400040000011109905880261000c054220741d80e5694900c0a551100c4511803d000f50007402401c0c3e1840c2004000e8034854181078450b5041071040765150b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 385239442 1250 385238192 385238197
    0xd031706011121040e01080703050607030b0112020315061c0b06070b0117070b0412050c09040203120a0203120f041b031109070507050d0315080a020d0308060111012c0312010308 78
    0x1201c580c80f5003400700240e10000414040d00900410001c0d2199500794207041e402d11400504000a050401010305d5480e64480210120011302e030000580329200c0c00310480b0f903c00700000040c0d000c00007080c08a100854507800704c1c012483c0d0030b41084410003c400380105400340410252250004000410040e0200340d11503c2c41d00c40f01c42071b0303019251680c2a1000c0760700726402488880d01000d012204100d410040041040780c121000c500c0c0d882c19500191b610b00c5402403190030401d000c40e0307240101c0e008005447c81c602c2080040800743c03809850710300040d041141d040e10318441d005208000c88846014141c240c82e003144910054408c12402d1000303c100150051003008400c002d003501141d000c4c0b142095001072654007041207000a07140c0701e514160742c0c0041a079504140340d880010307917504041d0703408240d0604010000e0303910140140c61010030b0303082c17510295091200030400070b201c00c44402d150380c0494061200007a24254819900e00600074a443e00600500051007c5900b0501 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 385240692 1250 385239442 385239493
    0x30d05090a0b100e0105045f061c110112020a030e0601060e010210050c12010b09152a0313061d060a1704050c0d0317060111 55
    0x4507559000d40d5a00da0103802000c882c1c0b903007014142c03001440382412180e11907006103400c0310240318010541440c15101c5505128040300000440c4102c9030f85c0c50803201e40c0681001c60305a41040724009150800500c00c5400352041c0c0d01c00b4800095030310710340000065171103e04400d080c8082c500c29070319960425100c3d13040606100300055107181c2c1c0d10300e5000400c0c0d03100250341d01251803401404424949581a0000703c21f0150842e160642a41e00141004110202100108454580c80d40010061040d80d400703200e42d04481002181d44800c56000307203520b910685000c950a540c102c1640c509028580385c2084186c58504481c02070084180c02044149414080d2858101d44450060203034080344c0c0603601285464100f501a01c86c141405800b04038140d415a1402d0350326900282240c40035003054141c09a00d001203000d100d41041044c3c0c21000c05410138117050041d040141500c44d00351101500f203424000051265481001070b01007403100d1400030030004000c0400c80c21200d2400702c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 385241942 1250 385240692 385240711
    0x130e011b050711150a17010803030106020a0809040906091b06180501031a06041403060a020703021203180703111207050a06140c0114070207140906210a03050301050a060e03030d05 79
    0x2884d80c10307006040007000030b84016110300980c0d41c450380d0f0340d07205041c050b0300c60300040c1c005100400125030041090700205522408040d915640d0b000060014038100b14080c003042d29142d42d4200704400c664190001c1881c0e8032a5484040d0346030402c9408121603030941a030070740c0c0310104114a5010703410180d0200811003540110103445004a0610b4000d079000d07060703020203090381e28140d0809000194009017042030544ca4070200d41c40c0070303643d9010f501074081d0840300080007981c0c1d0041003441510b1030310301c403042d146034607074a00b0503540341c032035106501c4d00c2261100014042c103c030004480b4100e40000d080e107903185181500c2503d00400d00c2403503003ea8401001300300d000000038490004001c0d02d00c82001c02d5810301c080c000389030000c241c201140d42c01007a00c0100c80d030340ea90b007a060b80c080011150440b00c0310780811100a4410308161259907442118014420107400801450584600781e80968a86554080840e000840094641c0d0560410803843e224820544c101c650322a20381c5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 385243192 1250 385241942 385241959
    0xc0204020d09060f0510090504110f01170c0d050603011a041107060f05150d03020c0f0a090c0f1d0a030609060608120d0c030507050a0c0c05130e011b050711 69
    0x907203c140030354905400c00340c3c2056888041000c8440d1500039070f40038150031601000280750a66a01402c0c203c031100c1d491181c03001a4184400c1d82c841c05100f02900302c50248201c0c6800d00300c0c00740c10980c00004071050114201030008000b41014030900003540c9010014005854100c1c0a110050010300c2911101da44100001804180c8600580b600203004010000350b516040d0590242c82856852041c807401c2480c0c0000c010070390000710021210005c94481a8484a840c0099600c04003035001c510158103054111134000d8003e4107003c4080001c0d100c0c220782c181049000b03650008110101c44d1320505c444c00a0010030040c1c1d000c241d81380d116800c001035150311506a245044003140702600d0000e0300040b16000300c0154080c80c580c140c11414240494201684003030142c0c05681d030820108904040e0810038000c04000500c010a0050428003030b54403203208103005014000e1515000d9070030039050b5105140c8511b001110328019648590800072943d554155041000152030f0303011118 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 385244442 1250 385243192 385243211
    0x712110c030a050c090601031e0b04021b0a03171e0604020408030712030e030a0e01030f0f0c0f090b0903030403120918060312020c030606010e030a150e070e070c0204020d 75
    0x42001c0c840c030030f00880040110000c02405c014006500401c4141014207140d1442004449079248401c20740d42c0800104031000b100001c100240909492944894a040907000e842103002c2820a06a4000c2c0d892561f5541c03403c08035440c0c0781040d1240b4591411500f03e202804076055461130308404000e01c054980380d501c00c001c80c0b458024407000e640424510307114811089e0144a1903400d030005d40055410101c05c094007a00d54000071840c0c0b4145620307402690101c51362680050318050416800700030b500545c03000100301c00501d08483c004107060348000b1039100701d004c2c1075a000960040c0110320300f609695a81c141c82038414010f01c00e0184503880030540501c82d06003250b1514140700006219460360500090800c0c80c00b4691041d500908401c1000761400304009510a1081c20b0280c80c4070a5040428070700050000050121109503d0003424000710b600400c1840c0c00c1e00003200d01c440e449400c01041e0320030070380c1d50340e0118080b1402100141041c0d0081e01400c8105440010076404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 385245692 1250 385244442 385244449
    0x32a0204020a0201060e07170c0a180312030b01020f122101270c09051e04021204060c1d22020d090606081203040f080702031c0f050712110c 62
    0x42c0d030324040035035160f031014400607151062681d0b00c604640307013441f420b11031100c110010442c05019144109800114001c2c0d19010b0f800c091100f000580c080b443c2550359080800030007005840c03520001e414008034010541c40010b2a5240b10000e0000e0402000f0440004ed09603000d00c2c08a6240f0b6541c29801c620143c0e0082514002d00d07003036651000040d41003200c00c42c640b4000e42c0b01320b00e0074940b155240009900c40c440c0002d8907425200c0105669410722200712101d03022403400c0c0d009000040c1071703203071400b01002240203501c1800103104c01005103105a4030b44c080400c0080c03040c11484584061864016080c502841146c0a0000201104040c0000740d9004861940c903030354444940d4810030030f02e03209202c020500750000d05807442c50420380040d40c4c0302c040c1015106180b61411181403040200c111480141d00400301c2d04c403070080782d010740c0d500c090312121036000c100242d00c84a45c0c180140201d03203100d0761081504942e038a00c40400d46580035007007035624103482544249541500c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 385246942 1250 385245692 385245697
    0x140f03030403200607080904110f0a021005090708150c1303141203060d02060c070b040303120b010f0c0201050a020109120929040303050f130b03040b06040504032a020402 75
    0x41c000c0301c00c8403142411400401821280000d90f0b4028042085640c1c0802c59403c1610030940381100c0109210703030001129502ca014802052802940004121603c0c2d50009580603501a41c8141800303240e03610400680c4402da076115240e0f00750010030b004207120341c8807000b25034440401e4458604004200f441c1c00e6001000d40c01c00c807480084d480c80610001c60802c00080320b00c0d007503611945185400d40200b45401c0312041c0007030094001103074010001c44248801c1c0301502c0d40a040700d443c0e6680381001005082084505041a85031600061681d44501010161150b154036500c107a40f03802e500444441e40202000c0c01103540e903801e0500019050311a0004890301aa00ca41207d8245103036100100c06510203d1048851018500b41c01042001510704580d058201545ca8007150000507101780f180740e20242005491340008100581203101560145015900c03005143d628a000d100403508180c07005000b25407680e003c840741115607484081441c011603071020068179036501040c00c1e038 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 385248192 1250 385246942 385246949
    0x4051314070914030105040c0501120609020a02070617130b041e030e040e01050609010603021b1c0306060e21010b03031602011b0f08091c0b010608130507140f030304 73
    0x5481c1107410010b07680f510b507001020240840003041141855034801c0e9403c0310300c1c130800b4188649540761144401e072030741c880d5000b001403000542d6904800301d4001d4880003903000750320100f10621f43c0c00d0392404141543c14418528206020b00410710390319224004000100304580101d80210380442c0b080e40314504c0200306200740c58406080c49088100025622214042d8500380c0c5003004100441e41c80550b83c2c0c2c1140d4641c140144c5d0303094002c43c001c540c48032150701e500351407081403d134020704401d85030f08120800e1603a03000c11040751984011a422000e04146680c030190500600d251010130303030302451108440c40000114104154007007800c6420064a1483c0e0211800c1d0301829560040e044030303000080a4840351036064607554203c4000d421103400340503440d0200303203101e00762102d030402e0380140359014940d21303951118500101420000d004900c0080c0c500008100404d105450101007540e205000e088884e0a2074900d007128510070007187c1d0310000c0b800215141d501c0c140000e00c0034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 385249442 1250 385248192 385248197
    0x609050f0402250b0c0705031209070e010b0429030412030f090807060f02162013020714032b060506030c180609091302030a0c1404060510050405131407 67
    0x3510f090f81007141d101340d8000c10b144490041001a0170005d41c0100c1220000c0742c2000b0362500a4032046846480c015998200c20310080688002103400201e070300181c003c6801c010b0342d80e2400c10034a410a03070b44041468004031710b40c00c2030000c00c4c001a00c0c8141106031900b50310340000d5100720b86007850709440c5400300c16154450001944070a01105006000300c10580c02e4040d844c200005410414600c00741802405a100c5a08900d00c901c1d00f0101c10014160010a00109044c2a1052400075030002400b100c0d030140700d04401c0f440c6240801511066081104100c5032a015400c94101d20424007800c0744849a03200300114491742d4682c0598012020001c180703407518000780710941d0708452240d92030f104542c140210354003075039505d00490303101b00701480707070540e448081c03000ca8a4640802e40043c580848002c01050302440010303203802c41765084070284411552001481203200c002481c540c002070b4100814480ea0130700c11070b041007140c404100051441001c900d26aa00a030a0307419400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 385250692 1250 385249442 385249507
    0x10e0a0c1d0102151617071b0809090a0203070e03060c0d0c03020405030f0d180e0c09032d190804061b060c050d06050415091e0218011106010609050f0402 68
    0x2103941d03009481c6031401100031041056410301f044003501c0174030290f05040401c103a100348241045022020754140180c090241d040c1c42c10201207074006504201c450800051400c4460719803440e001036440d0240c80200a00c80c5010505508040609407011105c0141a020030001400e03403402c0115410580b1000050941040041c00c0113101d90395030b06600d492290554400c0c080e05035201740f06c03504610400700d01c03a0b03030320301400200b41810491074507a80e42d603002030004100da40c410036000e508a446502030310208148454040501c5510038009080d4890900040c050180030b2082c5032000d001600444150f070016948507015a04591022800074101241c1110b510790701c1c1c0502070240000319002e112a80c2e5800e00300c010b0355071a2248003071140d00d8070005108144140d1240154030b5200d0700a55079540110708000084e900103080d24001519000e62524207031002c610380e41030340c42ca0741c0c9000f2024900010461045812880542e205034200404c0c1200b000301c58041240b00b080300e10300d00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 385251798 1106 385250692 385250731
    0x4080601090b121f0f110702191a0c0c06071109041115121501050a0f0e0d0302100606140403021509030307030503010e0a0c1d010215 59
    0x60041c0a1130f107041c60100c1c50b10003021444484128140a19160f600120080301c3c0f0541410500341c6003408904014039080800c0001d44c200118405880c80c3c60f11070810b49020907000050465000150302d0200180a000708581c002d000c449050130240b00c1d484a50321384090390b50441c0300b600080c000804002c403201c00f41c410701402034200314030013510108c0c042d02c2d9480090288070007614800018030442c05c1121044030584d069640500702040100290303800c1b03010018000a100007401e40140948400180141c1580240d004160f803c640c812207004541d000d82141081140c261440c440c0b6041c41001c40701120342c1660341d8000703512003451000050254124185d0715020000c0c0b81c1081c503074040042c5060f620366120300520b60b100c0036000001c4a03100346c25400807500094050b0704101c0d01e0314103100c40c4041070040e21480781607400b4403900d580341203c5183d0584e0681d049103 = true := by decide +kernel

theorem cover : BRFrame.Cov 385071942 385251798 := by
  have h0 := BRFrame.cov_init 385071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 385071942 ≤ n) (h2 : n < 385251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
