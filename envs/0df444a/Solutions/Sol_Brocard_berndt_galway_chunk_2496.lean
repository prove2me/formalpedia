-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2496
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:53:03.669979+00:00
-- url     : https://prove2.me/submissions/a5dee208-2e3b-4a20-9993-ff97389f93fb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 448741007 ≤ n < 448920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 448742257 1250 448741007 448741021
    0x5010501091502030f031e0702060f0108010908041503060806010305150705090105030406090602040504020c1c020c010f120609090f060c11030405040207083c0f04051002250608 78
    0x700e0104084000f5030010312441c03440d091400059503001c042003010300ea0a62181002c0210700c10309640090042c0c210744108079481c1c8030000c40500401010000300804d05160f201d03808240035a016002582720800c0c1405030341440394102001400c4807805450140d6907a1504070707902c210464000102000240010740d000340207e0940e8141c5c00180c440302d1447c0c0d503558400004000b43d0408440083d401d20000c030341500d851014000703005000000380f128044000051900c140312205d24411035001001840c00c59130700100211880c1c009040131098401c46550240103046503400884083e8030744000c0c00c05025a820300a0081070081000300000e005440e01158028003104c5840c0032a4030800003041641010b80c01052458060b034140340c204050b500a200545900410345000340c94900441d03445120740c00b42d00700010041000d85840c1000c140107059030b0b13000d240f091a10445081e41f6202690b070091000705003401c200704c0f0031182c903040342981c5500d440c11801400300048010307000440c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 448743507 1250 448742257 448742279
    0xa0602101b080402010507050a05030307050705070b0309030a0c060b0907050a0e0f01090b0a1b050606010206130209041101020a140f0f0114041101050d090b010510020d0917150a0501050109 83
    0x3a0607469881c0d40e8943e82d15001541c0c0c17988241030850707061041c0442200864800e0001c0d50042003560344295807280b03035040091400c980382d0040e04d40c0103410028813003031050000480e0f8405a49081c80340440e240c50801710001e1005801030350f0000218070400c810715034440000d10242d4229141c0d455541452420b01250280d0302c4089404141010780c11702030011104041e102e050801c0c9088180c0c0c81005021070000080408101c81c254041400e00203c0d40c0c051003a0782d8000c00c4500394a0380d100c030030740005501c0340d0042e1000c1c181080500e1517240d264828094041e000f600504c55142c0461190526503440229201c81c0102e1f0007540e1a00c4036079075040c003902d02041e50321480520183c82e543c591900a03c00d00032002c0c1030000400002001c50050301a281041d03001d403a40d034507113600d4030041c041d0522003410280219003203c40310700c1e0282c0e0030041e104140c3e03244103254821115014040791070305401090108180d00003804114030040b494025605990080c0c0e64240c5140d0b98403400b201c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 448744757 1250 448743507 448743551
    0x92004060f0f02060f011a0d06080a0b01080a0f06150b03091b030705031c03021e030114120d0809011113080d0206010b0a1b06060603090c170a060506040b0a060210 72
    0x5c0f2841d180d40040001e040c48807201241110905142450b08140d181e00008a9425900040068010039251000e112003841010f00402e020009419019281d94500c0c84e0800c1280e00200203a03510144200c03007240300140007015004100301d440d6641031400901d561820100081c040b007002503015104079042c0803c28000301e640c0903006100114100304c0101000b00040703681c0c0100b507800d03c004d0902c1031121100f0000a45407508840d541c2d410020100b0910b442e2811081c0110b0b094510640004000075249001019924242d0032940340c1290b41c2d4058014200764600011740441e102c1d00303074102c4040380021203d40b0800c030780e05650301c10000e07610f0340824031076010700c00820310480302018007511160444514841c00703220103080701e550f9002280d080b6003113000082d554480b000300300700000b5651405810364103400c1c29034003e4064540d64520b582032000304403030340311001b02e103054030b031908000451100101442100354071008029510304811038241503043c14100d11140340c841c0e18444203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 448746007 1250 448744757 448744771
    0x1b020a030b2505161e0305190e0a060503060109032003060a0902030c010c0f0512030a0f0b090a110c15061005030114091801050115090501050306030304092004060f0f0206 75
    0x160030229103546040e0403082e04001030315403003010095405c0b400113020401c0c50540c4a0303207446881d5104d040d1607401000d040c840d02d0050009604a08000759645c000310000c558003464100da481c0c0c0c0d40360048038656201d500c001c2c400c2c031b41801014411102a1040301030a0001d030b0440d0302e00d9840d040c0640580d404548082e4068001c2901020a541303d201904a850b00801d42100c1d013a070b00b503a0341480c1000f0310081c10007411011051201035089801490701e4807603e41400d1004500c0c82c00000d854000145c00e4100203540c695080301e84504880075540c02c095414240c82c400340c860000b901c078880003141c202d8800d00c0d144460214050003001039905032103080404100801e404401e000c2c0d1610040d003088800415075642040c038007024010b0360b01810303d01611140030304a40c2000f510030023107500280d05020084c010049507407000030580b012500d4840021510704044c04041c0f4000344041c07c0c80443c50070000700410b40c40d030040380d00740c0d0304400e540d640c60711060400c134200c1c0c461100352030301 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 448747257 1250 448746007 448746017
    0xd060f09201222050c010e1012271406060d0f060915050907030c06090e0a0c0e060a02071e03030f030b270a0609020f0a1b020a030b25 59
    0x1028001e002c50b07402540141c03600c034181032005a80440310040c5010400884481e844044075140c01c0d42e01805130114150195620f850700c6908504c06400052006042180740380d4800ca1000c02d0300e001c5950101c40c00182e9014038054500d814140c422060204120078244544c80104003c0e00b45175040303041043d00500080854401e9940c1e00c0c029000400741995202c0c00c1103403c540800a522a007406845108001c1c082c2a1441c81d004420440a501080c20f005036000c0c2000100288800c4070740c00bc034000000541c0c0c00d03445005482240703602131080d41114012650760b601035000580b203800d950040341042e000000500400282016030300000300002c40e5804038003d400d009400c00000d61000170100b00198448404441664540041c540e1002055405010681d1540e11134903000d0800c0300310941c41d11810400e250850700c6070080740c0b010800c03e00314107010590039041c21803605c3d40c000c0c0445055540c07410b0801c01000d00f51032084a8109074400050400d03d118800c49406500f5103503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 448748507 1250 448747257 448747267
    0x27041b0614070f0804090504020f010305090309220c0f080a091502071a15040b0301050403210e0102041205191211010e0105070804030810050f1002030d060f0920 71
    0x1800415400480045650110101045001604c4100500060700d1400000109803416004003c80c8003494030205060515000c1031004042002c0201d0710f1071401643c01c1c541c0c1341510003110120800c280c8540030050310303099007500e03015845400003640710500d41e162869500c9013202082103d1202c1030040c40d00240b030380c412406e900c03d85c01800d10b04c0d018800c01c0d003034004403454015986504a480c0c0e420303650901038503c441d00c1c0a2140c0803008809600800941c80c0541d000382854a1800c849804081035040a2400b6808e540002d10a01e0241000b551215a24100c8821444200310b00f01e07000d000e0354403580d8480c00c44a24106180d90880b8100380c08005000007550108446001c4800c10f540ba0751842d80062424050139010303802c940c0e07650089150904000386440070240c0505900c00310035004001550b200800c04007038a6045461422410300c0d10401c2e49184204580d4101007403c0100020303810140004a004a034064030b028042c6808054240709600c0e00020014150901848 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 448749757 1250 448748507 448748537
    0x702030c03071212060902030702150f070e0310020d0903121406040f0204090e1e120702060901030204030203010c0c020307150206011712040f1a03090a020f27041b06 73
    0xc3c541a010098148030300c3c102c1e440c1c4103c0c41910404c0c4c004078403c6800006101c0090342c100000045220a42d940f66401d04010405034541d00025003c4010010030940401260b9401d011140075000c0e41740d021540c808000e2544030240034aa401900414118080c00d40c144020340039181d20501106450522582d501c000c00005148054140304625030a000c081210103147c0300702e1588081440c018059414090030102880700013184122032500f05070040000700c0f600c2030030740f05c90300d5045904988484030a001200213016a42c4080c0d455800c040c10049e5a40d0814440c1e2001d9000760b0568025540b22582070814032145104000140d106e07030010070016052150718604c0254160075691074045d55002e8190a8115070030207003805040362402c201c5031503a00d0b0442c2030742c092801b016095181c00c2103640d444003a24034029020340809030305c1d20025074403240030341e85010b00100610b00b2a50075148100c2e00007400c640c1122064416003403414030b4514010700c501141c46aa07079084054140e0301c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 448751007 1250 448749757 448749773
    0x604050c01031a10020c03030f090f060a1704170418050f0907180204150908070e19021b010c20061b18030601030809041505060301261501030b0702030c0307 69
    0x100440110301a0211041b02554180001c140e083c002200d455100d0030400c003040301044c46c22441c0381c0715913400c01c50001c040750000702e903404200070300100965035a00c604040340c1c02540d240031510741c0e4500150124094104054080b1a0034500008100079070314a20005440d01c1f09640c80850ad50128000304801821640c800b806c0c880a0800542488ea4804c01903180d10b541034401e60100d081d902c424000c0c102e007044200000c1c0a900780c0e10b201801e112030441709429013909000c4210380c000500546943d5440100784810f00480000c100fa0060580001c0c0014441c0f0181a655048441860140309002802d10b0040c20140300e510300c003111140d24190f080e4440f9020700c00000c00d04080c03211550b0244141c50085000d450625561350340c4404001c2111460b2043d802c00441c00c500c140040c3c0c8820044da4152001e103214443c00ea021849143d000c00142147d05e03405200307103a1507030030f000b24140b900da04880c8240f52245068031580820790b02ca024020648101f0390082c070007400461029 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 448752257 1250 448751007 448751029
    0x2906030601120215121621020a05070f05030301050120190f050d090e07030216031101060503011514062b27050c01050405030c0f0406050904050604050c01031a 70
    0x904101c16074031284d1107500941c001c0860a07501c1d0100b44100b0060b02c6607001d80d0400c940080c5410301c07011490a091040b203070190319000500542c003003944d8014a014104665119801482e41c00300e2035128034199580386d00900460f0b0000e2150362805080c0403005030076070113500e400400352004016030303110059400c0380450256104115814045d000c01c0d4113011201f1400100e07910702801d42d080c40001c9030b200001820701820184100702c4110510b80d810414a109035152804903985a0048945130141206401031545546403042a2454101c01504101220616102c02e4200783d00c020400649000c1c410008141044002c3c0c41a40d02d1402c0301d00d10a207524010001030b1402c60700724110884ac0f40e0610f98032611052039101d10a01c9001c01c000e0515031003d1811510342424140031a40701c0560364903060045e03881003102942603403a900302c00080e210143c40310485140c42d042543d0b807950306030740a481d540900f61003811294820f00400c600003100480c40b17440040140c06104500c120 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 448753507 1250 448752257 448752259
    0x604030b06010c0f0804033f051e1801090b04140402040e0103030c0209060f3303040f0c080c01050322080307030906050f0f0c0d0207020a0329060306011202 69
    0xd151030703803c0000c0c8024044a61940102011a1507908615041080c48425070000020b160300700c004682c084001d80e00714244d070b2250361500c080044411410b60300c5004420351050242c80c0f0a80385842d0102c588080d00303c6804c4040c045604c00280f40065070401100d0242080e1440100800e0180c0c0c02c0400740c031060428060310051402e40e0b20315a0710700b80d40081c0c004a0010f050160414150b01d08038880641000d01100c0b140002400c2c800001c84401c40c0400302000c0082c140f8001000f100c2c6071070901c2c40c090700301c01465076030700c0c00740b60549075002071301c608590120300201c005c12203290004982001a40684034185140c9410240c4003481c49005005950b60340103401c4034001a1001010b980a85940d40703000c03030100301c075191010540718010215030102e1030354810442c82c2044540216080001c00317200f0380e520241c1e10742d000003034402c0450194000745042000420840101c0b48c0f1521601c18418262000d40910340c82c0c0d0300100140e407665850b9024000500007a00d081c025400d280e84 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 448754757 1250 448753507 448753517
    0x2310f05010c14030f0403031106101a09190501080903190e0f0d0b011503020c15040c0e010608010914070c020103020a090f12030801060c0302060f15060304060b0a140604030b0601 79
    0x3c45000c18950780c041d003412400d03641d0106080082580094142c01d403c3c5200d0301420041c42c0001840e14024154421000400c80c918120740205c07040000f22030343c0c0300010706240e0036041401d4018081c860a88101d07400900c424000032800c48020080d140c00c110744044941400d8500301040b1001e0b0480881a68401c00400c04c500b8295221120410a948141011030b41585810a66005068a000204c06041c010444c1c500844004181d002d80d4450f0030441415645440c18030303040911094004007122007101002041c001d8000010a048822511003842140e80d803100e00b491503c02600c00b000031500081284c2c00540c00f90f0081d04035908149400c0510b00c0c1d071400c80801400850307218810036411040c102c02459484034080307000d40314a0601003064041c6640080d40c40000500d80303004110a4004905604074526403482d81440040480e03441c3c0c106030038104000d001610406126100803000001c1c041c805802c00419203800403c41303410585076489131070342c1d00740040c14141000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 448756007 1250 448754757 448754783
    0x9071205090c10031103040b0a0e06010b030603010b0a0501021507050c0703061d07050a0b07030309060e0d110c010c030513030602070f17090901030f02030c030102310f05010c 77
    0x101034452188255003600c010950b02600380c082c85441030380000c00c0c108250503e040001040c40c21012030303420613800f00b07580c11190307200840318000b05500c00d0581c2081c0078a600002e01750308003001440c000d40c4120002c201d0100d0000030010310b110b052080c1405600048820050409035840300f44d0f11200c10f0900c03903c0c01c841062958140101e64008403102660b400000d40e00010380c007800903186412034002d0103090b0030240000c80c155800d02c17800c4540c41d000200070301018880c1e00290080d660041c418004140060341d059155001100c0440000d5103000c61058492800610511204010b07100c110755201951402c6640758400090724030342014144000001402c2031006052450181c0102134400711145010495102e100103003071400d031018000908240c2d03407a0049811a40d2103c00304540d113400e80301203030604600d190959490751000c41c1e0746425900f14250410948858200108000940205030301808440c6c0104220385040d101b05200c55401119061569070107680c101000b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 448757257 1250 448756007 448756037
    0x306030109050d02030c07080105060d02100203040b0a030902030c01020d0f1b050f030c1c02030a031a04051906050103090b07030c18080d0e120a08210f060f1008060907 74
    0x4140f50110700b0059000248006400400b4801e2801174000d0303900a124a0518100161110420900c0a449080d4822484240c10700030000caa00400002d10309584440074080c0190003030140c11000e078000e0052080d82c0c01258804200a45905220744410700400000c04040314042041100d00d20b5a980720b009003004560200300000c4180c2c2c4c008001d596030228110100d04140700162400038a201d602d107260b07005078003c800e50b21058001e140000724030719908401c0c40e0a02d40c100115401c0f6103400b05004e448401209816420403904d403050264641e01c1004404035004503201400e209528404649001d00c640c200300100c01080c43d00c2d0100e50140c5e00303d19040740d0300b0352004207a6401070b500007000a030045000406d054040381c206071a000040107681e203070400604020610b5400207001014680001310560510302c1030310581d511403915508000e1f406800303a0380703140b140030080101c1005140078460400e00e44c409a4076541c081d2038000074407030740400251480c1c0034004c0c0c005415041d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 448758507 1250 448757257 448757263
    0x70b130503120c010b0904050c0411041226090a031407030506090f060c0309060a24030506010e0109090510020f07060f051008010c0918060803040308030f2505030603010905 76
    0x1e104000d0310b0180e030360070300c0400301070071038071001e1000c0d01900e160f80802c00810030119041003242004c1d100400d40342c00107440011581320f04d40210340b140c00e02d20f90342014000050010809000c10300b403112541c2a1905020045010740304080e81d21000f03039001800011280d50341650201d8480b401c84440a8480d601c650a1403000c0350001f5481d8440c401e081c020407820070a00d0f8000140140440c41c5091a003503c54a0305001007800703048c261514544c0070b480022002c26038511b030000e4001000340b6100c0c54020303103070182841030040d0300360051300110f065000380c451601c8190740100142030f0320440803482d50180d04101c0c00440c0c101d40501074000850a640544403454035003200000e2285010350281c04102c130b60b500410b051b41e1602209000064000b1440c00c00e40b82c1d01e6425100d43e1040c8e021000c05450f0903005100a4080070500004001001024600a600d1007032410704a40d240b80c40782c2c84400d2098410541c40c0403450800007610300030401550000009400400d040d0059100c0c0c2d49 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 448759757 1250 448758507 448758523
    0x30708030a0507050721020703051c020f16120512030a09061b0504090b0a0f27020901090509040f0b040302060613050405060402090618010f030309080c03070b130503 73
    0x1911140020400840451601c50aa4000d0083c280705051111603200d9442540c05200e8070480710030b042c8081501180200860b40046a004040712001400d00c04d09030110001c12403407001510802111201050001c0380c030680c0214030000000b16241f40420011031584460011b030b40f180250b41841c0110603a0800440c0314a1110101007800002131404504170360501521118142c50341550841d4690b00030221000c0313a403802808035450883d90f001526490a95002e007401000c2044009122040303014038101e412000c5080d2220300c50025408070070382c41080074183c000b036181d050510140c9803078616550000e001d4900640c0701400796a4060041c0820790b001d80159002a0400c00749203419050f034040c0301c280940034402c2d41802d90300d0f581d42d110051710007485100910002980c64880c2c10301025a2070342491440740303950351b88181603600d006900041e80044c4000c50007007445200000c041c5c0003400080c0040403024a0242c0307402d0141c2060088040740d600c4468001025a01000340311 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 448761007 1250 448759757 448759763
    0x4312060c08010b031b09040b030604120215010e04030807052205042304121b030c030f0815040e0304050604080c0f031f1503062421080d0b030307 64
    0x1400306201901900850341680444240e540030020840b1400780c4400c03050542c2032050603c0c2c2c8926000300024003805000000c40d41520034181080180101c01078905004030440e02910780b42d8040740000f0400c00c0d02401403961100c1000003080020b8807a180d001c0e8094242d103030443c2403200741401e403c0d011188400e646508259921b0034003a80c03415205490a4100200701c000c41c0306960b100d08004d034000104050032075012181c029091318080c030300c2034240000c000000456115945070240903a6040b03041a800a400c90030390200342806004040e00407070646800612841c801e204100c007503c03d12482d651a40000d00001801740c5400002c0d001a101c0d9030090002e82001c00300744001894409000b0344298010345071098000c00c0343e11842c0f820006294003064009400070480c800c00301d43e501c010809403401c62030a0515074500010170508411081040140e079641c3ca41c1400b0798104000c2d00602d070111100103000901b00300051010b4044580086810545000040d0454001040503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 448762257 1250 448761007 448761011
    0xd050a1b060f0605060421080d05011d01050603071b0213051008010b030a080708070809190503060f010609060c030c0507081612081611030a0311431206 67
    0x48070b40701100d070185202419090703c105051a14201c4001d642584910100044084890054083c80780d03600c210f0b8040145d0100911603540d580448903e203e0048c1c08124000580b4000400e4a1400a00716801003183e51303a001c11040c41c403950380120180c00c070000c0744c1c04a144a04403000e10341c1130041d640f155000e00042c94003103142c003038541c0c295011300c91254842c0e00040c0c0c4000005042d07105495103103801c500055116a080d142080c450f00c203615895034400b414030381c203c5500744500d409806868044e402e6030742e5925604480c0c85400004c0c010100801c1c017840060021038070541c10309003094040c2c03504108000342512440e00707081c41c80c0c0004500d5040316510380300e440031f0001807900030b00200381c00e80601d62103512000c0c880d0090030304410001d48150584002c0c40a9294001c0e0320740c1c07005041d10444517a601e000360042840d820709210602a180e10001c1100081c01c1c80000c1d8185001c0c400500802c02c641c02106150303c065424038000701c128003288e10049101010602849a200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 448763507 1250 448762257 448762271
    0x30312150f09040b22050a0804090c0503090616030f0603050c100206010e0708060f0301021909091103010e07230301050112050c162621040201020d050a1b06 69
    0x284104a40040440342c018040c2106020010f0000020070b503020203805000e1080c181c04900c1582d03880700060f03025200b4814012184244012000208100c5102440c00c02007507003424010b40f001d000844207107800d50032080000c1e42011000d0b100110710030840c5400210080501ca8038000c0741d059400a4a440d448840140000d04101034008501d02550000781020340c50241c401750700a5000348140200000360020415907100c0b0090a184400010300947d141c10300c1c00102c015030301a80003d038000074800700b00005e10450910464484c0101900e003a45181e017483c41007061190040c1c00d440401c080d100b91604ca1088240700b20301010b1114058075074951510b8001002c6681600443c2c18813450701c0184400d540c2400d0840300c407901c0c01c0c40c20314082030481c28041081100d03c10100007a141e48d0052441242c2100000c104120811805c511036203651103228550b00d404a4009005d80c0c011400038444600400203000e040700c06280c030680030b41c0e00004e40102110348050840c1d2003a00c40c1a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 448764757 1250 448763507 448763509
    0x402040b220507020c0d170922060f06023003131a060a030318150903140f0c010c050a0f0809040c080f131a010620010911040b03031215 60
    0x621500041c2c188001d1070400700c200c0002e04000300c6c061004040701c0442062000300c0340c401d8103607084464000c1010098035020500c078042450800d6a88000d545170030001b14108103c004c0c0f070301c25240144c0c0105500c803041607800103801101410030300e8038040700503508020500b0348002c500c101c038a103d26402020b0031b840d141e810310703940301d6491107550000810440b45889007455030044a41529006441c450002500c904519141d0041d404011810345181d5030190481a0041100c0c4610704040e240d500500003551a185000700b200d140380c10410203440907610548014410704c0c0160300303850003480d013650303903000d14420a401240d82580100354480309107000c0c41100f0790680c95040c1501e4501e89900322805c082c070b0040581404000148120303091009040b0301c1d80c0126000081d040103543c552401408015906850030345e9001418260412000c060080204030f960040e0b503000594034020820010b400340c045040e0701803109025800c80c203840c031990035008501072840c0c1d40780700314040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 448766007 1250 448764757 448764761
    0x403080a090b090f130e01050a0618051b090612010905040b01152f060c030a0507140415030b040507032a1b0501090804060201050108061b0703080402040b22 69
    0x10b4410840358a060100704002d440e8a101e03110342440c2211040300800d00c07074141c100140205800015150310f001d00700b2400021980c015002c0c0e451544400380200c1c0050201d100340c500c21a016a081d030703c100502c1c00e05140c41c07405443c10500040a0b1400c04040040f008140c24090340b20440d803907215420302c42405002c1000502400b40f500011703203031480044001d448901010b00034130150311400117100101855420f0b404211071001d007591050b08140d41480c072250415130318500d00ca032030100850107403170052031001540d098030070025003414601450f04840360b100d0040c1906041e1124107980703207583c0380d01c07400748150317000d40f000101020500c100203072042d1049192040c000490500c1a038561f049064000e4050782c4c4803486068403290b18200303014000103140104502000b0074042151078041d00300318140c0e0f40314004c592095994460300780384540d0120b80810340300802c10141010030303c10554140d00030700140001c070b011015240480d000c501e031080f890b5518000c119005618000314 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 448767257 1250 448766007 448766009
    0x7020d0e100507031808010c0e100306050306070503060d12020313230d020a03050f0d110601060c0807030917010f05060406030c050607060f020a050403050c1002032502060403080a09 80
    0x3558501400c20801c0000361051059003009014480509044100d542d2410030910281440b80f0081c00f040c4070440300230b000d80b091014a0ba225500c640714401034644a23216140071128010002c0c0941d4803603020550b480da1020301141e401c4090b03404100701103490040020708540003540219500c1c0c0701c0020012a07030b41d068000000c1c0e050040000c2021800d011104012070f4011611031250303d0440c0b00041c5051804d51004001d409408500e4050200200e02d08400c40d54a440f0848030004c0c4120700d0391281002d00400c4c008c1910542000081070811000e804164402d0501c0c1c203800d80c0710045c03820024a142c11305100750303446440d41c030003081040c0503c40d0444020345051081c81d00710741c0d85186c0d10340c0a000d0346018100108041e4103000f05a000344220b40300c03041007107669202d0003c00034096030107404180d91500c101654070041d03041440f0b915a910a0b95806182490060b0030b074801c99200004100d0800c004924408002d80c2c0c42000400066100d00e0300c95554102000700a490302103e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 448768507 1250 448767257 448767259
    0x181617060705030612011b17010e012423090a1706070302091311040f0509130212010e030c011401060f020a0206340b0a090c120f080307020d0e 63
    0x2252090100040d00700c003d43e03401c41c104440d0101c000303c100e5030b01801803180141d582801080b550b2961042508004401030459840700007540aa0322190450316400b820b200d101c101c07899005043ca0b0f046854800c0d40000c1d00685482c10343e0030340300300e4a80d03504030301d40c50031020002001985001070b02c0c21000c0c240050100400c5080c01000207400240c648000500000038141c0000b550f003a52342e145841524118000c203800c000e504d80060030100503070400d020f40c440c0c0040551340800e40b843c1c071240303240c4965010710f1108954640c1e4cd003840000210500031003d80d40d00d422840c2103441c8240081c0079140041ca000140c1100340d80640e00c0ca16106030300c014280940c075000e0440030703035005c251080784980580381140c0c0e84e82d101c1e0320504940e0480b04a00c0402801d081e9800c11001e808091f940300b41c0c06841b988540e40ca805144404a81c9405c0c2d000306010100201040040035a825048000f40102001c00340300f2403603115550a584211095001a00141c5090fa5013a4101d103003041c00f224 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 448769757 1250 448768507 448768513
    0x905090f1c0905102f100605060706090203030d14160306030201020303011505131203080c0a20150f091b060301090b120f0c03150c12181617 62
    0x1c071019000d0b015010a000b6070b03006280d4410221a40c0340110031204440e42c0c041180300e2091620401c046a115140005a085004e444441020500903001e42c0c3c05a46000742520303d001d0455407420014442c003001207030140010b0098034100340c07240c03260440c0c04d1905003d080f414907040070b0700307411720051074689028585090010b1002d40d9000064030305450100151180d05030741e60350141e03550b0050f212801424400441e020805880c0c01e400b180303010384641c032071500c940c031078603604103582c043d848228000a111100700803011140c3d14804000c1d8480d035069480800c80183c900041c0d01341200c807066070010000c1480101001040400440c1107958441940c0d507004000140707113840103102e041400c40e1514100744207a9074500c60020168621400c80d400050340540b12501c03409030106291180c0030744c00301d80309030604084482d4802d002c540f01d524a0000b2905040c0b01c0c1501c040c2c4207900089040b4410719414008002d0303050324207041155124a03e2078085e842204131501c40380d501c09a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 448771007 1250 448769757 448769803
    0x1e0406081e06090303040206160b130213141504060801060f0513060308030a051f0f1401030203040c09270602120c0705520b070c0b130905090f 63
    0x100004c002d403604958102c0c1c586981c0c4100090000e918020000040c02141411041c0710b510309c6403005590440e0300c01e07605110a10b00300e031240812034a002c3e48200307054a40d6400101c4040121040180c0b5980040001500ca40ca03251058211022500500c0c0c090b22a50018089481c101130080c408038074440050243c2825a42e0b09007140c00060014400240c982c40030414440c6010714101303114000103110041a640e0341d2900a10454500ca0000c100c545258500c04951081c021644200e41226021504515004404000740a80c103840351655015400240d0b500a1a084450040d8026000582c8450303100415090011700038014103603440e003c02c01e0100290f001f00c0d4040031404d01402c040d0b600d560080b40f80c000b814528140640c1415886203d00683c00c203810f98000c540807041009170180e448082d084005d10800c18050b00280c01d0090401c06c5070200c0000b0aa8842c40d2940b41100944c1c460881d82a03410a844460560b04203140010a0010030000d80040881514914450fa = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 448772257 1250 448771007 448771021
    0xa051f11030c0703050f0c030d050a0e0a05030714010b13090309210209060604082a030316121e0f080a060b0a1b02120f1203070e1e0406081e06 63
    0x610400710004c1c14400040707648424190300c9019a1a0000d0290959a032102c050340070400600f001c80781100903e1034801c40c145000c0780050f011440e142d000000b14686512521000030307640b072000034291070359210201300d002a01e442460195144404502280c1030321503103070160410384541c12102400040010505059a034250030960342070301a203085229490305404070700c80e03104582218400384a0512480d96134048813000665444d0785110381c44041da815020145c4901c10003a9000501002c0480030f40402c0300200b40003004883c5042c0000456100503c141081f40100511408a14005c440e4450580c22009181d07118082d034500700000c9090040702010f5000b4071654100f040500d40b081118100400079100c010b54000303100c40084041c880c0c10b1681e03070580c14088105400383c006450f120404076410759005001c40e40b00c2d03078a80f500040501c01160308045842c020070318542011360a0b40c413944074420140800c5800b5059001130010582040540c80c160140c066114400b04881c1e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 448773507 1250 448772257 448772281
    0x80930010c0206071e030b03030f041404090201050a050c070305070b030a0506010201090201050a030b01020a0602030406051602060903030a090f020a061d0a3b070201050103060c0804020f060c0a051f1103 89
    0x2464005640c616075002c17400204034010141c00310b036160184000200c1c00508034400c00604101da56600c520b1480c0b09004040c00b0558800d10b0300280402c4060242d401e4050161000c2c0074a41081012119099601d4840300d1500c00c0c83c0c1d1240d24100c05c000240494160103009695001e10203000a00960f10103a0008100d0f00c80c0d50301c2c0b0300415075959601502c1d6031080c44200506500203000750f4a034102820840300811055480b07000384642d2000b509103c50010982c58800c41306a006142182da800c500c2c50003800c0a41c00c201c81c601e054050784401a540d242e4481e029048542d6881c04c5011079481e01200100e400da10302c0d2003a03083c0c200800c41c409001e011507501c40c03201100c5940080b450841c64012841030030301880c00040031010429030684c154030190480340510320500c003044100b1020340e406e40742910041e400101c1ca00d004002410060010a422a501022a00380c15215201c560170305041001c0300da0189040e06006242040d2409030700103a06400b108180b860074280074101c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 448774757 1250 448773507 448773527
    0x10e04050a02042708091219020d02040b0409060f060807180c05190e03060a0603120f0210020c06040506010504020a120f0209090a1e050c07080930010c020607 70
    0x80f05548840d00e0300c0d10030150920000000d541244c0c01070111a451601001d9a040003031164001da0307009480f0003842c013000840100e0103149070804190500e0640030b10030802c039144820390f08152698050340b21910b69201e522a181d02807040001c50700c65040300d000685007a68011807955210320340a101002c1c201038070f00349801da6480e00091990401c803040d07405018031a000840300e1728500804010a03007003c0149502c010807800d0350718a030703100050b4100302c580314080a05400444000001403038090501210144990f00485643c8103008160500361707448280189400d03000002484100324023003111303a014000848041d81050300b01d80d00107042041d413a03502c1e0245501d07401010b214500396411078a403008082c220188034078195120001500285400100340c440a12200c2070150051041c02d0040c8400c0b4102482c0613115191980c194025220302ea50102c011603440c1c442d803140e541518030720141600e140901014144c100342c01c5035441c28251065400c82020045015400300c4092 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 448776007 1250 448774757 448774759
    0xb070c1a01081b19120302010609181e0b0a060806011a250602030103230a020604051504050d030801081b01080f0c070606090213140a05010c020324040b010e04050a02 73
    0x38003e962000000350004681e420322003c4400000740400e400c288801c0d825985400307500284600759891a0303240490300500564420010940c080b040080c14454415145c10018041a0305050080d190004140d005031008081d041e65000e041010708028040a801400489840070881d005402c650ba040d10800ca80b10041d08041c415041e040381e5403004140c449a0401d10854807580c40c1d246c050488500d03103042c40500e108104101819000000f402e1544075805024036080900d04424407135070741d14080d1400d100d01002e0201240d6603c800e10803450060181c5d461610b40d500d45505a4106514100b01d5200710b00c2055421069903000308195810142042c800040740da41c0d2200280d182c058030500038020343c03e1107000200c94403d034000e80a01c0403d0305407c0c000c81c0d56641d20845800600c05a5600402601010032142d0702503191101c0660001d0300f610054030301c5c01c2c62501c005405082d401c078680203820502c814850710325071481c0504081c04e0f03419220705154a5096561045000c02 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 448777257 1250 448776007 448776043
    0xe0d03020403021807020a061b080115091a0f0f0702010e060c0304052713050c03010204030b160c08040306020d0b0607031b051c080406051e0114030a0b070c1a0108 72
    0x7003000f1901c200301440803150005402c200a524400c0352091641a050000c0700107070340040040740c1c03841d8045018401d41815200e0413141480c1c802c1c940c0031080c58100b0300c603b041050081c1c50702c1c501558010b204001040c0c80d13456030348159100150912403040011409000240074403405c404001086505890049076405030349a40700062040035000c20340984500304154043c4203880d0112200880d10500c150155a003180c03e00003410b01301d00880c400035003c1c8100c5800f10300c48034003807222801c060340249800c1100000d03c0e120451700b54015071045800c1640002c0c1e82e0010303c41e5114401e84884216011842c0001c1c1e520002c1001c0501e4582800c0d00d8000c2c120502040001c001d48000c040704141c8001d000c204201001e8140321085a0236501107003801d000400300c030342e03441c00800c9070419a81c041c01e143c0d00b004000030f900d626801e9142d80600c00c040805001c248080f40c0700c0e10500655071441c101603410700d0000900c00078004400b0b4560700580051103031003000304903500002040242 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 448778507 1250 448777257 448777261
    0x50c040b0d0b04020d231509040c05031f0c0201020712081f12021c030207152309100e0105030a020d140108010912080601170411130e0d030204030218 66
    0x8070001010000301c4254020300c0000d424003030900c0c80c0c2260032500c0300802c003202903441600040030f0000045070303104400302080754060298504156020307000fa0089030307103251041c0c0300c801181c03400b4204070340440d90b5a20703030f110403400300c446000344455207226200075810501b2a54900d8500b0480c1d0882805100c117070400699100004602510002c0407481490741d01c82d99005d9043c1c203254a00000c1c3d00035090010940f00440c0e68400300300419501d0380c01003510390301e4125403004005c0d042500000300952007402d185421503800d2030f080820940c664881e40c0e41300b90400c01082d43d01c0d403e040405d100700460a110a680c120050325030002c403034800540e031110b0750ac02d2800149410003800034008050704c0041040a0154480826203101c0c041441a550746610103980805007121102c2c00203030a020003541e00c0644548035900300c0d104440d00740100c11030200188240c10090000904160761f00d01c03450250104009500d8010341c0e80c1411840d060035074000c9406102c0b00d04951281201c8480 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 448779757 1250 448778507 448778527
    0x50d05070803150d05010c0e0f01090f09050717010303170f09071404090803010806100506031302130902031e01150609030210020c030d091508070c380405060a050c040b 74
    0x2c0040d070135a8808020000e0451954016000301420503c450242206040744400c03540259110300644247d241009041807803c0c1012001e054001c03c1e000411110059540241000c0040f090195200e030722000c40c0e00d02805c80c940c00480000786a4683c2c400e50005205a0840c040740030380544a400050088408043e4049030241c4070140300140020303800000010080b401250b064040c2404a11414106035202d0400c0500d004c1950b80580010240e00b10074014038046086c219880390707104d40030444018913000a03040001819980441d20485068002000d20038418144e040d002062001d80207410031100400c81081808028001e1128aa1001c20707903008001d401c40d240002411036113a8032070100000c1c280c200c0c0740305482070b21505000500c00d041c003803100315100314026511240d00007000c2d1601079550010380c00100020412200c0c0d40800714004c403031400140c0d051b00c0c1101d86401e203450030340d1800d02c00034800351505140400384030303807100176904a50440b0100c00c4000e44a4100700303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 448781007 1250 448779757 448779769
    0x919020d02191508010e07020a030516061b050918010f030f140631030509010c17030106270b0a0807020102040522050f07080c0d0207080a030603050d0507080315 71
    0x2c2c20401c90700340c4099060b5100c55208800780d046ea55100c1c0c4420395901c80d11001e81c3c1d150441c440042c0420424844640c0e42032501503840c41c131600a1001103040f030200e003024400300c004154840300054002844884a040200010741e0440d80f05104503c590301d8060740c0ca011410b9400010304030303811001030005010143c0100002070051a05842050504008040810384903001c031003010300000d014818200c90380408140c910382c06031101c6152000103001155940d80100080390040c031111145400e02040402a41c082c0c081034991011407803031000b004160601c113150402d0b611a049a081c0b00001d604000c3d0303817150600e802c0160740c944401e007083e40a40501d410407500a20030f01e03070b042c0507520600d0003240c1444000c40104150f4643d41c7c12034030354400032511180403a0b07000d0003080242c42e1480051980034890040103040180c0c50f55148007640c4901043d1000944a4000b071080c02018011030f10b00040ca42065032420311199070700e03211400024101282190031784500c1b030b032544601d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 448782257 1250 448781007 448781009
    0xd110a0501151802040b040b0a020307120f090819080a170c07060e06060f061602060f0403060c0f080415060305060a0504030801050f1302071a04050102030919020d0219 74
    0x91100e07003025656040c080b03207248a00c074110503800060b41c00946043c422203007960b402220151a150401128030110751042001c5002c51000b0440240483c580340070f1381d41c4207644c90340c501d480c8441c815030090128803282c01c0b00240350060b100d942682c94141207842e6845da803004040f602c3c0e03e2600340c01c2c0c1d1660544c1c030050781c01204a10400000b241d546d002814201d208403000c10044401d41c1200b40d9030f91048840316000b10824942e4012032a000b809441c078030024440709413200e202035000c1034198102501d5410707454070210781401040010301510220f002e0b01d180c411104101000d0003840080040d00141c1102c941310f0030408955103d4004001a42d003120440c0d0b8070b4280f41c1c00403002000115420b41c0090407240011404c3e1402045008100c000240115003a401085201d00290300080c0c0480d045000e442401003800719021450348518001c000058507490042c40483c02c1c0811041070940e0303004410318900040e950084850052030b01a248440c5811a90b0540c3e02c1c04091 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 448783507 1250 448782257 448782263
    0x6040e100c11031902010c09050f1203040b0d02041d06060a0810030f080a031401080d11010b1903030210050609011215110c07171218060f030a051005030d110a 70
    0xd124141d1040c4c0c05401080c1110a81c000c1001091581040303d4441040c0102a8414404490070419140070403c4580004d0302e5001d492502d9a00c601c1b6409541c4401d040d4040d042d00860301f00301c81020b11154600d07170f104c0c00461594034034000000402d14801d96006c08180071500b40070602c880c89403500340c0c029560110380c280741c414041c1002d8040e50070414601c800a8180714809980d4011020302c01d048401410050041520300360090340c01c0d9408040304000c1e903603102c50001540c3e44180014019200d0090141c0d0541c0c11800c0007810704007680c1100c81d4007410b108c00d0050b40d855504455044502c0c5d440c141500f4170103450010058500b80c03001c02c00607814580c040651010b83d000401081c02114125561140d64049000340140800c01c0c2ea8640d03000700951000703001407100203165078209070b00c01c05040c0400000040680d040000000300d5640d0200810014400501c665a000300c0c02540c4440e000f8680000203a40e00c010403400d00421181c40e40d10040d1210400030080c501c1d80c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 448784757 1250 448783507 448783513
    0x9150c04050402161b050f010c060e01230c040501050703111606110705040b030a08210f04030f0206150111030405090f070e0922020112051e06040e100c11 68
    0x5100d01c0500c0528885101174408040c8400040451042c0303403113034801c407000076102000100001f0015180c5540c02841500d01d90303125554548400c90a20030a0035004503034103140c1c070001c01500080c0070a00014807000080c00c0400003440305a8110007030b221250303894500218584c0c402d140e1503013400034140d90880310b40040400803410680104440c0f1030591500212400c2c5640c8c0c00130081960180d080c003c1d0181c201d002481c2c0813899010051101019030f810880c09101408240340140c03004484007034803031402d40240003c041d4402c84803071a00e0710720720041c05103041c842003009208030040d00782c40c10300121502d203115858061003a5001403400404002e00d0340f0b0010f64400c040c0360308681d490000b5018041000280c5800030285001c0e401482080494040c85401c0500302414401d0981c140b0100011680f0b42c0702050080f680304104001001880c669121043e00e020384e030103400e05120398184003d1a00d0224001600d00301000c3d00719022a41c00b001b440141c0b03524240a00c1c03110a40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 448786007 1250 448784757 448784767
    0xe07120c02010b1516020f04270203010b100e041a04020d02040812040b0708031306092303040b0a080c0403020411070c091401030b090f0313030b060909150c04050402 73
    0x36010b40c810400400103030313401e001814100d52841c0e9588120f8400c0300040d5003c1194601504200000410411000d0b0001802010050401000c007004c034001c4012a1045141481181001e0040b02e6011a0940d00494003020aa1024102e008800013130b60099039030741e0301b100c10b08015044011500b40040c2c000c541d54a4280b4440002c0d600c240500000e52180000406101c1c2c0282c0c100d5044418001c1a5030402d10295034070301e801d0f0b00240014200c8440d61740d100c404903501e0321641c400b080c801c0e46142d040b000d103403194401ba4041481c4107002504240010411203405a080300d203402e94074580b155050703079501d0264000c2e02560300040d4015107042d1071301100111a1005244090068020b00d010607624922281950300e6011120700c0351104500401c0050301c07684e1019040281101500d00603018000c40310301e1600b20388030010392a81600010801c0c04080008030350040403d646442041c6031440e03110380d5521401003010900d1070040c002030000d41c2d080042d1006020010801c0d503482e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 448787257 1250 448786007 448786031
    0x3020705010f150306140601050403021e040204060c11030f1015030807050d17041127091e0c0604030b040203030c0d1e0c03140a03020706020f03071103070c0e0712 72
    0x215400c3c1c04112610780c40c251b88035613504a0b4044491003130a0507592507240c07905513424080b18960300c15800b803010101d14254012a130b1140080d0010744115981d540c5003a21030b0811841012180c0e03442800f80c2c00203001c010018601161100901203404004545005034034807082d41ca10b00b6510103806000045907030010400007092850f400c1009c0e035151005c0750182000381400c034030150f0300248070001d158040009418611900340400000d1a0180002c00b64007030700e140d60300b500703c8070504983c1000c03003014210800ea040070030420a41c040102040c01d01003001c2152407140e40405442e00342201c0026085590800032110546030300000c2d0341010300303420005800c0b007184a190840a90480035041d02d05031086580c2c07820941c05a0b82d00c0c0861080b00111040c1d58402550041055020440c680119070706000030000011020b510954070b10740000000d10511313030b81d000b03031035140c00410040d80850704038003030354041d1110b02d0328090035070b11240425262610140d502031910760038200c0000070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 448788507 1250 448787257 448787291
    0x1e0b15040308190906021f0204080a050f120f030606031512030a030522030e1c0521030405120d0b0a0324051e0a060902030115110c09060103020705010f 67
    0x69600d2101c0f0384403c510100358103840702545030080e500181c0c0801e600d504050f4981c92600f0040000500051409480342038690070808006410381d5182e1100f00041c85041c07080201400c0725078041c440364100b0488400b0040e81d840003404c45441a40044045146502224200e80b01c100008004017010101d010000340c5940091900a01081c544000590040f40d0b000c0f42d100d29600d03107108400001555501929400131303401c00b05030020b1041556060344810214080d8031240500c00501840c00b0001620781001c611654034003001c0030501c1444001040082d41c0f0b00c01e041c1d0a4501e41d100e00d2604c840760300400c1e11906107988a8206040001400101d201620b82c0500c1946030484013805c0406130016124155191010100141111211180e801c4040c0d0341107925004007003011130f5500e164005a802c2a080213103880418103010340444e4029180c0c000b0f950460004c0c000e0300c0c0c4075100144200354000d01460505800180c040c041042c29070100c00e14005403202000300c50401014490 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 448789757 1250 448788507 448788517
    0x3021c14210f01171f021e1303050f07050a03080a02010b090a06080c040c09090b0a08120a0f0309120c020d0c0e01080d1707050705030f0c030a121e0b15040308 70
    0x340c0c8050490412588003000c5030984440c11042170b420030340910314114070700070350207091030f201d215a0b8080d01c2c00c44410100010303c400a00581900d0390141942030407030030090a20064039142c1e00020301006551149150b8208594104548170380340d0000e0101a805881c15022060340034900d0750400c0310822081d40100c0c199848031341150088803820061004440079450254040740c0240d0302000070b02c0e01c0350460758040d40003038a1700e802e207540d40714280e19260842d003041111410201740c91218030b030b10202c0300d4104182460b00b440301039203c0c4c40302e0700f811310240c400004204401c01044159200c50540024a907400103a82d1815a41e41030000080d0b075085c056940c01307004001101c3c0f10540f0030390300c00b080102e074020203103090f4132081003d81e5280d0018004650602080c03110401c0301d445840501701444e810005143e03200c150500040c141c03504201e8021f030343e84c03410341204000181e010010002081c80e14000880e80c100c240041c03454004c1549140b108400001c010042000705c0001d41 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 448791007 1250 448789757 448789769
    0x40609091a181302040905070509100324060b19020606060403020a14030c030d170a06140108070905030322080d020604030c0c2103021c14210f01 64
    0x48107020140350201500720110794004450700c0c22801040044a400d41c20480d40084040c0800300d03503000c0340035100c482d00300750340c039822800040020781002a20030f0790108002604d8031589065607104410300e0004845051010b4510817441c1c0f60414a901010203404040c070640d48a2202c0c0f100400391501c01c00381403005008442c0480c0380c506003801500c0c1580c0d0300500e0000561306040105660341c0105400725030600c01c4428400050302c084c003480c0c40e60080340c0ea629010b544400d500d40038072000a00724812852401100700402082040341a058910034645001203480d42c00007111003201c1e03500300c0e55240c000011900c40710881191102515525003004504403565803003500c0d03c690600702483e0168002d200043e0000e0310405420030100d00c15680c181d01e480e22030b0f000d00e403900710300c00000c0e0f40d110641c9100c03000e16030100000c00315000c1100305401e018031103110041004c00c12150412103a00042000e0170a207000300000c1d04461034500c3c20b00014034105003030841e56031007840780c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 448792257 1250 448791007 448791011
    0xb060f0d0e010608070e0a0f0e03070b090606060922051005040501051009030215040b0307031415150c0a05030307030519090c210501050712140402030601090905070b04060909 77
    0xa00401d0034180603080881d1004c4004d443c2c200c3c07902c0c400c600a100000c20117040f041d070f02c500d41106d2914501c02d800030702d0105c4000355160252032804e0182408042c1084095511220810140da9074160865060460a549000a01d10020b18840d2455142030004030102d0801c41080110012405400c00b1500200d40622031640d81d00c0c140103400b007190b051580000c8441c08184090300300000040c4400900c20710240c40e00d0342d05d100054140c4c0041d5003044c00a44c44004000403020000e4036036802c90b2040140d03400c041c4d0103c000031240404069809034103034004ca8007918400c81481560320854200040e02e0b560f1030b090a002b801458121207140b0300c90540704240c80003454500c02c642520354070606611006040803000b0b201c001c410200649601841c0d0b4540000842c00e0003514050030714ae464105e901881c0404000683e103200c02198001150242048003594000540c9411a11301c0740c0c0c00210000d6900b412420300d40780d600110310f1440002000507070310754040000000c503004c0c40701c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 448793507 1250 448792257 448792271
    0x1802091002210f0d020906070c0312030501171b011701080c15070308011a0919050f03011505060c16080c030d0801060e010e1906030b1201020301060503070507060b060f0d 75
    0x1c2c14858001c0e5051090090001e0090f885400c900303500400403d4030080a040c1813503565a00c444071113040340c2048075a00860414199140d40600034503001d003000399a0021000b1098400503503900d40840d800203004201d801403521640218042500c031141d1b0322104103d9a12002c0c825038880c0540d1395036011343e640c00381d98a904851002950280350349030b600c4c8503459191480750801c03c28054090440341c41c041000f40b83c29034850781d003420081c00303c406400c2050301d040d003002004920300f29954040d90400350104607a40540c00060140c5034102c074015100c0525000c110300c1c069042c09031035401c4c00c41c0f01011842c00c1c0300140703007150303145c0032401c4500f15a240c03002118951820300c5010041803030b01d0074550441d0300810f604c0d090540042d08002c1c64480150000720141881c0d4001404a56104001c0d6802c0c01c1801c407209071072500f54001d51855140240c01062032000814031002c0100110300b00d400c000b0f858020001c44203001704000e4440e403003403442072104d9000d000000c1b003403403074414 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 448794757 1250 448793507 448793563
    0x1e060506150f1905040909050c0f01050418050a0204091e051f03021c061d0f060c030414070909080901110c0f010302070809040203130c1a041802091002 67
    0x800c940c00300b0241c200300c03410102240502c1d02950441d8040c0c20a00c8410300002c07955860038030031040398034022001042944800c0062000351803484001a0401c0310401c802d00024514801115a8071118036000402e59511140c18000b07000d160440800c541c28031032009114450414001d1420a070050100800e40b00c080c0b01e4210611025242c5498482804042015140c002c9110480010481040650228075034a280444603d0041c07a220b0340d003484d4803030100050400660203220f040400501d120300705060789034501e000003400184501032501481e040200180251001440088414030801010780380190264019100007400640d11703d655044d84200020241d410031030280c40c110f01c00e000c500044019605c060f5003a514a46c081281030780c551a18030007184a2394034200042d40b0081949401070b420115a40f088050100803c070a0074540d10704000c4804840052001032000c884014030400030b4025052840c0e4080b08981c2c0048510390007140b40d0112000201c1b038684442c020034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 448796007 1250 448794757 448794799
    0x1030519050604020d051006090507020c0303271c03020c0f0f010e040209040603020a0825060503010b090a03050d17010f06050711030715031b08090c04091e060506 72
    0x1803000303807155016602080140c1002400f00354001c1c050019251001c00c6880c44a060760490342c4038403d020f9645007080b10340d07030707041c01025801c25040b000303503207400f04844ea02500700e01c003d084c8a41d10801c10280b41c00581c2e50ba03801034901c1044003403915180312036040280d00d92000a41d401cac0615201c0e40c0100d1185000132403146404816121100003166003030a1000941004618070341013541c94501002596910441d10004d080b00b00041034010018a013907502543c9000c0c6ca4902c1c001440418443e090f00701003a241900d20035030b4901d4a03008101c1c0000c4102d03c032544003070454014030880d0f000b0781d03500c440f00074080d171425041e1a1a40c0d82c1c401c0000003007080c0b8402c2c04d00007a4180035100000306d1142001e1501d440040403260080e44030090403e0020720721a030540420307981c0316600390007805500b0145204172030381050107062401c241420344607110b86070007034490784e601c560032001c004011252641d040318240c20b2081202a925007000140300503941c1c9407050304051007040c0442006 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 448797257 1250 448796007 448796053
    0x4050d150f0c02192301050a0b030604021008041a16090e060a0b0d020f03090f010605031b040914010c0309030e030a0218040c030830010e070513030203070e010305 72
    0x540e00034403421080058004100c1c070591310803a0001155882e01140c50000b0540400c00c0304280000a0541024811403040ba101101305034001c2d00074008110160742d80e02c4241c0340d180344a0808540a03038581c98a900a00300005091912403025001c1c0144d5405003c4030000f0703481181c5031101d02c075898102412405104480c0e643e40032640b0901442281810740242451081d80d00380941804503404002c002e40d041100c004005520803d000040c00e00700340143d000611041e0050a000b5040100e010245451000308a0180da2991804010841c0d035100b40119400458001c01041001840007070282c2503035181600083c00d85211104d00d0729010407084001d503401040e2000c1c501e0000c1d170a51f078862002300280c03420b016416001010030300110040038036804102e0302d854107007140c2c110031042000340b05900003503901b84c10060091030104241c642e040310356403e140c0d4a400700011620700c1107559803c020f40500800d00c5c001098040d4124680c1668490420744401004000d5908007010340 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 448798507 1250 448797257 448797281
    0x706110c0307140f010309020402040801022101081e03090907120c2a02060408060112022704020402090a08031303061d0703030804020604032102190f060e0304050d150f 74
    0xf2202c11000386098888034041d520181400310701f813490798000500301c1e003042c4c0c007000c1103035000500660b000c0c0e10706203150f4103034140346190b28107541050112607490700364420f400d07406141c0d040d80d49040d80c402c10a91707040340c10040501400d4603061500812000091440c1014181400640f4024030301034608501042c640d0130745e1541c0c0d0220039075134548102050320240e030840c0b404c120110f8440c10a1107100d01030030224540613624201031040c06003c000c0f07140040030f004040130090340e09020f0300e0f07119a0400d070103ca015032220300201c0080e080d8009544444c4651000140442812900384001011240a1a0108a04105100344142c1c2100b2800100000c1d0048401800006d0103680c100b81c01c0382c00030b0300c2a400c1584035680c0c496002c210380b80e4582c6800880d405804519410060002c9100d1000c03041c1c811441035940304841541490300042142d5110203141e5183d032810000d480c02801d004040300945100f90501c02400c0c07003504882082d1a050985008070341c040c0380140a04129 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 448799757 1250 448798507 448798529
    0x6070c15031e0c0e0d1a01090204051903110114090d230a020303071b0e010902120603120403061d0322140618152101120c031509050706110c0307 64
    0x542070b0104841005e14000842d0071680c401c9141007400c10028a080c068690a800180e5950800082156036500001480b01620090605000142c1c5050f51090044400e081c00314010310702000d803410324010850b106410040180504080c04280c1d01101109185a00a001c148401c43d8917151076000722000650950b03c10040c2c040000c44001c401500d21000d800038401e01078a030800c0c40c0080e80c080e8411610680c0100b11580381249070b0b800c2a030804001c800034140e050000c2e005241c54000c0d407101030309a0b551400d03503c913031401a03281d40c00003010303c8060b40d81d074103810444400460400c2c0200030004081c07140104812880351600041400020601400e0035400d820150040801050242d001502e034a03084c0c0c44107d48038040d011154100000d2440b21420782208205d060b016070101d40c4002e013114004000c681d007180e824050701e4003c583c1c08044c40c010034441c1c01401e0b084800501a00ca180400181d080d441142d40c840389080d90180c50550320804100f41d654240b038082e4080c036071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 448801007 1250 448799757 448799777
    0x21002150f0105091306020403020301050114011e0206070e0303090907030e1903020a142407030b01050403120c08040b070b1005031507030b0117010f0f0812070206070c15031e0c 78
    0x81720025070030045a00c950005441d0580ba5408282562020b9000350605101ca81640407150b8010000030030100b0070540f00c544c6c000c4404c400035500c45003c0e0808081c801080700398280380e14244101e80a2100103441c104042c20200d00040090200c1665151035020310811014401c410b007441e0218150581c3c000d08403601e01c0d0722003400360034040d00d50b620130b449003140340b0b1001400d010590046102403d201d102c58680914050140c03061003858504001e02080300b4400203403450030344540d10704985040001000e4625284569110385d0704891040000499030030104100d019813544902121008180702e641e0341c00c00d0560304e251800402d82e842000c40f0000304254481d9114080403c0d05151100740302c045904401c41e0110203811010024248010074080c1904618801e0010107500000f44440030301907003a45818001c100000f03101c0e6000241500901c004c83c03541c0c02c040c05044d0710b00d0a00d000c090101070018031000c00811251401d91640441d004880c4c45840d586d035815440b0000e400c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 448802257 1250 448801007 448801021
    0xa0309050625030804050d030b0d080307050c100c0e0405010e1612021204110105091311041802091806060409200c0604170f09090402030a021002150f010509 69
    0xb50040c05009444600c0c1618046003204640c0380c0000c940c0c00707603e0301407180c03c0500700a402d060442100c3e100741414211000c3c1d1076120791205103c0242c0085800340c5a8076619003c039924410845552403510802000f2843c010300d0358031803103041b03600d034a0340c54821020070240000d0303c40c00d12039000078035000000108501c50544442d849888186030211400d05800020800ca07040945444406100c0100300400c200501c0901c12030034200b428014109008040015801c000c055110b04145841d040284c0345001e1110694010b03100c0c071035451900c10f000c203841328003d4115541ca98802c0010100001500c40340b00d00c041d0140d80b006d032600d803901c4d0610034010007600d0748001c80302c05591159540241151400301038061040150094403443c01d003810202c0e618400d840002c245404204039124101b54600104d411921080e10501c06694990000030f0501e4003680340039402503241495014400d03408650100403100c1e0040e014241c1c3c95808620780040d0090040540200306c49002c2295 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 448803507 1250 448802257 448802269
    0x318120403021c15060503011104030b2d070c0519030e0f060d0218030d030e0c012111190306030206040b1e04030308150609010e10020a1b080706020a030905 69
    0x3034030061001a03c44086981c1c845030416441c422460507a84e4440090020340f900380508a860015451901d0419003036403520381c0e0390303d07003d030940e0f298500c2e106801d00c04c1c0404c40003a644802c100703075004a5900e40320b540504044100b100c01c4625005880c1d12603081c0031071009826180360181d40b41502c600f103010500c108642800c2d10258040f4040c0f00448103150203000070040d6002c080c0e80f10f422104508181460280403d40c40c070141828905004984440014060a014000d02c1e003c1c60300900d80c040400c070aa00860540c00302c908000c4035082c010940c03001018402e04d0540e02c060100c1c0000e10480447c2e40d9800025440401044208404407414014298041101561007104403030305403998210340c1b099104501041006003013011283c4003a020299440c41503038414500150300000819400c07099000d94824210103008040341c600c2040015640c95001c550b103000c035001e0300001d981084d0301c0c0c45510202e00c42c0800c082102880442d200c142554161a107005550a207010884 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 448804757 1250 448803507 448803529
    0x21f050a020c0f010603050d05030408091e060d06030b070e01050d020a020c030a0501090506070302120f150a0e01140103110d050402130204031101110d02070b0c03070215031812040302 81
    0x19598081c0b1001842d01d03010710200810942e0320340001041880c44c03a1507070034004d4140e042c0341840381c11300030880030841c0082282c502c403e044030a0980d07005501031902c0c0350308146030460b4004101045076080a40d03a81d22000a40b80140e0841d4040d82c0c400f50111042c280c80e1440c24001041485003064400c0d540c0c000d01010001d50040d5150615490046450f080b2040c900b5510303603441d4a801000d111090010607008041c0785029841d204400c1c1c03400034800800b0b0701d0019008500d800203622031040031740180c0c100f000245201c044a45d90216054030350303401e0007840f0408480113040382d000c0d030007403060307546c0c820f001002207080000c1043d0f000014140140166080500300c842e4081c000c07a648001c0014503c64000c82d4a1280b050000504c1d080c48100c0340703903065220106002c03400390002000307000ca400300d461291380c2e4080f4220481c114010f241f1300070b4119520501140620b6070100c05140f041c9442c0075603452070302030b1024070741d615550480075822843e0100001c2c005800c100120070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 448806007 1250 448804757 448804771
    0x6010c0f1112030a1205160c0303060f1202030601081902090c04030c03060509010c020f250503032b0c0f0e01030e1005070f020304231f0203031006021f05 68
    0x1010800010219003080580e00c24682c86800004001245541101004c80b00c012400300402181c41c02c0c0070581246ca0300040300b001449990b00c980c00806209401c400081c16007559110600e0b40d64023850150140808004c92003809000000305450100040880000703035000d50380030700d80700c2079024000104405020b06000383c01c100f00c0070003c16a0402d000e4000c610401c0006003500c0c00d0a0840e0031600d10010400440d002a6040010324a0015203040504090320242c204c0500d6110107054100075a400180c05000126864010000d040719030410282c00d506403140360f0103243d000e002280c452a4606d0301245280100441141c45000701001c0000103042c00100022079a41c0740e89070281440000705415241c85c200480190700411360103224141d400254245410080940c00c21203400c01b40d410f814075000501c82c851f50321204840141242c10034000071481140c03c000707440e640121120007102c1e0119500041e00c6100186420070881d6041079503401c0c0072414041400741102502031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 448807257 1250 448806007 448806023
    0x2303040b0417190503010e0c092107031505040302280809011106090c010e06040f050904061409030703090b0406020a11030304170304150306050102071403010f0507030902090a0506010c0f 82
    0x140f402c40c124201c200f40103114584906459601d00000c4202034074004211000d003200034000c0520765210015646282c00d400c2c44244184031107403d07a03524001c0690f10103000b9021020168220503d682d0006005600079400d403241c003200881c030313800000050010400111101d641d4180400c48100c09817010b800e0514040240d1000c0051003842c141003925000300c5500044417102043d03802c1090291010307000c1d114942002d10301a00d8400849003441780038007030503180c0000780c10000303241d00c420003401180b1400b00c01e03030800c901c420b6507903049808210040b440ca0b110210b8440e5500302a54112030141d4020032007c603442c0d503800100d0005080b4590103100030700c000709540362105001c0e002c03011994001d641707551514140c801c10403404078100080c5071421030240071507603001c569403007610001129541d61625500209004002034841c84070080e1a100900000c99411341103c40d840c1c1c001c4800c03e540b0340712481c1003001c41d601aa00b481c00706180c01851000260552580060382d4024800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 448808507 1250 448807257 448807267
    0x13030918090b0c03072703030305040507030807080d0e01150308090d1401020706050f16142106040e0d20010603052409010b060403060f1b2303040b0417 67
    0x641d010310401500e41c0e404248000c420007030758035401a00c8106c41451043c00c1506603203100342a80781c00200303000140405440704002001d00504000b2400190f60000c0c2142e80e840031818404015000990407807451410807030801c4a52505008111481c01901c1440c81e01a103196100d01d000d900040c09030350400c00c500680e60105611407100b05085804030b00240c3d41e046186009011958010500c0c201d06c00e0100c1030054529400110f51818076550a0040c2601506d0300000164041c54600703000c0e10001c0c0460105d40400115030300e0040d10265418407240326144003290310b40011210780c000040456075040300b02004c03410b8070900782c600e4000010f80c194581c3c40d910300340500403100e540284058a5200140040e003580268442c028500802a464602d800202d0b180b0441c03001808144e104c103000b009500040c1c0c4050103642c6505100b070449a542130010b4450603050001c1c85089400c0d4507111400f26080040324421503000000202035583d964403a10750031804a0b00a00c0c026007481 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 448809757 1250 448808507 448808513
    0x30201020d0f021606030b0a0519030809010c15061a07050d1812050d0e0d08040b03041e0308060102161410030e070b07050c040204080a061a06160b1303091809 70
    0x50013009003166980100e0070b400f16074144140f4042d2980058042c90203031400184041c002c2c20b4610075658040280c0369100c50f0703100101c4440380300e018058030b05c5018030440c1c1481c200356407141c0300b103a503200c0c5401c0e03c5018054500d2424000e1400142ca9604803012200c1c149110750048075503482c3c0c8000c902441602c2c0c8600c501c1310007003048121600e50190f40312043c03413608440782c6007540104449031468001c0c0f5a5440304ca60090b407144544007000403003c107080200c480c00420155000e0740e48843c0d400e42d9070400400103601907070001d0160140c0c4c40051010694144554241c82c0c8007100400c401112000744042046900c0e450703020156a11310710041240140080c10040c0400b140660b115129800d01500340240381003141d1080744100070030010b40401103045585030390090800141c00b0110303150080e03403c20026101da844580050007100760041c01303a410036054000d07203102c1d09594039807500ca0720b006074058029000c2980c250040100061448038002c7c0d2841c00742010901480e10341e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 448811007 1250 448809757 448809793
    0x90d02120106030803011a0c2e0e010b090604020310031b090219120507120207050a060e10050f07020c13060f15030e120d2309030403020a0f030201020d0f02 69
    0x140080f03404c10000001040308031041e109902d10040046602440c054842140640c0c81004a6142018009084c840040700c180f0030300d0326101400e0000103000032000602101d00900303803d80c0719442034000401180441c20300c1d03c2aa881180c8516000203018199160340c81c0701c90f07152004a4102e02c20b028085203a1815002422883e0607030340f0220300d1081d1100e4013074050801020700041e56407500080003103d0782d010307040010f4070380c031902c0050303981d400c5040460400e405000050481820410300c445103660008105c901c08e0846201000300d91030700303070b0700358402142580c844005901c40305800c83c0918140716842c55504141b100060ba01e59100e80840b403daa82da401958454002c000340318801e6054010f04c0c114820b1800038141064846002038001e0051270310200c101070b6945141d50039556880398182071496246c250301602c1c03414004980da29889400304034003982c1007610028884a4603180c800660b94142c002d80421000e41c03000711419a2101c000300214401c089001c00b0404100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 448812257 1250 448811007 448811009
    0x7030506062505241e220b010612140408070209060d0f0c05121504110a030203060c09030f07060c0803150d0c0602011803020a02090907030213020a08011505090d02120106 75
    0x25000401079100e1000c1c0314044c0720401814031000d0280c0310190484404003942d0075500984090b034a007030140502d00c1c403d000300000f200050032004101e00104078180c1014111511240640301880b070340c0d1074034101404269080d40c0003001c41200384178000040c03510b4040264802005400200d1072007442e203504041240d40d5109131584090b921060040d0300300724803801c19999550005088139075012031080681580200041c01400344500f201d50280c0d144049c540007190003d01b11b40c202d00b01203074081000d5120740420740c03081c03040e100d60515000300803544030700b1604d040d254140e1614042d1110070b01540b0007041100c5802e44400400e0345603981c1c281010000c0e00901c0c800e04075509107a0068212100c00e41001d0481c14944c2e45100001e038001020740d1a50350541e5040c0c802c2d10380315581c516000440d00f000354400402541080040c00c164040e28402055a44400159070394107041d035110384031454014009001081400f0803410b0507042c41040a201900307042e4080309449a903402c48540d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 448813507 1250 448812257 448812283
    0x1106041e0c0f031b06081306060b0c0303060307050406080d08060f090106020102130602011527020415020c0406030c0506090a0305030c07030303150b0a1b0f030c030807030506062505 80
    0x60501c04e00524800312803045407620043c002c4c1c142021800b505c1c1d03030001888010303140503040c800420041c050b00008001c202121000340c584000f210265160f400807100d0070301a00c10890001101d00d0315010701011110402c0262810402d00d1a0841b035000340285059003100700c0c583c1213465602c915260a000f400c00d54001a00c41c42c0c031035401da6402080d540441c045a04000d0402c9850b2845a030003000c880081c03000303000e0030381d007005009516108008580200d80c03020800217002c0070400a4000003007225400e481e50f0540303131000c10048604900000d031008540480c10300650602500400482000a0140d041c1e41e070b4a075565032442d44210303d109007036004104204101070709809964a82c52000f44400c071180d04050102004c1d0044100314001c201b00e8100480030445000034480c0c0300341d080240c00c910011a8100640011420b010880c009421600000c50aa00ca44501405000028046850110305d021a04510764806c10300c900009405100000000c0003049011b84070070f1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 448814757 1250 448813507 448813529
    0x5130203060132071e08090a0806221401110409060b030105090c130f1e06050307120b06160f1703070e0d1514090d1106041e0c 56
    0x60321000061180c48285a1200c0c0503003100a01c02e03009183c1008002a41d0842040988030360309810074070300030604d000c45c21403441c03140d14400c400c1c0b00700c40000300080c413008d94064401030b548841e02c966a54084a80045039030f4540700d1000c07a80b20190381d5050448c0940c02140106500c65840e9003118110000d03000b843c2e50015003080062828011500108609000710781558580340200b080e0b200000d01c2c02a03060000100b80e0184030000b080d10010b401c82c0354840c03042c251503400e5050a84110001001490000000043c1c2340c3d100304100e034402c151a6440d0900c40d0345203c9003001501c200001035500c0003052041c8a42011088135800285010b80045508050142010210020403d8030740f052032800704100f04015400076008070b10080700341e9006040c00040d017000030856410441c4024818108111741c0c040102e00740c141c070300442c070f10010f46070200c104034019a21522009550b85098200400145c08a00803810300d520030504030624103144c4459954007490b107140ca0b001121110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 448816007 1250 448814757 448814761
    0x90123060705070506070309030b070c05071208030a051b0408031c060803090d06020415120b010903020d0b060a12060e010c090503070b09030c040c1206050609060304150b0901080c031507050a0809010605130203 92
    0xc141003b00c1c800400c2c0101a03540d40340142c1c0c644000da0f201c01400b9804147e1158045160000c070031401c43c00094582e0701c9170341c4450316a140c0036200e602c085424207841c1c001841030641020548122411184000c005518101da07410a11035003460509095079420350074070001801d54504442440710f41c40d03d5940d00090360314100b07544200c4150b50001410031140030800d00058079148034003442103810401542c03a1f642c0f41c1000901b503070520f03004003e042e92422800010028550002000b0081c0301c0c2c0203020581c160001107800c2000d9100300d66043d8804070f0300300841101203008103d4501c02070103880000a9403004142030328444010034000401c0c0340340004451800748240400b078401100c0e1640b400c50f800f40054010b02028001421038144c01502480e1114994014108440d001d000303210b4a6035161281c64690b540702025a009005502c890807080b01c68241d124401c10103a10754504141320b1050407100418014581c4a0740c1d9621000860300d40d481c4541055180c8000704090303aa4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 448817257 1250 448816007 448816013
    0x6051f0f08060901060501021e0a050a061b08070806011209080708030115030507050702060c010b0909010b012003070f02150c03090f010507030c02040c0e090123060705070506070309030b070c 84
    0x2d40b00802ca03008591400200b8042a81d01182c00d5088030701d5580c51841151106103424244819014000c00038495a04c00400b000100d41098810a4400d0310284076400c400105840c00681140d0903c0060300d9200000c11542c05540f1641d59440908000915103044c0c0e912100c542d8000041540c48130404001000f180c411201490010055850144098180444054090702075254000d00c107140105450b03224a50951100701d0161004040c4601c80c20034a00b540e000f400c6804113180000c0c1c0756600b4a4850410640248610708901c008514140c0a91101d10b503000741c4400072a4080e01001c0034004800107000a00090350080d0003850381c5580c140100801003802d11546814004180320b560007083d0480f841180d2075405460220b0440351401c0d08407080241c0700492a4400e4030b00300086a00d0310403c1c0c10610121400712003801d403140d0301e010000d284c0500400101540d00400b4140000d040010141000a03c281448018182c0b01d1ba00e40030f50742c07011125200060100305071213041c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 448818507 1250 448817257 448817263
    0x609021e030c07051f0b10080115110a1407060207030f0204050a020903030d060501080f060d03110c030114220c091a060c06060312031902070804120302060f0f1306051f0f08 76
    0x1c01b070211401160509040c40140064005105411002065201c00c50001d4001c018401c040202c0e4010355806050303501d040c12a88602ca800203845103e15400450a28000140c4000341c0350408144100d44100768204030140200034503400314035030244102c00704c9403000c0014110044080034045006070074400014142c420040c040c1004040103418058241c66401c0c890064541520b0003d44100d1400310b0340d403a00680c02d07041a003542c030341a803144403c4485445140036003044920a50308607513001d02c071a400541c20902820070b13a02c00c030b81003028a0f07055200c3c52400030f100c08001103492018000402e5074001e5030400516070400410060b03540360a104c50700d00e0110440c0040c0c21400e10802081c0103848041100756025400998403050003030f40c405880080440341e000820120031450000c1d1034440039141d840300c0640c03100220b05074a00380c2104038418101c4003000711030b80d09262030303404c058036024000c01c240d800b100040d003100001d40002440a8511048030109040c079047c0300b83d103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 448819757 1250 448818507 448818521
    0x8040314011103130c0b03070207170604080a050c0a0602031501080a050c0a0f090b03091c050702030606010c03030b0d03030c0e041a10020f0f070302040609021e030c07051f 76
    0x991500540c054140b50300740a4076004006a121103002c81c405191610000c411500651b042c008080100910382d0390014034282038450031170240c4503a00d104d645c0c45a4940081d5070043c09240180301e18580a40301c0c001501e19210310304e04803640c1c5040364659034101ea20a42c0c0c0785682c0c21310f01c020104156000055076410443c5108200000d10f4041d007820a28022002903004000c40800f200303151030702c103d00c000d001d48407080c0703850f03502d0401d1444240d84203043d001d028005a15902003420190264055a41103500600680100e40c0d60400441d0580620202241410b9a40a00d501d40e41c656500e4603802c02c4c8030703071400607901641d18000340c80041e80c41c0115120300e0509440950607102248401d030010310980e10740c00003050420381603007048440c40c01c95405100e50404241002c074001201001c1704e000343c4003040341c15100d4101e50140d100b8141c4491401c48030340b600414811424005642c0a8442e1000d6400d0100903982c060070900365005080c407440f10286410310900a51290003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 448821007 1250 448819757 448819793
    0x91b050f1e0a0e100e040213052128060f02041509050a050a0f050d021f030902091b031b16060204260703240513031107060c060f06050607080403 64
    0x180d0132a2402100508070720303094540380d01541e0046072801c101200c00c6420009040f0003000b01d41411010b0307130990101e480c4001340036518401d20000b03100800900f103941c039100701030000b0400c174a00b59843e05000790840b2110040380540c204800100c0c0382c241c4140c102004119600e0520705854001040413410090300100e110b003220708400c00c69019400c1d0031104170f50b4141c2d01c01c407007404580001740f2503050b2240105a181141803020400070ba02d81c0c08101c01601c201e0b5040501d4440d0449082440425141c560041c00108007007a0b070403e4051410005d401a045800d2410100c501d0700c801d914000d50045070f880b900403405215400c04565000b07071001600814800035030961005941d41c0f0a548000340c03d14910700000d01026081d0600e00c204000e10250178030841c1041600400c02140b0160180c0004a620085c0c07100071202140b0441100c029070384400350515039888100c020540414a080403640e584d2000a844c2c840c0e0f07010f05690750140500584943c41c504082e640c1e218018000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 448822257 1250 448821007 448821019
    0x170f0601050613060e1c0b042117040f0203120a0206060f0a1206020c01140a0e06040302070b16060501090504210512040f0c0308090a091b050f1e0a0e 66
    0x768000421041100080355401d00c0c0640711a40102c01145152006d16000d9604c40503011810341403125600300140130380d214003081410703c0880740c684015401c0290344180041d40700781c00403282c5040c00000c1c41d0401d000e4856641409103e0303000070b03e0300c1e04600c10081c0220000c1041c0c251a0317010701015500940c1510985020760f521000200040000c0c01007030200c205118411048c000c0340e0b8140d815000c0c07a000200403281074018100303034070007080321140c4150f4181400030707200342c002199440c0204d626800800055090072000d5406410170f00c08001010850f069500c00b0a03072b0350268900070490017500080606190802c41400e00f071002e00d41c0e611030010105607014540c460201c80c845000703c0b52000303c13501c880ca00600350400100000e0314540781503c000c003c1c00811001030408000403a209004140c0c0c440c51041900c6440c64a00322003004114144500c41c0128001c081d4500e66444c00b600d0030019811001414046120320118000049064035005170060700c140e054031411a28 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 448823507 1250 448822257 448822267
    0xb090d0c0f06020f040b070501061404091a130501050412090609080c04051806090c040608150604020c0a0209070203030708150619051e0705060f0c030a09020a170f06010506 76
    0x54541d0300c80d40d90000a040640c00105251301c21032650039900500a92a451540c42c2c90702d0130520301910050140d40c4600f0788200041e03c85260510a0300449076001e42140c0140e10840521001007200811650b1303014840d404100000300d00784141c1d4403440c858000e400310b410440d00c00a0141805070440c10900007450030611040100040c802d80e5804203d60100b12680c480b01e0030700b000300750040d216440d882200c0c00d001000340c01107010702c040c0009940400c4550380d20f82800e03a8443c0d400c8000c8085581d040f0100761141001d4000301803040d042d804807031040d8201c0d8040744911104550410050300040180700b00f490307009564640159800c0104e40c440000e2100140d0f4500c1b40646107a84100f24440418503c1d000d00d080c0d400e044004108000014041c0000c031080354017a01d0304580da800b13034000290100740c6c2c00300d80e85d0096184111050840d81c6a83c600402031684000c00e9900104a60000401c002d9541f003c0203281c050340007400d0351b28418000d0900e03018068109521441080c04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 448824757 1250 448823507 448823513
    0x6030207080301030f0503090d03050d05061c06110909011508060d210c080a18120c03021905040f0b1305041104020d022a0d02032106010e04090b090d0c 67
    0x1c180d80c19242c01003503416070306040d858030300c0c41c0d841503000f886c0e00202040d68120500d0303040300140400d075100c880144901d0ba00c0408101d0450040c40c1d0100728000c2402d55130000c96050b6012030700c0ea04009540c1498101600c00048800b80c00f40c2c408a80c0700040d1840e5041c569011b9002900102c0039544602c0007000c80c1c0e101c2c2d14805000c0c4400c0c040400f22440c8426492040c94034a003020740050015a82d0f82000d00000e040303400032200c0050a400a40303000803414400c9181540103034010010002cac040c215404c0041811540c0301c80d6801881c40c4c0400b24460b580d601c599007400c85420800285000b541060002d03003c0b1024481800c8c9142c0b004020200703528034104008554101c4005030754030412007200340203000e04104880e00c185440413480d0f21485800792140c401f0302440440c1c0700c0141603402260703a84140302940589450600a07007030307d85c1103080300300c0c1c0002c014101021a44001008113044a05204007501d036003145405100c0724110510a10502600d1072420300348a03200780d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 448826007 1250 448824757 448824773
    0x1b05030d0b03030d1b180b030c090127050103060e06030604110402270108010b0a0207122906040614030606100216061116150e0f060c031306030207 65
    0x81100440e0349407403081c85155002d10880700c60402d0641c0811016511010400e600e84540b1505004640c840d41825503168007a0113100840c0c44601c0ea0b00e285541d030350b24644031a004042c5460501c149014040301001411418a042c03c007030710080701e005440e02c40014243e0300158003040e43d0005c40014006941c07008210198806d4100888051850000001c103000b0301c0742140780e40501c03404c207802031071810b468411070044201c00da81e01d6081e81d03265050510544251005440135a0000d4030420510404421000020f8041c0c0d451100020102040603d460740e8800f60840341c0211030100311092806108a00181484200d980c0d40c4900500c08a5a14080900194440c104805910300da0038070800080505595400940c604990740d944090680b400c20b815000070381c06154060504030309188500403c943e140b40c1344003220140703114142c07031717000c0103882c410740048280c040b94005465a100070410201c03024000e42e0745841c0d1043c068000c1c0c00c1c5030001401c26004103c0400850b42e01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 448827257 1250 448826007 448826017
    0x50309010810050406260c090f04020d080a080a0e0706121808070b1e1605070c080610030b090601050105030412020715030615090f090b0609031209011b0503 69
    0x1c1c2004011511003041c0c415445840d80c1c41968407500b85172011900d15044100a052001c03170a0000712060b810091203910b81e0241d02c242e64015905c04002041c402075104166007250010380721b03002c0e400b0540c403041c82561054011201080003102030040f01e441e10f22a8008490161028000c1c0c1d9041c180024107102c4d003903e01c0003810341c448005400141c540707001040001ea00131506595110f0920302001591b004990b5080029421840b451060409460540c490045044092891112060140e803541c0200078140e459041d100e10101d21500700f040700e24000c141d074141c640c2c031b41d0346145455032100134000d0007200f0540082c00100141e076004000d5a0700980e11000d024200164168201d00d0024503500c0f4070880700300c41c00c0e0f4610740790300365105905949403c141002c000e010103005583c95030507031281034118070210800b00800440c40d40300c290384600051049241400900001e481c01c0f0818011120704017000413150141d41c5c00c00a0301600f426411240c000950454a4580d00ea00039 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 448828507 1250 448827257 448827259
    0x809060f130203010b330301060c03050f0702090103050609010e1504060905120a050d0c0c020907030b010207180219020a0f32100606030b1f0c0209010303030b010f0c050309 76
    0x144504841c11550b0a42102071041c0700a0250140141d40058440c0116080100059110084a10380001881c1e54003280d041e21040d031210300c1c862040e82d404880e2684140c031010b840350414044d640050703440e000198001c5010344010000340c1450300e400c40c01c46104446a000366801003607181680c03505160707100e0340140c000100099003e07050400c10b050600c13600441102c4e144c005075106806401c00050040408042d80401400ea002c07503090700d00c0e83c019400654003102210001c0c240c1c602c02d4221024155040c41521589c907a42c007074030b820120540c4210451030350003040b008540ba5900300e000b61840c80c944001d013040030f025250484124060100a8019003004045140c0310303814550070032f5031b00c4144000300594030300c6015882e140d0082c0850005c041c0e00b0714030005425480f038000e111508800030150343d58050300303801908080700c0701c00c0c1410500003a02d00043c00741e0b032030180c96402140a40c502081103110500014040c5e50300b424070b9801c1c00040d60543d03000c41c0b0000144c4aa5403c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 448829757 1250 448828507 448828531
    0x1e06021f020408100509010605060705030904051812070b07170f090c1c0203060606130b0304050a0b180c100504180e0304122f1c08030103060b010809060f 68
    0x240c204108020340b1594104042c58410f103600f04144400315801548140407600080000907121400c115061041380070182c8903a01c140901702c0b4916080d0b0290b07401c084c50584105003c10407004050510425480001410001080d040180901c0800d1240c1c031291a19003051002d0100d28483c6c2500750192880d242200c035100080e001080c00c0020305400c840c001c10388134404142484001c001c000c0707694100d01030300410001c2015800c2403000c1d10203080c440090302801a05240c0b45138030700d40000b441524a40315009409004c54402c40141d0301520f240764130380c4059a0141121460410910f6150b80904500c0710308a00195011003606d0955000425080b003040c25542d0300e102800135900d0583d07407404002030001e92000d04ca040062036038441c1594158038030610281009840031003240c19400f820007144a541498990315015021040700390b041044401500c41800e00d41090300201d901c1503681042888e00c0d070b0085140f683c0514147c008001901d803812302e07a0000c08001d40762040301c175 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 448831007 1250 448829757 448829803
    0x60a06021e01140103120f030c0801050f0307092307080702330f0109320408130e010f0905040201020a0b180a083c070201091d011e0602 60
    0xd0020b400140d907078031450f000780345107503100d08024440d0f1154921a2001c2241200c1c0d19a0240c02070044501340c2d82d151321207807603507172800c4207103c14051101492035260240441c0401c03e802c07540309100c031142c0c41c600c0004610110b45400d07201c000f03002e41490244417503d0304010700c807940014035403c80d81c8c3d105d000307840540414241a03403014142c3c54002c4040440d40420104c401c022109034121030a000c803c0c4040c000000c1c00c0848000d01b058079070340a462a01e400d0440c000040f0403d0741003031092107441d00d004890010321006070b016810107551130710900300401c003c001c40201c20000d00361044d010001400e140d40046d56410300f000c002003601d890400003414035020051006c1e400c0700e4410a44018080750302d81844140d00c860284c2040340c1110000b8103000102d007010350300304e1015065520600d00d016070001000d41003000100d040015134600440c1d080741d81c0020011130600048014241d504056138112f890700da0820b0703e045821400d5040203100d41c0011504c00504051f081d8440d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 448832257 1250 448831007 448831063
    0x31b07060b06030405060702010f090c09020f0c0d0302090901210f030504150201050a150f1404180b0f06040b03030a0305190615020d02120306120a150f05060a0602 72
    0x1400c104000716034002e4012040006001c00842d2891040b1407a6008000e8801060f0759201221100c460103010454010400d01c61010190300501e54149848005410030342e15500742494181e028000400080e00030a08004504011823000d01412082007180f45028840b034054021005001020b440d88601c0119a002c2c940504200c80107029143c90714101140b0052020f80601025580c11007041e240030402080d10120580b881b0994500880e51031409141a034205840f8030341c40301c0ca40c0c1c000c1c1e407002c8443ca01601c0050421120b8847e642101842c5440742d0140e1505200030308a900542c00c101d40c02d4070a64001c000c0360040b02e45410001070342e85607000a03621034a074102c0624126031038820042000d034070401501081061a90841c0c6101495441c200e0700e910212014144c05001030000c155580780400004103100d040c0421204030b2030484d03e8004540400390422500d03282d84104c00c0003000007500810342d114000383c840c251070740c0c07405900a41e155011116081e80034000c0742c03500c5413 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 448833507 1250 448832257 448832261
    0x20f0a0c1a010603091712180c0d0b07020610080706030c09090905031306020c01050a030b030c090411030d020c0303042c070f032913020d020f0a14031b0706 69
    0x1d0084890403918072981c440038040c000341800e4509441007002c0401c054041a400c40c115481c9030515514480c0c151140c0020701c2200c0403c8a00c000035010f4900c0f40d4a0b10b407914001c03003941902540040166050125011741003540150504030b481982c104240000840043c1200071140a8500001d2507040e01000700c858030001c2d00140c80050070301d68034034240700c03001024015020f908030503d0040b40e0744000987e40c132050b1000e002e02040b4113001880d0528001d80c00206002e41c050150390321500e0703400c002007080d0307000c440488550401000e420700324202003014505a9190340010905500040c00083d640e0140c0d02c11001c040d08480c41685013400815060341c4100c8218413403190030705011202910b031282940128002078030340308081c040000805045510600c50038003265103100c01c5401c0c0300b070070348013000b011203210b40811005003003140c0c40c40245020803500e480107071a062140002414580328104600010b0004c0c404e1041c0301020410a100d08a0740307070020707075461856241141c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 448834757 1250 448833507 448833533
    0x9012717100203090109060b0a030b0105040f0e0f060a06080307020901182d05060402090d2307030605101509060305090a0b070203090f030601060c03180f120b0a020f0a0c 75
    0x110542c00072060284100f0150022014180300d05014044181c0c2002030145441c07007072001030f0103003605500410060805034418400c240d81d5031000708030040f644820b10b00d044003100422295510100810040e6911032141c000a0050380c0d0195140c00c51030340014088113018001c0202c0107030040c8511031130070569841034400c001c082d02404001c80e5549844e900c00c040045074240072030300f0000080c1c180c0c40c01d8801c80d0b40d010700080c000500c040103074031090010319030181ca880f2a4200c0d08151031f81d5030410001c8200131841254041048d02c0d00d01c1d034005003103001c0e601420400030840b00100341980c02607488025108a0320f00000c0950300c0c2082c0c6071900c5030718030b80034141510342d02c20b00040e1503011000f4103400705e0558041c5010000c01d010b25544a60900c07a0b600040c192041e076a000078032403480d041d032021108201c800d10a803207600e440c0300410243d10100b8801c401c04804400c0080c0c103281c141e4461043c3d5021424103007008400346032481384c800f54508100900482c0c000b042340c0511000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 448836007 1250 448834757 448834783
    0xf050c01081504021b06090601030309080601051003020a170c13050409030c03110c0d06050108060603070f05060a0e0405090105010608070503010f050112091704080c12070605161709012717 83
    0x81c86c41c00c01c03041c001c3c0c80741401c0c0004d4001440151020501e5040001c00504880000e0182c540a00c11f6000c114000c0d0000c20f29070040200040c1b00601421504030100e001c0d595100205648020304040010520400c1d8041c60203030781484a0900820b03001800162407540606194440b1681c2c400000d040c0f003020305505a00c074059030380940510102c1c0e800b00d070595a0315401c40d85030f61909010156078981e540704110280041d010240a982461800380115a400c2c0c18292610411400000d084d80c0341213070f400c03070581c0d9114010844107503c01c0d6020b07000011810720619550402e03596243d104500c2c010300341400300c04510381c030210046502507010507400000c6080070b08004d8002c5585540f103031181c90424403541200d0342980c5420081c2c485014804002490358a14000c800c0e02d05421a10b043c141c4000c261a0810120320203232130304145804800700701c543c0c6140d540005080b610305a441000841d0b01c14154181406070045050300380d4500751308490070b207141550003500d0501200030035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 448837257 1250 448836007 448836013
    0x6090c0a020a05061e090a05061602010e2a090f0601140c161401050c06190b0a0602030409150b0d0906150602060a0e0d020703030f03060e040f050c01081504021b 71
    0x20036443c0c1c5d6001c0000d5108400d95401107919503103200c0b69100140400074019400c20400b1030840020038120b03c102e0921400041210450012164200012841030b03e405a0300c0c202d582500710006010400200400c80d46406e09041030003521400c0c1300024151414084001481d1030200035240580e11030a034032504442101c800c0340002c01010b00f052080d50744400810302c030001d00e5800740003a248030440b03c00c001d104d55a501082402280e031105840551aa42e5220b1500c00d6152945010054002c80d0011961039140241440840d60a48010481e1101404d010301000144001300c0300f0790440e074100413464a500381003c80040084880329640d0008808001a9007500441c0841c071442c2058010407040d00c42c0404030340c4685040005074016040351030140002401030703801c118945141c2ca00010081e4072044041100c4206860550303040e0248074240c410444100300386261a80203192805060400c4490440003108803d1500d102d2038021450768290202e100d00380020007206421 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 448838507 1250 448837257 448837261
    0x603110f030613090f03020705030c01020a0209040c03020a0b040e06060a1d040e0706092103020601121b0620120306040b0f060403060e0d0c02010906030525090602010f0506090c0a020a0506 83
    0x400361506105c0d1a046016005514001560b4900810081810801038000e092640081e42c20404100402041201c1642d0305402c04005070f241c0700b071140040c05a00302140c1cae480d0304104c0007070807607030005120034402c2e20300700b00140c07005600c00c141180c28480ca446140071400c4440010b00a411202c540c08058401c00c0d2000a00d1988110140300f107138600d2491080541c009419421004441000035002d41d11200040141d002c04429001580e030103681030206010050400000000c401e40c00100080d100a190b0441465512401c441c0b80101200408040350100d1030150a80070042031148515640e07001ca8000f51907074850012500c20061800340e6598891a00c0780040c0076011441d0260711608514128040c0214820126140c058442505141c98210100c01400c00104101c004080d441038581683d59001c0d280120011503898030440d00e810300000908407002e10307a038110524105014016240c5540108a03000070300241041c0d5249400b07d0f0136444c000100000401912800c2c0c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 448839757 1250 448838507 448838513
    0x51507031806060501200a02090613020406080f010b18040f0207020603040c090e070b030103060b04020d1e0516121112010e0a0b01050c151015180603110f03061309 72
    0x80700760306484c0262141900c0600c4d0703010040400742d811102c40965480a41c000000d0300d0545d900c203a2100c0010800c2c10f1241001034250300780c5c0c0003640300e000455224800d00c101c9040498855014180301000541004581803054851340c0b910200380e4040c0e50b0b511411150b1116a0701101d42194015080568a043c0b600d041c480981052041282c802c0c5061012a1300c4440820a0021510f00349070f0241181d003191a02e800400d046101941c1c0180c0c03c110058081c00342e40904428408600840c2c01202c00300d4105c6015108002c10751034020509843c08280036401000e640c4018843d01400520540f801165500714402c14241600f0140715800014480e4444a102c07480388000003020310607185550019a407170301940c00841d10315003100d440300c080c17114002212540b02c2d100140080d4201d559100003640a054100c3c5140016180780d85c0c200340d400b07007920b40030080049140400180022a80040351400703403201161201400001058155a0b000326018417004940420044042586 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 448841007 1250 448839757 448839761
    0x4030203041a27090c0306010c020a030602072a06180e090d1107031a15060a02030a0e1807050f0f03180d0206061c0201030204080f0703050f0a051507031806 69
    0x101c1010340c80301894900d24200107024540d00501c1801402041030354445e0000c0e4103e40d04000c10b400d04120074401542c0150f91451000c80045000c1c0100507503800d41401c000b0050149011407804068010910742e89103140003154004440e107520300f01e0316132011040c1c880600d940b1903106602041c00704044c000000c2c5e0100f0b691440483c1515600303500014000c02a0303c030f150912028140025444507000300a000c41d09443d0300c0703007101c583d0100701c42130440002d00b07035003145d0700000c0140d1000c034041045540085441a1032081250500c1c00b20201c5404441204401000d90007081008944030b1005002201076a004a10010001e900c0345030204032140020703102500c1d403010384a60f604100901c1d0001c541c1a002d1070003d0041098401e00c0e14804041458154080341055400c0100140390f0009000c00780760141400c01038180e00c1e188d81071a902c0c10300303011030191050b0410f03032444000400008084a82484031100750030640d40c0c7c1c0c07a0641c0200340c40b5804907a503140c01c0c4540340400a5603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 448842257 1250 448841007 448841017
    0x20a14030111211e0a0b030120130807080d050913091505010b03161812060b101403130c1206050a0c0f0c11040b0a0e09120f03060904030203041a 64
    0x3045542c2c410365801100b089521520044944d0a000080c003040c0307951082e4010341c0c9028001b40011030010b00780030010801072031003250740c0008880480c0001580b03a6091410004045200007401400d0601c03182c581c42d200c05485c004140040000e034040c46840e14020050344403102d0400f0010b0842e01d00b882e036001c00400d40070485562a1100109442c40740c1e509482c0200300c01b4201c60040d03801100c1c141c2e80076804000401c0c1c09500400c1c0041c070908d00c80301c14050244104008103000c4005401e00101940c80c030950b2041c8960240080310f40300c030040030f40e603000c200443c0301581c0030200e0a1490b0a1200e513002046600d2034140040180720031900201e000f412610000c128840a10741c0454120310751068103800600701004207c003184e08240285240280140009254082c01c000507001c0b00700ca5006586003100c2c0b60400400b00000c0c85000154034180e11014a4030080c828205050310008210038410502c03c000b0800f414070070810f460241400340d045d06d9022040c070449040303039000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 448843507 1250 448842257 448842307
    0x30a08010e061c1101020f031b011503020114070602040902040e04030e0108011202090a1506110114011202090a0b19080601050d050d11160b030105090a09020a14030111 74
    0xc00030100e900d60074003e040e5030052511030088000001c9503681c02d8201c09559182034114400c00611001d145c0c810300080c8205001100c407605207000e1340c010a42954140c5802c015820380d214010405030340c020300401521500a0f0015a0700c0c0740c00d00c1c002000703010300d800241c980751010801281400c03c0f103120b0303400340780692030b910b48480c0c0b00c10044640713000c02d00401c1c1c2019403145010006041190041e6088bc041c0d120200355000a145084401302255102c0d00c001040f4105120148200380704001c00303d140f03000064100c2d0304000d078140c89490703c080b00174010080d140c005089294940d21100d01186d0041000c03c4038915107591004194907809440130314019040000b525241c88460b2480c625804000303081000c80900003030740e90a03001990252680201141200888c1140d0f182c040035060784500d058072541490300307116013180000d00501c0e409142607290005641c50407422812a101340081010349816071000ca40944074915444079460700106007030320000715060038401c01c108 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 448844757 1250 448843507 448843529
    0x1b040e0f0123010212070507031403070c091103240405040809101d310c032405090621010615140304060b06040b030412030e01060602120912030a0801 66
    0x41c082d0301c9185408190141d02580c0714000706040b00180d10b025203480d900800a40d09240d03520b0325417a0b2070904d40e11184400740c200285141c10014082c8201c0e01130400300d0350403c940c40c08609401c00521000d0190030782040d6403407510740b80c12000c05a4100400c40544188031038201880c11042e81e4210022540c41542e00c540605a114031401040104042135140f00071f10070200340901c060b8100010f08a00c1c8a02e10001d038a9818100d00c40d5014100400708000441c80d4001c000141260494125003807500c02c0d40b41e03544240900d05444105840040311081307820f4039a80000740c00081000d152407421900612903002010044d4401c1d82240c5854880700f11069405c0e0045446440c00165900d580300207102080115280707510994803150b024000784e01c1d1a0301c0f10b031000c0490300201c6040b503e403411048240c12856050190705003018400f8000c0c04002e04100020f0b4650b508900358171140d80d808243c03462942c0d2036152001856520ba02a00d554140500004020107424016802c08203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 448846007 1250 448844757 448844789
    0x51501091a06040b0c0309060a0f09050f0603191508030712020604080706110d05090a120e0a0b09031207080c07060903020a0e040201020a02030106080c010e181b040e0f01 75
    0x9150000076000c07a10004110910f03150600c60614100d0300140c0c1148124441841a90015100c880c001c010010307007030703c3e8050301c800300d50402003840742680c020314011001d185e544200f9071542c505070780e0032060892201800311030340c20001005203c40c074002d43d074200b100100000e05a40210040561602032110040c0b10701e0702c4441030f0f0340c5d207000b5038004290050801c41c0d100482c805500055041d00142400740c98013000c81a844141c0e1310944140b0380603000360340740b681040b94690b403e500c061142c6c10a4030089805000184a0194522500282d48000501d01d00705a81c02d1003031204141d017800210381c0b54065401e00000e01d40001045240a01c2440d0002c40c0c41c501880d1100101d81d40109075410203030500b00c5420059002500c103d066100c2c0b04440c0005035000e005039400761680f000140690035500e000140218101120300d4001d40041c0c448002c00380c040718419034410f00218124050314564520101340e0711030b950021000300c402005102da00000803004034100d44082c3c0006800c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 448847257 1250 448846007 448846031
    0x204150e0f010608070507290a0e120904020912030a0309150203160309060b090a051e060901050108060d0609110a080118061104240206090d0f0c020d05150109 70
    0x20000c207000b036101048881303002901192141c002009250322580b070f00d041000d86d113821440d5102180c00321a10480100c1c00700b1107a0b1045224880700c8114034402002184400b5103940810720034030456038015900082d100800c0e4680d000b020004035018021a542c0d030003040c00050003804544002c82c0c400b41c401528585418047c000c1c0c0707000b84e04108042080c840d4400d01a40108081c1d081103c2a071344510400503155106004207118031703c4072034042002d00d000018020030803606541182d051200c4c406000040d240d2100060541d9800c0c200300741c02d62a00c400290001c500944010146424403105404104602d60350140c410420f48110031030315181c0c00003d00743d0b060515940c82e1400300212820201d11036401220086160040240ca0151503848214140240701c4c280b400708490804802d000741d40c10405a58090140307005060341c5604101d00404880c1091508405c100762981d0803010756444582c1c441c0c08550105c02c8442614a100040824a100b40304014000346441c0d101595 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 448848507 1250 448847257 448847281
    0x1d160e01060203030610140a03060609120804050405070e09040f030813080712181413060b0a1211040905160302030106050a0813050105070216080307021305060d0204150e 75
    0x10303207103a90007460640c0c0d2102c0034400340d107040d401a007007000f03813410082e0500600d40005005600e0b00d59030101d02c0c6801d01b48042e182100c154081c94011043d20b0704400800c80301000d503420398904a401186544607004211088544009240e5020f481d400500c01000001b03034041e54103502c05d85071910203507a1304a440c42940010300c40074080340f904001d1000000d115040e521060202d5040c662000c00c4117807400340b81017800b81c0100e08003a100030210542890704130440e100800c00341c50b041c00024101907900300d084c040c803c6d0b4641800034601c407031580420250840d840d060305800029889580d03401312140508001e5440700360400d009001504414440e0007282d040c1c0c0c655440b540c0c5000c0a0701003c03540d044000b805282c0c0344c0c43d6a41e107500092428000d6501468095004112000061945140307248442c0e00011031a0700c2006000c00685441448101a0041c4000003900341d41d0100807807104a103450b402580103251913107185041034852001401d48004c0031001200307543d0b6222101c0c4d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 448849757 1250 448848507 448848509
    0xf041d04050f0a21020f070f090b060c1218041109010807020a0c170a050105041a0114150a1110051617160c05010e03370509041d160e01 60
    0x860060304c28007080c000c0b00140302400c40c3c3d00510450344600d801180d403509000c0182c01003100c038114204100803090090007a40000782003101c09520740700341420f20f0790740c81a406100c0c200030f00b00440d10100f0315065007050010048081c0007404803a50001500106900014807036000c0381c416800300300d5091000034040440b90b0711540000b030325410002a0700b00380036103e401d10000e1058428100004000f8061540a11311580340000d10310049a211003030900141c010400611105920341815a9514501c0150300364841ca040e0781c5040b0300c54101e034016510101c0340b04600c0303602c0e00f419228100b07511a034450394030701100b200940c1d55050111040f0800300c8480d0488081078003c074454880000c0c03100c1900d8040e050131008a02c144e80e449094491801c41d04c403e581010480c222026014250b5200d05c2d00d560070045020381e41c6150303512161920504840070458081203146854a440d0302c46800308000d02d540c15904c0ca50392400c2541d50400340400300c424007903002c000481c05202c144840c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 448851007 1250 448849757 448849763
    0x2070c080c0f06030c0c1b0f030313210839100b0301151202010e09250504050a0305060a0e0a02010912030507020a0e0403090b1c020f041d04050f0a 65
    0x101041d0b0040100310702038002409806070184108a03681000740f04100d5250259500c8500031614002941040f580401da00f2465029403c104001c28500f483c030500c94080c3c800110006041e1050286007007071861440a00401d83c2c5000038680d4448442c41d8025181c029600c0e0013042d0b02c03059200d044400c00346207905254642d1090107507c002615a40106d440d9240160000072524942050504454a103070701440e041d09681d030b00d450070755074840d11420304183d054500558a08084042250720515071001000900710080603500580c0706000b03c90040100803d81e00c41e464403812711039220b1000344c407130700c990901e44069410b1401010840d08072540d016169120b50f68600840c1c0c40300c117039141c00100c041003400c102050041e0b544202c9a0b0107040126618100c0d03141c545005000382e1165000070804400c03d1100c0001200d0800f01040508051803000d601c61080742403c08071383c0155000f080302c01519035100b2145081d070020141c4110b01800c00ca0f14010300c2a2070003a181d800c10b0f0009 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 448852257 1250 448851007 448851019
    0x31206091a0904062a030b030a0804051c060f0b1906360612050a05011a131815090b2407020918010b0102010b06030a0c020f010203090102070c080c 65
    0x22100385030102c09168480e00036040811034801560024113480c070716581d0102900390180b00d40c80ea481e814814030320b001006030000c2262042c1f641750390100d40120f00c0707a10b1140111107040c019607019908106007007a072012041c002c1d100c2c240c40d400050308021090b140140c038010348540c0010f02075000101124843d4445640e4014410300c0900200003c8524442c2010502ca008001240303001010005000e1a40c03803402d076401209034001601c4029000303103107050400b401030001090181c0409510080541103655410f401e00407201c0c4014954400c10494410140403c03104050780c10001081c02c115480c00402501c0b10441c20031104c01c100d6081e00600d10205890064140c4114482e55000c0810315030706004545c0d002a1441500b00c801800c000325806d610000c0381c1c800d003e0380103455001d000a10200e0042d001040441c00700070408800f8940740c480b000a42802804502003001c800c0f8000c3d944c0303107050415a8041c4d408244c01300d4101300142c400003518000400d03031680d140401480 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 448853507 1250 448852257 448852301
    0x2a2b06020901022503080307110f030438091306080a050607140909061c06090209010815060f0a0e040b0103210503042303070c050406090525170403120609 68
    0x9140598000902c4030302840b40038840170342151010441c3d001e2082e00c0e28010760380d80d41440312507042802002c4a80e02144495037000000c00d2406000d01e11a203c508100b9403904850000548140c12218562100318a00303100461524004241e1034003441c064812141c094a81c0d5104454500300c5000070411404140035044691034100c80c91600060000e1100341e00401d5101c0807200e00a014108813151565286042c0850401d2605680148000c1c005060003480d6564010407031800100000d20940032030204d011180d0f038044c1c0b180082c000e000c0e1a80001d2906203009482c0541c280403d40310005120141c1d0780c200402d03c2d81c1c82d0340001ea96034160940e2100d86d6103003000c04016118035600120705c2812a035100b07080001e00703505400f0306220721046240c8030502003101c115410024006080504100300d400c080703422165020a40c180000240307092820855841c01210175059180075000f0902003455840b2252003011280d80000700710845c0d40b007941c031085803011100c0c000e9101505903 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 448854757 1250 448853507 448853513
    0x31e090904120905090a0e062d06041b11060c16080309010e370f080c0c030d0804110301090203070605130b040b07052a2b06020901022503 61
    0x400b981c1d409880d400c0010310f1a0319000002d80d6411300710b03102040c2ca80d40300d9000380b21003000c002054010640d2070380060a98060041142e503420380c0e95001c0700d40191000819884e07110f55000143c40361a00c8103c500085c0e4208008084000144c4000002c2c41041c022801d0003440c042200d02c50006014104000c0c0140c0d41d407641b144e04002e00149843d5601c85201c410700342c01384490110440c2d041c242c3c0f2100f03055004440409050b100018080b9102c0c1d81680e40010124030301542c0060300702c48407a440349500140c042c07070302d030041c80740395014010002e804140c1900401524083c0307101c0c00f00c00c040c0181c001c09060887e2420007019505a1200c4005c00a0794000d01c010020704445003c100c450a40b40c542e0040c0b070358441c0d480b002c0000310000350502881010300c90a0942c5601c0080300200001e0f01c0d02401c4044090b5150511501080148403110056020185c8001c08072680e00c000c20f80660401000075080385030400d0240c0101c0714090400d107144911002c01050203000f11031010b080d51 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 448856007 1250 448854757 448854773
    0x50907030f02120d0201060501090e1b360109080d0c1b030f0b0402030f0601081c030608240c2703070b040b040914160f0905040e031e090904 62
    0x1e07090303801400002060721007010501c00090602a60340000c201c0c20301d0030000502c91140c035889100d06440d00c1c024011092281d20403c90101d0b0906c10340c1d5210103c0f9024541280440505c4411b900410355008451040940c0440c2c84034209072036080b0807a683d80d42590b141c581c503460510020300c103070440b8000124212010003090001d6a80e20340b0940c3c0303994910380650b40c19501a40c0050036801040300f113260802c61210001181d00c05080294580540265a800c60007072107814500720b0100d020000c1d209a008d88018140c020803038104010204040d240d81021041190040c142e61002074003000e0308000b01c030801154500402810003590800c5503006010011980e890301a8000c0040e00b00041c0003d0405017040c0c164503659189440c90780d8045812910710310b028840c4650420001125400d154850210241803420b10f02c00207001c1216951200e4010961052600186440691f8000044c202060034000d0054281043c140b101c08280100002e040c0d12210f40c0000600140c040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 448857257 1250 448856007 448856033
    0x30810140d030f0302130305070302040b06040302010f0f0c150f060b031b1605060103031115072c060a0504090e0145121805030d11071503091505090703 67
    0x7440c0c01421b14142c480350300c17202c450590094030b41d903000307900500540c070300307889003070f08050701298010316040c51540040e1101070050301010a208210840340c903c10300030b50544030440e80c84030350000c2c00114042c1120040402a0050003180c0c0b424001081d103610318411a4000e0748014080322104200b0100400c1546c001a5010580d200023030105001070700400110f0f000e14442e4941000e8010b0300340301d90b4900545d40e0040202c583c405420301c415070b0740203c0b110004a2010b44030360b00070400300c0c0304455104881c1e100c00d41c00ca0350000b0b081c412194824040c000361403007803009100381983d0101c100d09844681a10322940601d00d681401900b03140c012000c00019090a6010712032000d20317290100d980c4442017690340314104030380700082c0c40e8003118401694410002d0004154101400f0035074919101100c1418032800e4800c03400c0d00641007040e40001c0800e2203000f0207c25041d0317401000352401060803960050030310300c000101240e90003614400c0c09031400510b00e451664848400e0070001d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 448858507 1250 448857257 448857287
    0x504090b0a09050108150a110301030209060102031b070f0603140c0703090b04030c1814070509010905060c010e2107060f0f150f08010b030c0f01051303030810140d03 73
    0xc00024040466006150017080d50310080d20009030f1030603000d42507200042139000c01616100b240008159220244d03815a80c054519400c584e0700d820060345103119501444100801e0b5450304070580000060101c1522540940780944a40d241c2040d030545681844d59a488825000000c03694040300c009081c015000c2e240a0445994902c03012803194001c1d0400da03101401e0407010b119010890800b090001c4000c001000f854134140282101d0b00e50291034003041000001d0004c506038480c3c0b034504d010f400000c2c0015074641680d81054004d007452a2140103030700400d07444021b2101c105600f403000c1000309401514111041da501d000405500020300710881d40c4412036009d8400d180f00e40001c4c00c0b50045215103040c1060303000341c40291507611220413a070500041502d40d4501140d03088450b50180d40140c0410710318801a603040c002c4185020b0520b0440c50000f0505901c0602c1c540079400041c0400e18107030700c403280e50034501e01e490165504441c9a846260010744540d0160001c0c6003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 448859757 1250 448858507 448858519
    0x1021623120904111c0b0901060206040b040206040b0406021e0a0f080d06151d0603010f03020d0f050322050603060a21021225080d0804151401240504090b 68
    0x301d044d150f09242c0c1c0054640004101094142c1140305900d881078000c204011140c0116a6140010081d62000024070080c600c0740c03c41d000c40c4c11522048140c038058248011400d440d03d4403054000c1d590b1041245103041040d07100200385842c1800301c1d54261450b00141c450040e880c1e0f546400b512031784032582c001946640d5040c0000c03003040c1401d510712528604e07036481103141103600e04c041310301c00c400381da140c4115000c0004004480480c00308008881e416aa03c1c5401f288509010080c0000c2107000f4085010009410b000c0d00c003c1410340c03420041d00d25512007499124814042e01d40011100650040507441081c88a5044540200c103100c00392102c0e4014003003243c1c04910b184101d0203c120341a03200e1a010060351183d41d0540b81d15030340170311100c180140f51010450346d4000c1003112205100b446408901440b0664194030321150f4204400c0c01481c01104507020450824860900c1041da0603070050301b10703009000c04014190440d680c9504142c1041a0800104003191559900213 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 448861007 1250 448859757 448859771
    0x80c09030604030c060c08150409020402070807141207110103180c150e0409080415050d09050d1412010e1e0a06060e0d26070501021623120904 63
    0x55001c00505110b14401d9448000105040c07514000390b405050003403050100c04010080c0040000307c1e85606810300300c2d4003203402010790011030000e114015024085a00000b614400c0c0a40700d20a1080c5d041220125044071a80350380321449801001ca00400b02c002d00c50610707040f50301c650041a04034204150300d124074030003a0340741c0c10b0061250b84101e0302c1e11620b040502c1c0d4250480b110720f80d02d81d000e641c1800095820b83c1c44440901c118066842880c41243c80708103030318460801d80e460151011800c00403001103003499a950311407546131000003005c60f079160080280744010b481100e0302802c0228001e0342843e2440388c1d11903004180301c0b510416071480c130f400215000d01403400b8031515440040e90360f0426400502d107005100c281c90141600c44101c10005001d0700701c0410b104001c82d03d18000e80c441e200059414411104051310715800401c1400f810000169100c000754800d035003841440d0b441525600f0050340c1c0182e0240c00d5003009816085200d080f0000302440000200001a12 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 448862257 1250 448861007 448861009
    0x80a020315030f0114060103150b071a0109020403060506010302122403010f05060901080a050709020c0102090409060b01020d26060d0b0f010312170105010f02070911220312080c09 79
    0x1d9115040554981d1034814172a055090005155045036003880c0500c00c5c02c0160b207504a15503054415210507100002e82d803004c2c03004950503500d02c10794590102c02c0559483d050340e4003175040b501003034403a10b250102044003503001e4800c403803a122040049101584e211540d60442000c51039410140303246a600d008060b03a000c1c030503500c813014051800100e505099003449507103001604054041d034412028000480c10000320ba04c125403402d9009a40c0340460500107000e0301031021403503005410710b20000708100380354200304201c03202a42241c0b01c90780784c2c82040321a1000c103081050103040c0313902422012850312000310b0307200002515540c12418955140030b45614100c0304604003090b200e0050003080000c144071000660305241600461410902040e1294010322540741402072040f00c14140d6802401150001c10840c0010010b84107015081e04032a40b11541c00c0d00a8000050746c003524261040100c02501d400150f001c0c800c84888005445a1802520307814040d04148101212 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 448863507 1250 448862257 448862263
    0x30a0e060a0239040b0d20031006030b3306041a12010e070504140d21020f011406190b07030c030e0402030402031203100902220510080a02031503 64
    0x121102004030500e8191440b607400440110b1140f002e842207040c07005085069490100211000e03030400c20b0004a11502d00c0c400010340d10f000e00803030b0940202c901041c00d140c2c8980c42441105e01841150505d40e950011204000c0520700c00089244544944030880d01c5440703001c40d00513140644a40c0c50541c507220700201411409292400440d80002c0030101004607081c050300501c0d041e000780a2a0900a201a10a0045008511160060514034000d40d030b515800c005a1980001c1c0340c6242e40341e04c0d01caa46084041c3c2e1001c1015206108411480c0081480342c004503000081015041e0340b200005c000c02c1d10300a807002e01485600503808500c2c003550f08000c0107124841c0d1a041c50f030307408038500036088002c070a451500c1355205104020141c1c41c08602e2740c881d1042c2141c3c403030303580e039991101000504054000054052010491405000d0042000e40c3c2c0b0142c0101e0500d4090380d6001003262896101c08100c00080915000c02d843c80003d4000c1c1d41c1203011030008c1e0700c54100c2440800d103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 448864757 1250 448863507 448863553
    0xd06050418021f0c06050415050405010e0c030c01080f070e060d02030417041401030f02160b090606090412050f09090f040204051005060a0c2102030309070602030a0e060a02 76
    0x281d160744020507104614280a0300500c222503005220103080c1c0e003280c040c14021004002130241512100040c0400020b69030002441500420400143c2082e091490091261501414240c8140700e01490745140000b64104040720503500c1c0e440e00d9541605904030074801800c4802480b800d1400041e071540d407400a015511008100142c4a140500301a0402c00440c0c00d02803100b001000f00b03001c0300c038201c0002e44c85c900342824003041c0c3d42421940a8000e00c034030000c000008104002c814108004180e0860050800c00111045501d903c410090004825200203000028040148030454082c8018002646075030b1641401c2510100208101d00000c40b5030510b2000004200800c40c5803074441d0540008800450b00406070410020030203500c1481d0b00c14041c06080b1090a0400c284500d24000444c0f60034111180e1181828000e5a60380040e0342c80942c50160b420041005807000051f1040c010485d96030000c03242c0c1c0744061082a52140c040c41c0e086004011840e42044d42e0109184 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 448866007 1250 448864757 448864781
    0x70902181903020a03200f130203130b0108010902090f07020a140f16090f0e030315040204031202030717091804060f06080d090801060803030c090a2304050112170d060504 75
    0x6c40354040360084481009089002a00c5011404910401615001e800c803205039001103005941383c9032f600c0001d044840d078410040101050b400082041003040d000b442070310b4820380c3c2e01030260311500c0c21582c1c045021030705a00140e015030b201d40e0204941c1c1440e20155140941541c0481f82c0c0e500c0080d0070802603004030440b8a00701681001004000d228050007428294410001001004401c80d2603200c040c1c095001090f0340040e101850b929903040f180256404a902080c0340041c0700041d4886e0088141920020715940104010846240460f280000d0081085403014141d84079019a180050b106a0312943e403a04140b50f046241d01c140805014070780c001b4110b4882c4084010701e01035007038000d2001a414076508100e0150000309413500054000d80954440b184500070031151491944424261002140480c80d1840342070110000300d8001d950500c03640c0c0e26070b81c82c2c2507280c41c01d80d4000d0061203090341030398014040c0005070105000c41c0c04003242d1076945030009010780308012140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 448867257 1250 448866007 448866023
    0xd06200705061b0901080703020a030e0312010e0711210d090f050d03141302122401150804030c060e15061002010e0318010e0d03050309070902181903020a03 69
    0x8041c43c400040d100d40686403074030b102c0a15052450000a0410a014051109042e0040b03600355089000ba00709420214031078007143e45804035110448403c1d4000e1240506e41e0000c2404507100901c20301302c4540b0099190f00500b90f10801c2004040e10314001d40c0c012075031510921449004119502520034501e0144503c0c052500d8142000382c2030a14051520080c1403800300048445200c0c49501940035401444680c0c040710980089070390407a40100c02203860040c007803002c1d070200b5059070030754045101000543c02c0c3c0c1e8071140b000900210004038003010504e00c41c0003c0000348150903a5101c140300d81004107221017009141481c0c84403604040f0078400c044c074108003481c28181c034503000c0120360384028403280b50300c800416200d109400d03801c80220940c02c1011103990162034403500c120005007540040070035609000703000760400d440d6014036004600d80080c04001038025103107421240a408052030001108000110341440a00072000340d1f8980000003594071a00928010b601503910 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 448868507 1250 448867257 448867261
    0x41802090a140906031c0e0d02030703030f030609020f0f030a06081c02010b0a0e060904062304140a0b071b1a090706090e01170309120708010f06050d0620070506 71
    0x40185050f001460b03c1e009a02c0300340354801102651081c01201c42c00c1d800c248441e8495000400c000303004894000e500752003420400001c25a1218110103c0e034015a0100982900c4105c43e1090780300e02040154003000611403814122100001943c111010880c000780e1075644510150424550405091608480004a19001d902030089001080c401c84580f01550300f0021010590000900460300071044a40024100801c650040b02211805401174450154003440c08c6400d4900326012100080b105034800481e0400103007459105078404003802103966002c10840e603103140012018180d901c49002000452642c5140e003952113000403000c140c52034030300001c6180c0415640b00c403042000303070785003040145289000107040da2915091541c01058503c0450314500400c1510b5510598150140d0320403140019211b0854070028000e01002850f000507008980032481040e4004000c80c04010004d580c1d036000c04118a1508400481010488848061034000fa901110241d2000c41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 448869757 1250 448868507 448868509
    0x308030c2b0b0a121e1509110a06020d020c0103050c0409020304060c17011815050414040b0a0b01051b07030506150315012402010608031314010302030c041802090a14 73
    0x3d1610b000d4614090000010006a580c0c0240c001c049094002800b50b6400355204202e070b00200000a0018440241700e03108060400900d03102c14010a98030800490100113649800421f400880d0f00c803640140c829520304500560203807a00803d07140081900b004046100300c030a10185000301e00a52000032030034088031000e0250720345150151242c01c2244010812f943d40b510081c2d05100c010000800c1d10000c120510b01c1400f56034000650207070030407074109500c545001070070340300c5e90041d51800d0460b101c04110720210358259641a000a40801c0010038102a048a4004900c2042d0480304c0b007964a40b01c0078100740301515003040e145980001401e13946130801140d1f9025501c030107441c40703e51520000c44034118129000360008090400b0f29503109000794030407801022404241ca5070f4070300d0800c0d000c0f410905070160300300016a112aa2426510902c280e91050101082035803400c2d040c6041c408100e4101600d2421480c1c00f080f51441c2600d030102c100b40145010701c481c960240d040d070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 448871007 1250 448869757 448869769
    0x60914060705030708070204020d05010306020304050c0402090a0e1803030c040f06030510060c020d14030702210309090406110415030c0201050402011e122a0503010308030c2b0b 78
    0x4024188104028400074000c503601004640c00941d10035a002e94a00c094800b043c041d0182e526400d0041c2d24101c0004140f0489030020345c0b189100e04196000c141181c0100070890060071400d075044000395000348640146103040703170307003052504e040c00e200529550115455a4411109040d60283c041000c00c42241c58075044005018241001c1c0090300d00b0351608044401c1a1041c0020803080301645010b40d1924200e60701440e40020010300391610343c0b00d4165403a03002c42c004034000c0c5418100068a05601c803200b1100c0c0100d0300c0503601d44144041008059134000e00700350b811541d2851400090381d0740c10010b100074140014a00c550303180e004000f404490142201c08150f9051608000c0146c2c0c1c04211000711403000c1c241c07500110b074527a800311901049030030413500c55480c10401c1490040114440c1c00c03143c0003401440080c0c0c8401100b11110701080c0700003040711405101080f0710312034135001b41803604030b0305a0700d20542c1c030514404c1c100c490000039000c1c0203594440760425181400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 448872257 1250 448871007 448871039
    0x114160c060f2307111002010501061202070203060402040b0a09050f01060306080c030a021203040b070c0905010501090303020c1c0803100e010b040b09061e040305100b0907020a02040b190609 84
    0x83c285428141840c0c0c003103034900340400302004442e1070001061001c00641c060a00003201025094081810382c19801900914080c040c010100343c124604840011799030003290301556015001e4030540d2195400c2c84054a59242030070740c000500e032008170b032140040c81401e10412100810b170440d54940f10000d41102d00603007042d4419040000d00080383d8800280c1012a2541030b0303100d9900d002051008d80c2107000300c1d080f0141400b40041d64505100a001402c010f4801c0540200f0490341d03540010360340d581262000501682180051a08500c1c1c100080c81320422008040042c02ca03003550380c5d4a40d03903c1155103030682400a601440515029000d00380507180390002c040c80c0038200200084140a05158540304500000d1181c50320342d00c80c43c0062036101d1000606441369100e150094031948400c0d03403998118034020034a04640b4000300d005d07008010540142500301015000c1c0b101034006141c4071508940c00e0400c4145110a00c2c28a1000f00001c5c2c0c0e03240100ea0400115040c04482 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 448873507 1250 448872257 448872287
    0x3060506210a050708041101140a03050103050111120a052706070e010f020312150a080a031403130f050703050f03130b0a0503010e13150204032603060114160c06 71
    0x10300f40c10480b81c2d0703800140340b5801541000ca40740401040c5e50049503649001091400340e500c0120394440b0b03042d010780144e41aa40b08100904c40d40c00f42007440c2c4e0807800740d6180c0001824403800030508843c019848641c0001e0541c06c0c920204c0f204044910007040705107002840c1da40003000b003001d607991040310305075514802d2030448410340304000d00039502c0c0a110070072400b5100341d02c0810b00a551111349002c0980028009600107980c80704407075222100307600280d000c14920001c000c00ea412003803c60340b080400d03400d01130045815860f01d00d0070105184007150325200320040070010030310401199880c0100d42d402582c0c0c50b480341050000040c015480780e5010102407280d05055600002940d06644004a042c2100e036980a035100c450150100081d0415180e001e040c0c0101d2105e030000c0081d43d015150410001c140342c03040026405413100740075045442071011442d99841180b04003041081001d00c0c5042010041400c4ca0042c8540300445042c40403175000c222194220780700c000600030b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 448874757 1250 448873507 448873511
    0x90d030507210e010315080a0305030702150f0a020706180804090b01032c0a1718100e060a0207050901090203010503010b0603040b04060b0112090506180102040303021c03060506210a 80
    0x4060050403c010340c02c0200c0c1850344070b80020994400360f02000b0000d04480c012906214440d0a01404591040e00c92100501500000d44007401d80340f402c890180c540c5008214055958071003034402500544412100152503420703c20503034803e041d580b500d06000e0b0350104d9807030b8036180844084450904080303040c10305001050107014840e060b0b80350b101e01c50800420348402c1d07240103103060480c204c400400c20710111801c0d140716850f000280c96007860495280344c0300304400c010082c003039001c00b404030002408080c45480900b0310001505200074980111031038a9100c0340010700c480000d0300070b62041940413004014510b824068451501c1040e0b5440d85076040c2512001d0410300024400f40c40d441c0c481d0070846059100711420900c80c0724001040140010328039040c0d44171041600c0e5800c0715000300e907450845070010b00c00c0b501129490380042030040c1c10307259240c03e440542c48a1105040c2d550000044581f20b0a00504180b4070700140307403005555220703201602c2c031006800480340138 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 448876007 1250 448874757 448874813
    0xa0605010f0c0c0308030c13061d010306051012061503090203060a020a080c03060303091e150a0504230315070f05072312040920130b030c090d030507 66
    0x1038070303400c007142c103803600005c0c25581d0340e55100224803e4811408401d02101003440001022a807092201220f4040c68170352200640150340110180d41c49409030b1540104a129400c0c68071f030144c411000d0303900005901144403559081e8000050b40c0c0c940c5032402003074540444d08111701c0c1c1440a00c3d40107007480350131070911042c0240106103d0005001e0340c03000f040040818503541d400c000752581944018030b480faa24241c04051841c12100050f080d008600c080c41e0b030441c048110040e9030416040340e55a41c2420301e018501102848000080020407401c800e0540c580d8800f400080c5103003142d003408100b20b0801540082c6200e020b281d601081080900410b0000344401d0388600c060200710034000500380040f0b9406007003809000c4000002440050000f54002c51030704100462040c20340100d2070000b034920842004e02c1a64104644040c4c1114140060302010b40a035400c000b050b4502c0e17003450a02c0c0c0210740d010300b001000340c02040002c1100703001c1110b820540e114003c04800c00300e45103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 448877257 1250 448876007 448876013
    0x903061605040302010f0c060501090e1614101106010e0403020f0c011e0203090910080705010e060a0305040f08070510060b09010c061a03060a06030308090a210302120a0605010f0c 79
    0x507001c2e0b400000d040050410711101c643d8400c2808043d411f4105204100d10b5a41e011480010030f50b000c40308580d030160007c1da0003a0602d050810b011034210f0710641042c5d1440b1010404a950250784440910581a18951904d0400c000b02c1c0c0c007038100086003900034201802c010381703090a10300c0a40c0b0b1541c0180b101d0600c81e40e0001510840c42c10604100d6510411080280e0540c00b84200c22a001020402081290002a1030802c200c0705103900741d445a94668004540100500486070b80089042100880d51442548241d41c003d004041c6000e440400360781d0720031564401071060b00c05900800b01c030072000c04d003441680d00038086e191811b41303444010700000c0c2c0101000c07003026102c50340e00e0310b507001d40c05081407202181a400409030340761482c1aa4203031004040720700003900001c4201e07000842402c07000130701d034104a4210902c08480700c4148080d111901180c0b941908158082c05480b40d07050110f5a214042c0550310070119510741046c0004013000c444005500c02c00c07985d1041a008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 448878507 1250 448877257 448877267
    0x31b0c030c0804080f0703020108060303120402060726040509070c1a150402070308150111030f0a200a020315070e040b1207180b0402070201080c090111011109030616 73
    0x462545420000303101c1e66141018500d601440d400803825000d060011402800080b480c68143c0b4400d88415100e5128001410368900403a036190601404180224015140c00009406002d10030328081c02246850492030480d009104008849140003203400c0c000c0e480c10240842e40f110302c51070110000050394648840c2104000d5200b0700000c00710740440c46241d6244440d150480003d041903542d0612460014000714040340c642501280d5100703036107019841600c4a0440000a10003107091018070200301206034050342800b8148071a420000a0124014840341500e030a40000b0304868030f624010b050070110010810302c11010800104070b5243d40140e0112207829042d500090314852600c0440c41d180040c00061110780310b50303040060000b4619058240403105404184030021010f81800182c3c01074040082c04110820005a81c0c078a03814081c1c41c2d003d105160a0000f40030440c081402c50743c102804102a0b800001d20f451242800c00c4815000442d42c820500300460710030000300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 448879757 1250 448878507 448878527
    0x80f16080601081e072703260909180c01030e1c020a0b01091d01020f0a0c0204090210090602010e060103020a030f15020c160e0f04081c0509030a031b 66
    0x2c140010342000c1440c42c0d10102000b0080300c404e80030415a0b050208000d40701c07441600c00d590851034152a11041002030b45c40b610708495020482c07980a000388402c03142504e066060140d8940ca00f0b1020704500c1c0e44000501d401040c0c420800078250354003210030b07410040080301307003818142014561150840300244481012819807201c0203001d45044007241800524040038040d414034030700110b042c000c281c1c84270000110303500300e03681d480600c45203041c00c1c0d002e0840030b103901d0b50040c4000c0b200c0311300907000c03502c84a2008100183d021040d80c00101170403445880280006d09800081c4420342c0c092140c40c0d040441d400c0101102d615590001d690480b25010042007490000752107801c01241e0300d10004119401d44007503480e45100420540e50b1010404c548a410300004400030b903680d10003111a0048051343d140134881d5841d43c0b030f890201d40c0400d0301071410f0301c41000305018a80786441080d0180c1c4011010396134a610303001d4000e00742c415492440902c144a503581e1035030b468026070200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 448881007 1250 448879757 448879759
    0x61d06040203060112091a090a0c060e010c050d03050403080714040911120403030c090611030d0e031e030a150e0a09080403021e04060902091c0f0501020a080f160806 73
    0x507030349542c0c45004864409150114624481c1400480c1b400c000e200409803070700c0c01d0302255281a981e1180141a81d44840e0640581500440c00041c000b0b60310130801c000700c09406060a420749151995100d26102d4040c00030710009a558082c44100b41c0e025400b20b80100c41807a00e43c2c080f40300b00e01181894030aa119800a0903038421210804581120a541442504a482100381e1400d410081c010b0480c01d0300000008a07040004902213009034160a00310140e00025401c055007046064010032103d061205603100901200c0d05a440b0245405401c01c43c840c03510f5241d0504100f03031000d6508800d0b0381c0701e2032400c4001c140082d54402c41c0d19984912000c0300070450780c0076428503004500c5181c10183d00708801460310400811070300760440c400b5005841c00c12046641c0e1481600b04c0c00303502c08407039000c5210002b20040ea03440a0001d002c05021305181ea100c58101d0b5035060899000040100228020400700704280c021104155806181e4860484a0102d4042d0007004502d00400c0c43d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 448882257 1250 448881007 448881011
    0x40812070204090204090b15041803030914070f090f09030203070803040f064101060e060f160c06050702010e091e040602030613110708031f03060f061d0604 69
    0x45410765480e40c02811810340c010b0810401140d1904146c2c0030342808031207020450007080361280d42c1d41814402c541400709414a0941031601c961b9088029100080d0166074125001c80c2882c05541c1c1400f0a000400246003204142c500e403180030300694180000404d09070f80f07010108800f02e9008403c0b109101e03800100305680c0d039520300e4141c0e02d4403121400a424149084e05c00580e40c003c131141402d10080d04000d0400008600000c44107089103440c10301c41c00e04031140100301181c0510428901000000d248609000340f000300803440741c2041c085002d0900c0c40025030810b001c0500c28034405081645010340c43c04030360350000303400c01002c0d10030075008801500002c4c0d4880100803c02002c121074843c042c0b100e04242c00d240f00a9001aa032643c4940604c1e48888580f842c0e62240050000d100c6501d1410301c1100d4441440542005240d0540708850300d00c01c007808030b0b00440e1b0360003841c4680000207491040d0545202181da06130408001010030903400420301400b0750314654807150803071b40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 448883507 1250 448882257 448882267
    0xa26012d030822080a150902030c130e0a050106030b180309060306040f0c030f0617060a0b04060503160f090e060414190c0513020403080a0e0a1511010b010203040812 73
    0x18080340103a0b8881c0c0f0b883d07404401240458401c0000c00d0702c03030006004200e0700205038070040c05542154450303c002503056000b941030310f01074240320100e2602d1101c07c1100003402e800c0c481c042da0a1a0317400c0390032035469541380014020000e000b61516042540207407445003c0407620b078041e03034910074108018800c20000c40001c203250b5440d08001000034500c0f8003130003800845140600034042c1582081c500c2070800b0b1021a010300840102c1002003d640f00800f001d844078554503000341154403a0fa40c02c1610740001050586040181000905035030f851901207511340f901070b21051140d90010b1040c40c0c149010551410b00c0010140e8020340c000311424a0b12503900745413032070850050b44100309000155070301800d00001c03058500031a9400e5400b00041d85441000d04220320132800002c2071801c042c02243c403c980f03d107100f2607001c0c0c1c2c05031680756003e445400306d40001000300301020004003020075401c2c102c6800e004140d01064280011410306040c5003485445284131821a03004601c00301d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 448884757 1250 448883507 448883527
    0x2120c1c0503040506070b060901060302180123070c21120e0102013e040308040e15031c0f020c24090a0803070b010e040f02060a26012d0308 62
    0x304a80c01464002e101742d5460009152072010035800702c4403248101c4144000140182c081e0003290300b11111045044141c50103400190f42d100c040c0381c8003800040304c130b40c07200d00e05c154a40300a26500340a80b0208240a10b4090449005101c1100107402903020084641c0026011400444a015903040180d2601c3d00440101d0041c01d00c50910045c8210440c0300c0002110350b0410106040c801c10768101102c400f910070503205100341e01c001401c820040108018081100084035040340010300c1c0118251780c4070002910703004060070302591340b24010102840654200040c84030706d645170b00180514609540005100389660310b41c5e0344540081244680601803140c00300e400e100401807032585001d48652002e075480d00400821141c400d2410000300d40c842c07034614420301c01d80e40402c51240f44045c1c0c0e400c0c0201604068120380500ca217501000c02d0b04841844000c800702c05943c1c6900310366241451824003031500c034940065206100d8050f01900007a0001e8400b07890708480c4581d50348407011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 448886007 1250 448884757 448884763
    0xe0d050c012306100908121b010c080703051609170124032306070e06040e070c050607050a02030909100509010305060a0b0103060b0a030b03010f0f02030402120c1c05 73
    0x21403680722901c01c030351a0002000720740b440280109000d4404255a00b010f00c0c0580d8818942d00510500e54001250f0210b41c017484001841c12909100100f0950f0707034416030050039075a11359240404501a2000c00070034070b42c58480d095000d050140b000c1c0389401250300107000003905016001c000b181911400201074000d4100312044a282030300c64894a209030a11401d01d401e80c00b0071500001c80c02461465040091080c0312400e41401c00f9006a441e0f820341503c1c542000c82c001ca405c5441448001200204003078032798490001c1d61946000c60055190040c00c10301c0c005e2200b0103120091040c6001c4035400000d070f6244110a448052454856012043c4a10010390110768007802490022040080c0450240d0203141003403020f00c408092a0019010b44034940202c40d0118070a001d2810500c1c03003600001c2c001c5002a00001d40b0041d416109010f80343d080c21203001c00b0340c0000903c0110701300881c0000c9200264005004084103a030005848140d11340000c81105110340c041f00c1c2880018 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 448887257 1250 448886007 448886021
    0x10903110f0a120b1e06090115120f0903030c021204090b120105040f030e0405150108040606080d0f08010b16150204082d120301090e120a0509130e0d050c01 69
    0x541c94070602603141485070398104172040c42c5407164240b40907455030030600c030250140c1d400034000d256581c01c01030b1002a041601c50194100b02d10803080c800d8000240c4a4403c985003440c0006ca5800d4240c00e0180682c0e28043d10b0008661100c0300320003076500d0081c140c4003902c0380d030000450070003806400606a144030105541c0c09500e0102408100039141003c408418401d0b1100140d2807188010001110760840f0105024548082105030f0766200f5022203910511524002032540d40741c629080c035051040e44410701040183c001c074100300390000c00c2e00c2d0040540d4081d62340390104040d03c0c1c004034068071074000c3c0480c21407240c22000700341c00d4060758040c0060300207c8182080401340904c0210700319440e400007500013442110300680c0890003140584090000c40d1460b468842004000d100840341182c0703901540c0c103414200310682c0010540240551360300c90b2981140010001d1200d03d030310f82c000100346060079a00c1311820116050010f401542020368603030740c140d0f1405000d001d003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 448888507 1250 448887257 448887269
    0x40905100e160509120a06060b0301050a0b0c03070f0512220b0705060601050307030914030307020c0109120f0204020904051003121706190b031014010903110f0a 71
    0x1024200941040540c8841046078074140e01416280c85606040c1c41c000b400d0301c070203400181d0400c035070f40c03a508103d04e46400504040040310302800e21340e1a030000b10707032843c1c102d09966540007004100600e48455038802800c10a000249002840a40c0507a02e116401c0c001b01081c070310f07201c0c00003407100510003026a42d400c00780581c3d403030080141c07100c40c0c0340d01d964500800000468020a140385000700740d07000307581e20800410341620740000540b100e4200404245c1095199008100010010845030802e0714140300156204c0c01d041c18040c0c18804401c0140e4100a9554801c000304190081c01c0b01c07a0355088054409050750600210f0080c1c440c4e250f815410030b0070303e0180084007d4a0b0144401c07680954401e03000f01c001d9079400c451003413590410085112420b00420190300e060b41481d2441d03c9401c3e10000e506650350340c02c0c003490300700705c400c807211108503c820040082d0101045042810918100d8650b07811961101030280c0050341b16401510300589a91803601d03921200406040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 448889757 1250 448888507 448888511
    0x12011502010c2a051005100906060c03120b03030711090915010612021b030903060a060b0d1104170303010603110f030c13050a092003010b16060f021303020111070305030406140409 79
    0x260684501c040c01d1b007602c3d030310010400301000040d064040d1160342c064640650b40e103495912961412101c018200c0c0300300340c0d40c5640e609800d8096504000a151542c0324a0136003110101120400540d01c800420b20314098000b03110040c540b00400f8410740c195622030800342c0c00310148901003402409042c1c1e00385110060001c004e60114030000c050400b007542201150f40a95501400200385e0310076118010000c40280000b40d4400d44581044d0000341c940d5112030305065490401c4281c02055585c4124280c100100610071385030705018040205540396001440e004010650449920000303042c1c0d2922800840d00541c2d161101c1602e000800008054421041d02c1d1205c1e40000e00c4601002004180760104903659480c00c1c0094034100c4c0c0e400d0790464100001c0600005400131002c004070f51407561802032101c0c140385480a00740c106076011070414558103501c0090a040003007030780000540c1c402c07241000090000403c450a8a0075031600311040710031070401c0b0714203000f16000114024 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 448891007 1250 448889757 448889773
    0x303070c140a03171006050313030507080310030210050306011b0201030b13060914060303041401020a1a2403060105040e101d010501060504060801120809030312011502010c2a05 78
    0x1d0b51007541c91950345109484132030342d601c2d6444092611a810322071200884c0d428000030301d07020b4241044003d81c0340241411481d1842c196610107090b88105e600300074185100d48248194241038221a8407a0003a00b003c51541c00c240d000a002c0302c41e4444004604250005200700316446600520220356000c0c10b0100d5000c10903442e8000f40c1124060702e01e4940c0b0741000043c031b0f80e032440c100c0382c0240c501030082e503d0705060078111920401121519030540c801e10f501d0304000b600000c9105101c2d00903c036492040c1c1400c000c40744100c800201100b94005441004041c1a074001c145181100e00c1154002010100b04800509002d8a8650710f030702207140c00c02d03810b0007045041000c9807003200701d0001c201c145c2e01c41d0b4060761903009a008520020b82c8600050080c0c2d1180080304e030030580a91043d6041c0b84032034000038a1035006e8407070200ca0301c1642d40104507048040d01e0390314080e92580001e0090441c2600c0003801b4044000c002c1da902101e200f0f4041070100c02182541c0c0994121040d182c1d26 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 448892257 1250 448891007 448891013
    0x60f020c010b0f030111220b0706021201050901051c0309170a05060f09030a0f0201060f08030d050c0328182d2a05060a02011d0d020303070c140a 64
    0x3020b050700b900340074800d0003460100c0d0b842d06106200764064015199810036400b020071080c4a80d8501c1010741400020300702145c24a000c1c0050080036200b5040903079107100460f07948005034010380c42140141d0365040180080c1d45e41070b040340c0ca44581c03040c903008504514102160b803880154005044034034220b0340d00c1c10410001c102c1c0326100340103004885c5591280000406280070441e40002035400602c034005804d40308140310741c11030100f4070010039500c0c0c03129681000444a0b40c022501030b070002918410805850142c2944881014080c90561504105e50514184925440380107075a031241003072144482c981c051803e98200ba20315100c681070518010034109211240082d00c0b01040503e62008210b80131041d001c2c9138001c1c101c1202d0300d1608402a20a50191031683c01c1160700080440d064417018080c21403105541e001040428001c0400f28041100507a41380580e00a4000b04010071740000c100c030381094076464011051046403c0c04440305845160046050145030904018 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 448893507 1250 448892257 448892261
    0xb180a060e040e03070203150a1104060c060516050a0f0909050f07020f0307030207090b010e030d030b0415030209011217160218040309030305130810023f04060f020c01 74
    0x182401c140d40821042000c022030303941e01e0060510095041c2e00400700f2220668810740601c0c0c00160040c00480c5041d0121030803480c1d80c2040e080740c0f001408050002d4284107040c02040d400840c01e2400212454544000510502c108131403842800100c00301d100c0817610689410004144c055002c00082c1001d955000c82410162030780340c014402ca2020080303000300802121b4602e43c7c9600203141e0310b032400c40d402010f05900407495060000f80149200300781c6007445124945d400941e40081c515007040c0800080fa440f0f480000b50b8080104010b01c0181c885980107415180c2101944403c0d41c494507009040c421248090508094045201d0b0705642c10f090713607609000d201321407044401d100d090032410035000840700580040c80b524410008a800b070b100404d018030b6107030750b0b00d1109515440414500407145d1f0f100c5e0085680028003104070960744454140300d21a0461003800a40c01900e0f0954000307104180c00c5a016140c40810b08001541c0d1180c0200150264290345501000b200d10380 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 448894757 1250 448893507 448893527
    0xc01020408010c0203040e0118090f1104060609081b06071704030c0b0702060723070e010806010605030106200a120f14040515030414190611040506040b180a06 70
    0x2103600307000100400500200c2034400b540c01d140f200380c180743e1a01203140701364014044030000c01542c4071500300209240782502f036016401854104031846085007807104480705039101400b0414510020311040d0701c08140540c00900c40d000f015600c2c10000c0c0020400e10404400403d01c60341101c1601602400e18058012a40075a200b045a60f5070b92284150611503584000e50043c01000143d00107240300310280b01c08400c00361100c0008800094081c0307099005d42000402e44140c500400141604001c4c56016118a140840c10b40d45006400307070018440e44107908801d581e800111400310f00c104107a100b2140c001095040707400c041100506050740c0c4855100c00076050034241d10320107406000300d508440000d41120014124441407180940014000311045104140115440ca008010710079081004042045150440d031800d074044442001c001c1c0c00c51101444100840d07540ca5058904496030000483e030385074001d00d5500441d40e04107e000d6408482c02502244055111040300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 448896007 1250 448894757 448894769
    0x908030912280b07020319050c010906022a010b060702220501140f0301140112020105071203060e0f070903080f0c071403011d1b031501080d20060c030c0c01020c010204 74
    0xf005621003010407a200d200d40c000c940800704c1c222108484607880b41004000c1d004240c40001600222030b1768180581e4881b4502110400348061190b00300038020814801c001c2d2510003c01c4800002c10204030280100c6001a12a602d0b0301401c41480d240c0801d920400403191108018641c2c5a110026520209140310ba010b4599007010600504051080302d4410030100ca05100c26840d0030703003586600340740000407810001c0910000c4001003084143c01544526510301180705c074240005650b00301e4001742401c2c80344203440d051205140e005203841c01600c0d00000d45c01e80d14042c040f1070101c10320461082101c20310031020005070b5600c0400c804400710b44218002d2108103200c04681d601d50992903400f400e540c018042001018501d400b0107680c116024080e908400c5405402080c8203000740e0083e6055086000c8490101c0d5201c4550341007200c103280c118122611002d522551380d1001010070581c0720000000c00c0c51081d0410607600c0042d002c00c025561071842d40340c1d0f28081d4210b84915 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 448897257 1250 448896007 448896023
    0x4060305010b0c07090b01020c12010c02120f030601050d02160b0f0a0c0e04051f080303100e0403083105030705010f0516031a060706050f0106090803091228 69
    0x482c0c95040c14084400102d1a40c000301821030070100a18000c0000c4400c00b0f0540c070440b030369103180782c4a51070100300e21001040001100382042d0742c041d04149041003501c125200c04c01c280c8482c001c0010560b80c000ca828078046c0c2c0c442c3d0705040d600000344292610b20706c0041002d1041c1c420003003242081842200000004d54103a2104a400000d60b0054134041e000306000c0d8500b5219420583d000e1940001304401c080c4648001c1240942d507502c0d1030708808041e410000c20441d80501c0c1001110007040302c154045000e16180d100140786100152014040c240603520118110354201900c24110b6580d640758548400341d85400b1f50317603038000402101d0f2942400300003a98203603584101031084030264044003980746d030004110003d00c0c03e2103c26915900c5c0c0344d0008a40c2d224000540340c0684682c1000416007040d400118620005910201c01c1025140b014800782c03c0200a5590003079090b54440225055207d80f80e0074a03000d82c0c03441c40f06804042544000201140621a0741800b030004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 448898507 1250 448897257 448897259
    0x2060c030903100c0e040b0a0b0c0d09080a1707060b0a140906090f0c0c070306021206010e12210903010203090a0b09070b1b2104061205040f11150706020406030501 72
    0x150f0b50544018111544c08200c0c4c0d059803105034105a00150341a810080000d40d8045d214900310f845a004015072500d00d9009422a2078a00c0d040026800a459040d0050052120a40e91035142c440d001700901c2c0700704c60115502e010400e0641260040e210014040081d240d00d544a01242210345100e080c8140c00450102c7c0b0641000700c0d01c540a000203601c1c0c482950366926031826035134012132640c001480f80780d400101041c401c1c805080b410601070b01030701090414900061003000c0300c070030551080e0243e0030a10000440055410401507842145a4140c8044003412025001d40c2000a40650002003000b1041c10082100030020f80309a80329002522060403655403030005019003410300e282006040d104882820390501484591021209441c09001340d040e00b001c104514949011340214040c040340e038101280901404100108001381d1074540c0b035030580e12004078005025054013500e100c2c003640b1f03620f61051882c450184c0e003542e10075007481c044009600620070b82000038a0000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 448899757 1250 448898507 448898533
    0x90608040b070c080d0501121a0906011a071b09061e050603100312080f07030c09090c0309021005180a0e06010810080f011b09060203070f05010902060c030903 70
    0x46140100d41001c1421007641d24084290b982c521143c0b4141c0301c0103000c1c041d0200750100c5005a40c060194207004041078000c81ca809000001c030a211000064203410070041d43c104006541811142c42c41c04028001080401805580c801e8104c050022400c0c1c2020030002d40d007524901d401c941847d00c0c20800d855a91741d03841007148a08008503810004000700300614030b08030f0040d58000300603810b60406581c1d01d5803015500403105003004041a0044100442c4010303e40303c7c0c5034407440d10700342880720b8180300d01e004000307902600a90207066a2454044440d6220394003110740300741d000e4800b41000108540c0500560813003204042103e00c15103028943d4100302038000c00f01c85032501207001903162400107443c0d2110007040030030403940c040000619617008201c114400c0141400000300b20151142030a401c101c000e84101c24401c0c0c00301c081041d96800012140d03010782020f0b41c1000c40c070451608a02409004102070b50104000c20b128111103000320041c600d0f14801c4045070b1127505190 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 448901007 1250 448899757 448899767
    0x515060a05030607032c0c130b0d031404030b010609211205090f151809061804140a060c0314040c0b16050f010902030f0a0b160e100305070906 63
    0x10103a070350903420420228000781e0294114002c403c2840403801501e070300414052083d42036003903030f041c110360120700700450500f40883c040000d090400f00a028952a4101050b40100c44003001010442d201c1442003c141540303050320086c0d944501040c0d91135955540003007140585002c1da440c4001e920500e002d030b15070b08030340d040207903940111110302200390480142e030160030840f90140c00403a440103440031555610300c81820456011255502c82c402c640f4008030001d200400140502610400d102d11940c41c501800301d55003221050884942c0d9a16001c0c218010b406220051442f40a888404001d40da412a052180c40c0307a80c2007004041c00c224149050005940162034280c400b141880100c2c000002860007a001c0520b0301170301c502d207944592802c096004003445a035900c1080504602e024080140c400e118140100704003405510750000070a405031615051482c03119000d07030f40754000c8480c0c81c07503104002c00b855211140b15002801a202c100c8070b84000615a800c04545c81d4051 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 448902257 1250 448901007 448901009
    0x5011d011e050f01030902040c081b03041e03090801060e04140c130c050f040f08010b0904080f130806100609050d0c03081e03091006091103270a0515060a 68
    0x9264240000703440d110038070402000001c0054109500c4600490240c2c865005c0c008c84140d00d07039525040b51802001100441c01c0c04042929840400c01c20310002c10520018642c4c2101c6545400c1b129a010b86400d80304225194000b00c00355090150000d03042c41004c1d51345206502032001c0c0b0f01c1c00c0709441541030b215503d10b0b00301980b080075034108205242c12a844224000381070b060407450701c407800c10303050340c1c680099000010a2403000303410f02883e0002e008410904505848058043c10a40d854580074050705082d000a1780010400500c610303540c084c00802030150078141c4401e41005000220707c00315030301540020408101c00018503050011f100380410740c02c031001ea00494150358034034416500c01c204c4d04515503101403684560f107420b100154055a050001031500c1c011103441e05060302c040703610000ea050724052041000c0a9164100ca5000540c00c0c44202170b144031820400c4180213590314444503109014400c820060001012403007043c0ca4032145030aa0743c4d500070040980c0f95 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 448903507 1250 448902257 448902299
    0x30b0612041212060b0903010b010f17090a1406180d09030213020d0203010f03060513030909200a020a05070806010503070e1b0d0b090a0b1011010e0105011d01 70
    0x1100080200e04010180b03520100c1c039240488600707110308428010b03141c441c1c0000c85528400102c10780180340900c59104469420300305581c01d41c010040c0904811004c0454400551042000451801090002c83c0e0129030007241c0c50070f40303043c11014075550101100c00a0b4024024111061007400001e9800444003155403000ca81e03509660a00c00190406031420346203940900000403c0d00c11400654041c1c279074540e011020340e19504200342568000381c0b400304800548000034000c80d61000041d800cad0b1703030049404182c0303424440c00c03407105503605980072400d4100401d000801550100300719180b42e000d54221802c00307895810141d11000203100c0c850f03055000ca01e00700030484080c0d502680c001017440710002c0541344c5130012820f0b0b62000d0019a8490391320b0103143c545107441003426402810381c5a0410200c075030b0102040c0c0301800d1401140a22981c040d41d06102e0000750050103501c101c1e00004e01940d44d4403403410905901c40350464428a0f03036070002003240e0743c402c0081d01c52410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 448904757 1250 448903507 448903537
    0x1b030914120301170a0210080402090f01050a060c080d09030e030c030c0d03030b031504030f110a030c083106020c01110d20060910050603070302011d0d0b010303030c030b06 76
    0x110b414003404c81c0941180300e0f0034413406030445050160f41c3e006a43d1070404101c2e15003040b5031a103841004000036000b424051203540c80750042c4141d4230b0f4100c41d08260cc0385400c1071604a43c490038424a5406031065600c0210f040420303210403d0b034450903d5045a01c00c1e02280c4079019140c08143d01c030241c1d000e026412089000750503000c031f4425000a0340d9504044c00b1340d0b401c0041c1101e5001d4100c02110300750003040c144800464a40d502443d41c0808050b0013010b00561495550004c15545c501c1d0300181245c407004c074201109050100214100d00d04034207848411008074020b602000340a44034050240c081e0000c0d803002940514181201403801d0005803a980400c50400d860060741d2180c0e030214006000d51002c000b81e0108055405600e00c0d0000381140f25016030f111080d100000c00320342c0640c01c650b10400050740c116881d110b500800303411410369100d0600c04601c120201e000007815403242e10000000b4150141d005c00080d00d010794041c403e8032034550a000081c450140140e001a0b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 448906007 1250 448904757 448904759
    0x131a031605150706140a02130609030b0f15040f0906050a050403090b0706110f0306100f020d03021c060b0a021018021c060e07060e0301060b0a050a02011b030914120301 74
    0x50300c42c800070040705200e0800090f01907004032074041202411900e0764030503980011800b002a2071301d20040001c04103440c00c1c48082c0e0a43e80e0300040710304098030001d49824102c01248419081c1c6507180f00181c17006c0e204102440b01c3d50705040c06425002c009882140c90b09000c80d03694031403400754602c03031909a1100306c1c540d46484230035866607000c41403d9030481d9440402501c2e03840c0c4c90000304151450820215104d042010400034555112201c2000780304160074121040ca401003a00038840b0420b00b170068850002c01340c140c8a0311000e150000c0c10915010002c02c2c01a060800b83c1307403007a420b500f141c4120441020000481d50f4541c10300b113a11065803414001890890190ba8041c80403c80500700b11015030303150400c5d28120084030501341c2000e581448280e511014004044130120020b1040c0361800d03d20400601c241b4030030700f04002d00000d03081909070007500304010001040b6060030b40c03003000500c014000d03e86640201c4400c01e426080c940d40d0340e00044c401c1e4900c81000d04191171a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 448907257 1250 448906007 448906039
    0xa0501061d1201240b191b12170a05060f061315030c090e010b0d0507020a0204050f151504060810030b09030d0f090b01050112150b030403020d2309131a031605 70
    0x20a04030f0207904c80121140d443d40c800540c2c80f000d4100540301a85690308440c274003510307a40c0a104001c00035200c062418040004a90300c0c41d007030000d80707a0b087d160142d0b600400702c000c011200d00b40d0801001203201044140c00c0d03d07450751061a44800301d80c0c403c1c4170581c0790030501c1078030351007803080e20410541400401c201150b40c2e401070343c112585004175400008142e0114064800455850a01074480d5041008034050246180301c4641c04a50a030581919550074080324042e81c0039840410140000066801c0c0d0505440c034060368018100d11a1850a074118a0707a80e8000088000d4290030706d1b500140001103401a0759880b580000d0148460f0f00b0840111a000030311413460403001d4640b007100b0b10861102d1202005130018001b419520724040c240640307802d0140c1e1048080002c040794100b8040340c012842044c003104101c49a030b0f200244400074500c80c00e074415290020346403081e00740d90f0034841e480540301c1d450145e00b034450b144401c0f200120445540d10807541c02001da041c2524103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 448908507 1250 448907257 448907267
    0x14070201051809130611040f030f020102030906271203120a0213060e030c01110717012a0206010812090613030b040308010e0a0501061d1201240b19 65
    0x40c0b0a6030988203082054030001030b848040998000144640600c6064144800b0380179100c20b0000c031840146c501442d00c1e598107140ba005100260140c92143c8820045a10a1040301d00d550001001141c44030b800850f06603c020303005621403111a603503101c03840305003003000b40207111502002c0a035081501403070140f1311400004001c58102c80d402c004514040f2420001e10300035280c0341d600d401c00228418145842c0c881c0c041d541307a0520000c07490030150000c1c000b5406090783e43c4200f88001300e43c02e04040302e015021080c082545080f03c0c001c10101c00502d46151640181070354210740346640e0780c2d185a40c549924406c031200f41b4030f04001d4a419818420010a48031005a864108646d501c0e125508911400d82e81180003d011130010044030020044054002e0303000c00080105524101000c1c2c0b010a076800c95a00098552155000d90366a82078109840d100c014001d01024030b110410260303400d1001030401700d20a5604012610708110ba050390108003a400d001c0d410b10311500d000b568 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 448909757 1250 448908507 448908517
    0x180d0c03030506150301090e060105060f09011409061207080708040201081f0e01080c0306090c1e011101050903030610020304030b07050c0709110714030a270b22061407020105 77
    0x3e00704c88003215070116031544000a50080090000c0007900d1100044400c0c10820103a200911901c001e0144450f044c038000100d800c3c201003401c180150f4030300d130880d0000501404a0403544040e0200702580042603004955110302c90696502041d80e40320700c001e070b480c1801620f01a000070711007000602030352100248a9103012034100c41a841c030b03a94030500005080c0176000404113400080c8843e82c0350400708640360b08034504402070001c0694000200300203200c1030310720800465014401c0c40c0070340d010b4008441c0680d0340e00000d001074038004000302d540f6031050b0b40c4940a49091071a0040e46840803003603034150381c5d001e0141c8071a03460b50390046980d038102c64034035201c5002c1e00c0c000107500c1c082845828614801a04c0090712501d181c10549458030002c094080e6a41041292156159010290008402c2c801c1c1d9121713107907050800003440c00c80d4940c2100306601800a0907100a81410160f1b11039481808003402e40c154640134212649542c1070703110354800009001400043d8001d4010300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 448911007 1250 448909757 448909759
    0x91e03092c0c040e07020a150203060f120f240a051506070303050411090f060114160320070e0406020306041811040507030b0a030201030b121203180d0c03030506 71
    0x182071074a000024650030107660300740e0342080005080080e45003503c0300c2944075855002030040c9141d540c80d1035024035291080e0700c1031980e00000207803165554007003441010030080c0805c1340445100781300710355502038a10b4101c0c0510407110708405000c519051244800700c0301c0e2403031402d0b03103c034402d48014080183c504448a0007080103503005888000140444c0f0b4025603000c200350825090208452500c01705050043d00800c00b0025000700040c44075800240078032f05010b02d0300000e6001c0f01e06d406202107408449031450700410034154440134004100301c1400c0903981da92450303081c15945441d9441041d5a0b0403a0300b0008010911a81c06154090790240001c01c4518441c0a10382600c01001d504407181c80314000d61000c82c0c2050300c6065407059060030200414510800040c1701c0e440c06100080c10541c980116103640c0e2a01510b030740350002d05030b0840344005484d40281e00380342c004031807130308100c54001040007017800d001030f0489024206485294061600d610300701c0142800a00c0b40d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 448912257 1250 448911007 448911059
    0xd08091212131e0c0909020a03030c0f0b0a061802122d0703050f060103060503060c07020d08030a020c120412140321060f090402060d150b040603091e0309 68
    0x4040802c01400c00f4003011001294164110070161030b20040c000719607000113071918500f0318600d0050311410354120550360142442c07190b2105929103800c548000042c000c10399202e4074140100c1d0425a0031001c10390300d4403161000440c2811510204a0180f10004405804108003040c0d03001150307141ca21000348030310580c0318801c1e10301d01018001c0c5815200c1c03400203035407042008000d0020038609034000c24240390a01a03186400006980c03450085e00180103c0d50014400b4110364401d0303007856500d83d2010590307807649007040d0144003e4010b02996407240c09080d440d003144238009000c640c25180300700c80440410016490727801d000c0b0b483c00501c90340d07484104240100342d010f0f5844000c03000d590084100942c0742c200148621901401040c50003000c401d42440016624001910b5000c000714400066441405031982841c42c0c056022078000d5030002804201183d0580044501d40d0190200e40300d4210005486011076400c2c100c0034001806005051210800500035031200072000030305 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 448913507 1250 448912257 448912291
    0x3220906141f1b050d090e0f0103030e010309050a21050a02030a080a0204032a1a0f130509041505070806091911280e06030711070e04050d08091212 65
    0x2014420307800404080c1d0313a643c0b1098440c0e41c002e1384801960041c0c4604c1407142e0590404c6864200d01c184c0c11302004040c8850070803100d0142c0d05c242d00a000c5603030031000322107031450142044207901c0348082035440b1882011460041b03560080341224a4030160380e00452034070105c0f1000316005000900401086a0200000008950050340441610f51b1801c004240403603841014000416698400030154a100e6240801ba100b10410b07100a42242004641d5514003180b42e011029469040f40703a01031110b0f418001444000a01d49888600c0004200081c1c1c95906c0f0507602484210380e2540c2c4490600c002904840a405100c81b044844941c081900b812909556841d600b061200c080d51441028200c24a13940908510318a04050704000d44104103d2011914a10004040c2418171050f0a1000360136401004444002c15040c8450455420546411500c42528043d00300000307523020041480c890010400c2c400d01c44500101c1407070300350090384121000c040145058600081508 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 448914757 1250 448913507 448913537
    0x3070c050a020d03030b1315030807020406050d05030a1407020f011b1416090606051210080d03020c0d0306060206071d030a06020a020d050405010c0b040503220906141f 74
    0x304840010302c641c9003c22070822071002d21241440d00b0041e01f800c00d05042000d80c94407602035501054036000007038103550309101d0001c1340241140d50320950308820101803076800c1c048040068034000c0d180f69a05c0601303440d84000044d0b40d00503220302035072000004184ca5210b42c01550200141100401c680c0c00211850301c4907040c9070070303e103108842600109441800308103a4401e04016100450040201a081001c0109280118143c3d0403000f102503012400115509044000600c03512088803059100310394010080d4110b818414854803071021a00080360007402003030107590040c0d005280d181d03118501141c500c00100580054600c445070704030119101031140d401420301407200945c0e24400c20400a1510090003044420000c050200740301e135a9200c07085208403070700030140c06520b8403030741042401c521409010803038101c60704a001c4c0c01840e00100708411114010420007200c0c2e640c1c154580440c1c07080c0036066111054403500004404014070b8510031000070724240392191400e0b6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 448916007 1250 448914757 448914769
    0xa090c0c140d0207050307180e0a0506160e03010b010e040b0414251818020d02030f010f060504120209070c080313170405010219110a1707051503070c050a02 69
    0x52045419000203107075a110703c2d0100902401400154000c000c883c0ca0809801800c01d640f204480d401600c60004514401080107142101c0e1b800405030b503580e0500c06005040d490321118520007150340301154020b00d00c0c040c40348a0101e0410f860f4030900c15004001c0000429804012075030081d034410070b40841c030300094106031041e01012200548400510505c40b08100b141c81c4c04000c2100b03521301c001703501002190003011141c0c031000590342c0c50781c41c80700c1320b010380140940e9000c0d031440072041004603507103000200e04841414441e01000d58561008480d58812401207c5280c0031281e0680014200f81182d654015920310300b44800030281d6591070402e500c01d884082891100042c01028000052000080894108102032400b8503020010313444017560b030341c4c0f044421040c0000d10103112000d160784401d000024054260ba549a800d006010b1007000f604050385e00c03071510b0200301070600d403070301000c0320b8620780082c3e096030381e5580102c4040d410014100c54030300407801d804005071900 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 448917257 1250 448916007 448916033
    0x3110f04090906050916170a1a270d08040602040807030f05060708010311040203071101050703140108010203040b0402060d09050102070f0201113c070308040f0e04020a090c0c 77
    0x5010701280d00559800c01509981010309500404e4000c2c1018000029101c070b4181c00306c0f0349044400070403810b000740c81d900f0100341c910081c146070715030500848440100c1a1007403181d502960b2042d409058581c1d01503a034019400e4078000da90120360a00d86050081d90790780d42c003611641d00075260070f0302d0343c41d42d03418240641d0007251039050f079041c41c00030014181302d0294807440c80d18102c0c00544c51526000b01902d46040c0c224000c90f40000419a04e510941034410b0305450a4024069418034000c001c0060000c2c00d900d0f0030b45540c5d0f000100c0d5030941030081303c7c01190026410100b546864080020662100c61810310041e5901c1d40d5100044080c00907023a101c0c0580d48841484042d40009001c800369021000710342c2d0010070f00c558141c210006640d503414115140216542400303060390100344909a030b02076007446036042c000f0410010034014805da48107441105541d560300c0c10900703281e8000b6a030096000d9041c120034040005140d00c10b08850004d8034056400001c1900d0b89009440f103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 448918507 1250 448917257 448917269
    0x9030f0711030d0c02130b03030901050c03070f1202010606020f0c040b060d0c08150907140a0c0213051008030703120b0a1e080c100206370c0e01030902030c0103110f04 74
    0x3e4002103410f5162a1b50704002e80c1142c4542070242e08000d1000a03200e1141a410302d042c00380c0426141c14242080040d40d141d140d21544908101d00a400d04400000c00511140c3c015070170903d01040e61440400c0c4860b00042000c001c0c080c2e07801040c00c20020786100b5070030700d0b0000018000317240f441c0707001d02402c0a4108103803540c000780d04004c0d6005240702031640509005420450900c40d1081d40030984940780314071181000d4032507041e00006c40f5244c3c04100d0295001d14030b040003450455007507021900800c3d02d66410004d04d41e036104a551a400f03540006400308002805003c20120b050704035030204d1400a2034990815105e8402d401ea46a564181f000d56464611050084041c104081101c1d02e80448804c0c14841c40c1000081d5900c00c028030702c0c29076002c6030010540e0f13290f1740c2034170111000d44420710040710003121550b00000e044040743e503030010382181d00c0f5441550082c070403504a59005009889905180001580031301110221400000d40030494901d0301404240500085c200d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 448919757 1250 448918507 448918517
    0x506060a271e05060a140306060405150a030b0a060509010605030c0f13080309040605300c030d0206040303110f0304110d021306030303110909040209090307060603240509030f0711030d 81
    0x1004e600f40608540c0300d030041032883d00801e101404542d40041c40300c0e0f0192046074080f5103680c809420865590b0600242500b0243e1001d0100c2007080445403a4400c3d051401c040080660760800c00003908428801d41d000701300200007041121248200411003666643e868a190001507440008001b20aa0000c0881c0c0c101042c3d030f54851a01e40507040040c01d0407107488140c550007000d480002c903064032001e80355403c40614084409024481184045002003d07500e15201801000e510742d207048a044001078504001c1c1800d00442c84103450a0100000c8018116038481e60b442d94400400480c843e031055a01c0e0741c250040e9246003550450500340030010a0b42461440d0150645400b8401c8c04601c020174842c1c1455500c402c01101e51180d0100c50000280c1c40e50000c50f415449072600c0174122a090040c04804c1c040844e810350200706030140040e000d1203048141004540050b200400302d9041080340d011302040c59409010254055607180d140701e24400002441c5c0760081d9004000306e5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 448920863 1106 448919757 448919761
    0x110c0604060c0c121a0a020a0e010305060102010e070303022413030302090a17030414010309050a03030c12050f010911070b0130030c0506060a271e05 66
    0x1050084540e13a6a01107030030290b040803170b180039201c44d0400316804030b10382800500c00c80c0c40007100c594a0f043d0031400030b4011006004050702207170466403a03046214100d0010f018140003580310f500200300034400c4c40804640e10b00a00e00c40d0703071216040f50800c0000c2c49640a8001c2255151800507030b201001c00c0040e008210541103140c01c0c018200310741e404c0585c0000203105407242100150a1025850700440555521150041c803c0d0482180036000a0080d001602c0300400c0703081045028950b001230b0422628200c07800880701d44064010032803d9903070b00c683d822800403007510030724221190b03c0b4000784c400f046c032403007031609142d907807543c0084004c0d519100070844e01c4030600d00c59031140c10010114102081d00341c1d8507006120200302c0700d2920521060031940884005540340c1c501528402900b980201c1d060409a02e60b400e54034903c0034070304016007000d5003920000b154 = true := by decide +kernel

theorem cover : BRFrame.Cov 448741007 448920863 := by
  have h0 := BRFrame.cov_init 448741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 448741007 ≤ n) (h2 : n < 448920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
