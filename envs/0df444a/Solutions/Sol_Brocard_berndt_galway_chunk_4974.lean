-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4974
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:19:58.543996+00:00
-- url     : https://prove2.me/submissions/6eb57ced-f99d-44ee-9a1a-fc309a1a523a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 894424460 ≤ n < 894604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 894425710 1250 894424460 894424463
    0xd050921030f1314060901050409020309010f060b220806011203030b132304021c03050702041a030609070b03270706080a0f05040b07030216120c0b070201021206060a050d1107 77
    0x181c40900a40e05040a00c10b50312503100523140c090601d800e1155040080d04000e01c51130381503480e081140c00d911034034404c100240c010814515980c01c203109889040401c02c04100058034104241008000e07408241d0905550303c0203554a088080340c03e08402503c0c07000d0040380e01070b2074601e688084016650040c80301c200c2e0002d11a0151f0944c160340050050102c034040c0d000303403103040307035204504000103002c0e5101c2c42401c020f8100700c42500860122960384096410707000342200851158601044465484901200141074947c20100107055500001c0c00a52600c1030b205042140051000c0902ca804644201103e01b0a036582000500041040d540c540038546080303907005032582c1e43d00401303200d1ba401150360f044079150100d04070002d6000307820815050f0500c0c030511002401c00d0802144c1c201031550303046c4100d016030030644108100901500150381c410001e0100c045c111440d5203278880c00448007280c86409280e003d0300d0703d03c51020380003111450641c0704000c455002003d0031005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 894426960 1250 894425710 894425729
    0xc0d0e06070f0f0206061504080102041202040605100c0809010e130f0b060906042108120a0b27070203161401060b0f0d05041e030f020d050921030f13 66
    0x2c0c0b2544199400050708001c2001a000100043d056040c103200003078901c15510180d83c80c06507140b242508a0b0440d81086184012006a8074103500e0b26020342c4003d8001160f43d405000c46006c0090305400d00010000d051203c08a44e810b12a03004076442100e4004c05091054842d603e2195070008003031507211581075914000300c0340d02500b00241a1140b142010b00303c41d181074103246202c000c00003800e103100c40200600d8641000510504040d00700e901c02d143d1004000d0914201c3d40302a207664420450250030300d10140500e0482005028141003c0103011000603200d2002c101c2c258810503460030503505080c420441045015803501c5003d4085000811005849200490701071080c0d040028800005000b0200c40700031552181e604203105015103410703c0340d1135070035401e030f104404815030201e0315a840140103540c0510003101800c040f440e041c1c0c603051080c00000c40786003c46801d1100e050420000c105281000c20850b560410b0800c0b201c0c1d110310340c0d0b0040420590755800b404011 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 894428210 1250 894426960 894426977
    0xc0904050924090708010606260f1302150a02070f0e040201020303040b13050d08160804020312180901170f030408100506010507060c02010c20150c0d0e0607 69
    0xc030a000ca140c4a02c401548005186214050010441c12030040c140d01c0043c052001c00007a400800d10490000303105640b200000d01006440d00ea02c0b001e441900803400600500400c51920031206003113600c0000215400c01100b001e00105640650104c034a03503100303000040d400b1080303030001801003c40e0761001100071416210035a94a100c8400c0d54000e001d0713481031020400050405044903030000c50001c0d01e0f24900c80a0310b4040c5001c510009a40203d1107480510441000b10500c031006600f02d0305222455092540c0031070754500c55440309407e15207000c900784490f55800c1d02128002d01c00204080c8031540c5801d2011180c50031210007506a20801c4440c00009034080260f03021511148040c2c00e840722034410300c5c0c0142ca0b00500c6d281c1002070030025000001c000c7d01c034442400440b68000240c4680c03500b40a040c2c03034014464480030130b8890580d10f001e0100014090700c83c83e00400c6041d0541ca88a40b19803e40c0681c412002e0003504220b4041d070150310029030b10384107910550301c0012 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 894429460 1250 894428210 894428221
    0xf1d1513060c030e0703060605041d0a0618051002030103140102090a090c090b0d020301050405090d0e010e13020703020708190b19020708040e0406110301080a110a080f0c0f27090304030b0c090405 86
    0x40c001c22f4002c0f01089030308000301d01e034003191056001180c1c00690740c3e0402070b000d61603030701d103420908080039003082030350302000600174070108440d0381c90340fa040c41e002145820f118030001404d0300018410603034a0390f1601e0910f600d003841411100010328410000b0f90310350b0b1100da0301001941090180d00e002c0c80c42c14000400745400000c070001441040d89800c80c014800c44011500050800b5030103400140310035070070401481030303c000c2150902940c042c064084c18003501c2410942d021424006403002a144480401c00c4030340b549800603049680072100f06186030100c0045e008510f00502014008180080c0010540403100d200b02c4c4145000c001106161b00800071500080c00f032030ba2180d103d0702101000a40b64581c0c511500701c010090902c2d0b41c2d072034800d41d00e41001102c83d150307240c00401e0800da01d410620382d400e10100007103a05071060f40e441e04061100e00441c0180c0c04000c0303014004a120b00d4014412200915000030300400c8920b00b410a860180e408581d581c1d00452030040082e9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 894430710 1250 894429460 894429491
    0x80a0f060b040b131107021c02032e1e06080304030c050616020d1103010c180e010e060118081002040e0f010f180f1d1513060c030e070306060504 64
    0x70048030b4010045812030b001814418001e05c92051807201d103020401c450740269a409074460b0000240ca071581179a400389105041c1409541c54007080c1814940c031b803910b0130851000103803030401000440000c10200300c903503648002c0d00d01d140d0140c00c1490b1400c040b912980100080c01901d0042c409050155544e0003032024610442c610f030b003040b156412108005180c000d04542c0303910700403034808642c904070000087c01c540200c806903000c542558580f040360340b4140c00d100001e012041540010358503002000d00e10903030042005e8100b20850384800c010010000550000d0200c1e0f8048803240b407101140c0c14000e500c076014113420b4000010020704c00d412082c0526045e105600c410468a61404892180c07a203a18030707005540a40b50280700b80b4a202c607104d0b0399461125001090703800d0401403c00360500000042c036100903080700d810000c0714001010b100f02c0581e0b00000000c0c2402016004500601a40507114814014880000140080f40c0c0201080d1075003160b04000d00000701d003089 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 894431960 1250 894430710 894430721
    0x9100c0b0708040b24151309020406120209060912030d050406151502151338040c0e060a03120206100609060c0b0a1b050d050a05040b13060204080a0f060b04 69
    0x10710808540030318021742c00c1c520b5003051840c2d402031210342010f4101c1241140110580c00c1204415404201084016441003840c3c4081790011411071034051b503400450418803a401003580a80500d00780040b03415010002c50b032800e4018801040349081500c0c292001d0120403901e240b020403000b201183c106000c0c40000341840c0b89400030402c2c0d03031424803106042d95005058101007404c1c115204007044450890105c0c400c5d150001a102b8029032803007100300e0640880207422103105078108400110000c1e40142034071040c030b12000803940c0b000d00203418800340c0c5e00000c09400c03036800d040006076000500c5500983c500300c034001c041900ca02d011940c211080c861341d4002002c0c07041600109280c0a0a660001c000043c04150f80c0700100c00410f4400003101c1d00000124009445d2545450034801d154108400600c18844c505058581030640d4502030502e601c0d01ea695000d0030100041e60341243c005040540a0b00c44500c0303103003400800c1c0c00a50805540b86414000715020901e445c1c0b242 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 894433210 1250 894431960 894432001
    0x50c03090318060f0c0c180f010b07060b04020406032a0203040e1f0f092307110f120c060a02120c0c03040807261209100c0b0708040b 59
    0xe50a01880340b603000356003240b442070300307401410401000d1000c404242c01803952039840001800c04100d1501881468071185410b01c00c0000c1c01824021070059203120b05044490860600e43c40e2100c5041000040904402c1c443d40184001000a50283c16030000d9084513458011590124181010704a40405030b80b14140160030803c028002000e080c0f4000d034200400b15041d03500b60b07413240b82e0010340a04640100c0c400000c02c0a0410200510703003d4513084815403960074101414142d0071a5401c07601400000c207104d4000066902e00500304071147c5941c04004c225000c10f01311700740c2c0d4010741d800700001d030340140210000500000614000c44d891010401c1c02017600b641d42440250507500505520359041c00100800202c091080000c4c4025001c014280301d84030031080101d500407406030840003c550001082c0d6000103003048255001a141905d040200c000302d014112061110080c00510b0b0281200c14071408030307446040d0320300c5144102c540d2066625068100050020f14444 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 894434460 1250 894433210 894433213
    0x20603060420070803100f0b040e040f051209030c041b08190e0706090e06012f0111070323030402040c030b060c0d09141c0317040c0801050c0309 64
    0xc40c816003025800014010110310140b2611011801d4001c60303680310352410307610102c4c0031091015100481c041e420040114003084d101c0d141c6800301c441e80c00c3c056845179003189164480050103000560b14071001d580d501a0a40d480c0c01d00e2004921402e03008640e081c1c0c060320862019072040d00301407080604e80e0a880c03481d000042424030084035651802042040c0c1030f43c0007140001c507901d45001d030503503901000c0041c00c1150706140e8001d1031b0708080e5004900801c0e8080500c200341c0d0b08604128485101064858410480c0440c24030071101005542c010544ca000c1c6115444241030029100051080c0d441440c021049522440d030004140890b070b40c00d04040000c00d0052401d130b408240a01002d00300400c1038199580001c40796001580703071115540103951103a50142d44042501c0140007581c0039605410178420100d981c0b411074200007251001181c5c986814107000d03005084049000300c140b8001450549003640460750184103c03117040d82081c0c041b581440380a000e40303108190307800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 894435710 1250 894434460 894434467
    0x21060406180509150106030506091e0612190803060a0b091806010c1e031e050904110405060304030909050c120f0604110c030c0f070305070b0c1014150d0206 69
    0x1121680203180c0035110503c0c510401d10f140984400c00342e280750081c81c2c1a1000035030380c6444814000000c40042109511400785500901201c030a41da002d03400c00010b40c0c1d030f2400640c1d000000c3d0b00d880d0700302d01c400151880b291000c00421048000451241d4410740300095181c3e070300c103203a8800d4001d8481c49036221000072503410b1510421004603170311070014581880801c8281e144c03040800d0980303002c0c00004c0340004a8400740f40c2c100f00c5a8924104099241902d00e00c61a8000c1190091410380e51080b0740b91020810b0714142941941c2c0a010000c004036a03d0801e4a40602107240d1807054840136810580040c0750347c10385005a8001700c0c201ea660440658400d992901030000c010034503940155030721020001e1a02210150104004c0c04c001150348a01c4051420716103031120324001802da00840040c000a000881c00d0000c641c0360310b2008d921040180680d5051901c0000b15524841c074000502c543d1042c1042250300940c4d032003000b40c51040f1710f2014400b5840c0420400782d0410001c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 894436960 1250 894435710 894435749
    0x30c17180103200301120c0b0403080a0f0f0f05090d0b090604170307020706050c01090609140f010e0d1809092f010e0609041103131a01030f030e060903010221060406 73
    0x341b242c652581d1107000000078881d22030041210b80d810540042d24900c3e0080340b40c4040c960801d02c1813402100070304003980c546036113603402040c6002518018041000c040340303411041c0c54204d8240b8440d0350103403001c4400e15160348840e942309001c44095035604140100c681c0d54055440490b400384c58160b024001c6241031803415a6545d1020907820003566a84e45200d012503a140714a5942034070869103103050f03800e515541c1c1c0c6050b03451030b4002d007076074034200300000f4451002800216039141418101018141004280d034581c070310b503104031045410300c8a103404008010b5004500c940400e001140f40d440506010b0501c034450098941c086140c1488286003480c101c1d0280016500060010484545402c040ca20f030780c20a40d14000300381c00c140b00120030081e024048100b1041017a400c58050343c5180c071246803441000502138140b10f03d0081d00402500c038082100c10001024000390b40c1e50805114500480716a07801500040420001180741403605001d001d007103560b520340c5040c210080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 894438210 1250 894436960 894436979
    0x408070b031005040911280302041d0d05040302040c05031512010e0a08031602060f0c090102071a1215030703030e04090209010f090605010201050f0103030c17180103200301 76
    0x1406200c0110842c2c600007540303a607a07015608550744140c10352104078904400f4062a20011415115918034440c16a091100c2c00c442c80000c40390112800b0038090842c603101560400e0345101014240180d802401300183c1183c01401203d1082c0c03020004001d011004458078042a100100c0132104008038581d50320300321949640d408613810000a0801500d801d0519069407103100300c486a0020041110301001d40c6100041d0600390300140c141458140c80429034900300030702c941c80c1c046021031010340b507910810050000d8075440251052620960520030800d030002881d0b85503191035000001d80a0466103c140e003140b03406001481510305560f8140e4920403450101074010341d59481c1d45026a590404c01402480607251100ba014100f101640035102d05800180c156070400041c040f105104482e0317181102c1d05032610407910304079440c2004c00000400b0300070051010204040091310079a01040b034842e10700f6201000400c00c0c00e9688208403d2220244003041030500040006089 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 894439460 1250 894438210 894438217
    0x80612030708040611062214030d0c030e1c050c0a0215030603010f0605090612010b0a060e010207120b0609091507052203170f04030c03201e04020c030c0303090d090b0408070b 77
    0x890350048107880307941d82c23500d880e680102202e51480750b119841c10b86c581c2d8240c42100c1010b0000d4010f04170310003002092a0407401e10040c50380c10068005086d8007124030910003030000b05e0b80100140c00503e03454070a40101d410644416200b946480f500020088691161000702c4901500f007502e140d4408080100d07010b055802d150380c039521030940f107a05a0f151303122800a8000b98643c0115182840c0009240807410b0300079650708240d8090310004540461001c41d40725108441030b102c41c0d80ca0345040f5080c00f80c0c0d203031a1203914000000303100042d41c1103405080340d19140786264008824421560600d10041d10000e46090785200100c645000d040e8000c19150400c81006840e00342d070b0307aa450800748040d03071040c3d62100180d40341900f0700042c01181600980308581c00584100c801341c0b807403c03464424032400d01c035603400a804004001c0034000c3c3c860303a403c0c40043d00c1e140e03c3c040c910355490788288040034000a41005011a484c0500780a071010f5510f864000c11413a414035503003049560 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 894440710 1250 894439460 894439463
    0x105190506010306030209090708300d090501150e0601020706080c0c0a0b0717010e0442060f06050310090515090a0c030501060516030806120307080406110622 70
    0x1074480c4d0000c80543c98604625015045c0e200003090b01c40d01d0400c03480e00b84500940d00c1c01d0b03200d80110000c51100030102841082a80110910b41c0d00d0480458820060240c40c000508075402e000200c00304000b030410000444008945075429640e5040c01241c031098103008503004904958085003140c4120005000e4604140c01181c0b09044c003030321503894a08007258420300080d0503035008481034070800e443c070b40104500e140950440c04d15680b02010790715190360440c045468a042e2800e01185103a502010000300448400e905c00030040349405001280144070611001c1080000d107280320b00f003100c1c0319542c2d400c940300d0982d003003c3d006e02c05003201404003034410301c0c450000b108543d01c01503690b008100c0c420b00010748426000016003650f20503031089082c08001c0c00410100c003180807000c00401c2d8546408515541c4200015010b15003080780a20300307100c080b40d03540070040200002c0081e1612907e40d0b4503625084500255141d4003103905262001801401c14504540d80d04a0390456 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 894441960 1250 894440710 894440717
    0x13062105270f1c230a2d021b03070b120c040305011d0c0108160f050409110405090a060821160507050f0a030b010b07170a081503010519050601 63
    0xb82c81100300320310345200507024400c0401c0c10b010200c005504401080c1d6803c000c5201143d1183e8080c0005401e4001d800b585000d001640d030600c0541c0071848012050a1415807050001050302c3c40d0095480e0001000700c0300071801c004170039800b0714001454404580507c09640d1030515058803103211001c01501c1c5018800d4203100c007000060080c09034884903046010315408000001213060f14105e400791a060511101406024030301c0306500244d44d4002203400e04030320754030301c248044825100d40da10062089150080c42c4410300000c000400464504072074001040e01e0b40801c05044480c50f204030010380c2e001c40c43c100242c8032106c1825801c1c3c860074955500309203403010103000390035400c0b504980b6034021980502051900c40c0e032041d041c03c000e940c044049030465903000030005041c0140b036800040841e6075800c102c005421b4004200d07140f2840c98940349000301c05005884250b13521101548212114000c6007014800c061164140c824000d60740034030b900c0e4400050a004d8841c5040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 894443210 1250 894441960 894441973
    0x14061c08070507180b100e01231902070503070807121505040b01051f0903060b1c031d0d2402250b070c0203070e0c1306210527 56
    0x46070b810710000e001005103003004040b0182c0e04034000111000d1102c0e8605c24105a4600300c20203a020149800c1c02c50203007001541c0342104c0a60658200c0601c1c50314030504000100a00700b02142c840003000d0620b95000c43d40b09941705d03c101900d4007840d0180c0c09003544025400c00c12410031844400e41036000f01c10407026103400061110680e00100c03815107400320944010803540c03c0166010b044120351641125042c00444002401d0035201e20014110548807a800c200650f2940448003c4042c0318a10b41c200300828039010b0401c10403006440b08101c40c103040b02c0f005040c080d84881075182d000c03041c1658904a02e9a01c1081d0309080344210351140e0a002ca020180d814000051940941a18249580800d490031000d030300c00040c90401000002c00382c12005840000c1d180094801e000c101c0b120035510f4440c801c0c0140a07019071403141204280001644581001c440820485000ca0f00308605050701c140400380d80041c0d03140c5480d510301e40c09100e90520300d840203082c10041041a03035034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 894444460 1250 894443210 894443213
    0x406080c0d151d1f060b0405090c0912100509070b0706020a0c02030d09030b010902120f0a090b130308061e010c0510090605190c0e060f0918070314061c0807 69
    0x202032030703c0100d9106a0740700103140420f00341c0000040a1440f8400d1051240c07504103544400c0a0050b8491b00b80a201020301240a0503002016608541005003050418204c281c010030351700c0c0740e0005420707485441d00000c2100d60f00b010074110190f800c1d00c400b0510b0004140c0e07038900298454001d410070004110f00c10300c0169414041c6030b492200036600c090b10141141069a07011106912440c640c610400a601ca031070003400005500100ba00000140c80ea1441c80740d030003030880d4980050043c20b07d04108015903c1001309480d1740c0b4000d0740ca500752070380c07500c0a00044080000c104082c10040e51440c04856208001e10b10006124100b03a1301a4801c1200c0041500c01c09101103410941b181c1c1081000104202902d8140481036024440c010011070042c1c4130303040c841100d0307004480010310400140740c41003c0b5030084201911000d10701508070080b0721310403829290040001d0034100300c0b0300300da55207045003401190300620549418142004006803011102000c03100030300c0c188030080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 894445710 1250 894444460 894444491
    0x150c061d03030a1401240903151d0303040201020a0b060f03011425050d021b0a06090201140901140705160b04082103070305040c050303180406080c0d15 67
    0x162501180e00080d030b124240a528042074803000705500030784004013001041000150240d5035800c0750602019030700c044040104559940d460b41024110500c5840446441182030740201401c800c4514490340c04c10b03440343c003e9103c0c40261000ba0050f031041e10b0f00004100000521038000c0c200500701c01201c4902c0001c42e0a6130300d003121003d003104036601003150701084400b20500c00c050b294034160801022030000340243c003c055081c1200b69001c141591091100401c0e105048002d60440345450028a405030203480800c800300e0000d030a08085a085036071410945c0e20005050310351015040841c07ca41e401c50f001070f80140d0315031250068155510180c0d80d0b410019000c0854000c2c1e8680c1002c040c1480d1440943ca40104074051400003400100b894066a8224000d0b00c0d0104071030f162420309000d0405240c1010b0ba25000018590010f1130203e002c11018080c25039041c0155a03550840e6a2180980110950015081c0703003035070001446042183c801410002c4000b030104140c00015 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 894446960 1250 894445710 894445751
    0x61e040506130f090209060105041508070e040e0303060a0f12080c01020f070b1b040b0d02030702072111150a12091205090310060b09010e0a0e101509150c06 69
    0x203d005aa03100100b00035401c0c0486003c0d400354080c03c010b45040d1608089403140004888420100525034000c40c100c01d1040b00200c400b05070007481031000c0302d13a4030042501c952096031640c1c824071a0b140002840f0f00d882101d0011106040c510300b64503242d6440b004030703a603c20400d182e044d542c02c01c0a2a401c2c42840701401500303004580d1000030b880c0c0f00305001489440540300f100c000708c00340320403c070016030300d030031034425104841e000343c1c4948980406a25116841d00444117001034011011200c0c4510958403a83d140107800c03d01104441d64207102800740c0071b0300500381c100810007110307601c01e008003d0180c08400050700001e510401d40c480c100d078100b0904460f0300251000603810000d107000c0100401e6410001c00400ca018607001141d0140d200d15110241400181019000c8943d0303220b01c508010000040c120007185000881c2140c5020140242030094080c20200b13031500340f00d40c40c1d841c1a03501d80091141d2807200072005880601180e00103d80d0b660300d9603c0003c6802042001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 894448210 1250 894446960 894446981
    0x1b0807171902031303030f0e1002010c140c030921030a020123060a0521030409021902120403081e0c1606020a0503040923011d061e04050613 62
    0x42038840006207600e00c41d0314885031100301158414420f0908884040c61401c045941c1400d1070701e0301c107240400549624041001540e405014000140740064064000203c4048580d4640d1050b800900420090b401865808400344c0d00c02c1c42214840c2c20800c0381000c0000c0c80600018200400141a13403456120100003c0141d442c0c54586030427a602c40f81340a000000071941c01074078540117000c00c03000040d42c4500c910480007618204a01c24480009039081052241907035603641d1a06d100038043d51022b03a0303502d0b4440b0480c2c0e0840e0a01d1010400401100c681003040d4903291541c1c540c90502e8002c5411101000b1900070350051645200d030052400c1256440500100c1c0700e0241c2d105801302003940540c096411031000000003450101c2117900f564ac111400151034400941c20a8600d0411041e81d283c502070071001164203140745800e01990302a4180e035008541d40c4000344000003250803400000700d605c0040b80c501c0c510f0944c2003c2d6201c00c2c003412603c1d0b40c5243c0c0c400c4030240d0366030119 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 894449460 1250 894448210 894448253
    0x120501060501201005042a030b0a020309030d05060f060427060b04120c0503150f01060203090a050d060b031902180103121b0804030c2102011b0807 65
    0x10081e65800141c07203400b8001c11041841034a80c0c0394082078680f007816810452559030f85c0002010000010b4441b003c0c0c078554500280c610300d466040c1d0541021030300013a2141902d030400079500411038021039105903004c401550030b0182c01002c0c04d002d0480a06181da01921040d440045c40e25080040c01c020110366561817402d100e0b0000001c0c0030028440c2d584030003800c22005001144500d4111030803075905205000800c0c281c2d0500350009141c2e0b4110a07450300800d10482030300304040d41440d019a0101409044e03503681c480060343d580c41109001c2d03030440880e00c0b003040306152040e8451052400b8413004108895018002410000061200001100b04992110a50420100c0d441406508000e6001154110b481d1283e03907070400c2220a0800010f1058140042c1c107e804450216512a56141d1a80d4813460080040c51190182011030082d20402001c00d40150076955007198068568410840d85130360b84500102c0b4006055a95081c1000304100080300c607459400849035064 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 894450710 1250 894449460 894449471
    0x6190f0608090f0a17040e040624141e030607020c031c020d12020d050c0406020708060c030103020402280509010f170402040c091e061404141c060c0c050607092409120501 75
    0x24010142c13220100c0007412b8004072014180080603a507100207030405030803580562501440c10f102001452014081c40d054040e00d014001074940000b10303415410750031819220b040d5446511703580017903154034400d401039100c1c40c84d800850340550b89010200d104164098500600c5541d14000d8a074243c0c0e40c0c0c580b0390000603042000550620047c00a0a113400140100e170604142c907048602040c040a449a40c2c00074043c48614103c240c0315150312402c003040780004010302c1c80604030303400c844003141c0421564048003203c81c0c801c042400040112045040b16a100c903002c1c0801401780c40d0440c0300380014100041b40d8100f07410045401040d29582d050781840c00e1002c010b2081c0c0228180704000001840306104154000300710700001d0308292400b00c090342080410070f441080ca0400646414074210000480652195240311210f000d02c0440e038103606c0f030031803c0350b44100070301c01c1121000600a1f900807111905600f03100122062a08861075501c54528100d8140058421545a0b5440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 894451960 1250 894450710 894450731
    0xc11180910060e0a0b0a0f030f0c0b0403150b0f030f031315050a0f0309150e010b220504060b061b15060d030806190f0608090f0a17040e0406 62
    0x8222030841c03076850722014041ca51900075500c00041e80540a91080c0d51a002c6541081c0c56604e4264010050902e05040541e80c90030314100c4442c990f18141e0300410446004100ca520381c2d01204d046a40c030a940b10a4103414485000003448861551036006140c4003841c540345da0200310f040000c0e0345082c065540d520045200420350403460780040344c40343c0c000c0c4d240304429070088152030f10010203051541414410b000201c00421072488002c000f404984a00c011000596000282e400540c100030006950000704100041030348031002c10300031a05410740404680c25070040c0381c2107480b500700800d07030446003400504540c004c0e4980c03c40b10b0342c202c50068030310b080410480c606003848400d14089401c01d14081003800c2a074100103028032050001052090300c49140c600c03031582640303034591800d0b41ca80b03100680201c0c05110308000914440c01184401c07030042500120f46000d4402012018490760318003500c80c00c86644110b07400800d000000e408003564070034900c9688601000202c0356201c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 894453210 1250 894451960 894451963
    0x2090a15032403051507020319080117010e070506090301140109091e1109070509030f0705030f070e01291903230c031807080c012601060c111809 64
    0xc02c5000c1e003035200c081e0200003103840400c0108000c07811000c4e50348955103103003040e403561080f007040060b0000e04007800c056641d40502904d040c0c0b62107030b00c1401035134004070300c180c26a4007504a003410b43e0000c4000304082c0c0703402801400882c00180020030300300f840c0a04900b0111090707100e0b0000c83c1e102c00c0800304101c5d200c02048885c040c9840440070100c243c3d100e015803114294402c40c001e444a0010a002c0d03800b481c01d46600001c0101200e824800c0000d4181d210345aa00c5198024820510440c44851002c650785055408080e90b006861707183c4580301000c0c803c54040c4c01403100c04a949040c03940c090030f0040c400721442101c2010800e0122100400300c030021100d0807101b58196444c01c141e143c840000542009103c0c3d0032503202d444010301c64884a01d02e40000c82c0500c00c1074400140b554010698400e5004241c82e02c80001401500860080003110061041100850018004a0b008000e100e42e42c501604500e600384c0c40c08000300d103201850780c1c039454455107460f0403c51310010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 894454460 1250 894453210 894453251
    0x2703030e090c07080a0c060c11060117030702101403040c1a09130b040e0a2004090c031203060308040e1b251509082203030c0602090a1503 61
    0x201500c1c801e14500d0001c010078020b014403000182031040025034100a50701c80c0c00c07920360582d00001c04102c54a05403201034004a4854451103c0e402120300010304108403030489013168031600042c1d03151100540c00c01c00c54006a40000c000c0c0040940c4040740f001c140400740d44502c0c03180c400752444074108040c0c41181c0c20714003401014144100700009107512224129000c0e8150400045261881d500004000d8203811903190514450010300b20140080701086c4a40c11903248518405a0000014441507605500b0003a040009410007040000c045649481f034000f841d140029056869580308040340c0d005500c4001040402000e1094460700d450040040c1c00e0344883c07840c070341880c0e4600102d1404158034604098000200a8400e000710b0a03900c00000c00240c0c4100700300200e501c0c00b81110342103552060218004160040c22500784114194281c0380c0503101c04164246540c0c2c1d81000c0d40c0082c16040c1c000b0b006590014200d2200003400318002540c0c0c0700840c02c00326140c0740d00714810 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 894455710 1250 894454460 894454487
    0x2130c02031e0414040905120309030a08060a060219060209090a1a010c1e020402090405070309032303191b020601080c01170106360e07030c020d050a270303 69
    0x148100300404c840d800152042084040660f40494255050305001c1d0901d803089800c04100c440001c10481a40000710041031100c1c1543c0700c401054507802c05102c0756190500810000d68050303042c0b0114402c0350a105c1910070321400f0090302d00607916002c18000300c81130f50103d00040d196500042c0d000030030400c3c1c3d21800003e103070640744d4601a0319100c0400700003154540d0110b004407084002e40d15103404680d083c5001510038400e0b420044e00003401840030100031740019003000544400e600343e080e0b020503e41d9070408520300f1030300c4600003002d510300480321513000140c0d9154010151410700031490f12036030b81a0064545580342100f01070900c0703074640034241000005941e544809075035110084c15941c09142c109540c0120b003100400c04c0310000c100c095100b00c80171890401c0e40c00c17688010306a80105520381e0b03250300c41d010190151398280542c0030158100100070b00f080d600c204090500300a440c0740c0210882c8106a02d081081006000c021210112590034414140c100d001210480d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 894456960 1250 894455710 894455767
    0xa172a0d270911040f1d2202040c091508040b07030c021002130e010305010203060f010c05031204021306060e030d091a03060d080f03070e04020309070e0402130c0203 73
    0x2480d0001402030400580d0254050866440301c242682007040b00c20b44021385402c804c201c04940d280c4a5900800b0604450088540c4440d000124080410009281001c7e10021b44805050b05c0d41e0800c000b4240c0c4101c0c030010484900c200181d4100c0710305600001d0145910355503482d040500308a000307040c0061000701031606058a18800a40c0041d0340e02d2030501c0458010388880303495140d0311030b40200c0d91054150030389440c0080305029065000f903000745d2044f545410520100c0006440303555403d000a4a0f64005201d044e0320180780c0780c070706907110744024040e490b0000d40040040440b40f040d0002c000040c49140401500d041c01c2210001c99000c60803e5100d56182c20181e8035001501e00314054400808008541c254440701c0300c803c0282d81c4104003648402000c43d680415401c221491000540d03117040002290420303100301c070700928120740a08610790a201d01130f40306480c0070344100d81088a014401e4062080e40c4240c8407100215405142d41d106220490030b44c818612001c0304d0390 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 894458210 1250 894456960 894457007
    0x40915080708030703031a1906090503062424040305011d0d200109030e01080609040b010911074d010f030b130f0e0a172a0d 55
    0x4400d001007514066585403078080360200b07000e1004021450b558803065004840203410610560058482c4812741e4103580d40d0b8020140c2e40c400b01a41c0e80b42c240c9420300d002800400e13041466698181e50010300d070303000e03000403203640740b580c0e0a21000c551000c00304000c0341f000c00d003801000028016061000819009240c03908250b00b84140c451050782140001d000c55101300c036451100303080440548115000080120140340d0401401809044c00170b2400a2140c600050141c68080800e50040e40c01c841d400c4075980c00c03da00c1000405050710310050081042c003003100002c0c148815020200101000940c0510140032003040c0c1105040b04204107042e01e0140111505004856020000007442c20050032800008150010300400c007081da00800010752300b404811564100407001c1c10600c104005101e103201000c1d880e428644030040c0000300401c9842018210203001e4400b0f4401c031029410650104224143c181d507102d5400250b40d000890130038100c0e9040300c02140c40351018031001aa = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 894459460 1250 894458210 894458219
    0x180a0222150803030604150f03050d0905030303091c0302091c0b0906191e05101703070305040b0f090a090f050604020307020d0f11030a0e040b010c050601290409150807 74
    0xc6a010040916014503a42d44002c289007034080440001000001b403c44d1215842b0b040c010303102d13200c90b5810404140081c40000c0d450074000101d0b07201700c508034090021054400c21030344c000c452070200b540405409000c411680c1c0e80300343c42c03c80c40d4558030b0400003108a641c50020b41c0ba810007081d0310700c150040d0003004450505c1e03040f41c0c0450041120300003510140d4164022140203000c07054400c8602e00b40401c036102408800440c00e46c1c0000010300a100c101d00e58031070745c83c4601040180010f800780001c20560f076078500544003151101d50202c2c00c01000001081a1181c00e5000f20800c0d611450f0600754040944551500401d0544003540303146005000a036a406c004081d05007044084d03801215050300c00d81004a904000c00e05813580ca01404038010010024800c1c8144901d1809051040c158022440020fa00f40d0200142400e03030300c2d181c921580b494000170b80c0b14042c11006445e007050074080e0000c1000d40310002000070003980b001a00e02c003c2c0c00640000c0d281c0d40c0f00c088140b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 894460710 1250 894459460 894459463
    0xd140d020a060c0206040b0c0a12090809090c0c07090203130f120e0f06090f0103291c032003070506240d0308061201060e0106021509070b03180a02221508 68
    0x50388001a0100103507a049899000c468202b007001034210801e140524280400500000805404404542422041d00c5200c010b8101d03104a03504144107502c040800c1100d00007940103181d001c0755501c8044410740c0e04e600c0d00300c000c2c00c4500c8220b800b0041058503da007542c21180745003103018165422801b20303103e81d01052091203040f102c00e202d40004001411107a00c0394100c0640c0034806030220305182488a15031820440d030603c1c07148268110031a4042510f1003031b040d04007640c2c0641d01c031010407424159240a0210000c0c2c00c000074041049038501180301000100d0140001070110201120191480d880b501c0c09005114411005084540042544905000d030005000c55401552803815058103004241c00d40c0482030b540c10003800001c00f20780210746821030000c4103410201682c1c0b100d401c140c490b4414081d080b1840070500120386803030121400e400711600c101044450303080450300003581c0402d02c400c0c1816520561041403140c80d4040c02607000e00c000c00f40d145102d035401e212409 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 894461960 1250 894460710 894460733
    0x3091208060319060f0f020d0c0311041a0f040e0f06011d130e07090204210c0303080c0d15050f01020f060a020f0909070c20010e0d140d020a060c020604 67
    0x43c1d030101c41c81807112041c04001d034810500007800304810040510000a810043e400c24081054218034120002c04030324003038015020004600c86c1524505410b0818a00341c1c504005101000040c040c045c00200c80c046400810103131408402c2856207107000b400e440740207000141070344d04000380c442c644046040d0782d00c0c0c00544110111580130109000c0c400d450018444a280340704140700d040800140c10700e05074010700c161011504422105420394100a48038034245000400300030000c401000400e1140040715003080c000d00c1034501d03101103000c0540c280e0350b040440d807103189104201009185020150b2110030a000c1c0043c0030100c07000c40100e43c40d00c0f002000011752580004042c80942d5600d4100c07000160020142c04441c20210301c0285404a0b02c0400c0315010281010040c1107041040c0c40060030005a442100900e004000d0108070341490800320341d00f41d265a44007011100521645250b4040303035000304040410b6041c040152050b00907a030065421100521000c5844e45194 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 894463210 1250 894461960 894461983
    0x70605120433020d0c0806060717090d1407050301062106060312120501082a010c050f0d1403070f110a0b01060302191706210d030912080603 62
    0x1014800c60b0080e20510b4115480c00c6100c203603500d03615014400140c580c0a04500484044200a4074005400690b0321142c242c40c0310f94840001e0207040c0010750140407072541c40781148070140c02c2c1016074002c1000e880c031800301161607410240c0341c411050010403c00e402000110024021285010155002d03010b00c02000780b84c10310500492020700c4115000540216480703070302d451280601610041c401040c00c0401c5003440e0130f0000004030003100203400f14581c1110000d403405140c140c180380150070400000141405a820740a0012641c1400041c0c0705103d124050044207420000090010381400c5c10ba58402c030f000e20902149541c000c0344100090f600d401e145601e13810f801211842c200c4050001020482c201001080c0b1030761503000791082624180c405111021404400d035402d2540d07002006c0300550351000280b980ca010240d201e00e00250100901180d5030b40d541d20390802c0e040c0307400c0b180442d80300c20043c020000c08500703944003a6150302d07184645090410000e034844003a1f129 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 894464460 1250 894463210 894463223
    0xe150901060309020102030c0a1b2c060f0a0e071403010f0501300603140a020907180905090c1c08040e04031116050f2704080c1501080706051204 64
    0xf0343c02164002c008aa40d80051041214080070703c1d4640400702081c2141c0c01a11000c0345040024195010400d261120380400000781c03c111148034242d0341440002c017025407000e807000c40c0074425254692504040d1208500c88400c525042c07030050001c400f96001d0610f075590400040203c0c0354212101001d0b500c1c00d1030003601d0f110203034600501d2444180d51a65520a940d140d1912020132030b030260003180d1082403500c0d403ca4022400729141e500d030080280d04841018001070b00144035040514031101c23411000c1720016281c0010314122070342103a40e081c0c640d04c40004000d0034502a15074061407196111851907040c025500d40209005e030380b060101e0b0602d0f00020600f0980181880318103040340340c04980d000d44100036030524003061031042c1400b0b03003070180b03041d0f001d8141b54030760000032040c0d540c000c1e0000b8101c1c044c8000b0100014026651036005120260513440e040c0203290440f459400380100030350511038030324149045580f100003440020803805d144094461501540f05421a0307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 894465710 1250 894464460 894464471
    0x60206100b0706050601110f0a050d170a0b060d0603150b0405060a1206230402010909020307050421050607090819020d062c0304080105060d0c1a070804090203010e1509010603 77
    0x5c0c0140c51000c034040b04004940074040072020798800004040304c19034080c1c411558445851b250a0782c50344030f0740d100c0384903200c0500c0000e10b0507829504180c1c5080405044c01c0d1504245204c0b41088174080c0c0c001b12941d900d01e1401881442140c01030291200c4201d80c208824104400003c7c1d81c0805807048803040e6913840344000c107100d03095110010840c628101d1007800015503600850705001214100e020942120012070003800602c2a00e109006a8440314681424240111000290f4516038440302c0381c2032010070300040d011721640c1d010304000e4441c1c91486042c000040d080541c50302030360300c40310340290340c0f880036031355482c52904044d802040014a030f41888030900d40011440c05072401d03082182c1c400b0135205900000410468210000070881603e42404200001c515a03c0281002c540c0c044240f203404900309040003600c00440810f89004c3c40c0707a40b074240e40d400903401035103000e038080300410420485020203076200c001d62040b051302e81800c00c00690006418060807013050740d03030f5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 894466960 1250 894465710 894465721
    0x130c0f0f091203080f090106150c1403041403070b0315061b0109120f02010b150c0319050a09060f0c170705030c06070314010b030106030c03111201060206100b070605 73
    0x90500c8006404840d94860b9240c50500780070f003140b6020356030f58000180b4000003c01500040c440c0d4003c0d604424601d240c004480b460489110700d806000342c6c1c62400142100e00445001c00c003d000400424103400b21803101e00e000c050500102c1d611aa1000d0010010004402c1150449841071030f07040358844c0e110b21444011042e20b910050b00c2c01110340c40c2c0340f891006c0c045426450385030300601e613803035244201460400300d080c2c8140904c1c89820140d01c80c0101410701c1c0d41005030800902c0c0108032400c281000314038140302c0c1a02c0380584049035000951001c0380c0c2c0d01c801c13003002500b00e90034040000041100014600c1105410281150030036001d03122080c4000710480d070030107820000b281d407202c064104d541d0b11810180e62030004240f5182c02c01c4040816045400d040703c48501c107032810b6078a0a4400c0c3e024000340c0038110f0800d0b94465245061031040d10241c10303d100100390500b142d40c10101c0181c41c003840a01012441d041d5402e040120004e101e0403500d0450340610081181d4566 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 894468210 1250 894466960 894466967
    0x1030c06020a0308010b0f160303051503030a0e04051f03080901080c190c080c0a0303020405090601140703111203070c0303051b09012a050d080a0b090a0e0f030c0c130c0f0f 76
    0x1200707008c24a10001d20704500c20b01d6495045030340240381c42c4880026901030382d0704240d40c901c1070351070406c08101d20004c0000285880d9100ca94407554014600c102950b040c0312205000d58035810489004102149003101545c1c010b819551000316983c1a514203060028140d200300b81001d0b40c24208088692440d04011250b416a0407001c2c40130b040320007202141c500135021390450f01405004080c800000b4030b803584282c0e0b000481c0c0c4c200000b414500001500c0c2102c15041d5143c50214500c1a90300000080b054040114801d01c10b981c1c40107802080380c40c005080d00c0c800340c01c945190600008066090300c1c02d0042b20b1003c0c2d4242000ca00a00408495806c0c00e0f845500682c401e81c121240081809004a118180c2c42880d0f9514050b40e5035590f0b0744001c4515506c800d07904500d080c000203480c008194081d40140d5403900444820108140105156500c54140c4541030340000550903602c1c200465000440114004103102510203e0002000c1420864070b400070052480380b0800403902 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 894469460 1250 894468210 894468217
    0x6080102131a070b1f030f030c020f01020c03060106030c02150103030c05071e03060b0f1f0914060304030503060a08010f02340303110d050f01030c06020a0308010b0f 73
    0x50400003551038601c200d0781d541c1103000d90b1045811440380070308681440101c2004481009501400000d45600c030320403c542a10700510441c08044002da1010000c81e60a0b2440c201c440d1181e603a400104c2e030386105020b40a04520f200b1410f540c800124505075507004641141551501d20303001400400d000c01c100d01c0d0450601d04610b440c0034550020051503440607240800c14015412154041c0c1c0d20381d50710401020210966414480c1800148009800c42d04104180d4000402d4910400c6c50355000415201609525200c0741c0b0250704540c0f0300c9134100c40b100008042d50881180c244040b880455218840100010200320001000403090f42e52081280c0103810002d00802002e090f4545c800300039030020040021840e10a03101c58200016034105a03a2030b42502da0341c3c000a54241e809901410469070180c814020910132202801318602c1803d03c11207150341d040509524500341503404d4050750700038400b150801c07103400c1d0100c0e03080800181107503543c0e00103030303501c5002c520400003500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 894470710 1250 894469460 894469469
    0x14010201062601060f0b040b0d0902090a0f050702032701020f1005040b100501170a0b1210061a03181005040515010f060c0201030b0d1a01060e0d030903020d050106 72
    0x215498062401c64000a04111040502c640208501070f241c00942d0503145440c410107602c0c1404100500c1116801c00180918242003d00803036544420b500042c0100f00851381c41e00125511108440c517080b90340a031942041c41e5002031841c18241c004540c5c0011aa81405140c2a00d0343c4400d8100764420003007000445503540c19200d18580a4100c2d4000d0300b401c0e03500340c0d181e408210116810584160043e012200c058403980d0203000030000c071031130100c03000f0040c900c2c19590380080c41032520303406e044c010001c1d02203010b0064080302c00011000c4542a410800c02c210088a00c00c501c40104000c07607800c40841c16400d00504000c015052424140012542a041c02c1005000030010006100c0000c1e643d0051081c032940c0c0c80b00c0100300c3c2c0900610982c40054200d04648001d9400b0ba405483c41000c040c1207502d05114030b45170100610360f1b52070240d8440c081080100304c6c01da0300180a0405c100700b16500c0115907110f8500902c003592901010740710b041b408500c0d00411000354080c50041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 894471960 1250 894470710 894470729
    0x604050306010806070216050a090e0c03030301141309080319020c100209040e06040b0c0a05040302120f120910210c020d0908120a030e07181d0f071401020106 70
    0x1980c46400e5161144c4054601d0405449054520154250700c80d080c601520b01c0a0709c40007036640b81c00301d25409851aa08404418018842c8c0422035403001d000441c060b01400b1100c0040c02503c1040c0150300c2908110703050a036140c802900b00080d5000c1c02c40b0b4020006820041c0c0c0c3e4541d4241c070300000e00c41c2e030b00b0701d000c1f0303103c2c0307082c00f51400d0416000f9050140049600300082c0001d9410310b6150a0100d800401211030040002c0b4400080006000d50308900d1500301e0030940c80b98049200800c01c50440e000f660303c00e441181050307004210f0f400d00c03550b000da569070514600d40b000c103e5000300645c603503040c0481900800c0b20000c0210180049128010342480103031110403019403150440c2502d840001c0c042c0308042902000064451011219607280610b0204c9003d0210000c103000100b0902600031441d00060200c0b030304101902042c0700c50390000740c200803010f540340240e052090402c1c1c150001d84c0d81000f020b00100301601150142c18103034000501240c0103d0040206401c18502c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 894473210 1250 894471960 894471973
    0x120a090201021002040e040c0509270a02060d061a0a02070302040b15031302010f030b03190309080604061401090e0d18050a0f03150b10052d0304060f050717040206040503 75
    0x100e1916146c0b19000f0390141e0b03c0c51013500c1d100c2d01440710f0100101c0d052a2030043c80614114902019040c021011107400f058500c091400e500190302d43c0d0090048100741c907140c04040c041403140064440305043e507005400e1804080501c041d480c2c0e4818030006e0f200b05c2d55407010706825254a8071012101d04000174595032890078621302820b200c02d864080e40059208891019820301a21544000040040041070411502d005108451a8008040b010406000000034124038204a101d0190b48581030200c0d0200c1c1c03a809080601905900880c40d450428008900b1030b1004111085c011920385004c0000c80306654540340b500505601542e04101c00c440b00180141016005206482c8180880818508052491405c1d036075052a40d580c8090462440c13000302d4001c500614003590704054048611035084041003001d0300d03000340ba403d0300780d00004101c1004003d01c00d41903407a07083c1200b08814100050300500001101c090f5010710442d00003c201559510800d580041c940201103840703 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 894474460 1250 894473210 894473219
    0xc03040f121a010f0509040c080604080301090c0e13020904090813080111031509090c0d0f02030607090b16062013080d022a030106061e05120a09020102100204 70
    0x800712154001607540070380003500070403850001d0595034104c0f111901e18219460418013080304064014104694403003071180001007241c3c0600410384960b000d402e10a0f160342c54503040ba016180c0c0b002c400c4080154984424001c1d554115528040482c1c00c031005032680780490101e40204111070014181401c041400824401000010300584a071a00244401404901d07403059a0100f43c9042a44210f8a0b1100d1005d0a15603a2240d106624200f1900f2030006180032410800301d0040507502d20303001004820540c1000c00c140307031300002246001d0700c01c035140c41d0641c0d030540501810b10307801107242d400300014009150490207280b81408012026061982416a000e42c07040261030304247c20400300040842c00403400b00059a916005000c000c0344d420000d0603d5049000e035a01031000d80c10b92001c0989091045001402807a21040c02c6951603032081280044580462001c100042010141c48070307820b00b005030000e030111004140c0401030300c0180d00f02200002040c00d802d2001c0340020703 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 894475710 1250 894474460 894474479
    0x40203030a08090a021f020f0303010f03030e181611060609040212030f030c040501020f150109020a0908100c02010b0a03030e06161401020d110a0c0f06021308100605030712080c03040f 81
    0x17121b65142e001c0300c541e030b1882421a52a80001d02c50322140d40005082000031a018140030f0000030001801e061004102c03215251485000350b521403034200e58001452802900070080c1501c04074030b04000c100c14600040000d105800c0100000c0c0241c800d20400401941c0c02c005840718048050601030310383c900700310a00c0d00d03034219108290051080c12181c1da07081070041041c0c01c4400365010344150300e81c00c0088040196015400280400815120001d10340c01c00f0f0065490000181001296000040e60000e0035142c03c071000030700c682c450030702c01c00c002030f04003260340f0080e941554042d880b0314401441c42400309100d00060603280100d404c18141c024194000e141c90b03440c0c01002c0150304c003403094204140c0a18200d8502242202c0b803500b01040d214092601524814000545030901801515410900a0b8041c0e1000d6019880500e00401d01c1d000300d0015140a03001000842c0ca46040001101e035268009040c0c400c000561181c100018400c66001d00240f00382015a0303551410080d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 894476960 1250 894475710 894475759
    0x80d0903121a19080a1101020709020d02130911070f020d050d21050403050d05040212160501030506040b1f090503070b12090c010801060f05070b0126010203040203030a08090a02 78
    0x5110360b0030441d1202e0003c030340c5004142600c1900c8014445501c1c3c03640c81041c0361750f0801c41036065101e910000114050300b4001851003008180025848020a514841c042000740d00300e401d44a0420440d0070780c0088100c01d440d8425006081031010f00241e00109a000f2022000540940500c59110034116000005045c844001c0c203201503880d400512642c044074419140200041c104202008098a40e40c01c40341d0001d0004006018649019600501d01950300d64040010407650404001d075603003510074541d2180c07050301c003804030480e8400050064000003000e2a213410800c04006403030342c855032090000d080c02408550220ba2904c090120680100085c0f4042103010310004003134200c00709428010b860103840700445a4240361007030350030007081040a0f0030084d0074040d4401041c8007100d00d5008103680c0001074480340c1740c0e40074500e420740c40d03400441043c0c1c0100203000041e20004210ba03410400d43c82e00d08800c3e01e80940e1581088040072002e50300040703080d00200b100100c1ca50f503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 894478210 1250 894476960 894477011
    0x1b0306021e0a020703030305220309181406040c0c0605190f090b28060e06040606050a021902150d0e070f0f05062209060302040c0903080d090312 64
    0x180c0424080c01101201ea446040745000058000040070000a80290001904000c015001d100b41954607400d00107000b40b049015000034079143e608000b005480c2147c2ca00b1558030800900c01d001400030000b05019010380818022551004202400c4d8403138220381c1030082d4003d00c01d00031740c105a12300c001c9442e14a8162041e00e40303854031007210490a031107010607160703002082848a0740c803002c206d10000c00d0042c3d28203e000600b003104003040f0482c4180000741c007200204c04030300e05040c0e05020444040e50030903010b208040180b40300c96900043c220260100482d051a070718907081c8040380310140204201d01501d18085000c00c0303e610035030400e9400307549480444181b203a075100c3c0f0710001e03904d80c03080d0000e00340807510a1000b401c100c1c0c020102c1010840380780d00d4680c05070f402c001c10010a40c2c800c6155030760b2400d050046251030b00038000a03500a20b848a001804e584a40d40e66215694071070702a0355584151408050280018070220705c0e000c0c4040207868414121400c0f1401c1000c02c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 894479460 1250 894478210 894478237
    0x2130e0105270a0f020c0703140d0507080d0b0f09010e070809071409060f180a1b0f0f11011e050a0219111f0e0d0206090c0105071b030602 61
    0x40300100d8041040070b494020480700c5403503403a450f0010b5076001480020142111079408000442c0124402c100000c015440780115405880010305543c0c00c20f030125140d1400c100082082d2004521060144c0d00006040000021400642c0c000548040200709640ea040f9041c40000185801600d8403184224405d4030f0f4408142d940c0300321680c0711112400f4008405242154010711414085003450303100e01b000d0650700c3c034000040000780070520080544503240800c0001c0010f01045405444902c100c3c2d441404800050345034054011a07083e07000c54100210b2820000003030b07106950103254a52540700030001060700303c9062461408642400c0d403014204000f15032024550b200300e851202400c01c20b852400380046040341d4100082c0080c000e00e210702d20410603ca10841594201d00b503a03000c00003080110019000d09050304100e49000f5034100780c040000c08803010a401c001c5400919200d5a1b850141c070b4014580007517803e24007115441c0d01400301c10481103a00070001c0803400034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 894480710 1250 894479460 894479479
    0x509030703060518010c1b0c0503060114120c030a0b06042306010f050c03030105040b03030c0f010504140c010f03050a06080102070809010206100b1c0204031e0201180605040e090102130e0105 84
    0x1004e60300703854030b03001c038080051110242c00c2143e448084210400c248a40e00c0504681d0340c420009160910170703001091040c8082681607040d14040340805c40c030004800103045204282c100280d2239102907030000d09540c100b0300014005948603400165021844900c0c4220304242d00100c3c0030810b81100c006000c03810508031b00d414503020742e054980c90081100154510382c20718052001030302d100403007140c01d48024010b100d40c54405002d0f80040c4840800005124038007400e001d080e840603041440ea940d0006040d002d1070b643d01404819107400f560602180715112100c120009203201c1d8018000d5500c00309010040010360402004d489409034204d40c81600c524201268012092040c03103115030b010042203014a400c42011408070b200f1040c01402c4c5940c0e5101d80c611561660030310050b868404d02814119038202050590101d08100c1194110b81007900140241c452030080c0c8500e880b42e0000907a19510940440d40c5101240c1030391000c850351110300344400442801000d20910021 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 894481960 1250 894480710 894480751
    0x2010c20190c120501200a020a142a031506011b030c0210210e0d08092b020106062313090204080c0901090b06030103021005090307030605 61
    0x4a01500042603820081e20100510280c80995140340090403941c05001c90310006148030080d5403ca9424090000030070b0740e541140c010320611190f440c3c290030301d60003071000c00622503000030390822041d8884480103a01c81d141000501c2e000790102d60b00b208105a611101080070401011201c01100b42d003298140032401183c0c964003801102c2160016400003c000341000644404010b174a001c0e041000f51541d050300170400c00c5000c0083c603004201074440c0d45243c0c650810f4401c043c3c85860000708103a03100405072035183c081d040c2c5136408110099000c1580808180400c02c1714020b1105210150030054845c0f40110ba801302440c40594a0000001000ca01440040744c03221b5491000019516556038640f005810401a4580078000610003003401c40c56440280094148040140171800c4d200e8100614040141c00c082e41a80c00c148070004c0c03980765282564152581224402040382c10450200c3d00303030280c08015a0315210380200007060004542c405405034160a02854405100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 894483210 1250 894481960 894481997
    0x20117091906230402030d020a080a0c05030f0a0c0317010b07030503180105010b04080d0207181806050a06031a070807030515060c0d0917100b060903060702010c 71
    0x3280d00e280c46070070146408006120004108050a104440c0069503030302540d00d42c000b040080a036501180307240c0d0705200a42ca01000079201400f6035100078074510185503508600c900582d10703c5024001031401040401c0b03014019148504206c00b0350a44401c5150341c010081c400c000429030210320b00d018a580400a001e240c1c6059601c0f40010300d1510950755022546580003d04003000c10a1940301010051002c3c020180241440640182c50743e007401d45042c1040c1c602503154083d5030080c0420406000d40c2440811107e60032140000c0940500d149000d44002003200208014a05001c000e040c00180e4010700c2540d00810380c80140c0101a101c0d01e45444096070b000011410002c00644a5486030b082550f000120380c0c0e2300c000d540c0c40c9070046000c036005440403481d2900a40b11400c0c5031540322031807000810704080003007007144018000540700c060209040d41c1850f141da041c0b602644400742220f2035080c01604032807052516200003402484a030307042c1d4000502c03549101014540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 894484460 1250 894483210 894483257
    0x14030106020c060f040e101a0c100c0201020702090c1c0501061b05070b04030b1e0610112b030507020313091805010c080f060402041409100803030903070201 69
    0x1030540042035600d4501e01003000710b03006556034190078402044003041c81640d680d5454059034018000c3c0361158185004915403400344600c64120074800e00105900040001d80340d100c010100100155500d002c160803800380c4142070019420014000c280000a101c0d48001c5c00c516044c0801d0003002444a8202c8050710401c0c820080012031012040803105c0ca0b05000000151140d42243c0600e1b035507100c080220703003083d402512414040c01c2013004140c0c206e50700f4246100601c02e601c51034900b81d000601600b40030304d8a8001c0000b5a88031802138101081540340e07210702c1c141602801c0c2c1c052504e0440100d03c4044240000c0d040101081c04107000206895100c840043d5041d6101e04101303018000304864060090700311003245901d00032507801c1c400e5884031220b80d070f91b49466203400c2c0010307025208098070090241c0d20400041240d50820000400001c00c01c6908585035201c0c5000040310294a40103c0d07418000001840601032001005045652003038880c10846c5840240d843c03d00d10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 894485710 1250 894484460 894484469
    0xb2d03040b0f1f140f040e03032404020d0b010e0d0b15060712030e06070f080c18040c0207081e0703021002161d130c38070201140301 59
    0x103105a000c604210301c819803495000c810305200ea40c41ea84040103800e8480c61603070104c451114225051051403c01e180188103204090364184124084800842c1e074900c0010305220342c0d05540f03801140c5075080b0f5650f80310132940060056490340c5032000d01600a244513100039001c121100303c2c5001d9414501c0078000d000d50450440519542c1e0740c104a51a00c035035021251b80320904004000000b1201c443c569030742801c1b507500042c1c10500d4880c1c02d103000d2015018005000b054104039103016403200c0006c1d0f02c0b610f11141c032510740b612060f40e41e2030103070a80001039010782800310320507045600044120440340140d0842c1e1070294041210000c400641e0681070003500402018000340c14880d84070b004180c204e00c11180801d002a184411444450700321714140304c0758010b81c1e010a5500c0700c4180c2c2000d48040e1100020301e4958400c0200513484c401e40c0c4c0765155050a4940c8500029402150001360000c2c0c0002c42811844c458180e5020410881c01310340801d82158000c402c000030b0f03a05a0303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 894486960 1250 894485710 894485723
    0x527030a020f0d0f0602090f01020708121e0304150b011103040902090604120b04110603090307060e03090409141b0a121e030201050403030b040c0f180b2d0304 70
    0x40c0281d800b4004100c14290070250032070700c0c8200841c0050071903442d0000e400d008410058a032805041048800d00440e40c0650440d0302c208010b119a00011800050070400d210310165038045056610080c003655032507010206202000b04030a0003000304a0141c01c40003103404010040c1e00780010f5407045888c0040c16242e510a21003030202c0c2002d98020210003800400450030540d849001c1c10384020f40d01c078210b035809002001d210400203400790000c2c050320102c2380303e401d5103480003055070f07640202c0307001402d080e445100c42010301d80280304451b050203018005010400180c20403603500c08041c00650300d54496941c080d500c104150300c7c1c0f04003c0d00c0c01800d01d00b9061520741c142154040000d0140c0d414134000303500c150b250749000e10104a203480703078002007154540750801408985240100c0350069080c031403410704440e4015540180544d2505101c4020390b542000e100d02e40e080c0703401030030b441d110025906e200342e0f07421520a116403418240718400174501b40c1c559034240c0025100103110 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 894488210 1250 894486960 894486973
    0x602030f07020f120f030405010605030105180105070906121509050c0a0215010509011a040f0f0503010506010801150c241407140901050a0c050d03020d0b0303040e130804090c052703 80
    0x405d10004002e64116010341d001052440d02c03500020300b10f680070748900c10042c4040017666809082030003803a81c4100d090401c01e01c5186480000fa10405111381410b5007550368038905617074100c80c0c2032600c0141c250400c1c1005070307242410702d2802c030384c1c03002e82c00c800907200301c0c02080501400e00d01036505940d406800a807499107042c0800d000541c604031250b220b054203020116401030b45100e4a802011105c1e41d035242c4600d018285421280d000d40102e0402032000300500c8800543e5000040c0c0780d51510344104002510b0410070189110a01031045480041010311043d04071904400c1d50100a50f0032030303040792a5204150346d4250204031b8038001000073b111200c555030040000d03040b403c01e1820062086032459540c2420040000f4210001c130f6404160720300500080e00c03030032815140550065103014200080b5108500004105000405950404204004100081d038006010b041d1040c003040c07200e020094481d4001084100b410002c1c402e0101807002d01c0c04820500c5040035014029 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 894489460 1250 894488210 894488227
    0x250f03020607140f0d09090507051602100507020a03140f0f100513060e100b0a0e0604020a14030c0403021305070804020d02190803030604110307050d180602030f07020f12 75
    0x1c6a01054100b510134003c050049404481c2800600b4004003107075034070800b060600d1858011500e01030055020041c0a0001503007120b0700c9100350380a590115680c802190030035208550512400800942000064800100700031810795407001459644080e150440804400d1a544500549030501d90b98000c0308e507170301c41680d941d1001d504404d0019003a8003d4009440300300c00d4540d5103080d00c00507440354035256041e103c2403180c00d903040c000712284050145055001c00e0b081d0000340112340700d2a03000504015180c056000c1c0f80324002c030400f06a0f140e00d4a2090415140c0103844141e000b1200c101410980074034038410b40e0701c50f21950700d800115840b20f8080c001d5044449001b282c0107004200601d044141035096075005220050003540e50b07281070320500095440c80c1010401e40d030310030f005000341a078025080d9100310340001c0300001c01f012141044070000d8210307540508170510000a10202100300d209107171003030302103030211a4910100d0303600c07598a10144a110b00031a105000540 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 894490710 1250 894489460 894489473
    0xd06060b130905070f1e09090e0a05161a090a030c06020a110a0f030303050603011103181c08010e13020a0b031e0105010906180801050f04021f080606070311250f03020607 75
    0x503041b2180d481e00c0c0e04002e84030300301402100c0400c818026940d020034a4002081810408800340a01d000100202146040301c0180b0f80b000c0f00c1c40407400d00d180410300200036210a60b00340011900901240346280da00e0001035103030004e500064501c001c03030a000c0c02d402d052038603600c0111039140b441407100da0b03d903482c101d004000241100c0d505540b9102c035210044101c101450181c2042c0303150143c84505500791a1420025859001d04215460342c0360600c0364014040303504440c09a50840c110b80e90300107204984920310301c802980700048042c0403403990141c0000d180325800c00c865058103030303404428008002600b4403803130340094101e1070148031442c4580500a1034910050304203541c5074407100030b01d0a40f64201c0700241154202e001b00000e52408602561045c0d004001150301070341c505200502001e402031180c2e00031080050100d040601c5450002c07001000e21040c0d90b01c46201e03401c01c0440c9844200d2801c44500314641c042100349802c01984100c0b6030040681c2d04d401c0042da510f5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 894491960 1250 894490710 894490757
    0x6050711030102070f0b011805060906010e0d0f061b0c020f040f0207020a29071106130b1c110c1e0109020604270e0a020d06060b130905070f 62
    0xa90701550240048000960100740c070501c024450344140380345606100b500602a0000348080b1500c030b041000340848c1e612008180794004000b840d00c0c0940c07140080100b02c01001c0ca0b4401031480480d80011818441150b0222000004010361042d0300f0307400b000111107400c50708a0103940a440404803d00da0b04d0319502100c06980300c01030150405895400003580454140d01c03068441d0001c2c0c0d4242e100c504202c4898002c8040209000e04240b0b030303912200488060780c100c46001d1200001c5038036480040c006140020031341a07122580d607001004440242080c4c4105108206082110200c00c0305150019a060206250020081c0203444c8610351913411030900005103039580e5039643c8d4050388800c2c008101030101c1302080c9002e40102c2060075080301b220380c00c0380307584c601d80400100d0a00020032044030b407070303011180d00a60700300609224006102d50f0788450103030700d4002080d640061340c1c9072190080b64030035641005035a1311030b201612001444100d01c800150241f100100925074009074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 894493210 1250 894491960 894491993
    0x6010b09102304060302070215070f030c0f0f1a090d0e01030b0604090606051c020a050427050108070e150d080c150a0219020a020f040c02010e071d070801060507 71
    0x214039421a039002008441e40c0f0503005840007940004155003541001c0034080009201940c41d1442c111154940301407a4036a0b0400500700811103030340301f0500c000040701003251608800341c0042c0c04441c0c5031009411024002c42103034003103000e00280038601c020490348841d0910751180015203541c0300045005000c024001c44c2d10040500010401c240c45100f074001405481d00c0d050754440a60071845415001c4000e00c41100e401084000c05565210007618119110080b82144040b40390091b0108100d11a14074200c4900e0715000040c0f54100145900441e0007000c0703205810784640400c84c03008030501054a0300b10f2010018000000ca0388801050b152009100b5508540c030352039070701103031b01d54291142c40c0f020342c01145a40180d01c64a00f990802c811900062248600035404952141142c5a03d10300c1541e82e46100e2240078003e400903c2e00012220950720040d4450884842e10190361000000c9024a0000140100c0c02070a0060507585c25458450400381550740f0004004500b029 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 894494460 1250 894493210 894493247
    0x7090b150c07060809121c1b03051506072003030c0f0304030c21110a031e0506131a0c190e152b0204080d030e06010b0910 54
    0x408001003004002030308400d1007820140040524000c0c0040c0042c0d009880c0c542e40707030484e51200e0310020383c0400312201920f000c089503c1901002c0c01c40c50040a008100b0410f410780c2c46200408140d05510540c450780c1e401c0e0070414800750700c5080c0001c13030080781d0004282070884509003181e01c4001d044201c909070001c2c110392130a80001c409078102540c5c045d0390f91660b07002090034410003101000c0e00000e062180c003440d10b0030741901c030304200441002c64058414040041c140c8881d4881003a80f6000e503401581c003403400c0001081c106081190141c05940901070000811070b80b400383c813034a540340c83c0c1040416507440311114202c1c10744038001c0d1400e408003c081000089010444400ca41024880e840d40703230130090814148050b500e6040c0d207904540d00c0400103201c0c208140400c26004503403036480210b20403402c0c40400020300c0343e134001040703610503410a11406540b64210514852811081d903040d66a101c00c4403415000740101254403065180d50740c0182441200c003165150720782c0c2c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 894495710 1250 894494460 894494479
    0xf030209270f071404050906070c0314070c1a0a02030a05130e010b0903010c0206010f0306091b0e1504050c0d02280908060f0106050712030f15051002010504030207090b 74
    0x842003440d100b1100b02011150708801d07020032008495030b0210703500034010740e01404189809101a5282e660080882052050700704004051510035400b40200c04640028555640b9031801c00500c83d003030030711034075101807062081050200c900c0c4099520250380c03a0000c5080075000d200a80d4190044c030031201e0b4003020b11a0029103590095040703030084c0f0b800c60a1540e6034034920141425030701002c13225015948000010403401c3c10507445101241d030413581c006481503452410001120211507103401c114200c510120340c900c55414079078068080c544224140c40a410306100c16101c08850310102030409108000b019001600200803d5410320006003815205188014140c2481c0711070000180c10640305005014080208981060141c411301e0b4540d0305d0102e00421a1064001c002e000f0642041030b8940a07000c2d0f0008026200d010106004014540781901168101c40c0f02d124420020100c609115900602c10540181d4040d405016502d0030010094040c162a0285a40041041c3c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 894496960 1250 894495710 894495781
    0x40605161401061d0f0103050705100203211e0402060703080402130906022d07030c140a2006130506090d02040e06060916120506130e060603070f030209 67
    0x1c2c0300d0f4001824604080c10300c3c081e0304813462850580c1c01450340754096203141c0184041140040c00302d0440d1012500101820030443d01282140680b2291040c180c4c0d418800e01014104030078607520801b24012080980441038103010700c81c00050f070317000e50055400c020300e0010906c03914580d6402400a00507202e0882c1040c0448104c2e60720000c240c0745107a0210302d140c40c41c882e0b0705000d03281c020280c01c00c0300000701070210888144100d0000505014841c6020b204000394507003001d90380c884400599542940d503091009010100140d44040740c61514000c444514021064500ba10345d4405030088050400c1d003881040d500246015a000122456210060b59a40a0918000000c402402c2c4500b040e4051119401003e00040503614400103c190002d074050059806000e0400d80800e16072260404100214618500d1007035103820000780081c00c040001c0c0300c1b03014800680468203441e0361441c002d0b071908007d0000039400300c01c010116000c4c0c003641280c2c80301c0c1540c4124030b44135804c81 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 894498210 1250 894496960 894496963
    0x6111c031d03120f06120c0d020102070509100f09020c03030414190f05010b090103080a03020706140412080106050a120b0a1205060106030b01030b1f020c060a0e04060b0406051614 79
    0x10408600c0800031040030050713a6009003c0081e001076007070f1050200a0925000f042e21204280041401007038a582d8250a43e0710800c017610003408040c01d029540c0c1807500180300c1141c0b0178042c3c40b072403075542c0e0300000751601203108840c17820011602840c2161295914032156110071101c03120907121354481d08031400b40003c071007292280310300060301042145162090940f08050115482240345c480104041042c0c50300305c8081075001e280c01a522409490480028060b00c01009032100402c4200010420494503035030465400351155402c5a0b070b501c03022501c0d84207a602d842e00084000d8401c400c6807007240c00c83c2c0c8002c04001e1814013075540394401054203c40900090380c41d90321420040002a80511030306201c4c0d4030030302c2c0502c900d01c000c202049622100ea46403841c010748408286000502c2800b000403c21001000c21b641ea40014070010300041c1680180c5100350f252210020b03040b28408200c0301140d4868588500341302e40040741e58a8100112002d84407140b1210000084240 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 894499460 1250 894498210 894498217
    0x1f03260f04030c050f0603040b0406020403050d0305060418050705060a0e030f0706090f0e150d1703090d2c0105070c03050615010e0a1a0d1506111c031d03 68
    0xd00c24040e850700c1c610305141800c0071241e48503d005d1808003080450303170f8031504101c0e40d10903004400c044450310f862a00c00c0083c4290741c0041c1582c000d01d1010384800b036050300101d00907c0d08441c10700c41d411040c8140f031010018404001d0680d401400c04002c3c50501d0720103481d1080780c0c1d051041e0301600c00400700341040c0c2e40c44244806a006082e0a2003103613084a142c00242070302e00340900710503040408c2c611038040041c08052a00101c100188031550b602a40002c145a1210403003400d8900e0740e0078111541c10a41c5d07484030340e0082c1200b502c0758611928401ca89842035421500c0c1c2812204813400c142002c1080c5941008810041d50010440c6802e154004501c40c800404103841d06110b0103100d0703028030f0f03030351410003007225883c4009030345400030401a5030107003200c01800704c00d00d0621031083c450211400c500c9801e003469400a1345070780c49060f04a61003600c80304855500c00a146480381c82450421040e81861582612200d01c40d81c03203400040301184484980c0311003211050b19542 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 894500710 1250 894499460 894499477
    0x11091e1311040807080d020a020409060e030a03090507170a1112070324020a481406100e0403020316060c02100b0d110409080c03121f0326 61
    0x101c00090400007807804002c40c400501c034100207040c1001001d00c009485800208010b44a80d44803a0180e052140c203074050040b02c05040c0450b692906240c00240141130303a50016207240c024028001000206842d804c204001503001801c2c001041e0b9540e00d0b0541c80079808035410400e2481c58242880041007818040c5003e003404a02200c003940040113140c0a01280d4402180144410170220341c1100400d15070750b80d1405810384285965400c200e080036407043caa40200f041504071020070a0a080070200c0da8050909401028003541c1199551141a01d0a8030f103045007400c10400300b1100d004040c1c03c184240305603450070000c10008008a044144282c4400d81e58112403010715404020100000c04044000d12100e008100054040d4985840150041c0124040050303690b51f40da0204404ca640000c981c2d8036000e01d0105250369400c6820001c00381c8440f500800d1060021007415400c00c1c03202c1c800c102c1941d06540d00d1403180c03400244459403024000c0038918000104102a00101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 894501960 1250 894500710 894500741
    0x11040b0a050d0b0f060306010507050c130209190f03020d1502340b0114030109080d050105030d0801210f020901231f200a0c030611091e13 61
    0x4000002a903030032aa2150f003458400e94640113100e205488500c152584200c1c01d080150b140c542030b0a00c03900300741036410b8155011a0320a000365054240354003601400c41d080d12581051044070504541490540c01355803800c5104900403c0149084800407407000e20981c003074040f1070700e107100c00030698005102c2c6502018680c00c50000a40030400040300c806100104400281d55540b41c441900c00103000e6044030b9540301c00c40d030215071001d40281e02c50382c0d4800c1401c1c1c0d440c051000108000d040a005442c07082c060920180c1400d03114505440c1621440c0801101c100c5a440a8601210104d402201c1e0794140d01040000f607510045418000c050794000c81400a02041ca41411484104501485080d0780030040130710403181c0a100c03940601609200158103180c0745080321300d04c0326840e071101910801d04014200321a80207201d080720b00c117400c00d0107000e0100d40024042e0050801c00c0b50804c1900700c0e01c0c0c0f40c80d44107415002070b508005e030a00c80c1d1080310580c1801551440062419107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 894503210 1250 894501960 894501967
    0xc03050615071b0e04111e01032c1b010801060f0806040b0d1a01050402120f0408040b280e030a150b0307030506060f0301090b150a0f0806040507151211040b0a05 71
    0x2031040e5064030840308282101c102c81c2c4c02d1103110804a48410560300307c0d04050780c0303008040849100d41e21642e540303504141040740304807800151655590500c41440342e030400c00c8040d245c15501502130300c1c4c1601c120b900ca0700d681c080a02c00442c0c0b0128020403103540a501c03101c0b80540ca444050b00c00b60080d02404024202d02000300d044411290180e002d103001c1c0d84100220704c02d055800d03610b0b6030411403404101c8925116420071190501450304051105000001c52146c020013050701d020030040180002c454600e41c1c80390648050441c0b621064150708882c0c4120006108245000c583c107900040002d0040441c0004ca0314010180e04211040c0d8000418000c1514107514484882b05003100240070800050b56504041800981071402c1110b00c3c00312320046a494180d030f03102500002600304042c0b540c0e4034400d690f07404142d50640c0d4a00415001203142c01c0c1030244034002405a48498200403526035083c002003203039200340340c04510140004110103950b9030042c0000400c035911241c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 894504460 1250 894503210 894503213
    0x100e01170105090d090306022d0403050c0316060f1e020c04060e04020a03020904060b040504060b190b03070c0501090602040914180c040903050903060f0106030c03050615071b0e04 79
    0x2c41c0e0000d80348240c40c0c1d000903500f040ea2640180c4440561703074840c4002d0380b9419011030840f0082001040380c0d45071740310480d82140729165500a4400c49004904595062248100740f40d01d80e203c0c3c4076200c0510382e40282c18864140958005004000c0c03501d4550b9002c0e15445950340e4003000f841d0800c005070030010007201c452400303018200103844e0795007140100b8281070380043c410103000e1000038001c83c030002c0020107100d00c9500030100e44c07102034000d0240f49031a15140000700020044580f00b080c0c204800309141c00c0c3c2c40c4420040d943d440c21840d240d0b4586280075110000c24001c21a015900c8920b900002080c81c006040242400d55002c108090303085110344034500010203001f040c6c1d080b4070145483c0d40001070042d06001090300c0c00150b2202c641021a4548140822241c2501c074107014042c2802c41c69000358100d0301180d608114111001c84120f050b03440503105d0a611082d5541003503801c00d6020010040140304548a11640055080e42a084c9026500c50b410001c2404200700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 894505710 1250 894504460 894504463
    0x17040302100b0603010f05090405150c1209030c151f091424061308011503170903060f0c210108120723161202030c1801030308100e0117 60
    0x280c203440b04841c040c1c11981404000f100885481c484d1034440c074030300808201488000e001450080c036051080890f14600000700b10100c3e44401c200c50044807115000030114000401034400c940400c101038002c0501418108000f410302601c00001c1101e46440b820140c40d0a0304c6050062400b0000480c44002100301c41100d410001d01007002c0840031445000c94500020542442e588100c80054580d00c1d1b0480d03400c06480640c1000071035602c1d0450081507400c0000308001100d10440440b20010f051180c6420140a00c101c441c0d016408100410109000300c03181d01d90180c0d24200182c140801c1c3c03556200e64000e210150040104418010710040c42c061040d00b07051500d9040342c510f083e100340d43d001c40c42c1012600e4104003910b83d009906004006001c903c5081d0283c00103d030825480d691540100300c0c2c00c0c98220b20034031a086003042c49080000080740041e08601807001580e01e15101500c02d040000e08501d8050451040030405883c2c8280a501801c50f10701001c4082c5007041405 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 894506960 1250 894505710 894505721
    0xf100f0c09030f03210c050d0518121606021303050f1606110a150605090609090d0c080c011e140903030705070c03020414061f1d011704030210 63
    0x30418141d50030700c0464214148201000e51500c0c00c400a070b00e00400c00c4c0003011454050f00e01e000e040c000f4000a01d40d002000e40400460315900700141d8813651000c101184144411505582188801855400060f0040d03c2e0400010b20398041292a41c1e9801c422680150fa0700c4e0121032048106009020741005141d5030500014000e0149101e244c0e000d6001c0c5044e0b110b12010007280b5400030b00d01c0c2005111840c0580da003e1030084510b90340182080140800d4001c0e1800380c0c8558000418a143c00d03804075002d1010400540304151103103034111100d00d111002a68414800c120030901d02d0400d100341d0f80b00c0f90721000c00d060300720148001070081c1c42a820040703031010141b00034001c07078083c0401200d821a00f182031071a0784440910b040369864009a0000e0360003850246201c140694600c0d5061094008850000c2a008040c5807040001c0244c00440b0024100031900800111000c3ca00800c4800504214a4600000200f19008042103c08900580216001141402c15400345 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 894508210 1250 894506960 894506981
    0x204080f0102120a091b14150702090f06221a03030304030e190b0f07050c061305010c060e01090f0c050d0b04080a0e060c010c12022a0f100f 62
    0x82d450180580b0803440c520402a15882c460b50351780d0320000401c049043c84440000031018000d0303400755038000c0581c030b4a01107220303903000d14032042d000300003804c0c1d8008a501c0158010b01500c05070700d810304440c442d400300401243e0440c00701e080501002c8058110785d10001e12280c4089071610800d111411415207001c1c0c502c0c0294424002d202c002074110703040780128182615500101000e000d845003600c806503000f490301d10000075003400003500f21002410030b28001d50840718007005040c10302403d44070700080300800b040b10b040c0c140715541c810150310001d203000390404103844001164242c215600340c0f00c200c400e03001c050849010010b4424500d001070908542c001d129404070b442d44002c0d00002040104010b50019601080074001d82c00f00744550005040c2ca40c4540707403502603a00a115000041010030f150380c2900c41203140e14005c640d40c2c0d010100d400c2d610000e082010500f0740c403581418034044c0c041c5541d031098a042c20440c0c840290854140400d03a0104001070b00100c4100303040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 894509460 1250 894508210 894508213
    0x3120e06070218040602090604061805060307020601170705090c0318030c0d03050c0403050f1005090d0c0305130504020d02070c090c0c030815090c0301060f1d040e0a0206030405010204080f 83
    0x501d405a0343e149501e54043c04080e000c43c0c00d035552032500c0c000920500c6220f5501400c08540414015403121140100c2007a0b05000c1001c035881d8020030500740821130f00480140d00c200014090150b03400d14503185c00154404881c42c8a444800040d0b4500e01101c2840c000070011041005600c4d210811035072643d4401d01451034490b400e64400c0d120000360600400741034803100454418080c4134100c500841d0480c6c2503130b007040008100c441d1102c201d050300380b14850404001c90781d0014046141d910951842d00c0e00170703a00006a40513540f0f41c1001c440400303c020400800203243e01ca078002010f5038003c0c03c10050740c40c400c40c45c000d002004643c200c003000514100020800e1600644c40c5030005405048c05101c0365180c00132080141025810613402c04904000e008540e00300401440c1030310125190900214001c42e000c4490280900e038091f04020070000c61045801c25510401c0c8000504041d10410000351700814101d43c0191070486903a9400502084103903401e02c00d02600d40580720 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 894510710 1250 894509460 894509467
    0x15010f020309150c0f0106031406012603190306060320030f1f080d200d12060b07290c030105130e010504030f02011a010c12031503120e06 61
    0x60001e41d68014900c4050040010b090501c05101d48042914610713540b480850b4507090f4110300c098082c1400348401c0b42c0d9156207509900401102040d464140c0c0c075a10f4404500d1034443c2c40000e00350f0414007458102e4007082020310404280b40c0540120f04205440102d44945044c0700142200d5540d0304101c8152502c04c1c0310340d4002d10701d1086a80020000c2005203c0d51201c1c40b0056a1050b5402c0002074190f40c060001510705001c100c454504005449004a81584c0044005181c000c08040e00664000c03264a45125008060342000320404003000185592600038100f400c0d8401e0005a40c02410243d5044401401105290703100c0031014010030242440d242c0e520f542d01043c000c4500c1000044090801003559500515004041c00002d000904150402800e510240e503203020055080a80c0311580710101000680a440180d5403c041681d250311081c40e2000c81e400c1c40c40405480785011410b0140404d06500603500801e6040c04a0f500c0c90b00180c0400c04a40c41140510800e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 894511960 1250 894510710 894510737
    0x108010b04030803012d060903020a090b1309050106080a050a02040606030e030409090203030904020d0518030a0c0308090c030d050309010b03060103170703170c040806010801090209061c15051501 86
    0x2d1060382d0441c1c0482c8006c82c001192140040c0003201c003a001c44a224106440004030264000c0064040768020344008040540f903500b204181c8421814250f00b00c1e440040205005000c0e130701c0500301c58054400006c429860300c1000d803c1c011441e40c00c0d640daa1140c01e000d415441c1610a0800409250034200705070741158041580364001c0c2d1048000304d03640c41c4a03200035920207000710340320140002c3c401c550315914011420001c0000703030740f20a02c06042002c2c801342800f002048410404c8140c851111002550742d0854401100800f8903420b80038001601d01c00361400c000e401f6041c00646c13100d640701e1030584d039001d003144e0311681064413aa001000400100d400740c215440e400501d800010303640e141300c0c1070544025545a4081040c8500cbc6000c10248842440190060300d4800e03050307a00da6603841840d00e0a840c007161000e940b1400d0b02000ca4140e2a10b803690308000c000030100d102224a15440d200e220302c10700e94919004d07035100c07001c114403041d8449003070081407001d013407003410400c0f40d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 894513210 1250 894511960 894511973
    0x11100203101715070507030e030d02061b12070806120d12111306020709181e03090305010504080a031b021b010903060f060f050105070818010c02040c030b0108010b0403 74
    0x3600c1440002c156040440031901018044085445400b072042002402c018030020b000d40d04c4181d0680c001209189001c61501c0d01040803c04080b0f15401083c613600c49416014106d0040c0d44164040f440c1003000303035080c1c030003041818402c0440e92030b0391002d0f1802170280500201d0714500c03512203820440c2a0820550041c404049103000100700240081d20001c048007944074807502d0240c05624a00000340c0c03a6400142e6809a070000d180a00101c9034041440b03550202045000b40b0303500300542c3d078a9a0190100031007245500a18040c00215903d072641421144241c034142c41d03804001501e014019014050b4030468205c0c1c207440345600e200ca0344000d481d00711110504144546c0304120300c003980e114481c428040c507000700c81046030400310300075000106114851540e0160000324001007940c001c005840c18181c016065038035005121a00418112780c0342d0102c0c2c1401108520900503849500c078082c0700d000c143d02c001450f00c40c5a40050110b9405070311100030f0000400090002594 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 894514460 1250 894513210 894513241
    0x10e100b0403060b0109092a090b0d0b2205010305010b0f030a030c050c06160606050a06090303050309070e0901050402010e091e060a080123071704080a030b1011100203 74
    0x3c003d040000c403903a01100494240e0800c0c0c0c0140c00c40350400d04064002101c08511344900e4440117040b01001041c4041501c10b400d80f445100700030f41c02404a041001e4040d0000034031048010801c0c4560a13407600d07201c640c450350421241c0d0444c0d8a02c0107104020091094940b00c24007220500b100380c0318030340000c0d07540c0c41c5500000d082046282c80041002003c1210b20009000184116140c00240003008a070080710700041e100c00d402c1035000901810403401c2c1d0826601e1a580d00e8616508603102642d0aa201926450707640c40382d4040091107182c00c070000c9014802401c004a042e003041e00004190717085c1012802e20406141007489188070000030712b0901c04807100c168401c1e65948200040030808568090750300c81d401c290312284d80701448015407950008904001310140c603900d80c01c0700c58020300da01000185080c00046004149080050280c0750458034012680417000700200d140f010362034030200003080d61038812050740e00b424402c031380381e01ca004c180460461400034482400310f0b8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 894515710 1250 894514460 894514463
    0x317150409051e0d030f06121214030411010e0f1c0503070b07030c09060215071b0501060e06040c0c081e0f070302160803031e07020c18010e100b0403 66
    0x80c1d90340030310410440c1c10302964403031680b4114000b080024561401d611244002000c4000070301c2c10705a208840594424032058480c400c2c4450080d1403240d5800048003403c50403003080c0b011504a490600c00088002e600c500c1c07240906010070f044580014110300030000920340310380c002400510540c6c031807503d00701d0f0420b180603001c03184240c00d04105045205240c000b40010000b0010001e0103a050b400c40d03a990606076032248041a580d0742c0c00c9846420329034030303030580d00e200c2c20100b00410b104a0704c5400c140000700300003025102c6541c17001c0c00c551050340060580d21102081151901c0c080c4a0040c410610341000c02141815981e486464800d41d00410700c007010941c8140c907445100c0c2c040d07030200300c1081002640c40c081410080e680d901092080000204402c00c0440c0441020040d82c0c041c1428003201d40099020244150304d10710700800410440c840c661003c101a51900480c14078140b418490b5055941401111919000000c01d05c1d020584070f103404010b80c551600c1141e0817079 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 894516960 1250 894515710 894515719
    0x3121413061808040f08060c1806090414090114060103020a14160c0e1614090d03050f040b18031203130c030f05033615040b0a0c031715 60
    0x2540c10030b0040c80d01c0b08204501401000c1e0115022454050941c3d890341521101402c0300c042e40e49000e1500d4151042c814650083c0c0c030341240c0501d4609149001d8040401c000f00007044403010060b1903008554101c40c0380032180c0d15423085101e00d80380d80d14140d4014000b03103404d524109552001500b40d8921442149440000090103c0b8103070340c40c0c0d5400201640010103000c8266501450a070000050b1412440304001d00c0340700c0d00d424004c440d00607405d032851800c1070034030340c4a404220680b00500e9095003441010400c000300c0c50100001080038010f000d81041d00c440b2840040c3c61250b020103c46402a4003c1e00d582c01d44c094540182c03a44000c1a00d80a02c50190310b15000703942490b0b5170b1006000909a06a00b01004000320141c0085860900241158000064079413100070841010003084400d01c00300145909122202e0024048035101891510b6504d400d1441503601001d171000c001940815444201680540803200c2c10310940c1c0c0700101030404034100b1703000301560508240726 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 894518210 1250 894516960 894516971
    0x1090b030910020c0d0e060702090c0901021c02010e1510031e020d0303060821040504020d02280f0212120a0e070f1809150207021c0312141306 63
    0x403030341c10003090422448480d815900c41c54040d03406a40d41c4004201180800c402d2100a156030415406448a40b50003c001c0c01c542d460365481102c80d0b80c4409030076411402811000c6a5045180401040b4000554000034002c0312039515281082104c0c006500c1b0090f800c81804207a25032030426400f500c2d0410004242c56024007000e500141d603072440250000e80c0e51040b442415055400881110144001c0c1da10b03008819403078940c803600407200b1032048003041c0004c0c003642c00d1940c0605004815160f005240c100c4017040a640c0008501550004501c8610b1510302e01e64410318000240c82980020080d002c40c40c1000c09443c082c0400040707503551588002002640146c00110030190b01e182039960b45622400c071600b41108a002e055101421480940300540580c1b0a803610b01d900010340c3c0f07a440a0454980c0069845100140d80c01911142004913662011140c003030414030980f82c03012505010b07c40c041c251191010340f45c4d803480c0000700b0000c0442c0082a0f5624250344030800040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 894519460 1250 894518210 894518221
    0x507110307030c090608120702270702060708070203190305091e01061a0c07051915090e0105010f120902010306031e05122701210209030f0c0105040b0315040906050a140601090b03 79
    0x2c05400c050740090040d034ac040140039605401003034041c040d04182c3d503500786070796508030f060303079240308521004e01c44590303902d0495105842070707204540208d00442039070310070101844560801040031300d80c00002c6e50344020420a4255200d8580c1422942c400210b04107003421000f5a10341c40b5900c21170b030155000e544400c07a102402408107001d0541503840404829018900600c40c140b140109038085030300d00c3c008909036003c2e5490218144545d0f6501c50002d038080240d1014012130b10f0103d0600d40c684001100003804003003060460f5016a6250110118034286689401100d00320071142c1e0008025650b03e9001c4bc1d035440b00c030504c0d0001104020002e000040710400000d441e080b031010f2390640040c02c1c02085400901030100c007101110418164030410540310fa1000b002c50307002c0b0f44104010402018984099030b03010035245007038185c21001e5404101a541504021a030302079039041048541c1c02039205002c5030310700f1103500e12401d280c02c80010308075020310f01441003a020302100050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 894520710 1250 894519460 894519499
    0xf01180b03120304050105060307140a090209040b03030708030a180c050607031701091a0a0803031b0403020a0621090c3005030304210f0507110307030c090608120702 73
    0x80c0700040c2c0750320065491506081ca00d000301000e42d60759200c0e010b8171500007030a80b20082d098452040060101491601e882c070008000c0d40b00b4003999810a4541c00c0c2c50310a0fa45c1032018022050082c11042d81ea0b02d0408401811a00746c01d680325100da01607031a2030b01040b2074030b41d080300795001510392694808a5042c240c40745001c050034000d0304c01c4508004910f01056410015203019050403506001166008001c40b18110f4014100c65a00034400545140040719008402c0200304840600d016100c0e0003007400118950000c802084031600450401c0002c000d28403c5c00c000c52500f000442c8080d0f80381c00c0c1b08a91b40c495280f1240402c40748010540d81600c040d40b51a0346d250031030040a0b010b20388035480350012070302524042c03025107040002d891461a04041c0070303810341d24500b07003103007142060b25650000e450940d07400710500380c085c0480d18100a010301950040d040040c15507c0c060900050f07038495004184542c0010319000b03e04000d80081c1c608e40c80d8104c0c3d041843c10340c0c210014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 894521960 1250 894520710 894520723
    0x100207051e0d020d1706010c030c05010212010e1f05064e010303020a1b08010f05011e05030a0b0912030c07020901090605030303040b0705160c0e0f01180b03 69
    0x31802515001d1402540100080d005000004507029101c0f0350088034420307164a003554049021801c095800605203603c11050303070141c1c500c41d040200810009403180303822078100d18110074074415075200600c100009140601d5201c52112074540e51603014402d1402070140c2441b409000d06c40100d0040600205900d04c58000003404442e0a510103122400f1030b003800c051814a1040b503400650034440050b1012000e0680c1c0c0c16400510001038169a00c9501c0721015010f0400502c06d0700c00895050402c0c0241c02903000748a10220390395041004030607042c004141400f841407070f9114100116107001c600e1400007900020002000c1c3d40b8540802d0030042d02607209c000c502c00000401c40b10f840c030b40b40988400c500030f44900d41c181c2e0f240c0381d00200300c80f814098158980d00038400100040c122062550f0310810703078036080e402c0520307024400d00d480c158a0000c440c94108854240300030b120710403400350302003615000c402283d403400101000c0b101d051925034804a41380d040c400121388041240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 894523210 1250 894521960 894521983
    0x703120e0f030d050103121701151e081005030708250902030c030106080603070b070b070e040e0307020415060f200706080a0b0907080613090803010b04170f10020705 73
    0x140c81c0c0c0c3c1d0310880440300080c08240000c450180c85d0454401205218030f00880b2142000c400800081e402c14001d8141c405076403c2cac642c20440d1000a540d030402d0350035030384603041c0b04640300d0143c1e505007080080e2010041d6004a40039030b0281d40c0821280000040107000e0401c01c285042e0fa0482c440e4580c400000c03180c2090b08201d00002c20300c0081c1c01c2000040d13048441d282e0703c81480d0389414003019210552841181c468260600645000c10b07540110190010704505000e11a02e541c0400729094440440702440c082e00081804000d500785805a094503400700045401040d040c8140a40315841503e096001c202c00c00c2c0404c0342ca001c40d032240410101802088503410350b0b5400300200b201c2007c0340c518104038100704502c2c42c0e40c28a40c20f05800f5400d07580b10285d15a4540d81413060323400b0300c2c203c0c00042644540c00d10011403c468011030117402c100c003e5980d0742d07003000303100b00341c0041c5c0c404182d07100e60006413425000c400214030079907a0300400c5009644c0f507250342001840c0c010100306 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 894524460 1250 894523210 894523213
    0x6030b010c05030a111b0d030f0e180a0b04020705120c030706050a0b0a091803050319020301080303100608071b170a030c0e03030711090a0e031c05010b0703120e0f 72
    0x290700482c0c4e5044020b013507400c5203440855401403081c5c184020100340003100b0a4211003d2002c210003c2d01442e8003c040d55818903103508007050000001b5072258280f5480c07036804c1c132039805025503103102e401103150098040e1801d52400c82c0320b80c1c440359180100d001c1c220710f41c000031491041c088028000ca5040a40016080c0140d05020071070400400c03602000071310a20f5100c03c0015041101d01508018141001c0c240d0240c030b0a41e1016603040d48028a507000c4038120754250742a9464501c09503010b464210f00554880c81d1070610381140d5aa00d0300081d0a00400000300103c190f44408181d140c180e215010240303000441c54042660f41d1040f181c0b039100e180100310107807020b905274010078030305c503c5540312603400d0301a0003070507100e100d20140034010f056812002c036428140800e41c1600000a5040028003500b00f0410a00310b40107800c0300d0358008004d107905081090b40b40a800e000d030074020310301071030040e4030b581c0900701c080c0c2001c44100c241c3d1541031420b0400000c0c400e4540e803090100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 894525710 1250 894524460 894524467
    0x2120d0b0409081209012403230d21060312080703021e071a0108100c030b28091a0d02030c0406061e02070b030f150a12051b01020703150b04020d0203160c020102060106030b010c0503 80
    0x140082c080310f0790541c00a52410300d2f08010100b400680c020201140d400550600f2008100070b001c440150008002c0c1c011f0507002c211005001c0001c01d5101000c0c80e6000e00142c5500ea546000c8045e41d01c0c428096040c503170490014044540e02041001110781c8c501030018100c010700c5400c0d80607040400c42c007a40500c0300c44500d004880c0304490681510031000c44040401d844617881801c0f43d81b000140010001040b48005e102e052841540d200103000800721107040b020080090f0503074802c3d401c031300c0c002142c0c20384015001c11614030400080f00c15001426200b82091848003290000a001c209041840808550a440400143c24110318054455141c064680d810328461619007402194603219107803294900ca01500300c1440c100d60141c3c0600780d000c1c50b5868005000d594040d07081c80e080d45e200260b00345996203100030104460b2a04000d6140e24040c6641511449101091828000e040c088040181e9001c904030707065940500300080c05543c4100101d0f2805082c100c0100b0510002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 894526960 1250 894525710 894525733
    0x170d0b0405070c0302011404050d0c15051f060f0e0105092103190e030a03081009050405010b01032403020913080d0f0c02120d0b040908120901240323 66
    0xc00b036421513000b40c000740300d00121381140c4007000000301d0f8054250b40080108045061180c8104050745000743e00015010f041258000f00716101628a8440854401e0328249020070301145000200714a04041e03400508031400130b0002040b0311207150400c8070001b4840c0e100e40da0071442d540c401030304ea107007110581d910701d070040c1e80c0e03038004140041c7e82061844d00407440c62003264400b03081c90015024180481461360252400c1401600b160303080c0218020105500407248030382d42c0320381e000c5c1002145d40b1009000250845616902c9103100c1070400c4455440f000c80441180210b030340c1907510040e00d41c0d51124030f954080c2c1ea504018800c2c10001444000003100c0c0e001200901304000c410007034864117001c243ea84001d441506243c3c95014081e8411000d03081d032101245036809000401d145600303070f403100c54a9004031456603d041a060510100d4502403141101c40005a400c4007020660392101000304011403100400114614400d4042c11071482d806001403070b0b010301210503030300e0f14 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 894528210 1250 894526960 894526967
    0x31a13080d0b091605090f0307120f0210031107031202040b04090603050d030e15060a03140d02101a0f030c0a030b151005071b03020604060f1407170d0b040507 70
    0xc1800751060f500707000851100100c0d0807007040300e86465110a032418508905008441142001c103a525029a800005400058810720603115105210760030b0034040300e10411032070740410f06c00d41041515041c01301c1d03260030703c032012100c603a600740c185255150300b05151a00030f807185400031550600c0114000400c00c00e5a0400000e483c411015038400490210045085814010410020341d020801ea4044e00c0c103860007440d04920302500c480c0c000398894842d40003403821840c114801d03038010300340c070b01082e41c1c1840700c0800482e000300309104000c1c40420101d030300e8880b4900c651080800c8400c0d460b0b035179000c1285401011029000d01c241c0360360f90030065038500301221703411030554442104190034a80341000340985501d6840c1d080c100a4151130348007414001840240040c0303030100002c000343c1d031510043d00082030a9501c44101a110010040010b0840c003400a403d502c1070005a0004046080911084000c1c1e1600340d10307014004200c2c0f0145c4191405103070000d11304014004000ea2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 894529460 1250 894528210 894528221
    0x11d042403060e030c15040807080a0e0405160210110d0c090501140306010914061e09030f16140303040f0e0103110d05100c0c020a0905040318031a13080d 68
    0x418040020701580341101d501c0c5c1c1300303405a5840e20b03004540080c600b1002c54800580250152941c8e1b070a10010b641c0310280f030b5012007840004125249090f00c40ba103450f0140c1070b8082c0c801040c0301310358001514003035560481030a00d011a15101d520b02d44100f6411401d86800060404092000d07201082000d0272289c007901480340041c0c0c252440920791103035801103900440040e0345400c0001d140400001030303c0070450b01c02e58020350411104a4061004212040c0b81064039249035583c0350b00320425160280391050815650000c440d101c0d046401000c0e0305084038840c181c0240c800c03802400082c1140314540201000c4070340380c07102040311105c0d505414103813441681c0f4109001c100a00f002010f01c0590340041c10f50f408881e4000a500090b0407151138041c1c0c07410004041c203c0e40d0300144403102c19800414105941c3c1c000c2000380340e44003000f1000070100140500601c0d0543c1c0b00c50525280210f402c1c584101d2030004103c44071000d030441040303d90003103262911890036203e150054038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 894530710 1250 894529460 894529463
    0xc1e06150510110c0d0f020603040b010816081203132f01050412140705120102120609060d03080709180509070515090904110405040312051005011d042403 68
    0x7900b4800c60040d241c00f0b14008007401045400800010602c5010081507a0b82030344121044038a070300aa600580324440076600485c86034582d110b42c0e40c10300d07411924050010001d0107142070030b9401000201d20100f40082c0001da404040e541e255240c034078040d041e41c0d170500b00900100ca201c0c50540c10903001c40c1030244201421019490030b55a0600440c1c2d940a40e02680300d0000300203400c2e500090740c40030134070740c084071503829540e40f182d41d600020440c00020402165503500042c40e9250300124180d1554821b6049420850b1805c142c00801d9404034220002001e121640380403d6490b8001e000c5100108010030040c994121001c03010006000141e07450240761088144c041107500d07044590f400503840c500360f0300e0700300101c413420000c0001009d441540c0014400800411a8955000740c0f80f0841c02500c8852002d1442e190803411500c00401d81c20144100010074080d0f82e901c010582002d10f041e4401e034460808002c0018000c081400000001180704460f040070240c40340200022203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 894531960 1250 894530710 894530719
    0x40c030c03030c060b0114032a03100f090917030a0f020315030606030d1d06160507050a090b030a02040c031503060b12010504050309010f090e0112060605040c0c1e061505 75
    0x103e201703900540d1048100b40c07001401072800e200161901d00d6007804a05441c602203800540240100c80b0080c1c0ca510030b42e51002c03281c0142000340310500024031110700a2000c804200644601e90702e0714044010305a004240500001010a0395021150031103c40504044021941c90414414001581c600340321164000d020710310002d00e85140109110b8081c40c030070303107480e0050041c2000000b0b01c0fa41c90f40d091740d0301403414000d14034840b0a1342d03203100c005881a0700030103500d030404e0100302c55008142d002d0700f181d60405d0300901240d1004601141c086a040e02c020070b40b0a030311041500038107860203000307030440c0c0484c5001092100d0340e081345444030420360b03c0451100e0220743c824280c4600703c07009030407a44100030745a4654421400510380413400e240c00e01d442ca40f209400c000700301080e4030107020030205c50601400e01025202d400e0061008940c03c000c201c080d0040a0706030594540c0c0901303a100b446450702840e00e1034481084c0901c2e40510b00304850411000300a81c0940107014480c081e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 894533210 1250 894531960 894531971
    0x5190311011d1c1110200a0c060e150a0c080c03070c1b230109080c1e0105040e04080c0607050702031009060b040603150f0b1e01030f0e0604050c10050f03040c030c03030c06 76
    0x941418204550300c020903640c400c060301a0279203490014020070a61803095100b41c10510900d40c090448990041442d1440890045016000103016103c003610b0000442c0d020000d0004064010002081d1154003400e4090505915081d01484102030342c07040003403805d1300029036004054108200301c4040c0c00d0b01c0c0d4101c05501c60864650342c40410600507002014541d5424552442e040c401c04800e5052400601c0c240d211040721700300003000c1e20200c900380d0000c034449101400501c101c2e0703404100d601d0b01714201159500060707034400c0140703080e10302684c0e030342c1300403041c040f654200012940c0090024081c1036074034a000e044000448034454451460400915002d070880c0c090ad56042f0401400d11850010340c00d82c12370080502c009613814165a070082c01a4100d80e030080304400c0040300090070041c505030400504082200404030f02c6900d50020304050703e80c200c4192202202d0300ca44454803070b41e882c64511612110f40d04080e00da80052a000010550301401070300180780305101c00d122 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 894534460 1250 894533210 894533261
    0x901020904110a0518120f0a11060f0a080718180b0f030616120f1a040507141b12031b030103050d0c05190311011d1c1110 54
    0x80e00503035219200003001040708140040040c1c0e41071000c90801802c500780c410803088550307d002e081c1c2d18600d1840d0041c0404a00784000303043c14151080d030a561031480c10b0100d00700f5234083d00c213800344407042c002c0d01030114180030720603900d0545083e1039504024400f6140e20710641e451420014400416050000c141c0050070408441080c5600c064000e1455854124448021840d0180100c0800c08441074010100b24a40074402520781910030004100c61031140c03c1580d083c6440c103680c0681d050105110b00c81d64000c04031110504030400302078580c00113944a40140702c4210001056105002000203800e21020081d4040d5403c055007200b00604a441c0c98941d01003440043c040e5040105403608003402180c0f50450302e44103605032403509440000190107941881c1d03060340011303e086180341a94809200b50600b242e02d4400c045425000034152958410402072213401c7c184440c1640191140200c0035181364028000551391a0745900c000d0381c2c014103c5001049859546080b81030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 894535710 1250 894534460 894534491
    0x50a090f0305340803130b01030f03030b010206090601061d04020301140f01020a030909020f0715050106112808040b0301120515010302130e1207061b0f020303040b04060605090901020904 82
    0x2e0a100f5508140c0d10444103448a0989800060040e581034840c0400b0100040b41490030b54003941c442c0c1c1600d9a902903d04005048809154149040d50322001c240714090700006029811204075290800d8207074009510008154048e18400e0340190010001145020a03060754100360070060b202642c00c0c02903000126603480c040000030f070104d0032041c018004000e81e0340003040300c80c02240009140814941ea4a800b00070030b458001e5102340d8450051041592140c842107280498800801580c8030500399001e5011030301a03020491040c0281e00010410080103a4006104001c011901d81d0307580c0800e5618400203510440d8240034006030f503c0011010791105040c0d80c4c0241c004420301e440c250040000305100e1328150a54414540c5042c040d4800da401440b28a01c83e80c0c022862911960001c00c0305001520381c00706024207681c41270381c4103a00100b51b0f41e0090308200c0d003500039255410071000929140e002a40c01204480801800d0007054004040300f50060380d08201d100080e64260 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 894536960 1250 894535710 894535777
    0x1e08011706100b0a0c0f060c020c0402031b070203190323030403080a0b0a09060909020109090e03090105030406060f0f061107050a090f020d0504030804141b04050a090f0305 76
    0x40c40c2c0501d03854040c020240d000d80030302043e07015030a0030400320b07013191a80d15031240d81d410102d540790340390500400050360600202a08004c1503800354107508104405010841001001c40c4079120041844010741da410004462440d100d035000c48880e289074140141814030021001403c1c0c400c02514038a4111100c040340c0c4110380550b1030707031030603140c00390b010010b803480e001c4241c1c0c411044040070410220390712030007005042d00540040c5820b02440003405552041e4420b441d10352610300c05c1c00025a000c403c94860800c24030f03080c1c1d0b80b0b0380c89180801c000c0c034040d00a00e05c20b8010000100d03001c8041600c5a00b56040d90711014485940e164000d50b859000b402403542003800b200b4108658030141d0450800707000c88910241c01c207886c01000c4030455004846c180e000903c3e10040c801030195080b10500f003910b2010240c0100210711b01412100001481824003503039690000030b001c100b880e801801402da010020603130400d1207050040c001e03000700001401e1080f030652920340701002c2d16540c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 894538210 1250 894536960 894536971
    0xc010801242c090c070519050c1011071202090105060a140c0c0414100b0a121406012015040213090510050709030309050424091e02091804031e08011706 67
    0xc0c211080000103204409a086500300e23881d1107940c00c003908036036444d09854000422650344104100c07020407881d240a02c66408844220100321001b00540c644800b901e040d5901038079020307661107000c074040300c407c6004c480d00300c280391010030480403011000c60600f2814000321000e00044041044e81901c101c0700392061424001400802c0001000a0700508845441030900041d00395142509109881d00c141da1140a600e00360200496036030000142440c4014144014144260b0281010741d1001031843c116003110050f0009821990307580c1000555039010030301400b00003007034a44030340d5844034020b11800090801001908079071103654a01d0450381c1507a035001d18245480c050000a121680b8441c1401d460220035540d203407a016a940b00070300c5003034000a207960305142c40b501c6100086004444550040200320701607500c2070704030158240f00c00d03c445010f840c1e44c901662417207000101c5c082558000040e075010744d40c02000e214101c92415084444242c044881961a070604480 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 894539460 1250 894538210 894538213
    0x307030309110a0509040b06030111040906050a09020c030f071b060203090909010213090f0b15070302070f140415030b1321020312070e030a0b090c010801242c090c0705 74
    0x1c1c00300d00c41147d2160400c1019000103172940184031401e4940d03000f500074404c46074944004001c0ed05060866100801c00303a2000c6040080400d035446d00c80c0f14014141101d0350700410b12078203202420070042280040c66502d032031030f1303560b40384003035144d8015031811442440e8082c00140000018002c440d03250025601c400361135070400510308010104001d180c0b91095489084864a4488a0948084040250070103440b50f0192030000c0c1340052581000d011084a64400c00030401211032562107031404403000b26544402048094443c002640090032198540382849a052070105e041c100243c0a840186400d0f9a0307580e000c441e01100700f035040010b900030410100490704040d080780c0c2200301440c0c107606c20300c100340010345080c0313035004d0946012107031038284034010700100a078120600080c00c2c0800c0ea98940f50701d20740003811040c400c6003030410403022844824415101061440d1580a60805075603c509a04402ca00348011350707401500c0110110360b00e40c0000056800280d480070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 894540710 1250 894539460 894539479
    0x105010603050f1b0d1a1003020405091302090103030c021f09080d0e090a020c070b2115030c04020d2702010201051012020f150c0606030d0c0507030b180307030309110a05 75
    0x4001001c101c2e8540944015074001d8528a9072000f0489514001f255000740c0c441c0d0034102040441440541184100403410001d00e0060701e50001039411207801d42001b22000c801400841d8114880c10740307007443c01c549001c0c4c4425881d006201c42042d140f040c0100c038014000030700282c400b101980c11459010a81c08001809424a60010b045080c4100181d078407032039580d96031030a0303034000c400c103441c08108040ba05c40c2c07a0080d245c402684100c001070041c0c10340307a8200129850b0600200107600a58002808603040c40640d0001000c0f407501c07044200200401c030f03020540c015041041203006508000100d03207500e5080c5214000d075010000400c881b44003c0d820800341d004046101c0c0e401c0145500e0706000741c07460302c1c0508030201c2441d015100030703c2d05e10201801c11800041c040140000c0c041da00012400010300390050301c0e800401c0e0a1a520703600c0391620b1301c0400c440d41c150184030001300d13a810140e242d08a10b00c194403421481003400c0403402002508402405565001412003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 894541960 1250 894540710 894540727
    0xb040b030a020d1d010f11164106010b030907120c03171e18061b120a030609051303030902130218011e1b11030105010603050f1b 57
    0x742e000340350ba14903441d400a88070811604420011020442c0d10580d030355a00304141c60311409000d4000100c0e20f000308185016009081a011100c169202510b40100400c104c074564102d994035080f003820f4020620801a00448203015041030a08200824051080006100d003242415031b4003c001c444054003000e030418035140d40000c1c0e40f00050382c0006880700c000022a9080b040b05046500d8001c801d90350b0746804294400c0200030503038140c0641e504100c60701024410fa4501801520220760160f620100b0814501c405d01c0c0855240000c0d019814421682007072480013060054601c0c0c40610810360744121074022284200e03012103110702c180ca40e003000a4030940c4450b90107840200048401322244c03070950102c3e00400040e8140c103403001d810005c5907030002500740781075941010703440380743c244c9075130042007014103228109400b01c9001e004000c200743d1480600d6034200140007004550fa543d40001c01500040d40e807940750720300b03c501280309013189401035401c48015410551074050300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 894543210 1250 894541960 894541981
    0x15200403061107110d21050406020c180703110c030c0105062d0d030512090106080c040203100e060a0e0403031d03280201060308041202031e0604080a120c02060906010b040b03 77
    0x4100d030458074040640b02506003c06c0d4510506000103150740c840c0e44440c103040c40a45004415852103124003070310309041844550042c443d5600c562103140100e078000c8400380c079015600641e911111075000210744810380540c15400075100b01012604c890313003c14019001e2140302040c030034680000c0000c610103089400c0c00c02c00003410b42e10038649180f0f0402c2c0e08800100764203040e5421883c070b9454010422002c01e00700528441c41004984c00c42c61030401144001c0c140c1d07451701c18070354024050800540c07280d4481e00b142c00245810071100b0a18038040c41d004008014400c80c4840c102c0d45515644240b12001080e160501c4861403450482c802103043c82d810380601c20410402c56482d1140400000e01585c0070300003c11100c041e05104890b40e10400d410139051032942002003000c1144000c0c1e009000030340c103400582010138641d0300d01d00481d007103604101c408110030a0340c0c200081c2240745903001450520440703059080d1209a40c82d03581d90031892080e48103803a00c1007000c0c404944d081c141c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 894544460 1250 894543210 894543229
    0x3050a0c1d0c091f0f11010b010804060f0b0d0809042901080a0e07060c0c0806100b030c091c0201200a170c0d1805010212071520040306110711 63
    0x8004120542c16441c135403810b0721403d030750144100010714a1030380c42a03141c1c1101080c8684d500f110001c1c04004070b01c1000900307042d4003c102502203034035104902a0001154031280017010060700c0304c1000001403c0003602c81c1c0c0f00340c10050003213160240742c1c1c2d126424a0324801d00380e00000e1108040c8902040115203032000540f0344100142e88000761003c0800400200004103c0341d2661110280c0c6410100f002d800c0070390200030250003031820003101d00b941c000e8620603280d40315089a00c0391206100e2248038010034240b1a005008004071002c081030004100740c00f02c2c0300360b917003c1c1080d40080c1c1e0080c13680e40c0c2140e04c4e070284c1c2c80043c000f0001480c21081d000c10610b607000160400480c40ca2301480d000c103112092011466030304c1c082c003820940c04c000c4030150400703000030030b080903800315824068800c003035000d845031540d2040e0f60070707207a611b400c04403510146c009151022180da513450000343d80203100440d0150b04c0c0000008003038a015007507900c444d07000307100c03500b5403240c883c1817050007070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 894545710 1250 894544460 894544477
    0x6080115030507080f061807110c09060f091e04030504150306030305090609030a1203021e1c05060103092f15030a0905100203040b100801020711010e0301140103050a0c1d0c 76
    0x7c1000703943d900c8090084262140305142c0d500855038030344401e01c6003081d151810060083c0b030350204200c8039403511520044912426540c0481c15500c540b042c03540d04088003e0042000da440c400d000c1890742c01800781064401080f807000c0b103450a514184c0860740e05101c01404a00c003885000f019280030700180100c418082d05440055a00395501e01d25940009034550100792301080140c190003000948101d01000152103c1c0741600c4912684030080103000c40c1080503460384001407072a4803070b07080024240e070300050318820100f03440d40d0b60a0079914141540c00071078611042110300d00c2e002036014007411071080d60500c1c5444900400380984609581911b007880b86540511011a80d0301c015486140200320581e05400d0540e06115a000c0c0f5030300c040600d80c01805020b0119581012503020042d09081841c1407003105000b00e03014050700d90650010310000340000081c0b100204890b29014407940040c11015241c107001d4008070440004181c50740fa1880000d050400001d00412022 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 894546960 1250 894545710 894545719
    0xf1d0c130501180f0f261c0e060c0d03050a0908090609040605120105090106171e0f01140a0b01020a08030714070b040f0302010b0f10080a0204030501050106080115030507080f06 78
    0x156203483c0742c4ca0241205611401c25400140e030204011002e0301d6000041e1410421052100703410380310216520b0294641040e80700347e40d1006000020b0050014500300034001d090740703031940d001001d03160303e03400050380c08008607041400080d1104200d115a10189500071307481c03410f0120301001c4c002c29410821409030416a40c0e10040781d55a40d5000c03001d03804100340c001042c84c1c5004003002d4250b602d940c0c001d4080c0e507101700480c03500031408100c61a03007030380740e0b2424030400241805080c41d200b400040b0390059482d0080d142980c07043d401e0182e220303d0355400c0c1800700254403001241c0d078404400025100420500c08646164443d101881d2449549462141444190b8a4000f008042a10103ca0014900f0009400c158080c0202c40c0700c1d0704c0c1100c248005107007038404103115a81c440e11000812504100249000c00d86506580185400030300800c141c0d80c5175203001e0240700083c05070f00c1450840342c03400c00301c0501c28000c142c840d182da9500c80d01e0039140e50f0320101920746c0103010250710 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 894548210 1250 894546960 894547007
    0x405151306140703121d07031101020307020105030a0c121e0b030a0224090301021303020306151c080d020a030605031c12090201020f0d021e01020f070b0c040f1d0c130501 75
    0x203982c01074501090b1b100d044c400b0701141850f5240a40000014441d42410354005110140250303800c1019a42c1c400c2c807031140031031034107010441101c0d81c420300840140a54901030b00598a10080c40005003d00d00303105040100210400c1095a1007030381e400025800000c445240c088400041c800030038010303a08000900348014500000d00303a07005455081c50105c45180c04005500c0c04005060b00300445402c0d0303110404021012860040d0f60201da404195000304021040000e60b00c1180d46142e4000000c5442e40c1c0e007000001c020303081a00c6614424031401c030300082042842d040c010b210014548507400361400207040b51014002101e4140d0541c042d070030203542c141d4003d00c80c001d00c1c01c01030350150501d42d4413441d0300030203041076101101850b0710503c6001c410b80d80040860300c025030081241555603440c0e01c0c84504500c12078100f41c01e0000c40c032600003190038801c0d40c80107611500d08040c80e8695107010b40c0e00c900f80143d88003414900003000b01006594051036030f0400a0641200c0241c6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 894549460 1250 894548210 894548231
    0x1050c1e19030203030f01090903090b030601090f140a24030903050c0a230c0d08032503020d360311010c090f1217030a02040515130614070312 63
    0x19426401d6003540960400001c002401205690540c0036041c54101000f2044594034010302c0c00b882402640c103451030000110f800e5a00642401008120301450300342500d403582101c06000142e41521400340340c41d90f01c0400c030019003c0c2c03851001d4010981e0109403200880045010300300707a200681c00c1c42800c0041c142481e909121007a90140945031000d520b0b91903888640c107a0040028a103010b8000c040750719001c2d502e85c1107080000c0d410008103904ea84901e10b4024052820720400105149a139080514154140d0041c050b1540000010411108060720b407441d2200042d01203a010281d00a400300d06034550302c070100c00e140c0a4540802e42c4c6030030020721070854161003001c4000c20742d0b20100300075061102c6070020140604c011244809441582d40c001c07901082d0605a040c00c2003c00001d070641c1030f5606441c02014000d000f21401e2400c569802c416512442c00d82000c0d41121704041840c038062000d000c441001d01e00ccc82813400d0030b1514115400640303501000c9105480c1c804226 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 894550710 1250 894549460 894549493
    0x1902100c0819170a090308060909032205101e0c0c03031b021017090a2103020d140f0603060408030c0f0c0105100815010e060f0f280501050c1e 63
    0x103104440500000440320f1070b609007c3c241880042c500d9114100590070401c40120100030f80e809960450860801000c1c0c0002140241c603058103c5038100f140410903014030303a81b1100a002c8076281c951606201c07440b04200f11000a01940d0181011008ca482000000d100742140d810b200ca54110340440001c3e10b9000802107982c030100d0100040c07000310001c0801400512140d0880070b0341000340f10003489581d0f4a0b45e02d142c4455458203002c1d11107140100140649c040f28080f1114200c2004414202e0304100255681a6040782c500071520000800d6402c00151040c0200c1e00283c61500310381d01c00b00140034640c400740c1044811401441002280c6009001d214051f0305425010540141446aa41d10700080c41440710300700780b00140100800342c24001d03d41d80001c400d032040c4c9030184203440840c00d03000b15580b00541040e0b113144c500c4003540c01120211120b8040d85290801340e966100112460b0150000f6140d494100c403004045900c1d1201381900740303440010903109031403201100300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 894551960 1250 894550710 894550757
    0x11704032c01031109100309050312091b1e0415260f03040e060f060f0a020601180605030c091806010602010e0607090e0a0c111902100c0819 62
    0x219042401a0301c500748540c2c16018083c1c060400c44419400e0140007130005552481e2000b81c1d006041e0349000c060240107080c012500007101c4811900782d14144071090b241c0c6c84409900051203410080e181d0011403400d401b21701d04104041d945210001c25040c2000000d00d024500b5086003d001c0e44005000d00300c036110260910364804103459503404440084c0e0406134050100442500104024031140c0c000e0191507400a0060300d5220b030000061010920314403800c055001e0000000c2842e0851942c00038507181a203244a00640011101030040f0054408038003905504da0400c030000c0c00b8a080c03a0280c150b0100c545280d80004408000c070a50515000381c000f0030060351583c40c1046080c00401059400040516004120b41d1034010083c00c400e0b0042d1011a900e925038464615980c0b24900e900e005180320750942d03a441007102c01c0b84070a4249804101c0c000c00310b20440710115400b41645200c21900030079030380d180c803a683c5e2074183c09000c4455080284400170700c0c040000350030034010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 894553210 1250 894551960 894552017
    0x31c120f15080f06070504180c120921020d020d1404053a0b01060309020f03010617120f03061011030d05271f11070c150201020901170403 61
    0x14048100f00040b01c20b003042da0040c095414404100400c101160703110128948001c958030f8001000c826142c4112980007107840071920050a00ba0404103004036010034681d40501c01c244003d9242114209903150f100c0810303e2800b6801050080b10198011400c0d240e0501a9404083c5000d48450004e6200c0c9a06502410001c000b5402c808012605271245101480750030751581c0c8007420fa960320806002d05010765030801d80c94144071811511540444468018014001d201840d110300301d9604041000200c0c800c0e900c1440c1c8030b2815107500c1000c84564a60302c01080c0e245d40c0d594402e000155069031a03c01c00c0158603601d011988030140041c0c1013100e5210300100d02410901c200c07a10701510134a03420145210600780001d00d07180003c400c009010141042d042c2c3d0221141808010100e82e1544807028000140800800ca10510541e081d0ba4020713640041c81e14442c0710482c00c0b4000ca41000d030118550140e0035481d03815410707075140e22920174540890134a07429510740500398001102c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 894554460 1250 894553210 894553213
    0xf0a03060513181707050607110d03060305120912030a020a03110f0c010e030f0703050a0203151006032d0e010605041103010302040b0307120c05031c120f1508 70
    0x3081c090352400d81c07080c641c041c4400da418410700e085000498850640041d0040c07050314140c04d03d0005440003026128541d800000380ca49074a0503e00180c4030128045c001c040c00d0040c5503011010364001c0c4204016681c000c001001000c03c00581d8084170740c44440c9403980041c0600c00302d180c8220800c020b152040c07440d4080c004541c0075180141c8900c080d54020811a003045015a1000d00c000407142d06540c02480c100150700f45420101341001c18a8800507024000c00e2004002c2c80f80000e42c088000d4406c2d01140c0c1507068240c00d0802c041415074040040003031003a02080314500c2030300184650200207071042c2c52030082c504102c00e803441400071a0455501c51100340c001a00c28803c5200600c0c054800380256041c03034550b4240307444140802849665a40e01d108100d0710100081005015142c114104080d0b507810508284520352003054441d00c1081c0b00060001c0d00c1ca040303d214510300d9110070b041451000c0c280005803075400c6030909202d07501d900340048019440c1d0204024140c000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 894555710 1250 894554460 894554471
    0x27091e1203022b091506050a0e0c090d0c090908040e06040b100c110901120b0f060604060c0609020a17070b040b03070309020301110d020a1205010b0702060a02010605060316030e010e0615060f0a03 86
    0x1f0280103403003006902024003c81c00808001d0520300007000c07190011001c50306030072620300710325002e142521950055551980b07458401010072801400400036a510000544000d580b100300b004195040c0002d030507042014140c82000050044a0700340085120b43c40c0541045c51182c04168004803d034005002c0604420b002820311500a8404d60855269004680d8514129020074024803861050030100030000c4681410b1180561200386555402098400340c41d64943c0107d07651401d088503542640500c000018508011504540403240500c1c4403900f96540c400d4140c0081031b624030140d806540344c0c641c1c05080880d0307070018542e6000103180140c9613881000024005142640a41b100301d18000040c0320380704c411819205115030484095a0300c80001204a002d00350340d500454000c0c2c40442070020410b20828060080c920325541000ad04400804031400d80340a00d0306130701d2503080000401d0014140c103400c5084c10f1000391669103000803102c02042c081e404038071802d00013544c54 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 894556960 1250 894555710 894555719
    0x105040f03080a09021e06130b030105120c03060a0b030319050c07060206040203060f180a06061d040f06020315130f050106020727091e1203022b091506 67
    0x4542e0382101e003c070001c21030300c1c8859011404460a110320408112800c50010510f50748002c02c84001038400280c0340002540c40800c44003a420a0103110f10440c00d5582c0900420400540010000030080c0201043e44454004200510b951103000350140010800ea02c2c40102c040d825070655a030f01e40e20b180d51403070030600302410046d05d6000300085420103424400541e60005030b03d6040300d10f188000610762220610f03140039164214100042d0b004226002060009651109044131440000040d40c4103441c1440316003003000315001030103411000000c1d40030686560156030b200100d03002000400c2e40c03040024825151100302030340603039214010b410502089001e124014000c034001045140d00304010300e518444002120381c40c4041c0100c0d4006001b09030340080700034a030081a042000e04151801020210481906440040f004140280554800d10031603404070901c10794410703500804200241c60b103038140c81c514101e6031204011004a403500f50010601c0400040001704146403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 894558210 1250 894556960 894556967
    0x402040e07091a040e040b060f0315010914240a09020d0501090c0212071101022803080f1317130b0a0215070e0409051002131a0a0e01140c0105040f03 66
    0x10043d94401c06200800034400f540f07030a01e0300103502881c6028030780d641a020581504102041c10740c50300c20b4500342c1030040b0003600300030305035040c2d40014001c0301842c440c2c50240c1c480a03914503188620080440061038440020001c4001006000c00002e1f541d8003240016a048800880c041e03035078401c0108030303011040c481e0424150407030001d440407941410031060703540140d19001d002003040c4414008943e10130300000400031450030102a00d4200c1c0d2002d022005c0c190982100407522240103c1d111002c6d541d951441140110461094241c0507500c6200d503010720030100711048010301c10400c2400b03102481d0005400702d00907880c3c480c07041010091802103180ea03c5029404080d041c0300c0680d522500c603043e04c2005490100700800c041ca00145081d41001070009210310101d040c0c0d5140c0d210710300d004200c1c1d0309074912561140c410103455080e44908610306000c183e1040082410b94094240c501d00100030301c82850405281c044541e00b516000c5504581c104000c0380e8039400c0641 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 894559460 1250 894558210 894558239
    0xc0f15020a02161e050d110315190e030418060f0611070f0e1b0c06150f18180715020106060801091a011d1801030b0f150402090402040e0709 62
    0x22603940343c4071420b4200484401428020304c2d00406c24452141d0911010a285c80d9041d0006022100420328004400b0b00c0d294003a83c00d402400700e05450a1041c1210780100e032401d4520502035403030a4504848112006d9030b48104014942d20340c000068004442180b0b000107003d5501c59401c0801b049201074100310498101c1818070b054801c00340032094200c100c481d030000c0e440a51841304404503250f4003050281001d0001c03548684420000580c2d0051280003100900356500098000d000040101e048400480720782c0c100001310000301500e0044003028100003501059808442d125041b002c10007032040402c03c003507911800204540381d4080c0e006070040036182c40820441004019141c0320401d034405042c1007200307584c0b0f5602001d404400c54071036224000d046d180180410144891120024030082c4c03910b80030342c0001f400d1880007081507071140f2282c129144444840c0c4003004003e40106031a00c1d0807541c240130200d070400e51040d00c1400350895448130b07200240341001055001a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 894560710 1250 894559460 894559469
    0x4090c030b09120304030c020f1003060512012007210f0f0306060507120315090b12150a11040504050103080c06060103060b070221011104150507030c0f15020a0216 72
    0x14041c0541da40c500035088244c94100303a041c501407148400f1800040d8080000100003a0311504103c0c01901481c0c259201c242160016502d920913500108400307803c0310580003903100c80f9445003480032001e0680e403008203031f001e101e003840d41065107118138102c1000103a0040500850203030348800001540000910040c20700d58642840083c1c1401d50040083c050500010110501401100042030003034000e4600e07032880305c00c00741c031440e0744030a502d0103800b040075800d0007980b0300244901915400325202031b000030303100312081d801c0d190489101c0042400c4030004007040c20600020541c1e50325409400e009600406460351506078401200381040005403881e0705051130180f04000500c0d01e02c0075159000c2e0100c90940c0d04180b1034909100742c8045680c4050035502c1c0101c246030389400d044c040c02c00e48051310100159955003c60580f500c0c4110140a0003160003105c20400040300c5c1d40392010014807481a0b010048c2c0d296040b40c1c1607800590740c0b0405a045610300b10002038901a04000a1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 894561960 1250 894560710 894560713
    0x3051e0708061501050703030e01050c1e1e0a020a05060a0c08060117010b0d09060903080f010e0405100e1c020606011116090513082b090201080c031504090c030b09 72
    0x604102c0c05a030120f107560200343d03061060108100e400d01d400395128800031484100240010f00d0300c07030100f1005034481c60180e0801405114458202031100d029141410548138903494050303050010702106410080c00e034400c610070f02c24810002013040c0810344c006c40a0340400303d1645218480581000700c01010700b81002581c0c100e1100c0034441c440064115004d102000396201c0c21101610041c080e1400050101c60801c0540c0003003645c00745000d8403401d030601290a04e66202c02d84010740d0181900d015000e940300ca903401440b11291f600c601e400300c1d400002c4859503801140e0b5905100201ca82c990096000f20381088403a58118082c1604105428082c2441c4180c00d020007840711298041e20028030396500000f182c2204030080e6110311600440c026459003c020704558a02d407041d111001900d1030351341d080071001d01034000c00f85480d5050f140c0300c22a6031000c00081d102c1e04020911103882020549207000360b00d07641b04100c1810f0041544508403030440c00c01c00c0040d2805403040d1180d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 894563210 1250 894561960 894561973
    0xc0313051203181219050f070605031003081c0e0a02011e02062a130501021002040e0630031801020703020d15140a0f0f060b090405060a03051e0708 65
    0x95110406107a4169600302c0d02c0020130100301245518044007a4040c3c026011100c20200600100083c0008824014012904901e4650404481600003a030b101c0301d010305100c030300b40009407501c0c02400c210400088400e50340c401030b84500060320440e04014242e50400c940b90b1065581c00513a4142480046281000360300403540000c0d51802c0080504904525000580441e081801d443e1419074010b04c10b641c1d1154a0001d5198007409680b2680740075118284149000c1c0381c050003594210382c0340e020000c0c1c3c40d40d105014402c0d0b0b000030511074001d011414100000f803110503201508801143c500035a1503161712141e68040f446e2000781075041d94800c00301000140c1d2081e840e41d0722568031020b17050400c030300e0003100c4014024407001046480c5d03c060030042d26140e03d5102d4500b1581d100001d00c840310511012a040310090b00406600b2681000b0510880c105130b0401031308070101030010320300c5e42c0d6683c49450030410f900300c00400000d90441080440b0394100050000b0b0203c07100500311 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 894564460 1250 894563210 894563227
    0x1314030105010b13120204020d023001060f0f0e0a140f0d05031b1501060f08132a090c18090608031206030115031113020415140c0313051203 62
    0x40464032403007141300e4805d0850400c002c64546405071062071030803000c15500c41c81d445882c2c49080c04214581c00300e018580100104051954401504807801030310f9801d1200000703482141c00466005182c0300b44000d08428019645611070700100515010344c100c0e0345047e108080081e92008550242d12034841c0b44490008504088100e03131501e03605805001401004000301401c0c406c8892501128444541c0002041c0381c100d001082d2000540d611000d25030350740c0c208010143c49040000c1d002d0810702d020340100700101d440401c031004050280d140300c103648020340016294100c3d411400214502c02e0351851005404580c005441d241c2d0081c803c040c00d151000b81d40c0e006900d0419000711015000c202140c400703600c110034020042c1c2c0e105c42803035100d04040001119010f902401001c010038001003800d0f0a20035101a610352551000750740c8a6440110340901c0c11606044040204110402c142130041004041d60f5140018081034180b0304400c2041401c0c6001c1d08000c1d58100b00100d01e07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 894565710 1250 894564460 894564487
    0xa0f150803090409150203090706080c12070f0203040b030c0408010506010908100c11030711030d0309020109150216090b0a05010302070201020a0b09160905040204060f03020901090903051314030105010b 89
    0x48807042c1c01d4800180618050400c240c940d8a000380b0404924400020700aa0030390101c1c510040d6403160702c0d40c1409403180c00c28821507109000285000c01142c8000c030790024030a00030301c070803c42c80744110ba0626869244005051b40b00341d814482005001904002034407080c000e26030b00480c00d0911208482c074000ca029128082d491116401d60b5561585a040c28099030713030340041414110403261900507926208840c80000b001d81446031080c4690303882114402d02514400e41d506a64001100b8134144c1d1511002c1403e03c901015401a20600c0381001d03003003a1300500031f089660300820303141d41c1c54082c4082071255030011410180108010750250340c00190031041c2039403082c0082001d560b801015070500c000c003651480101e50720000001c80c1495604054021030085400f004ac4c01d0b9140c400d0340c00000c152000940110511004100c0c02da09079022240050080c1403e500c5d2a451405a40568016030410281c0c4810701c41c03600d01c42d00782403017164050011440154600400300c031004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 894566960 1250 894565710 894565717
    0x6140304080901051b0610090612020f0d0b04050a14060f010e130b01080a020a05060a0905010503090c0414180c030318060f030f0f0c190509180a0f150803 68
    0x26140c404002032041603030f441003017210580da2400710040c501d0b42000b0440d41c1c59540959982d00c0c2d03179006401c0031900c40c0c1e091241e5400c40d0011180070440c0c005a0342480350480080c0b0583d54041001d032204404204074142c880d2280d4404c0300500301050b00b500d0701e140034002031080120315501038004c0060941d450003001e0305480c0070103194440c66a0380d541c07524449201070030081010381c006000007040103000030b80c21040381c0700b102d00c0302d01c00d0344440070b1000a01070440004000ba000220400003540200c0040da04001804150303141c2c0d6040340e0120b81681d41040e500107051200008000b540d075401c00d41800b034030b0b800101902c0420580000603990340a8464150380005c0203400b8650907948140455404292050795152645069100900300e40e100302c3d101d5814002d6000060b40518540003180c032402d501c41544006030712200030440b9950409004036030805803c40000d0b51070384c0b1300250588210a49000401d90780c00d00c02080e0141d5000407528051110014410f105030710010041e03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 894568210 1250 894566960 894566963
    0x9020309070e041a06060720030111091503041e12030b010503070c02090c1c02040824040615032418031205270115050a1206091103030d020304050706140304 69
    0x10b2285450355400100d251080c420300921a040d030841101c1150240140c0d488c4c0914220000c000002c000c1d184c1d0111442404116940310f00b00805520181c50701340051600700d805012407400c1400710100703d1101490201c03064030840e04030070a46210b15854000c0781495602882c00500b5400c0001c2d015291b5860210003c3c4148803808c00102d8140024058071024815031100b200918a084408002980540910030143c010000071a0100d075040890314408402d100b0030031845d13030b610703100e690003400f807d050001c000e014175800001003062a0794100c501e540d164552007280c059454038400712000305d140c2c1d51144886442001c007017900f02d180c80049c156000c0340847c2c1c9940300542c04212407411452901d0703180690080c54084481540880d13082020380f80d5003501d090700d81c010000610054440c4614244041340032000060359034020780b00039441803200d4071003a4100030000703040d81c2100c0040c081a55003c0f0401c42800300401c0600010070349070a09214850390110603480e1392100400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 894569460 1250 894568210 894568253
    0xa0e060612010e010212040c1d13080f0f030f0f01120303020903010b040507050c06010f0b0d0216151e0b030c1905130e0d021f090602040f09020309070e04 68
    0x4035070038260081d00100c0c40c1c1a000b0000b1996003805010241105c08142d030140d0780b0240b01000410784812030018500300140d007005010b1130350349180900c05030b080c0f0140b003224030307143c01e0102031018801c2d540600407104080800507128504100990070842c0c0c000c20300100c0c080144010041005c0805040810903054500540d503241d00a0201c0d0241c41010f103001e0708a071918081008165004002c0c0c404c59a44a05444150740e030b40c0c003081a5a0124000c0d450fa8040400138100a10031650080403500740c050400304215956494411b160340c001030600d245541c8078490184c889a003a9619503001171080020880741c0c070136101180d40e41026415080c01050000480408007506043c5100107020080000400c011198500b030007500d01010b034503070b01e41b00340c0300d100d000d860000c80d030701c1c940039191002a881c0000402e00f0802509030014107a0f915542080003080b0782c03525600b0b038406003d44800150f40e030305100d140140f0f4074039254014100c81080c80240800281c9402d40641c12030300a10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 894570710 1250 894569460 894569479
    0x111903090b040c051c0309171011031006082e0e16030f0b010c060203070302120a1d030a0905211504030e150d050703060308130e0a0e0606 61
    0x10029001400d20410141242403400704100400108005003000d460094403201c1c082aa0348664415940707403480b00401042500c0020300c1703500501034403100031074240303412290754242d506040000c0b03074802c100030082c140000040000210700500307204010202403400103080d20344540d07244201d51032a560808101e0420381003091008071070038480007500c204861541d1500b4404218020900509940d10101e410140120803014152151002065040c0c4a12141e02100d41d1904002e6000501ca501819400c0c42406100c41100903128071030414041d00080100c1ca4180141141c40680c00409050340308000c1c0d400404d0f400211030003192030650f00100700714403a05c503082940341c41c0e036455892440f0740e0f000e02c200b100985150358041c40c013075141d2a20301c2d01960b0500c1351200c2c0142200d000700f05c00300100038220405600c03155100301c0038600003802d180c072075441c001541e02c600030804290743c0000c4248020309032000b546401c0403210808100800121030074507190400146224811107020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 894571960 1250 894570710 894570757
    0x70201090503100b011d011b0318060903150209060d020903030906070807060e0615011b0507061d01020705181509010f030605060d020307030b1806070e01021011 71
    0x2421000054070000702515015400c08554100604c20f0141d440c1c00507070480c01c4040304041c5020030360741c8004181e6813408015045903449001d101759540840401440840c1450782d200b02102903005040c0e41e9483c5100c50b40b4504001003080031609181019074410804009a95079450480e503030f07111210800342c0c0311660900064210f01400b0fa00e142c100e480011103504000c08100200710131842540100014214403100a54540c3d00701d440c0132a82d01c0b02d2800c020590b02804070303041c07424902d07103c40b105084240c0e07442e41004001d03440007010811300c0c10194408040b4601340110306000388003e02c0090318000004082901c4619590301100445000c1000c1603d07280813801f030100e004c0c00c414601d50b503503800c0c0321002d1a1480705550f03140ca0280426214600f4138650130300700d5002001003036000d0440d00c415000340d10103071110b108084011854580c00e0404d0010340d00c1181940c54801e4180c1c2c514001a0901c400c00002c01000c5180031200d04804060360142c1d500c501180f4040c40060101c1c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 894573210 1250 894571960 894571967
    0x1b0907020111131707230a03060c0804050609061608040519080d0e0a1104020a090e090a0c1706070806060903100504050d260406140a0603020307060903080906070201 73
    0xd81d100402070100003c0c2c0c8501c04852200e00f90100c40110b003020400f0b600201403140c4505103401048a81c044480c1070681c0a1481c40c42c10030310000042c218007541e43e480d0790b80c8040f02c50214102000c070b0303050070420040c0041130155940c4641c951014050a01d0120021701900000b21094030031b001100000c40c050160070000360b0f05420000c40d02c20b402c11083d0904c0001c03074105080301c009050a10324544014603020030110940c5070700501058405488008000203500103506800c10402c84400014010f0f0601c1c0d1124061200d44014056002c0c10342008079078000313190054500120220080114000c000454540c0000b451420346656214580080d005100309444c195051203529694070480f09203a02a5009502c0703201150701883c4045015181414170040c030801c034070344049400b00583e84240e042c0d0750151040100042d401d096100f082000c1d00b064961300130f20b0791781c0c1c54140210b040400c4200003030401810482c12144c610740d83c0d40814812100d081d40151400724201c42103900 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 894574460 1250 894573210 894573221
    0x50603250225121403070b07080108120405013606030e01051b0a0c02030723040c030e072102030114070924031805010e030d0b031b09070201 62
    0x1030040460303124980e020000703541d4050b0719200b00102a003400350501002003503070090b0484801d910030601d00e07241c2d6250002040c0f43c103404100140001c018001c00035900310003492050702c060712a03070410b504212801d0700e401001e094048801c94200028001c90381c001c0c29000080383c040180524180304111100c05c0100c1418104002107070051f0040303006a05070704510b01800c1d80000030045561280c0c600c504c80d0201d201000101d0404200003044548941ca1115140740003900700d403002a5601c3c1442521180e00c2c02c01e80c040c00741c100c4005550700d040d01403813550420034070307003482401d200000043d103a1a161140340b98001c2c07060320340301030030558044241c4140d40040003003004801c10003114913032280880b46080050880c80780030989075901a540b01081c4c00e0040340720108802032209400810702c00c0910f1095140040510000a400f40503028800c6041d10180d43c4842038210043c044d07500b034151291180c0c10004501c0d100090354610b104200c60300715a03291494076035407010ba00400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 894575710 1250 894574460 894574501
    0x9060f0a03050601121a0112030c0c0f0b0c0d0905010e210a050a03110616050a110a030522030503090405190c08040326070305270c01091707050603 65
    0x3d0200001d40c0110101c100e003102c078040d041c604c01c030701c1c6a8291091890030900510740d103000e01001c0080800d22038200c4c296011300c210094000244c603805845800480d583c85404070200020341e40d20382020502c403110f8404000d007041200c060500c000a408460700d0441903001340109800c407288111079a00c540c01c121480002d4856624240c10940d8684207150340c02e40114448903a240c603080e10008403e8441c641c00f504003500c0c000c5e401c10440b11035000c900c4803003c00041c1d48000d040c03201c09001d0603040a100c0d0311019035402c10000300100d0449480b6031020408442e0200704082107000c405c03642c1c005001c40e800030307071561260100d003190f40e2100001d1110380d10309010343d41400d0308000400e0043d8040e48a42070406440112505c2501003a14403070410505840400c100d54001d41200d904842c00b20008207803820500d020020800ca45614441d003076004040003903082d6004803100c0098034846044030005450302c00b010340d80340580d124440c0a4000000081d0008200d00c46098850 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 894576960 1250 894575710 894575713
    0xc0509030c0118050d0804050307060801031a2815090b03070306022a070f090203190b062b050a02070210050334031a24070b0f150301050609060f0a0305 67
    0x100006d00b020042d07038015014440c00ba208000b030110304980100c2189040740d40c0022546e4850a40c20b80010748000c0141c01d910404030f04010110304444c09075541c600c60003c00e000010b8440c5c0d07620005041240592019091707520745518410300f03460200b400e1081d20b820200150f5145210301281e40c240028402000c03400d03403001ca804950000c08100c0c00102c0f10142a00c03c6159201c40e682c108070300c000ea4000041f80240741c1ca00481e0b0070381c1c0e044009100002000c030390500d040c0c10824040061101074032420b44c050b11842e564551107901c100c90b04010b9a81003103017841c0113a800f14001200c2100c480b0203202c07002c000203c0782045c494401d20074400748200701455501d660305161030b08011180c03444c086403c00f80e000e81c800704401441c10f58a440141000c00c00c040e00c000240d80b49a0501002c003c5131010401c00c0c0c00f0904000201c2d000c0d016105550703219282a148a10b140241c0c81810380c840d074146818002c035503684130007032a00050101c5616001500910003c3d074181c00c180c3c402002c9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 894578210 1250 894576960 894576979
    0x20c10030608071a090a1d07031107060b2407050601121a2508091e0c130b03030c0c030d03060f0e090f0a2d0816080c1507030c0509030c011805 63
    0x10706011f1a07000d042c940362019200980c1ca030120141c0c00d03905240e84070350034407074140b04100104100d1340000d951654050400c814101c1d1019410440003146407112580d0000021508108081040054010145200d002042602960320320781d240d07084500f1084040e190070041001100030014000d40030810040258905569260203409050b040700ea25805003d40055625112000c90300102e142d404030000e000c01100b50810401d024000314544184203941e5a800800c03614100002c214050b0b841000303080040c1d848042501d0440c1100d0100304144c102034082151141085840e01502d201d0781d0368034569660146503038944a1151220300c0e25115241404043c4100042a400d203404214800001c50001c49569104400708032001000141d041207901688031003101858a000d10800f034041c581580100014540041e031807498144003250302c10700c81c2d41e07a050310031040b00001609001c1c2c00d282c1080006030711040c4502446041c055166031440071140400400c2002d440002d01c1c1e900c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 894579460 1250 894578210 894578219
    0x2031b0403120e0d02030c01110a020415300f080f070b01050102061e01050f061309050901050f220c0b040b030118050405030a05070c030204060303020c10030608071a090a 75
    0x5509034501c0082d000c918900081c0015003010003a40100580140003850400b001d00c0044608440e2880603ca10340140503100006940e507000d0144141000f4141c0000c403400d01c1190421b444100203500d01c004403c1d40d03683d0b4010040394001140320381014019000c005a81000f501d94403d44450040100000072204108040b076401107060301c1c000e030300b04c4000d50703200f0f600802542440c0080540c4600342100400070b81c41e10307000c0706107083d40140c68541410740c2a14590100071441d000f15106c40c1e00d0b10308016100c0310074801e00d64480c0e10f0701b03d08081801c1503100c07102500a103401d035040001500e61441d05000e50302400740300401e484e00c8841d0ba2030341d851442d21140e0b003003030003003030802c0200d002080d44440c480d00a00b4001c98224000d503142a00c550410396065002803001c03500340d82c3c0c0000c008003503070351841840002c5001e074029145550343c01d070412200c0c40450f920f032000e00d8a004da0501003008002130420965901c1e250308103107108111841c801b180030302050302d540036400800104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 894580710 1250 894579460 894579473
    0xa1407020a0b0a080703060e07050409110d090c0311010311120714040906060801151e02010e07090f150e0a0c030b09090a0b0c040b07020621040602041a030c03070302031b0403 77
    0x10b1017520350b0740d42081b00039200d20134046090025500000003d08c14803050106800c1c0c0c0d070114294103603480450f40b90410100d4030000b5100f0f440c5081d551002030303410410a201d600c00c1c1c5203641400901e8100482d0b080003409401c0b0f401007103c0b100d1701240400000e00034902400d00014580e1042c0c070220388a5945da80c289029110b01c0c09640000b070211400041c580d2103480c00c0301b100c2c40705030702d0384041000041c001941e160b844034104001c641d00c52060010140f410321102003e41560324021840c0907658081d40e09556918100c02c0c00707500450801c225039100801c0341030300081c10410210720a01160350403030180041040080d8030034038000900034080b400152080c0e802d4803618640c21a552400509041030245100d1000d621800b0002040185040f00080001007100304c940041c40010041c1050340c044112000c4070b07040d900207000e0024286940c081507002d00c1840160b031540c42c0c200c101d00020300000d04010306140c0c010010601e504003105901d001104241106a2508d581c1e0030002c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 894581960 1250 894580710 894580727
    0xc0b010905160507080304031b0f05011d0d0906030b0a030b0c0406020c0901030b1f0305190501060f061b0819170f0f060d05070f121202030a1407020a0b0a 68
    0x10071964002c00d0760705503407500550980c2c41450b0040c50a1b030465507240c0303064130700b5400c0c40341283c907503400c150021001900c10350100302c441740108000030316071440c26001030b0000100c0c070810285611024214080713941c08580d10040c2c42c41803a01056010208000c07401e580b00e00c3d00000c0080411000700300b046440040540125525175088900070110311301406800c030000c0c00050300c4140440d000500700c0c801c240d20345007039500107510900165a603841f90703030a10304042d02082c2c94115421503c0d00341300d024060000070309100340c52044250301d4480080c0c18000285400366100c406145401c2c1444950002d40b17049081c1d0200d02d007010001030500401900c1c0e0016141020b654113004208181c9689220b41d00c0f9203841c001203080e6454403006c010700c040f1889022a154468480045441e003402024400100254104486803e445103400307023015080703004050842d07009200d98520203a01510800d10418105000f555030f0f190740c000b2440841a5030802c0303101074030000705c0140050303102c100f0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 894583210 1250 894581960 894581971
    0xf0f0c0a050402030c0d18020604031a0105060c0d081305031633020702130c050901140c070308071401050f0603012d0e0a0f0506040b07050a020a120c0b010905 70
    0xc4034005070300c1d90100012400180e8026000103800e00110204084941c00303100d41030025900c41e0200d074281e90000751241c1c4141c200f19100740140c01603010081c0221000c80c0500000c40e4482d003001c03a81e12526944810710740710724040007000804902d509042c61200256103401c00c094035618403514a1650b8200c2c1d090101702c8248151400804607400c002000182a00e034040e103841c2d410c0100c1c1c04280181d000210240e038085417a003220500d560541c81800c01c0001c50380c555980b41d0760020005400b03010a0b0000c9401d441f0b04200b52081c4407001302c2c1140541b9481340c0301a40326202c90030324070a070680d0010100c90962920f814440c4040074805a0362040004800034804104e40d462070383d9a00c64070a0445c500781f1f034011400b105071600c5030440320b000d400c04012102d00850640703650005600f55002516580c0240081c40700b8003400004030340d84510181006131419103000030082d03840e600a54054076404002d8110b43c200c07480340481c5814113400080d0802c555844484180c0140002d803034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 894584460 1250 894583210 894583219
    0x1c0905041b0f020c0d020f01030f090b0613060311100909060f05100302182110021b060705040909060b09100608070c030e040f060509041407170303180f0f0c 69
    0xb8410105071000460780c18203180901008500460b9500b40003081a000c0040d50505442c2c0070041c410a503184214140c0c0780c09442c0003040c0341421810310180700180034404003e00d040034418000310398032841d003444018003500c1c3c03040610f80c0258200c84206a0703070403032418642418400075031042c04801c0d50f400d841048409905070020310400303408900c20001000340d03101c45618481001e103080152540e0200841c2200c130302d40001820018205160a010a421180d0101d20041d00960108080041c000240002c0402d070038880d00c0036045004600c514622170f47ca03980e840c020000341d601300c00800d060107440c4046504082c41d80d0540202c00d40140400100307682c00145450f03201b0501e07500791580503200c05601c0d5407010140400380007a50403161403680c80303000006903501c407003004600c83c40c0102c070006c0c4502d000f11281400d149441c1d2110a40b6545544046010640401100c2c0c00400c8143e0502d40740000218003424025565400700c901d02880610240344203000c40e01d410f02d00c07001c49 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 894585710 1250 894584460 894584477
    0x20f060c2104061d0109051306090b0402030103020d06020d1d0c040e0102160212240f010f0e0c071109010b0d0b0a0f0303051804060311090a09051c0905041b 69
    0x1c8208014000c40c45001c00081e942058880c50010f000e0121a0019041c03400f010165281c8002c50848180c4010581560b981d40e034081184041c070b8400d100f013511381110b00790b103194910f400007040c407400c01001510080c2c0c0014205403e80050340410a4500c20320910300700d264074020810340320b40c90f081e0401d0043c0c0c107150020070410f0381882200c40d844904444078200c131041d80c09010240a840c41046603c0c411203410030880000c101d04400100510303034880c2c0301c44c07920ac5420081c3e8441a071100d80c10500580e03042c00491001040700c0e45c85841c1141180d250896800c04d41011501d00d090300d42c000e002d2070008a081d000e071100400c02e558440900b40401c1c6941e40078441024100c2c8524281a45840b10600c00030741b0690080c00142c14125240d1402c00124000901715280f03a40100c0c0e240ba4500b510343c80a080400070503a201404100800c102c00c07860f1500e544070b00300d14980b0018148002c9088404c1c501600c000009071101500030451520710001216400c44c2c0031808502045880 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 894586960 1250 894585710 894585763
    0x60901060f060e010c08040801020a02160501050d020f070c060816170403110f0d050d0c2d03020f071406060d03090608190c03050103030e1516020f060c 67
    0x140180c200719003059110040703007482c150b0200c41d4044030301d1001e410415071000000103c0c01005c0a00040d24210000503600c520182d8040d03d4990039044030ad100c2c500c15082000303a41e03001360a07609c0c480310412015960720128050380940740b150541c01800006140d4020a4060b032228005204203665225840b50180168042c1ca5540100c0f0781c48200c1c3d1503540004000a1180b10390080702c020300022205000fa17410862800c029045c44440c0005030040713454031100380a80034400f100620340c103000100c1004696802e2002c02c07054500d0307600381c2c80f201541c54130074400e44c12140c40d5200b840400341c0712026454402101c041c001ca00d10268441c00c0003003002c905d8200626900c140d81910b9801e081890b144059920220081800506610007041a003054219000b45901d4a81c10396002074150305514010300a003242d0080580240403a41d540c0080e1031445044840c1d41c98220440c0000c04810b10014002c0030300c03940704507007042e000f040e203c1c1c200600140740c0d00e111a5085901d400072620 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 894588210 1250 894586960 894586963
    0xa08010f1514090606221502160e150109260c0102030406050a0c0609120203280e0d060906022a01020a1d1201110409050a11040e0a0603230609 63
    0x35100115400510724000c550036180140040102c4541203154000304c4071090040028507815074040c0c0c7d0b48180c0b484a0800321581881000c4170204502d1a14421034100503400810200003402d00000d5007002c00c10b43c1300791b8000e40c8840000e02c44081852030700042628801d6200050b44d501410754800c03030303010290960001c01076405641072555064180b044510003210305030030b45c000c296203065880e112240484c00800e81000e0301c0030a50001d40e910642000000021300010544401c0e54480d1019007103287c0e8840c823006110001112181821101d030b091080c001c0680081c01050f0350701c001203c803050444818004494603540f403403903011401070341c0414240c0c482c040340c0500003040041d080d0054000b805031840c5858000d05042406003010035003d084039580405807080c403d01090401c00c1411501425a00c118452000c2c0803648142c0110390f1140202e004a41100c0c3e0042d001544000c02ea40c0f100000316000651a0240e0b140c5000d444e11100c0103041403076460007004001810184c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 894589460 1250 894588210 894588239
    0x6030b040605010e13180b070f080c2a0a0606051f0e090c1e031506090a060e03160b0a080105090f01030204020d0209030102031807060c030e01030207020a08010f15 72
    0xb410784441c150307040003008000060110501112205584060007800280c200c4002174045100d403410200500745081c0c00b6040c02255205c40c5c04000000c020051041c0ba44001d4440d00c0c400e11180c1407000c01184440410404809100491441035500307020600c065a00a40101d40e81641c0680352105d03125401980350300d0038000b010205128130f080d0907081c14039090b240e5101c4003100f051810607001d6119040140d051141510b1013850200610410f541807441c0c2d084140c0302150751600e0180c440000c502500c50510440303003803013040c00100c001510103008060803101d004064001c0242c80c0c9251504503007000d10703d04001001c040011916040924006000b600000510105a86075500300800395000110402080742c0900019003252000d001a50040c0b40c400e080c10021008040d9151030b0000b10380c804d03030400010500c8034000c40c0d0089103c9841100c20300c0c000d40e1f1002680085043c10319907500c8045198680b1424181050386603003d22811038011b02d0303c105140d82d81c100644c000a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 894590710 1250 894589460 894589469
    0x180e01110d1b0c020d0206040b0a0c020f0109080a0f0f1401061802030c12150d060504020f0108060604030b101a030f100503070902180616141903050307020f030d0606030b0406 77
    0x44003c0c1001c005498844141107040b44000c009515050721000441080e8000b4584407010030054035181e0b086203007002d1401c0c840301c001c1c6803209031a480c014840c0d0361b412500da0b0290000019007803881c1404001103056903d10340180207400b401e201184810700900b914418500d01c19501c0030a090345141c0c600880b40502810035030641045c141c2d1800d24059207000c0d1880c00c6840c113582e0311040c10b071075041c820a0014040c405c00107103854240180f00c5510f415100e41810441c1e5001009a142d0302d000640301941d4010f0a1030b0700e290360b0480b103900e000b034640e00000030901e111078071143c1d42c080d840011445030702d1a60840155407203412460010703221500445d54143c0001c2410300c4211065400707800300012920b210309010800d5404174515602056040701910030a011280074024030003404008445090020441c180ca602c188080b5030307080c0500107080000004c081100300d8420002c6d010b0513100001075a03035070300d0b003e800070f4020612485080f0200f410807100c8040c51406200d018200c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 894591960 1250 894590710 894590717
    0x11421150a0e190b090109020a030e03030403050f0c10140603210f09041113061407020a06030e100c02070501090801021206060a05040e10030c05030a0507180e01110d1b 74
    0x103444010f140540c60100c040c20002c440d6a90507420f0b10b80d96562a017900034045200016540c3c418580010150b03031090242c141d040d401002400700203540402121501000054100d485802404030ba03820580d100380456116400c02082c1094070032a16661400b5031821004c0322085440000d140707090142c80389905442c0c0b0001e100d0007a0b004000e000030324604400400005040d501c00e17412009030742000008507480001f45005100300ea401c40040c148903114800c0e0756040c900e003907001506015050159404040e100d031106207505d641000825100c00b03040741e00303004c20105803400079500e04c0c25220f1240040c151280014071804180300704da050031021207912640760340341001c0c0059076000410903030400c07608100010b018a404a50603015036590310350601040d1540c140260785070000d4100074800d820030764400c00002d0001403558101c0e034144000d0200140311001c2d01c401010f51050f4810300c2d500380202c0000c0e03a11501c000b0b0100301043c120400150756180c071403103c80c400b81001c00011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 894593210 1250 894591960 894591989
    0x1f06080606010806130e10020c0c060301031509020d0204020714070501050c030412050a0b190b041a0d08091002010203090d020c090106051c0c031e0515011421150a 72
    0x181001c00d603032888a07450030b5012400c100004010781ca441f4051b55405820340c3c0c08207848500400c103020fa09001c00e0102c54035420740d4107503181c00c1d28007288401020b80c000d03911145c540c1107441d21061035128a400900c215207501d03c506010300c21130710901200710b65000e445400305156015a01f036030000c240c444003c0d8142802e0000e9904041c02c86907040d5600d00c610f010000000e0000f000381341c49089000b86c40b00c0303040c0c2003a1558081c0c547c01c507049840340e414034124101d405252a13111910800894906a00700b60505220402d4824999840d4000c400954940c0b210b0b9015002140140c66800031910401d859490890310b030a14102e500b0b5204501c0001081404c0c0b003030b0040c2100024480480880306202d60621302201c0d00b8607a031001203521030003d1402c030f0014042966900000300800e11a52404902508250311860050b03410710450700c000c1e41044071a1410f07a44c14000044001c2030707048003c1c011050340001110501c925032180c0400e0059820850440e03802c5440740741c4035041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 894594460 1250 894593210 894593221
    0x160305072f0304090213030b060303030c07110a05130c080a0b0d12020c060703030c2003031f1701062408010909020103090512030a0f1b0f050c1f060806060108 70
    0x705403000a81990742c4020300021500000ca44010058400381d81c030449030841c554542141c400100811940c0319030804c0c010800100e030f5542c2203600240d44a42d5180400d00b4000c0042e0300b0f806507030429900300c0941d41c001d168000c001e03441140c00309915102c09016540b0b40d14640140c0d940840b015801030350b1a0443d0b00010320b0103c014140003284d006170f84154030040007055003a0810401a00026110340c40241c0c40c40e00074030041a0003540e06840e40c8a07800c0e809c1c6855403848045c000500c0c10506100d084002d50483d45400027800990103480700801010440601070f2105000720200c00c090140849403291b4500350070b103240000340c0c4450701640e02c0c0c03d41c1000144140f08059040c551200c201100080c000e010121408000c1d04a484e100d0500c07204134004c5802460407000030030f282801c0300c2c00100c2d64842807902441c40d481c03c006e00d80344501d03003101d0601800341078045500c0382800201485450307207284621f4540c0740104001ca1641e81049643d41c11003540d0745400320340050701080307 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 894595710 1250 894594460 894594527
    0x7120b1507020a030f08030114040c0818030405130b0103060b160201082809060c020c01170a060b0f040303030c0314131407180c0c022805040516030507 67
    0x501980003c04925425949490303052102c08010012a0501c00010040c016007c0111126603c84c0b000c0e0341c2005134231050345001c0e11845016004d450b807014591020481400304000700c03030103010080c0001d41c44419031190200540402582e9901003410b0050109120744282c00fa03540074410522030040103006074005458446000e040044080301000722040788004620341101c100e5101c03280000d80316401c0c01c0000845040901e9641103420074044031030340b80e0340180c242e51044d41202105045481c0c0d0400c8600074005503228801b03140d004624401d420780303400050400c60340643c809014140c14000110b0882e5600080c15100403400380c0440c996260360840400554400c1a503080c2c0c220140c903800345070003019402008501466040559250064080d603102c2c10054185441010380b10350000d02c8100c00d0321510071407450989040001d400c80c18546000400c4098401c1056040591400945e803100e800380b08007090500300441d03043c2e032042c40c000e40201000e07104c910304041c0714092403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 894596960 1250 894595710 894595717
    0x12160f020a05041d121c05150a12050705060301050d06180b070f020c040903050a030b0310060f18090302070b131203050706050f102c010f2637030201020307120b15 72
    0x107a81c03032322180c400c5035400c0d01d600390034601402c2d100d00380c2551403d140c580349140c0302003504102c0c00b50341c0030710040101ea1502500e88811a0740100d010403d10507203144404c09890741e41000d0400c0000d042486180c0744c10954840e0303a20150341c01d9074105841c5500f0301058642c00c03103000300011000c22600c034400e442944910010390009064811040c9100c84c524240c840e2070b00480303c11500d90302c4c10001c2c0c01c0c2e4940b290b000342011260a001901060310045e40f1460030f44900c03941c4440003d542008050118070f070401405818042c1d894860305402c0c000c115400c0307140c0498003107140070301043e0780d001e807102624030603c0c140e0102c0b680740d800c04a290024241c000e0440410200e110b00e445030094105101c2406031503a6803281ca0318503e489848509481da000c4600b9940034004a00901d03048003040400c00110051045041890b1624400b802002d151030040b642c0b05421380c00d04c0401d5810340040d0b0141407280d07a40007540741e030b2109503406ca64001c40d400350321255001b240d070345014001c000b5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 894598210 1250 894596960 894596971
    0x1c0e040506030a0c14100311040b0f0c060f0a1413120c06050a0b040606140a03021303060c0c2006041503020f0a0e0312160f020a05041d121c05 63
    0x6a807076a0392941c1d26600313003054940107003481c04034114500c049406c0c0507400c5e842d04089450305100c100c107607140790300343c0e032145028010041d44000b82800303141c402c44c02110103005070360301150440e19002a24100021050b20076481070380c00e10381401001640c60381c03d00d0090300d43c0424101c501c942ea40e103070007580049d800752005200042003000c0102d00c0c03a1003068883d40d150440400c0a99003001040121203054212034240710740c01500c0c0550351203a901303480c150880c0d8200166107810f00c241e006210100c6030300060020b41405515580694000c00e0005107070f00c07130300303005400b0f4141108803200c0c07081d0081c0c1c003038201c0d8007030004000c030000c1185803000c411254200145030001c00c0d24800030540c001e03103507507002c12451058045281000c110070002c034012481c0d00350506502e0320300e000200e4003104001d0300314022400e1032825503903406440d00c014107004004000c41600f01c005401402d90b00464500c040c043e14440102100400080715a10180104400650707600303c0c20410081001411 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 894599460 1250 894598210 894598213
    0xc16081b120304030c0f08060108030d09150e0a061a06070f06060e090f060c0412110a150309140601060806060d0912050301031b06020d050a1205181c0e04050603 71
    0x441c8000c03424002080594040e01c0308030095420050f40ea5812440c039407000321150302843c0100600003010094500007113010b0008145598141040c0f007002e000a086542003920300300390a0744c1c512000608103030031032081400b407007414507083c2c245910340c0c103440c0c042d900102d081000c240050084440ba00c8200d104610003e5040d440d65020354014400b100c6011282d1300000e200c1e0101d0004001c1e103a400900c2c090704901d41400e1440b6181d803003901c281c1c01822035182201400c50b40d40c50241e600081c050340308140100c10341e00c120042c05000c4500c4113850101c4028008070a80f51301003400c42c1602d0490321031050a440c1c040034429640c0c04000e20740310f05551020b00c4800611503907500c0c0c15100c210b585058880d4111f0400c50500c8030f076200190802007104408008080e0045801946600282401d0361540511002030f6202c2503d5102404018686000c000321000d89107410400803100380111181c00d1241c25101350394425050942011980301e1358000713078900c2c05801484d4032a00180 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 894600710 1250 894599460 894599479
    0x310020703170c090910030309050f03030c060c030703061403070524040e040303051303080a0c030612081902030f04140d060507171003031205060d15020c16081b 71
    0x4410515054043d111084400c10010310b4207403602d01701ca0481c2e0461040807021211600e5a50302400454040c403030103004181c20501c0c2e0000ba81c0500a40707010480120a0700e8251a00c0c1d041c100c1564011550f0718046850410301144516164110300312004000e0020640d0724208410003c01c508a510800b80c8080d41346500d5002262200c01b40c0300405160043c4000d90030305142c06401d0b80d0000b021241c110343c09499040101703602606641d04212107a0001610107210001140903100940020024104020f2506e0400010400800400d41c0c408209404006c651404988034030449105a4102009200038001d5124441d203240035200003c00856061045603560015600101c0d00c0c84082911481480c10400342941c0e915070104640c18000425402c680e009000410f5a8004a48042d0344a001401c00d8440440400f00b41c0e0304001d06020140c850f002700c0c00170754402590403465028070227016202c003c3e0350b12142c1c2503460460240422000000d400d103075050219610030f5210702d240 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 894601960 1250 894600710 894600737
    0x601140d0b01261b04080a0812060f010e01080c0c0f030910091203050d0b100c060c050c1005040f05030f0301060e0415050d051f0204090b092203020c0910060305150310020703 77
    0x20002c50b4000748c0b160441d2500c0700c05008418000d079100070001409030541c0e6000032505d03139001020b41011242401c10001e540c403141c46200300350245602540e240c1c45868450800b0032400000350050440441c1c0244004440701e900321a840703034900c81c4504010202c10f82c03800090051024220b24988002d001607260a1003000403202c20100000c3c030302045e000640001441554080d5412440c91420a6460044001703500707651416103502d4100751a9880e4003003001c0040c0c9951401d0746a400a08030380d02d800381400107034210760080c400e4001203920034449405c81d007024051000502000711054007040e103007106004051b00e20200c205c1d040d01568003134a032018400c030740341c032040b5855000041e202c60800156004403065056818442c182036810807014031072208003942480c00325070030518509100c3c80c0580c50025401c100551104580c0104421650002c10410444074555002c2c0150b88030342d00012805a251403c1c65015040032503603c0702851782e5001400401d02c00d20340510f410305031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 894603210 1250 894601960 894601963
    0xb0907050f13140a020304031d0303030a0e01090b0109050601120e0705040203090f06010605221a09030a080c012c06070e0f03011e1409030405090601140d0b01261b0408 74
    0xc44644130043c1d4048148028503900060007100102c1e0320f003602c0b401a9400c40001d0340d0340001002e1410319074841c1c1d202030f59500290060035800d5070110307070030040b940c4030030406014042c04c468880c0002d0410b440f4052641c0c0030701a000c54002e02c1000341c100c1c6418501484040d600080c607008040c424000c9840ca6668100002030003850641c2c0d5841d1903103081001190703400481e46507089124513100c4140071100c16140300300278021900c030001d0381c2d0f0403043e40807a080080601010344000c401103041e580c0000e06400c042d4040480c0d0007201180c2518103041c0301d6240d654880e911940d4080380010300d002e03004140d0707032180e118014500d0025594140001e0b0030744030751900c1030303084501466450903810414040c4026211440c0c1c41000b81d8a41a9802c03a0340c0d00451241500c1440c1c0b82020070902d9000d000c0407404030142080c50b555a2070701100c6240a400e804505a00090301c0c2446680144407442c20000c4402e155220440310351205540c0c0c2180e81c6110b0b40100509004200c0010710010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 894604316 1106 894603210 894603251
    0x50a02070b07020a08070609090c1e0c02151b0f07181e11031e0601050d0b06160308100812041e090e07030b0907050f13 53
    0x1900011301c0000c0385174040e07003040c0181c15000c282036030f01c4902c10b801c1c1d4000080c24441c44920030422200310041c11070080d0f0310a443c00704840d507a07100c1c40129620074001030002e04116441c004840031944004a80c1282c0d00c1c0210354403140c00c505000d00d4910301c04a8000e0301c0414501510800501110301c0262122985c800940402c03e0b41701800c5081701c3d240074803c02007040c440c180141198015a4804481c01300c031040f101c00342c2c018142d481e10400041c0e403901d0038070740018212070240c0210380155030300c08014407a0360107505020400440a501035501c000080c01e00c01400310031020290400a080c1d0017000c140880207084c001180c1c02c4403800101c1d0b10340148084520714a403c1c041d0000300f106030610100242d5030b400010401d00f980e0080207180340d26220001046d0f07942c0c1003445002c0d04044a000442e0340f91038000005404021202c0f000f00b0000d034011020580c011 = true := by decide +kernel

theorem cover : BRFrame.Cov 894424460 894604316 := by
  have h0 := BRFrame.cov_init 894424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 894424460 ≤ n) (h2 : n < 894604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
