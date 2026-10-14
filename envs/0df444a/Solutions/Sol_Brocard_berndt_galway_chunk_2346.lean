-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2346
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:25:50.686985+00:00
-- url     : https://prove2.me/submissions/89cba015-f80a-4527-b11c-0c560e2d3a4a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 421762589 ≤ n < 421942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 421763839 1250 421762589 421762597
    0x90509070314030a09150804110411161b0b030402060304080906040603060509181e0708011509050901150608090106090c02150c0f07020f0d050316110103020906120417 74
    0x80642d40000580701d100d20745c0044500c01a00402c900600c800015032001070014200800280c51601000100c0c00700c0e41d1960000e40c054102c280000e9200d500726000e0b0501d4240944040391407103251007242c0380120001641c8402c0720300303849003541140c0d00e42d000c1c00310a5100400403076108104100048241d5038804c05407000d40140e9030001001810a0240825a040600098210b02c034103211000001030015410300b1b001e049184203400c41001c00788280c41d102403508050403550074495100e4881080400b0035044894000080c0300b19144d00b0720302c034220b5001000b24039001645d4941841814001c0c1a56a00060104000602c5a03601d10244080301c10440030000141c10050609642100d010400c0350042d005216052610640c04801d283e0741c410200024041c6810018000b0383c1d075034021200c5840307500442500d0b43c1e02031103100031720348002c0c8190403201c01d0401d0214020b10b51203482a0b46c0318100c050040d519210000140c041442001801111254080c010500804040b14080c1c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 421765089 1250 421763839 421763873
    0xf0207080c150a1517100f020c28030c17041202090f10050f030f07060504061e0504050112020c0d050315040e030f22030c0e0c130905090703 62
    0x1401e80003042e076441030401c081c007401086203103003058405044882004080c104480105005000c0e9400602c521410041d4a02e1100c10303203413904070340c038000080d580c000b010021040001c2e0b5282801c145414050040000004006940455281000039002f80ca944107100c1c0a030701c2003500b0a20580c1c810b860703640183c20003982109201002401c43c01c08542458221200d40ea40403028500155004c0418030303684101886a5003070b81e10f400464a061000f450440e0301c400c161441140c03100e5024005903ca842484006211180310081c2c480380c8051088002c81c066032090300d410714140044070500884610791254590030004000c401c80d00f04541441441c40fa21116201c3c54608082843c100444800a001d1428414503420b00d83c000f004032085102d9044000c2c0c0c850090001460400d0011074404603080300101021050040342003950742203c042c50481952035549d140c10b400d080c01950102c00100745070150901284c04142c05c080c1e4003014400440391069a81e84801202840078111 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 421766339 1250 421765089 421765093
    0x60605031b03101e0501030b040b03060610050708071a0105010c151109190906080a03050301030f0305040e0903030103061b0804171e03040605130203030a030221040302010213080606060d0f0207080c 87
    0x421546d609030007040c1588904441c104048480c5001180d2901c40007071103075100340e540340204e0315554000d0301501c8400390490035494aa020516000b40038480c1d13610b52581c0041c80000004d65903104100d1410f2942c0e00a006441e4007136544a444040c2003403621904001c3c20030f00ca80305054881d11842d26940051050701d0030b11728980742004086401c1c1d034110128035000481c207603000c02e800c1001c0301d0449600001e113409200160604868600407500103200004a00050000040c400405141641c0c0203420800c42d00300c14880b02e03040851007484690100c0d9590300010046003002d094000c0902d141c9400b540751480300d507e5041e0710391603d07a019155550100c14002400000c0c855280d20401c400c0344040f44a48540020799240a60403000f0109a00000d51015035032401212182c01d01d03c061070388605060500e4064081e410a07201722040041c0b812000602d405d0018420b4040c0c60b0261942c0d20b401464a00000a814056170002c0e816400300144000182004001e01039a456500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 421767589 1250 421766339 421766399
    0x70b0406050a1d120d090807030c050105090a02010903080a030f020a091e030f020904080705060f1608040201051c060b040303090f060e0609060c0a1709010201060605031b0310 77
    0x281501140d0b03880020540030030301100030461a0f000043d036030b804200d003034000325200c200307265a08020708540100289200c0c80030461800305600111440f140c148110700911007640c170820500ea032080d00e024040d001444024040010410358802402c2a070708074503000c10180c0c0c003031000000380da000300403200026414880401c60b41c04400702200030701c40640c0040c0e5285103151a00144036820b500082c0c0305005100209003080084400ca5a0450b44901502c0304c5250112000b47c075035204954008240300d9011a52001d244103424140c40b4650513110039050290f00740c02d580c1002215200c92a8139640c0e108041001d01c40311340500000c6210b07981e44c141c805d007090300c4110b079080b00e0b41c0700c41c091150b55140c0b1906961040252804090706803075068441c034110003003600d031000000009d489010501000e4112941d907a0081c4000d034001e0300280400303035403800c2c111010320003200d50b00340005010751181e042118800040d40c011916500d03140001d5212500300f225030340015200f03912601c1d108 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 421768839 1250 421767589 421767601
    0x60106020c030f0303010f0b0a05070507062a031416050a0809040e0706020a0f0812101e0302011218080c0102070312051603050702031b100b030f0a0b040503070b040605 74
    0x401c46192048042c055415540340c0391301200c528445000b0f0461841d008240742700510701c50404e4074141e9420104942c00c0b02c0e07440c9009825840c034040140008640214552200800740c8100700110354142c4d03503000a00e41d0003810100070b8004c045007503c03041660a0180200b20304003c0b810016001e0902c20b5620403041c0c040008903001601601170980100758200005500881e001c1041500801610302100707507490400d405c1d1081c05540d44000d4090018002121000c0c103080c015a101ca4482c8558441c81d403001000180300c5100090001303044070040e4109480c550001c4042c00221525105401c0a40e07954034410340001314000804d83d804242441803503480300071041003840402d402c202c5e904004c0380b400001507005550ba4103051b1180082000c051003042101c1c02c22003014503022a009002c084141c8850401d01200019810a51521180d103000700d640e80044c100307100148003030b08556850002e03c0c4001403007583c1500080c040640825403d0400f03500c25482a003000a00e45049 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 421770089 1250 421768839 421768843
    0x18030311102901050d020a050703020708030c0d0507150203070c030207050f0105070222061e0801181203230901180305180307050d0501020a0f0513060e0f03060106020c03 75
    0x12440e180441401c0c8000c020540c1c540300001d031910640c2e8118102d01c0005140140e4081c4185202d83c0b01c598030009440305010760250280841c0c030301c43e07803d40d100180d6402d04503a030784c042d9082c0f400f0190440f400a404460140c4001c0103158820f04204040c144864010003c80e0401c13500e15020034100450072081603030602200303024040484019020a1685000802c0c40c01111300007402001d61000000c0d6428400b1121048255418401d100c482c1c0c0790040024844808030900c0c08220040201050717079075041c01550041044c00751340b0300042d040d58643e0300d804041c00c1c0046043c1903550105440c940740081f0303140f0072141228820800c0e0f0400700d9411b4211200c0d001c00340f044c00d5040700c0100020340d00100b180c81140405000e0060001c4250000303081c5000350303010a41c0030716000d80d5101000010b40150a101d28a0b80304c0150150701404155041d101d1400d0419580714090000c1c890380d0f00601030340741140c00c041d1002c2d0b588894200440d1a005003a0400c80240e4811001c80e4514581 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 421771339 1250 421770089 421770103
    0xe060f0a03080a02071a04080d030e1005090f150114010e0d0c1d0601020f06271c18060215040c09050901050103050106170303040204090819050913090305070f0318030311 75
    0x3500303580e507e42841c003454a901c5d20000e40c1c01d00c040645441e20002a00010410140d000340341d45410001800e142c082295500c251005601c014000c003e541a03040d85100e104504131303201040c200e2458003290f0b0045501340c540700900c03944184200200008101440c04040103004030703800007010000c420501440842004200c5811507021410303840c0c2251000c62a140c20030700001808094601c01e80d0301401c0d41c40090700207441403080c81720030003000300a0346c0503202814807030b00e44d200c0e003242510840c1e06810302c5002d500c01503400341b00210b1506240e003000300d40c85070082040b0441d181d00c80c2500e0003a41e0741503607101860f0391180d0062090100c20700c00d2030004c10103542c844e85c000c85022036040d140d000007000a0f108036540c0c0043c505220400003284d044140c0310f5800c550020074402c0190039030f007040300f426006000c0c3c5101140100402d11a02c48015090b0321500e040060b80e50b5401c0c0c03c240c507901c0441c2041074000d00d10308807046c4000424043c0d0b1080e00d4500e01c6030400703440140790100e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 421772589 1250 421771339 421771379
    0x20a050a181104091a04060801060506311e0605090f090408070209130b070207050607260a0504081504120c1106040608090f06010e060f0a03080a0207 66
    0x90164010003030540000d214503000358a001011802540c0c0b1409016a4081c581c410f0344064108085154108140400700d9085c2c0c00c2100c00300009030320b400d034681c2212481c0c0500b54001404010003110102005060801c080c2180b20681030a981aa0a10b408101a0744001440300f21018006104108000c01a003c4c0407149410340c00d285031600002e80441d404640740b03006074200e40c081400c0c01003180844254a80107071814945d03040202510b00309105144050310504516000f0402c01440416080204d9034001d00d8a0700345000c98132000c061290fa442c000b403034203810072a00e40320264058090074181c03a183d10f075191214581140103060000d8103080c00f5050030b07204100000111045034a0041ca000c901d84620100064034011041c07a181c0001c0961124005c02c00240c1d190f4402c2515124000b02810340d2000c450034108107990714030a0240b6100e004a51000400a080442c400170607840000c2c40c2c0301d28503950b0744803604a40d01c5880310000503000400140a03024049034402c41d056 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 421773839 1250 421772589 421772599
    0xa030c1107060509030c0303030106080609160203090f040b09070f03060b1309022104080d0c050702030604030315031a011401090602031603050903011d0c040b091503010905030f0304020a05 83
    0xa16034030301941e00d0725054050300090280100340c240550304c0810210149000113800c680e07a95031621009060003804484640c0700307550880008150314003902d9291003022460300107505068201e8100b101e03071039503804559002a0346103481c9400d1f60314410501d01403581605e89092001c0f81d0017000f01074640f290850154180108603501e8012402e140c1c0c14110742c03114400581740c0f0581da43c1900160903940e8030701e031401c81041c140828854640000c2c250020360010400c1102c0c80a1000d6803280103501c406903058100301c0006020038040d8000362130344000114000d201079202d42d80d50211040300303000c082c000209000141320303610850864003102c4609081034242e491030700000a5403845880c18481d00e20002e04030f80342c00c05000b0380666a00c0b00c00100203111030074480b0320126a0f004803824a0065101309080105181024441c000c28000c0c0030b000140c0da80e85021020500441d101020740c4c140d0743e12070301e0101082044c8080c013202110030654a0341ca0401c1c1c0104107000049070003282c410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 421775089 1250 421773839 421773857
    0x303050a0c0804080a0302220603050601141e0408100e0d02060f0a0b03070909030807020c0f030c0909240f0604060605120901060305030c01022212030513080a080a030c 74
    0x9a5008900c1543c02a0300001e0680c0d41c070800a000c40c06801192010310b4010030540b00044040e0710740384c1c1c01042c1c580383d660404c01c541d6840011540500c034080c00a0240c0d41c10801415891054400d40040c8510f414903a0b1070b10350f481d59120b0ad030420200340c9041031603864100300000722050101c41480c400b41d1005000605205091001001d00a850340d4549030340e59801100c40d450a000b001e00a0242100800401341c00341000f81900000b1500c41005019130ba8030b002146c545142d0341c603003860002e802441012481d0061001c407080140c20f1729407a1250007000d00c0c0b130f81c50b040d01280c80c40d0120740144544e03062001010541a0004e08614803440c06c20105114a40e404803d4078030080b20025503c8190f00c801807003900420507500040c0c034030700000030b894101444c15001407800c038a10282900300307004040803808009900b80a1410820b10b40c980050219104a0151454005004240101903910070b00c26251045940044070081804252a41c0d082c0d054410103a400d4420b080400780 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 421776339 1250 421775089 421775111
    0x3021c2001050a20030316110111040506071a091c020c090a090305070b15030d020a0f030c020a150f140304050c010f030e070e01030204110a0e01051b03030f040303050a 74
    0x590702800f00a2400c00c4808000c108002d1850714a04808600d2070b425a9660b0504000d1400541c064000080108604c038800083c03000e414030a442001d07040c001d00d541041d08080c100711007135000800036640c90148180f90304940804020840c000d41d01440201695900c2000d010402c0044685030025501710444080c0f00c1d84440c0714956200070108000500a80300742303030a903528010200c0203418000e201c0b0400a6220101c3c84143c03020300201e00320340600c400c110b4201c0c1da50f41032080c0180820401a0050002402915040c2c64240300626099555071964144440c0a04010030040090924281c802c51140c006e40d49413150050b400b60340380b80d4a01601d80030b660303900c4120703c0c6042020000440b803c040c469401249400202c00c01d8603826a41c442241031002828042648a1480c125400380074012000c115001c903583e030f03241c0d202070440180065456400c130049211140f1105034500d05c00340020300046104003181c840e03d468608041c20018200c84000f041017002914000c60300344 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 421777589 1250 421776339 421776347
    0x6031e08040b090112051602010501080c061911032206030905030922060905060a0801090b010605160b0108030a03050c090607020f0a0906080706080906010b040302011803021c2001 79
    0x401d50781603007140c035a182c201e10f0040751421400080103c1d2185031a041c00f41400308510600c0da901c6455000340000c4e42c0300da02c0140c45160303140c101c5503c040100096041101c007254048081c00b2203081121b0302190681c050703411648071400d2620601102d004142c0c8850300301c41d80c00050300151604104c0025030307035180d603560700c10801502e11840c2c9070101241a0701c9051001425081000028000306588510790790142030700f6101e0a00c1072060742004509594144205800c07560040c800e00719a07440d048098495910040051140801d030494140104810410759802068583e0046a68074040c51005040700c00140c244014250200107840c3d0341e58441c010350300001d404481644c1550701840c00180101c025611030042c85080080000c0c40600105203042185d03000d44848445554074110503480301401d024a92000d41c0074071050015510407110040d80100008440031556201e40008a040410960540102e500c0443d81c03010030031912074103046218040480e000d4400250300183c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 421778839 1250 421777589 421777597
    0xa0f060f08010608130b090c041802030f0c010e120703020d1109060d080a1b05060c0418060e0f0604150b0306130e060c0f1c320117031c06031e08 64
    0x4d4a51b108100109020400c207101c0c0704031050000b002003141c111403848201540006030401e274420701868001d101c21400209030700e0f0404034165101614861840304014154640644645585c4541c42d004401a15008220a03c56005040300480c01d043c01d0104a002580101000c0c011403900086800003843c540c259100365010341001800c5030004180481c0e240380c02440680355101e4081400f002c100484010300a80e2101101e0140303083c2840d82400603202c0344c0c03045205280780c3d000002d50200340d480045412040081c000b0440342402c0d2041d00080200c1e411080050000200340407191403d801818162204804240402c4d5046465551078400080c5400030034080055030a052410410446103141c033070115849601000c1c5140900420450141607030102d4000f00d04a04100c03000810402c904401c9a21070160f030901c0d0680d820300030303440000710051005104000301440b420440601007110450300150311b41c40c5082000e40780481d64803a10f001c0e070002d1490800f00e0503070b01c110707 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 421780089 1250 421778839 421778843
    0x1501090314010b0307090c030b060c030306040506040b180702071205031206040207080301030606140603090613050c030a05060906010b27030c06040e04150b0f0108060a0f060f0801060813 82
    0x1c8920074000c0c20064098040002100d9050060450200d8484000d0340982c0c00c448070740c0c0c1d003009009110320911845101e2007980489652085c00090440d280036001560f00010140c00071480c3c200c4c1c8008a00d0300d40054040080d20070824041240d401e41c1040600020149110003082801c207a44070b0315161b21550100802e11140c000010b80075843c0e680444100300c2d40b03c607041d5642e6a6a081c1003005020078010f88401c050070700030071803051906005070b900031800c4602400c1d140c0c9901084450b18041684115103c1c014a4948422540d080c000b0780500390003480034000516040800c181043c105030002140d2202c103008030014180c03100410701e04141c001e443c00700c0300c40c440000a842c0c40080c441d401d07440600090041001c10599850700c0c0100d204160025020032251106c6083d030311208002e54010a003001d40c50b655610400c8000e4100380c0240c1001c03402601d4107405110990b094100c030000c5070444650b01d200035841120140103190514010b0740e20b0030103450300c0c00e0109201d400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 421781339 1250 421780089 421780103
    0x3030e120a051005070509010815040618021b030c06060d0c0f06110f010c0806060706021605010506031b0102060106030e0f06091b030102181014030a06050915010903 73
    0x24925945401584101804040044815400d141e00c0d00030b9640d0184040c00c02010304010110b90030601410a58030f40207416100e42145603581002031400038403018030310340d015841d0580001d10310b014202d130400c00303190170382e01680d640040313256030001c0100a8508002a1310030400c0c3e01001d000071070075640000049611352004070103401c1c0009170b00540c0e00301460090000314001007183e003250f0442c039010081020380d141c40200c206001d0072207002c2c080000100c0c00340e20028a043c80c060005111241c802c0b28014200517414001d2507000e1400f4a04661682d940e10600c94546010401c0b13105540c504141c1c11000003101000030348946040c4030706010b06484200e91081020700740440e07000c09030020221849450070002c40e542e526940481d11440300802c000c060810300301030007201c0c440c42c240071600301d002082034148048800d80b46181130410a5500c41400700b004110004c40c0100403240d40850942d05100c03c000d44e03070340b001d0101e9024400842c0640401c1c1d8000c44130341c080302c4d04021 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 421782589 1250 421781339 421781357
    0xf0a090209120d02011a0d170306190b0301050405060d08090409030c050d0f030e0721030c0506040605090105070305091509070f030c0e0121080c03040e250f05040303 73
    0x8038450842c4a28080d00d00c1c0a6218000920b42d070560041840c521141042e0782c405d909002400f58403040c10001503e10b140704120a144400668019500103002034542250400c0740010945402129080441d00b41d50010040120740b8040c01203640041c41107481e129040c29036903e540d0750f0301c19555040d01464954003004141401803c080c1c4c0d0064100b8291481c501990b400208242c2030700e000301c0701007890f00e0010002c40c40001610010340700d0b80004d1825800303080e0002c08100d69a008200d08000340314605070009881805030340d003d20322072200406c60f41011451a400d40e04010010340c10035140030100140c0080001c0c0380c100c4000c0019099507581c5460b00c504e07080c5440368014070464400800000108086100160200d07041742050204a0340c039007004001c0011249003010002d1240d9400f000866042401000c4240a00c0c00712454139a03030381c0c944181ca90003226440241c400c0e40701e180360420080800d41000640074580351500c00c144103400f5007103000d41d010103410411000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 421783839 1250 421782589 421782607
    0x703031d04110a1409040e0c04050a0c140705011506020f01290d0c03050d020c03010f0603080a0809030c011506030b030601050105161e060617030a050d0f0213060905040b0f0a0902 79
    0x44119401181701400910191b80341c0400f0076901c52844100318000ca2500c00081c1c181065031003035008440290369050142c4180700c84036044d079007081d01c05407815580c07112030415001010382800d00600d40360b005410003154421606085445007038425030390b0358401780c0500c01c06444c40900c000c1110111800d40b240002c03400c00742c42c4c0d40364680006000d4803c01c20121011900000c261045107070890081c010780e000d1a44010944405210060107040203000601c001402061001e40c45000c51045a003000a4648140c1c2540c103140701856070803184200900c417042d03040c06610f0b114401500101100d51510000900324401c3c071400300510018201480c0810482c0c802e06240790141480c40d150040a03814020001c010703d11643c0552510642050300707d040102c242c0d0b90845c080e403607240c203000c3d03400b2900028100c01c0e0130445e56940d0800981c81d0b151505018070001c1d1080e0344d1a102c1d580d042030103010498100401c083d00c41c10100308140c0c1103031388000100058568020b0050388650601c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 421785089 1250 421783839 421783877
    0x306101401050313172205030304050913050706210b010c03140706020403060506180c120406060305060702150603070f1a2104170307052205030703031d04110a 70
    0x3030540c0c00462060781c5c2d42c00118050140101461859010012260b50f104002d84080c8907098242d001800f04000c189403025406601260006010300d1b50300d802d58032141070441a4203d20041900200d03c2d04004640080a54004400740002c10088601e0030010381024950f440040420010049101910021806846c409c41c3d020205644079a140d19041f00034240448034940a0b5241d00a0032a05c3e82442d0308460089040440d51460f02c10310903180c690504000b00141d96983d200c0b0300010000d9010040303c0d115144580c05800a8402869507035829074002c0c1586101e580009003c1c0440007a81038100200c41007801280c11200d40d000d603c40340b034020f141f020040304420050015954020544540c880e80c421155800c031100e028a10455a02081e00c0c03140020b002448102c101b001c1035002c0580c42c15803c911010419030720350000707141c5115500704400044440000403c84403445255500103c4125030903c040103694100103010300419403540104074410000c2402c0b0340070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 421786339 1250 421785089 421785121
    0x3031d011e05190918110706050a0b0604091505030601140d060e010606050c010509030717070c15020c0102010605030d02030304172106010210090b01060509060d051503061014010503 80
    0x40b00642e48401221914003074103c0d04144104078200b880d01011461117240d501c1401c0192150281640c2880515250300f00205001032a16981036507591001081e6a02c0038040c00c010300c202080403481080031241440030800d940c0c0311f41d0080d80014010320000215014640084406407103581180c0e4060078420060000510448620f502e02034000c10f08943c007000a00e8556a41802440240c903010301c05a130700d100e1641c01400c1d0b104100d0700d4441c45080d001c0100915405003200404603a1111088118001928100e00c0964446001d510b07455030280149401004110060000c080c40f00d4006512440002c01c0184820003071141114055405410342d00101148070242680703894415003140c07513010903500c1a025208141c10b04042850034094652841d0b401204001564a000016149908a000540e40c018801d01400e41d6020b010321a0320b114840f54042a4400081031017403504050000e030600d44400c8800c90107004401c0000c200440b680d0302840c01503500d5071107003120000014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 421787589 1250 421786339 421786357
    0x409030c12020c330a0509090a021902070302060d020a0c050f2d0c152503080c0c0a020913080304150e07080613110306040303050103031d011e05 64
    0x1080c01c00440650004a91000b400c0c20b503064220b200b41c41007500103426052466514031111000c14000e64446440507045802590800c54148501c0b080000c18a01d000c40350300300c036039074045215910000144c203407400c0341e0401d001804000d4119000b0802d948500090000c03220303000900450014401e071003c1010680000503150703001000c00d10320761162120340390900c034083d03d242840703200d030200f49200030400054001000f8a140f8601407021040d81111000e201400c02d001c01001151440310143e0023400f401414141c0007090314028041d100701805050280f6418004208120300002d050502e05404942540907580c410500381203d002d20710005088400c00f10620040080c41c1c10406d003a4108020280b010352849040a543d0302c00d1841041c0007030b40070102150501511021611106029110a503203030012000441c4c6041019141100080d43d204010000d05911040a00341e42c201061417440300028280020160034400142445549440126040c201c1c081d508540c000d403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 421788839 1250 421787589 421787603
    0x1b061211040f080c0f040c0c0624090603140d2c060a0201021819060e04110f1c09080910200c012003031f051f0315140409030c 56
    0x95250003181d502d40e100e80b4030b0f0900840d0010a205d040703240c1030041064410b503e80c1d41e0744415149440f86009400d0041188400001254010810848841581002d0240c404001c1440c91441c0380280181040080f10001a008606060700860707000101207000c401200d5580040100c0c00d40101856030b9554a0980c04400029442d2507660190050620034580203d0701401900c544140181001c0c1c3e0b0424001d1011424000e0020394015200e84081000240c000260203a015401d1222507100d800d01c50b00d030510104c1e1903070088840b189012142c0f0103a07501842486255907502d2002d014071035843e8410304165403050b101d244200c1c2c07400764070400c031f550000b88804040a0151500c1b8050106400074061012903815407100941311f01000aa5200652460341e604080e0350f00c145240c00240305608e600c0200088569941056101c480b6051412000b407031040360010b401c80c0c1d0001100302564000c034204010000c0702403002080344405640204201582e03241c00c480409000800605078 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 421790089 1250 421788839 421788869
    0xc0c12070303051806041e05010b060a05030108061006020d0518090a020306010912050a060c17010b040f0909031d0411040902090910080a0206070f140a1b06121104 72
    0x315a1540129008546203113000c0854240204050b480d140200d0b00038202084d00c1c4400229441e082e010030194078000d400014540c1982d2b000501d69034482e121000008002200600000006001c402d400c03040c070101701c1e04513620b0054041d48450f101d030218801d001000ca8000010303111212a0721704a0310050042d40c052500c411840c0003500b040c0d42140c000303000b205001c603640b980b202090686a03002001499200c0c4555a41405080702010803010001c0506030070854004019806001c0c00403075440781c1d01d480c109064041d8115071039000240481c107100f520404a070304148490400444031141040c000750f00000b1401034078000110303030300703101c1d0018002800741e001d58054540100210340383c01003525848150000720030180a607d5140d00100c150f03c005140c410018035529100f00040c031142c211a132a4450203030003498561a01307402004400080010202005070703c0820030307120714415814100020100b0700e88810b10021699514400f900382c0d0b40720304c26900107040d003601040007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 421791339 1250 421790089 421790093
    0x60c031b0a0903110103020414190305150702060f24040608100203010905010b030103051c0356010309050f0a03021b040203010b090d020d1b0f09020405090c0c1207 72
    0x420540c83c8400d41c2c10f40003503101802da56210303001320760032100030350880c404403000c031010854010705c040649102c0c0c103662000003001070401d000b01a00c03011a5560618a440c000340d000c0d0030441e00400a9245840703040c208030300907110300e40301d040485c014031861004007035800c0814001d00b429000075015101c0c3d00030007100d00e880c51300250f068401703001c070a00a50740d0340c2c94100502e0100b070000800641040d50540000f10001c040f00a0b840d20b00d280c00704075800040601081c0101881d940107400c080314074120101001d08003843d4802d0f4144110003118881c04a0840b9003141d80c001c842d0405480300c5001003130080c04c0000180c109081c1301070340d4614a00385406551524091703081004225049420903051405100b5a0304a5140c0111185807040560400c1850300d54800c0483c2e2044031020108007141e0a4403500010003a040d00444599007000294100d15855901c15240580100001d00450f2a80207010f508614004507060725124150034a03402c11400041c1d5480081c0c0124001003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 421792589 1250 421791339 421791347
    0x20a170711090108030703050c01020706061205060601021c0e030f030c0d1d060306040221190b040207020a0b07030c06021206100206040b04110f0a0308090f01090602060c031b0a 78
    0x899503101d08400352455480304144a4918400d2150200c3c9801c14802d0740c0100303020781c0007484c18000c00c1d00014542441613a8840440c2c0203900302c500c10010241d02541001002c1228540000d024001440c2c0c080207030500c04c00760f0500301e10030810000220425100c6e600c0030480d220070756102d1001d481d12003468102450790380f4040d9a8580c00603916004000000e00031180e41c411411014081c0d902d5543d83d5410b0001039400800c0400707940020f4510400040c004500990140304400d50961900b003400d918101919103803c0500d2207140f0400072840141d41c2d040c034250480d10701d004e03507540b00ea0a0b0308040d91000c4004030060030342070000904500e102030340e031261740c45803904841c00303a904840f41000300d070380705000c41d40200783d40d40c5840031501140c8c0e003c5558440384001442101c009041c0004a010f260b00e0b0f9004a80c1c604000c43c0040032807034501c1c44e2a064680c20300e0301a5850340703005030081d9150805000090080000004552810031100e05e01e0031603201206640d030707900040d92000b4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 421793839 1250 421792589 421792597
    0x5090a1b170103061109061201050102100b3a030c0507060f0e090a020f0a02010203100b070c0b2508030a0e011e0209030f0118050d0302030c07080901020a17 69
    0x12599811500c40340e40040d02906078480501c1c00039040c05140e0b03095544280081c0002ea00d0303025080801c0c055810580d80d135800403c9800002c0e402c0c1100c55250400180c5484018020b80745d800e4200b92983c103250b199154454145111201d00824000c0010043c40103080c51701e04080300307407048202400c24190804c0d61001924400e00868000650b84c1c0011110b4141c040440c4001071188040c42541e03140060744076403c00740c0c01c2c030b00601c0d00e030140e20741482550150a091015035004002c110310100c0e101c2c80b9030020501001641d2400070725590318298800c00b402084490030740401e02c10040c900304021341a5503c000344450001c000c0a00b00351180d0b0b0012101c0d842c803a4144100414040c006000700c2588001d4071540f41e900500c0c0320004d00194011066042d05132046480b8070060003001d000b00020360f040389200d448403142d41d081ca182402e200e000004c0a0500402c00d0241401100c070880d07540e950030a991684900020340101c0c1001c89400000d404030204000810340b41560b40014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 421795089 1250 421793839 421793861
    0x20a080a03170402010903061d0f0714030a05030a20060f0105120c1c05010f1a0a09110715020c06180106120c09051b13060f0516080f0405090a 63
    0x502c541c1c00b502d0b07075000b80c0ca20403070b0001d00185038410100006411504080786e0024a0420500d07406c1c49480401d00e4004038041c15149a8800c41040188261980daa1524444142e001d0f0080280a40318141e8a1254489800070045110741a034100e100c04000c10301110400c0060f2800360915000b15001d410007030198034454112031080a1402500041d0b04500140203401c5501503409605490302c0041ca8a0065443e9521212003020b1543c06108c1c000380c0320049492209000002020b02c80045c0300c0350804403ea5162800840c80c00d4019810b0f540f507103a00403a20040100f00e074800c0e001078010f456098241d44601028011307101c6009034060341100c018002000307034076a9150000e42c440c48441c00030b0249808004140703d80c0101d9007000307900c034518204c60703183c0c0c0c40c04a100d0101c6034810345007601c146044060a000c0281e018003082085070345860081c0c2442081d100030f1124144441c0300a003099400aa4140002010020b640051400604219181c81c190070f154001d8801c4140d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 421796339 1250 421795089 421795097
    0x12060902090703050906070f0e12010c080c0f09060f07020d0609031d0a05060d090c0b0406020715080a0906181a0c04080d0e1908031b01020c28020a080a03 68
    0x1d120b09210340329162103070841d00024841e039100c80c04151480112004a80208007004001c104180c0324840b902511940720000004c054409a000a100c24800b500c1012103d13010045120307803221003404d45c2c01d031440488119540302a0000e11262921807100000e40100308064101c0134080d49902c00c208041c000c2d111901003491036240c180f054480e40b0380d010303400b0604000c14000360400c000540303004000100c0000d68110140c841c80b507490070aa02100540c41c00160611a031503061000380300900a60391400b0b50009584000380000f0340041c85029129070b5010702e10b00713000d61a0442c034103407048041000380d581001d081c0708265440103840e0000040c240d001107414142c8040c120703070480d0000300c0a0700038000007800c120340e400300021340c07558010900c64640340800300d5886054020a03c035401165030300c10310032440c0b00d64103407070942c0350403a4030600208130803020114050103000785070600e4010703040f002e101e0002030420b02c11000e500408000000300380e42c4800074081c050503019450b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 421797589 1250 421796339 421796341
    0x1202012304090906050f061c0312180f031d0a030b060103090c09090c0b0705060f09010b150306030d090b0f07032307030915120e010b1009140a0e010b0c071206090209 73
    0x14050f00003011118181c1900c002d150240c00f2a2107a294509185006c82e00412900c401c154610300441c150036080d1033202080c08000e080640056007401d503441640c44000140414400040544915100c007070202c140c0c4500080d0349a00c00c2d84190000303a0311400e186000e0b40c0310032245005100b00502103a034140c600e400440c02e1001202500e9985034803800914496450051658071b580c000b901090107076407108624106582d070420013041c0c0d0b81c0e1000c849a228a060300401d80b40c0268055600c060007550a403d00141c0c010758100c55016201031009a074034000b915040300d20010a00b403540d00b03140a22034203000258807100805403203009a070303035200840e2076440620884841685060200341c0c08074912140c6507144d080300004510328000001c918003c900440c8181e0344c1002c6404c0010101d000c02d100d806d412101400d280d25090729042d07036060a090103400b00201c180244107607544c011604105200003040904003510080700002000b61280c68594060700104004034800c100b104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 421798839 1250 421797589 421797601
    0x106020106080f060f070e0d0b0a05060f0603100509060130060608160c140d1701061403130c0b0d02042102010f03090203030405060f03010f1202012304090906050f 72
    0x140280901400845c1e800d054031608000d8a284641c050703050f0b08000402d110502040342c0d194124491307482c100b408151813801c0e604104509680c1c50103144034050030b005212122403910700d0081500c2c0b040c0c40744156500d5a00060b2000400403160441900c00444080c400b400c1c48010b80f0641c800d259400e001c0c094a902055500c0b820894088040c41c51040d00c00c2c825900c1907003207010b032a000d8908546e80280c0c00070f50310700340b28001116001085141c140c10729603203140411a80100f64504c0c2c07001d052110400100d603e440040c190103200605084c009050103001141c0000500c6010b07000c3d5991044030880341d0194025101e409155107a0344001c0d0460b192901c40200c032035905035103003004207100f1070043e8001d20a00406030b815120502003c1507a440300401003819200c04142d00f45c803503140122082444809403c401c6a8000d01142400140d801c540d01b0030700412041c036118079195005958502c03c5c003495204805060601c0b81050500800790f01c2207025001c0c1d5221300c0c409603510 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 421800089 1250 421798839 421798843
    0xd18110406051f0315270614010305271c020d0e060310090203011403060a15180e010c03050925150909090b060907110a080a0c06050106020106080f 65
    0x780c46030640101001e0840710000290b6a0400e08061003800c002560030b0042c1144078030103600d6001044504680355083d0045154241e000d43c4080d0103070000d00c41300e030070000a00c075180c0e013540c1c62038140360300d8201007038850808117002130a049407642e040400703a030182005603480725078061910f6413214613140c03003584d03900c007142c0030410401540b142c080000c00c403002c0c01030a9100410381c0761900d01074000450031640c540021402001c10044c0000703940340600405090407406000c000d07040380751085408030385681c015400d0071030302c42c1d00700c3c3c2e8100c40100314600013403c0414030114080d442e01c08d1854089805030310250090120400300c03129188121340100844868590410340e05401060800076642c8152410100382c4240c6881c50040e55102c5004064a811660440300385121408100c2c040c02c0000055911411030324201c1b40c0c2d4183c480081c0e072070703030a0382e980984200000104032960758011840b0f4046c3c02c1d4003c20801842d030396540020300a041c0c0e0701400451307000d55001d082d407510300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 421801339 1250 421800089 421800101
    0x2160b0702060702130902031e011a03060c0c030c0a06140a0c080a150e0108060403030b0603040305070807060b18010e0a09082a03030403030e0d1e080406020d181104 73
    0x4081c060a03d0700d0703803a8007040304000c5900ba22004041d11800c0d0704005803802d01402d000404000c1042e0072000c42040110b00352000c548810080c08850540008a0f5500060903600442115039090703441041003141030540c0f15422240000c1d03ca50405003040080ca54071002c014103060307440036066101c0e901840190ba1a100148001a000c80c2c04601c0b01c10f8a60301c240c8100040012501c6a60394451440751113070800d0340400e00e2500840101700030715405005da8203100c0c1c13044542c1485d500c2c2c0350758040c0860103502c03000b500310030002c074580081182c0c0d64801c2100010080c00505070804541c46486c124009004601d400c2a0501c00304000c00000c1c00317040d60041e401080b10382002000405075085400c3c10384803400c804800d81c00c0c901903030707024070003503000e14020fa8011840c41c00c0c000c140b520b000b601020071401c00038501852440a0f84008001c00103d80300c0c58041650303215400c04034003070300484a0b40c0c0d4090b880c01c9500002c0b10a00c80c030960b0002c2c42801c0c4000c3c2021403204000c100c0d01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 421802589 1250 421801339 421801343
    0x7140a0e15040b030106050d05010b04060e0f01030f0303110301081b01020304060507020409020616200a05090106050a0e03030f090a0e060d0b040f0609110f03070b18010e1002160b07 80
    0x8549009031590b4907041e0090790380c0d010040d0002420036504e40c0000d562815241081c2c502d6590b42501500c9070070030340a4103015050070340600750700303051085203152400c005110240c8012800081c1301d08252003a040788c00c43d10074445180791256110300c07056442b252850410032404c0c020390803491a55001000340c504541d55034031858180340283e02480054001e0300b00403a400300341000300c80708038800c0f120b0100020b4014144e03a03289100610008070000107a0b808076201d00300d0207008102603620902028103403000f03450140e881e25000e0b803094038600f000341c415a41c14040072600e40e0074006120f01034400c0303a10856180340b00355994440403240d820113030744c82604944401d14a0001c500d2a000594010f44152018201140d642d21510216014100100e500d400004002031043c0360030300c070705240e1400850161a64500c1c00c80f555000e0302c02c0e003070104030b40c07090b4105109aa81c05001ca00c110340b00058640741d0302060000001b522080e08002c51480300c0941c40c40170842e60302c4201034078022a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 421803839 1250 421802589 421802611
    0x503030405061218242a090105070c1215051504020a031b0f030c0503040c0b090307030f06050109110c07090510170609060c0c10180602070f12110601030f02010203040807140a0e 78
    0xc2e1b5001404030250f4000080c3c141805000c100e5400052601d800d02c0c07000340402904030140c1d00340c41c030b05180f6405541c1001351507242803005011f841c4220b0003040c510303c102101c0050b41d58480711740690190607249102d603040036510307003205503007504645070319a42026564104846440000c040d20180402c1d40e002d04141c0d80104c042c000002024010201ca0340000c0c1221481e0740c0c1e0750b0b00c100c104580040200e0b074a070b45035401040104501e000360032620404940290401082d03448880c0c4d541a94820361440d00d4440d40030a1524112840c80d40240c0050484503201c12503210010341d82e030b40213039500700b254450100040d03907070000300c1d080d140c83c0c8203043c0181404040600b550b0014103c25000c101d08049a10300e6600010000d1000b800b0440c816a401e17000310603141411521007134040c81c020140420400030032801003011806a0540c0d5010408404044050004038514021031300001018071412a01050002029010f2110034008450051040752a08640e540c042e105542c0c1c01005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 421805089 1250 421803839 421803901
    0x40c0f06091208120108070f1a1204020f040c0c0b0708041703070905040f0b210709111620010201021c0e0a0b150a050303040506121824 60
    0x8900c840c075074040094040c801c404c0c02c1402004100303642e04820f0303110032a180d0002c80104030047d015880040103100c0412404c141c10b42c40f00003014180310340c0d46c840c0001b8620a00080031503889100c2d400c035102d0094030030010120b030440044c0c610100400c086d1005440440040c181521451045100d25070007001d851a03001c08042d031100e50b410182c40034080c000c03110000702d9991114072174201a00249a800300e01c40a1420501c03942c900300c1840c1003101c3d81c04c210902d041400003e00300c0304981d10a00300013111410f9042c40c985900451803805c200721540f241103030500400b1000c803a403e400d0034070030100e140220401a8202c0c071403c061018103080d45181c040c10ac3c001036101129258036a426a814050259111100007100f11224280c61000e050a0912400d00460300006040190005c40c0340c1030501c000a14540a900c0800c1c02c3d42b1884800075601c820340e035007000c80c0401e41804681c0841400305200c0411103c000b444a404040b80d030009000044200c20140c0e0030211200d0b5500d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 421806339 1250 421805089 421805099
    0xd0c1b050f09040501090f0c0e1302010e0d05070b0712020d030e0c270106030507030b04020405090c090619080627010537051002030304080a05091201050f040c0f0609 73
    0x80b02c403009000782c9076550f0b03507806007000ca400c0341800c0142c24400e11842c403d80d03040c001d0300603003105c2c0501045855000c014403100186d800059542d4588011510500b0f194100e00d442c51410400d81c002031010070307002c546a000c001c031402c0c40c955401038035002d0350a0400725080890441d159045040c5150b070014928100600308411020442c00507601461441c00440418210055080e4030407030020355100c003000503255061254802642c0125000d51609207840c00007004280080c0c0600c8201c1000290601e503039a8500840f0f01c102282d80704c1c021903202c1e20038041c050700c00448045010751101d070312004d041010005d0002101e1403104a00d0400d1b428507050110740120310000c80b6220080000e40701c00307141c1090116850303c051104904205041038240704050f1400c840303035003c1d5441801800300182265080e180d500e03019150050322003062b5000a10349102c0194112a294684828012619401c040c0c06101d0380c02103c2020245548000c1c20030030280c2c510441001801d85001481 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 421807589 1250 421806339 421806349
    0xf050909040c0b03070804060b010219080d151706280c020c0d0f0203151608130b01180b0f01020d0302070807170415020705010f030e0703050d0c1b050f 67
    0x1c0c015000e402030105294880e400c0000a03070096440c5408200c80c038040000f00000d074040c5081c031131000e02c003401e903001c3c0c0e02d6030b601d842c0700c150382000300003050105501102d404036a200700441803003e0040100181d4a00c08074650910041d0700705528040c600004080e000d00f01c01012040502000d519119860103805034001c0180462610440c09501490141940e03040811001c0502415030000386041910400d80f0700a41c1800402082030000100511440c4c24494142d100c501d505120103503035650314010001c0c3d120511300608440c9000000b1403031603815101e40c49024840d8208002c0e2880c031700b04001650036000c1040380103034450302681140c0341c4a41c01804041e03110b00c005c80d04180a99a4400710b505240a010784280400700302040120907221064150320b296001900e841c0d420800000c100c078800c0d1448800741a110008c031036070618100301d454004e68200b000e580400e1108800117048004c60360041d6008102a01010107011060041d03000b1a2002070200503d061058144a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 421808839 1250 421807589 421807591
    0x6080c01210921080901050403091203110105250e0604060c1106070807030f0c02030d0c080c010608010606110303010b161403120403030501120b0a0e120d060305010c0f050909 77
    0x20403090302d4030110700006040000079101914140c1160300c1e5000450002001440d0082220600d68140750038000445e4100541c0b0064a09411481d00301c130100b81002c5e40c80352001070701c0c000706620341010042d584420245904000c140c00a1a8003800030340c00d822600e00c40d0381d40c00d55610640403c002c00c00603004590341e2010034402c52502c0b003940100000181e10350400c1505407107991001420301c0405901c508140502482401d00d03424100c100d801290351481d00113444d0050201e50511002404910825134443c803480300003e0290300c0e12032150358040d00a504c12400801d800401c3e000824501005490580d24060121b03414607690307018040805c150203000740d804540f801c40380308071958240000d181d410014041c1c1c1c0c1007030a00c1c0c5401022504143d00154880d18441d07007a10000b00d0355103d0503000340200c50b0110b03101d1040700b2140e00744402c600151214440001b104910049280c0104007201d009030003c2190b0074000c5002d58420b500c140c44031000a00c108221035282c91710007455 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 421810089 1250 421808839 421808897
    0x901090203070903050708150106080f04030f050706150f15140702060906070b07120207050c010e03010b030d1e05032a0409061e06020c0f13090b0408040906080c01 72
    0x6215940d44e62900ba08019258000701e030315810402d06c90a030640800d031030030b004100c11302c1d0812061514181c48240c59001400060403c800140d0301e1596a20810503104156049407007001407142d90301a441070035205100300c00550b910360b08d0000314041d00400f0404440044d490f000005041c0202d90515540300e03200403603004008ec00045100e45401c2c000d012018031803030010b000d60070003503406000c410180400640003030041082c400002c0c8042518241000c0a092000c00380801100203405050344681498051003040c0c220941030f07078450b15111800360901d80003d90b22a00c174504807032503c0212402002284d2146124646100301c00011100e0080708030001d040985601b25181a45c480303a0168200280201c84001c0d00410403044400503c0c080c001452800c240002040f803d489040816202e130700c0d05c031400020070f00305030410500709602102456581c6480d20b0040016000343c02140b00c500e24040011800e1403000511007041181610742c060744030810007240b42403022880f02 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 421811339 1250 421810089 421810097
    0x8190b04050a0b04080309010e0120030709081f0e0d091502010e0d03062102101119050f0f070605040905091f021e040509040f1a07090e070c02090109020307 69
    0x10700011507041a0058083da106a005c10380d81e040001c602d9003901d00c1482c881e010741e4076104500d03043d216501100f1140b9200304020a449990f091410303580303a10154400c111a00800d02c804801c00d260a000700c0c0d200d055020b00300003882e9031b40c03c1c25540d0a150b000d00808201c40e6031061103950141c01165032002c451f840042075444000310940c0c180103a031540d01d00030a4441e0014000d2088201c40109060f02d9448216048071950b000100420341c840c0384101801a180100d41450030144200d50381c9600f44242d58800d03030001c2c54160350360505012196468042c3c1a2070300c2808034046513032002c40b02ca50340e030503042900301b80840000b0800075014114900c2454448500260801d0100d16030001804005807207003c001c03508080c04078422007030010701408002c207020701d681e03400803203801940091507691121180d02c0d2190700954910200740116001200700f2500c00d502940120540b100300e660903020b6216600160381c5103000100003035002100c100184889d011503806558030400d20b20f4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 421812589 1250 421811339 421811353
    0x30b01062102180a08030a020c0105090402090a0312030b0a080c010e13051317090d1211060f10060302071101030c140f07060606111b0d02060c010504020a08190b0405 73
    0x507462080764494180000d15048140410f00c080c604580600002e054003409945003d48a0307030000c0d00c840d601c480160601a010038001c00d9034950364103607040140081c02c5080e203140c4a0a102095260300701c00580001e0610486a035a8201400e805080719061801008604000c07401526180c00c2e013901d507074000d0180303407a6a03520a59030103164010302210041c030354500420700b01003200c4508100b840044040c01c11644115480e220a500c65040d00950321300d003030040030b000884202d0786d101c03403088044c46404148031501c04d1090900780500400400300340500c0c0d80d00001c4d170036401519005440c90303059909044095000e80c0050360b40000600e08178102c80589800c12803d40c019100d1000004000304211040010a00c200d00103481e0780c0c02c10f0300c1d800c03042c0701040b036841d80321b00600500c8103241c90820317543e81c403084c900c3d0020582c002c3c0741e42d45807040e130304215008082c00c0701c05920a05407000e00250701c060114056003070031000b49080010780810303100e151039564094030880c0c3c9031103040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 421813839 1250 421812589 421812647
    0x6010f1b020d02060406031b02032719150e0315060d060b0405090f100e0c010507060b031b0103050a05250e030303040501020a02061e01180905010e0c010306090204030b0106 76
    0xc8000d1021b030100b620005001c8884074036241c810311594003403805641c0208580d0195815005840080080030246aa01d1001e00004070f0030600d15080c00560b01a15100702180914076030319040d5244045644014001011100b01a03491010640c0c47d1010149000802c0b21402c010b5403e601c8140960380214105092501060032035a0407079040803140c1026494078510001800030f2082800108402d100b503661095070242c440704503002c4103040c031a002441600304402c9070001d010201c8000e00369142c1c18900f031480c0820840c00d104040c0040e03d8440019445551442514012404112044403034003080c0300f862841100c10114005020100d0340c1034100c1c4e5030410056104510910001d40c0ba401f0040010f072810602500005c445003084015401130845804103a0464260306082c07050700021408039801403000001c058255405e0081083c4000d00000340e10310700000070b0f641004807a0342d901c503d000300c1c0100d0200504c036002c020010400746101e50880250400320640c1d5810840c520 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 421815089 1250 421813839 421813849
    0x1050c06011811120f040c031205070c08160501030b03010f02031003120206240103140403020115050607020a090e030f0403140d050322030e0d150506010f1b020d02 72
    0x242d10080014444849100040382c09015595507030400080050030101c0d4004940e8489000501021030318501c10001018407180c6a207040003550007490340c0c01e40700e0241500030213560065000751102d034800c900000d2800400147d89541c440494205003145040c10011806000395043d0351380d0542d292607619400901c8ac0c03009500075901c0018164155180d4541406111152094003055400c1807007040702c0a558042c141d0b00921400413404000c40020006030001e141e00a0f003001103c00308010401050740542c402122011103454592040b0f503200c0401120784034a440c000d4104044140812079034410303422203004611883d05803402c14801d0603000456421940c800c0e04c41819910500040010a105800034551a8a006461898040803144100c2100804d83e140703400890303000820305100d1704002c50305110040010003c9000c17030a08045090001d2880b0800510b0413000c21708640c0140305450b5042c0540c0c45482c1c00d8007031044d40c514020b03010b04003030b03070480f0403000c44100580d10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 421816339 1250 421815089 421815091
    0x91b040b0d021308010203010501480b090f0d0c06060503030313030905060909130f080a0207030506011d04030807030902040c0f020d0c081b010b09010f031202060c0d02030601050c06 80
    0x1c1c040c0060721119460340b2182c0c0d45445602551159104000600099902c50240005803034000b0030f50542280415210700441c86422034036100b4002c80b13001c0300c0c0c0d10880034500c80c90741e4050001c40429440c0c240f00c8549500d03400d084260650301c00c42c01d588013640034070550445540510700c0001c0840c2c0c3d0f00c0c00f0a0850b4800c503503441204090b152884101030b00007160f000600740941c0d64601745582903010900c0d42c1e1024091001c403030044a042c0041140d918011201164031485c1d880e02c60342c44050185d51901907000c202e409000b01c100200741040302070b03503041d81e0308280704031824191901e03241640d60707e4012306010f080507218419840940c40c1c600813124009a00d944441c21400c44680003410700000b00b11400410000c503c42c1408034141c5020390340d1008400b0b40050002908124481c0100001015560403c8803100002407480c01200000c01f201d0142c0046110810280745c102c2c0c880808803000102c186050200041c002c1d8160302669000380b0604006240c402c50401c05490404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 421817589 1250 421816339 421816357
    0x1503130507051e031506010903020d020616260702030604021018030503070c27050702070515030405061f060305070e0409050606030d020c2b020d12140405091b040b 72
    0x3d00501e440c01c60341070800800e0401c00c01414420003504003500000c1c000040d40c48040c0c400c46274a1038032419980da039012613210204041140c9450005890048418194080032039844503c0100840008074442c0c2102c6081d40d00a014141a03aa03d034200074040c0b440075020410414000040360000065400000103540510011600c0380c00a1a1009084110360011b18080d0503212644e8135000d9803441d60a441c69558001260f55951048100c1c0380080d5940f02c1c6030f104003081d600b958400305110055014500590a440c0300c0e07580d000e00f1a034502e8101107003525401d5030500421106109522180e0081c1562902c0c8921500c200e0006040d610340203019101d6070803031014003010b0700d42040592044107090000d0403161000c40002040c041c4a41c8860203141c012101100904a0001590004642c010000e00701c082e000c0c20220102c051011029000c5400d182c0c84040084695083e10b040307500081014002d9625008a110118414003990304d40304001c3c00080707001c5c002d04d005004031b82d03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 421818839 1250 421817589 421817629
    0x501060503070803120105150a030c020322031a07090b030601020a0f060e010c0927020d0204080f01140402130c030b1201270b130c03050304060804030806150313050705 74
    0x881220941d17605020181e1185102d2241c8445201c08100c10700705480c03017855242400100c058003080e050f4114810f409560741040d030110b545013104030001e080001528000d1006580d0140250350b0f41480c40401d581800100c7e48003581001030180400045078003400601c1a6800c42c400c50342ca081116800f52011242140c13035800040b0b0b209002d11a59501c10114a01800c0092402070308542185000100103140e070305000f40ca03890428540c044640c070007c5100c04555680d0340d0540c4a0316095000b5030516594240100020100a41401e03240031f150001c01c408604a00c800340d02d0014550060410185507d40c41d03495215550f056041d18000700c0760340041600c126140a0f02003c511444030303524010507400720700000ca000300314096801100d00181c24007132070035801d20b030b101c045070b03036100030720314840020081070043e030100303441d40540e100352104405a11a181007040c0001d402c8024a01c0c914180002068083d42100c1010014000d4090b54034503610307100032420383c580e07800e018036140e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 421820089 1250 421818839 421818847
    0x50d052107021206040213090309050303040305250810020a0315080c01030b0d0f02090402030a0f060605010e060c0604110f0a0906080d112509050f04030e040b030304120501060503070803 82
    0x15040c01c0c080d0703d038180382d0780d806012a0b1401c1d500081d0308013414942500025070326041c91003010f024041c507030064100141182d0311a69a450140d0ba03440c0070340500103411242656050038494801c001c48182d40c00000a050b80c6c240f40d025000c02500510780b030760101919008100c00702c00004442d0000340c90f52101500c02c010610001400744d9807403041e0140031301d0300800818003050101c0c0c070000361660704a805076510b07191400064909261007001409041c962002d4204010781039201404560081c1c0f600003038500b4201c10445940551440704406c1d410a500140c0002c2c80e040310f000020000070038040c048641c407404124880d106402039004140d81e500f00380040c11701084400721641c0180f609103405851b500386d4689404c9801024031704807046420303140d00409001c1104000d056924402c104628007000203e00801007a41e00394085180c16814041c20700f4a8014841d500e0406002140791529215020032540d40c40c050564144d5a121408284c0d41d40c1840200c0091000e20025601d0b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 421821339 1250 421820089 421820093
    0x21606050601050f0d110405180402040510060f03110d0f05100b041a030a02121e070f05120402030f01140f06040603020f010e030a21090b0307020304050d052107 71
    0x100d03a800751929040c02000c0c00300214148460007116200c42c000c2d2000700304400c002c1441c1003280280d0300802c2d44500c10402c89002400700000461166000316024072054860421030715816045001c0c40002560305600324440900030b4020311140718403c1c84407454030025241d0101210520f148070b0382c006890b4014021010107070040031001e043c08403165440c0ca46003200701c1340c00a0704070412002d001000310021f613101c240c0754195a009485032142d400c5501e0100041e2a10303100e0401521264180c01010074042485184440f200342e19503100c50b4600030301c1d031500381c20b100c4004004076030520454541403142c500a000c0d0f0b11005e580750342d19a0040c20400c60b0880500f4008107120300451800000b0005a592001101c10701902030030001810b410342d00100341803140c5444040c24030311114140903900d11030a103881032444441d0f610180a00d0325a801403859200c260b84140041e0300900c4207000f50324040c0d0160700b84138411021a40c0401c258940c19400c6580c01d01c00c1c0396996800320300181 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 421822589 1250 421821339 421821341
    0x8060409171314191820040302030d0f0914030f160512150402060d0e2a0105030432060106090306240317070605090a14070f030201050d020409021606 66
    0x4804841c8441349551030515800031800314401c64104450031034013001c62034400e0744020310b5204900ea40c00b8800481c1082c1401d141d000d417200700d000c1d01c00c0c4460151250b05c5042c202a0250255035140c0c8010f140a414008100e40038612a606004540704550f81010421100004040e0012a030382c14610340020002200e0714056402500d811404030180380300e0b4000d06180d4400c1d811103ca54079031445283c3c200080440c044c2d83c84c82845011181140000c050007144180b000017032005022901c1c00004648500080e5070050601d82c01e08481810781860306056001e00c0507480d50300c00d20840c0c0480705460242c003a8004800300309040820310911243e030182c1030440f503090850075801e4982d1368404984a00610003d00800c000c041d840b03020383c1e40300c012280c1480d0084010320040c20035a041d44d40321103980100b03c4c0c00d4580b13200c105250174004114203007103034810503040c91840d1554005441d203034401008001000c7d820031001c41c000085101400424450521550a0048520b0588 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 421823839 1250 421822589 421822619
    0x180604060b2107030b030d0806030c241e040905010602070b04080606240f030612010606020d12090b01080a060e0c030d03091505070c0c060807080604091713 69
    0x301c0708008005451140c00380c08500003002d904002c00c1c01c2260340e241002c070b000300b004400c5c1c04c1d418000d124034160348a6101c0d200714001c2d20101c054070521140300040010030175050b001e9a00c1840f8542a00c1c0d02c0481050207004582c058401240c900c00050281c00180e50086c2c0001002035503490061090560400030803000d081041001880c25003030100880e900c41008141500c0b40f020221030601c0440300d84555200c1d031075802842e546840c1065405011750f04100c0f080d9002e80e10400000d20f01c2c075014041c1e0012110140c014203a00d04200b002141d160918114000c0c446c5c2d214602c038400540d031020307814000d000354070107480e1017005403401c5130503202c0f05989141550b02c80020300b0242e42c0d020030301104c8022541800034024034130389030414090b43c03003d00c0e0760034881c644003c00007520341200145c68414803410120103c5519158240c0e42002c050341d655001494100000d400d904040e403000c00d4650040001d0b5100b451600c4009507545c0c45210b02080d40030791000200480c070b091303031752031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 421825089 1250 421823839 421823849
    0x4030c090513200a090f0b0310090323120403030207060c08040b150a0b0d0e10090302030f0c0a0606140a090501050d020126090102190f080f0c0918060406 68
    0x601c001482c1d62900000c0d00c030840500307039803c0241103403101603580c1c00c02e006006000f284018043c080038015403400900348441800d00038015403403802000c2c0c060f40704400b0060790640300d140301c0c17555900c1152402c2d07420381b04407060722400300950401d288a02040038441c520958000d42d442e15140303407441c1076540942e01c07034080c4202c00090200080b0b1031200700354004210808030941c411038000088251869600c13130040c0300340c005006003608605402c4007002d110401d044449901c0c42d450200b0403030b44c0c008030140061300240110000101c03400010201900007108417102d500d0300b51600707002c0b076611754007400781c3d8045610000401c0c148030801400600030400100701561400c03012641b20352071101e000f410004102c1e454541c0c244204110100b242d20146c404807070b85844000300d4000d51200408140d43e8004250140000e0300c00c05060f16500e00c1551141c0b841d4640c03d200200e61107014080381c0454006010720240c0391a06001c4c0d210305640d880c0d105003141400c1042c00b0071544903800c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 421826339 1250 421825089 421825111
    0xc0e01030b030d111002070c03030f050c0c0d03031118040b0613031202010905150f011403030d090201051603120e010605010f050d181217150d0809040204030c0905 72
    0x350101d0b0740109100320007500604152440c1448448030b103081421a140304c0107024404180c860511400ca008403081c0c030300c00d85600300100700d02d07441030360745004e00440c914040c1d020013160030290034401115041140300b4100851504505100040a904210b54401e030b049504d0740c0707442052400f402810400001a5041441c1000710b512507201480c141c08058080803147c0300220f0640d00c04d5102081c2250404c1c03d035050303841000030702caa05800aa59400c0003080180c0007007030310200d021858100b04001001503140c480004481d00c05001001002d0307050003020b0048081000d1420f000c01440c40c40f030f07514044000d400c0d810b024101c0c0c0c003402515001d40e24210042c02941d8015032456034891140c02d1085e1039503000c1e04501c01410442c603141c880c03c0103807403180040015400891114030300d82e0701c500612120003181c07855a504100c80c0c2c90a01101c50784c2e82c80003401c1407688000320381d000b1120341d480c0c0000c1c070011074103a0740164011240200303030000c100007030302151013619044400490 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 421827589 1250 421826339 421826351
    0x3040e0a02180a120618020603160305072d0207030b0702010905010e0703050304031e0503040e060f0906090105060c0102090303030412080c0304020d02100e151e270112020d0c0e0103 80
    0x41381c5201e184c038a5000800042da10340c07a035845458401981030308030303030f005180359070fa8505212409910106410440c001c01d05100210313006900501c481c1d1311815561581040e403101c010b240300a1003805106420a50146800c08000b042d0414003640c4100b060750008903041e6002e2070b0003821103071a68079003581c0740c0060713100f800007801c00b00c2100c0443c3c0e00109040e010905510101d02c0101569030010140e00c00010005404e200c241c102900c035074400c4076a1080d0000680900070704c17410031505141d0184654005200b60b20308a000340c0317003280403c0c00040c140304c2254003280c5540d105850a448072135170403200503e1641d0058010340d101e42024030990540c01c1540c003142d4a0080311030000e114a81280700400c00d28828601031041c890001c20682c1010900701b80d0000175031141070501e40c06020f100034107200b1702140084945a1001e54280d0007044840302008520400002117281000b4012407170102d14001070003e8081c480e0180300c0041d11040baa440602140c2c14210302506040c2000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 421828839 1250 421827589 421827599
    0x4022b05070216150e0316030b0403030e1b060d090f05030408060c0c0d20010f060e1b072604030308010e06010924180f0503060a050906070309030203040e0a02180a 72
    0x1030780c441482003c17170404c002d48604800019017803450201c0c01c007480c1e50400304008280201000003500650280d2010408420345551058440c002807103d15003a1300c511800b40154109800180954000000c0000300241155110010000e0131002502e00780e0011905002c219024080190060b1030300b0150380c904442c0c200d0203a1104420031080b42400451584000ca8201c1651092040e0880368020001e8078440400c500080c4210f0242484180b00400010752001d405460302e98641610800c442c10a80300b5a106d503000a0701100c1801200021803400800c1d004150203072001d036200c1d07110030340258104031546c20030800080003c0c1c10018800c0341085031450f159844007040c0e103ca0200909210701e668140c5043c10401c0c03202c1c1c4407031031440b000501c000072840b500c0151041102691001e48600d0840c10541d01c080c1c41c2100950450000710354154020b50080c031081d0710a0054900b0195a024014200d40040320203025107500040c402e101d40382040288002e1000490780102917500788 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 421830089 1250 421828839 421828859
    0x807050f0405090703172a01060b0a020a021507170304110d1707030908030f0405010909020f03011205010e100f0b01021203190f060b04030b07030501031104022b05070216 75
    0xc4d10014011140b1a00d03e00c1006c11020200c60790304400180740000340c00ba104c0c801208204e40416501c16518121010882000d98811248202e949a00601ca440c03c0c0e5003c00110408113014860040000c0100c00b0005a20069084000145c80702d42612440d00d41064183d00c2c64104005114250845828000505444250034020170f541001d17500d644d024a004c0d641e280c00c9070041d4449110101c1d802d200130103400c0040003500c400707903a46003810b40e8a04034102640034103003881802030020700040c440c2d4401c0c18104800341e4042e800208081c4200c1d84824104a61034440a000e01d0716040c00e030741c0703070600781c015010120400c1c40180a085c8910552517068000945103c1405140c0b6508013501c414607048203401400507201008842d60341c080c1d824695005120803035615151000003000c00d4040c0c820181241d41005000c40101450400c000c000d622044043c10f0070b41c00d40c411201034802c40168913010841d15040010541403100c806490420203010310403141d0001c62040c0220202 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 421831339 1250 421830089 421830103
    0x20a1808060f06010e0405010803030618090a031404030b010e01150206040b0c18030f0a050106060504030f0f0c0b030916080c033f031603023108070807050f040509 72
    0x805071941c2c0840e01c456004072030007644003410980c007905080c008500c03000d0200040d4059981128014444244200d091344a100116100c0c516600a102d003880403030301840d1110342080080003000d2401c0e440360f89148408600b0307001349061484450061216040c09103d5008042c51400100010320b001c0d502d20422490082c8126400140454121011844c107152784441620040a403030340d074140880144e90720003d2103001d46480d8201840041c00e43d00800403501903d806c05c10503540d103025503d400841098042d0116016450404001500350f008c502942c001d5200d40302500d00440202454180459160002501900014050300c0a60380010b103031490140e01c400840d28000c0c6800a400b1441c00c0c2010305c400340f0300c2c4820b82103141c0349218010340c800d80c03503204aa461100d090104400702d00552840c803103d41c8a1840500c2c104100040910500340d0683e2140034407515180d81c1800e2004580c044000c9034000f0714244480e01d4012010200704000743c500300114604221000ea032441 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 421832589 1250 421831339 421831351
    0xe0a09060c0309110411040f32010f0302071e03020c0901050f060d1a120313080303010e0703180c08010e0c0d0206161703250f02120c070e010306020a180806 69
    0x10b5281c1642510303450070020341f802000220450503250350b071400200200085245480ea0040007210600034440c10203513141074954040c2e44540d084510304509600944c45542c0a84d5000000119003100188224543ca080c0e03100c3c2d800b40042c00071290034400c1c80354040e00a0b512a071034031400e0701c0c095125582a60a801403480021508903401c402c400b00320032111140581000c1d42540d0205500c20002c003c02c065440e9603100e9042d41e54850701c4070707102d02081c00b558100303c0c100300210f811284284c1041d4040884040b4171000041c880e070b80c0c6840220390f503000d41e00603511007440341c0c481074081c0724010700b201050b40e100d801d000030341e030015486102d04010480d8120000b00e907001400411580324200c1802011f20356034a003001c241c0c10f2840710400400d440c00c2c01140020010042c4501c008080e007071030301c4e0010403d10704000c01035035040d00000c912124a11070400000707030728002200c6c81030096001d0400141d65402c0c0c108000c02c0b0100e451a24409861000001c1004140004078154050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 421833839 1250 421832589 421832591
    0x1303082814090f0303040306063006020a0e0306070f0905060c030d0e191a010501050c0c010e0105070512040501111603080a110a0506162a0501060e0a09060c03091104 73
    0x4107800000740c1e80700c480c0460507804d4480418080200300302c41d80f2074000d4820080612890811041c0d8105480184a41081e514488201d800b0b0000ea07040e0041c110095450801d10300c40d00907080803c1c9041400c0f2260000a1030414054204941080d00f41c0c0c045c0034250740c164545600748481c590b4038862510382502e4a556250b46c0c4015090a0003540c0c484008100300e02407089a604012041213000140c0181034001400009019030045003162004424080036001c548108001075590080f403681c01410300000b0003c001c0004d00900ca40302c0015455498203840b00d092500040c58480c0429560030603a0018210f80d0036816900c03e82c000b01c0741e1000e0304613954401c9420440d907440900494001da80f0502011004010000c1200d502c9004082500038081c41411030490b03d0301d0b071002c180181d406402e0555030f00340c0e0031039046203032aa0050001091703850340c1e4041801401c2003202d010005594485c00c0340308229250007081c0e1409507d01c0c0a02602c00940c40744001002882c512a10075 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 421835089 1250 421833839 421833847
    0x60b10140a030e030307030605030c04050f0610030b130911370f06110d0e0a050616080a021f110414041b0f110a1a0c1303082814 57
    0x400d1083d0002051000508103590300c0742405100500a000c1b02c0c043d075846400390720042001800c261003000d00c545841c074126003060f01c652090002c00312210f0b40e0b140070103445034000d10864480c400259806c80d041200040e0781c4525090424604083d410700301e11480480c00241190700b00e5136200350f0208507c0d001d2010380c15418602a0002c0803680c8421104501c000c400200d09402c0300700c10b407088900c00f0a032441d980c81210104c4805c0e1106d0794032584080844000e01140c1416000b6011104401e01c43c008100318948030f110090304800005001030340710b40010107080110001071340c80c0d181c07000300034804a00d001c00c000f121030040d0700814051900c046c520040b142d4881d004031140c58120900d104060003003981c000e04206401084030b02040d40040f07680c030404d9001600d038041c11f4000808011548147d03040b110049000ba003074803010302060160f004803801d0b40c0034082c0210310402060b0754078802d107410740004007000c1c10001d41c0034860302c2c5003070322050304801100b10006280000300c1c0e80f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 421836339 1250 421835089 421835107
    0x170612060711070e012d030201051b010b04020705010213120203071208190914031204030b190f0c030b01260910060b07050c09070e060304060b090a09060b1014 70
    0x43e1070380d603501070000da061a80000a210040c0301184a841504a07449031a508107200a220100030903c0001d00240c0204038074180c4003510f641d04210018080700200c0c070884158001401d98221017010385190b5400289008110a6054540d00901d4100c0d07204c2d90012298000a441d0050740c0710300c041010b0694014000c1001c003608a0b0b41094030304501c207802c0c1c2003040d0028120360701401040c06008034218081c0103072900007083c000981040408500d4079042d0b5803a44440c0030050070f128084005951030300c134540b20354004c550b4444261040061740126540c0018203440881450b80d041c0041c8840c0c100c5900c1c0901c0040c0441c0c140c42420311040e03150307403040038a443d40780100c0004032071a0100101d5203a1540340200b01c0a03015800322980c0c14280000c026009070140d80340343c00b041e60070000c401d1a0a004001d11740c06406010300050a4010750045521302c5002c4030090603003641d950f031800c10042c980c03203070264503134042d16149182100d01c1405811040c1c034101e48540303d680811040300c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 421837589 1250 421836339 421836343
    0xc03010b1605160503120702031002091507060b040b04050c07030c1403040f080d142b02030f0703150513020306040e0a030c03030c02010c08070f031407170612060711 73
    0x6101d40e803040031105103a024003880b40d2440300500a8034468061051000590880402510b40c000e400078007a00718141d541c60408020340c0849a041c2d0400002003403491044c0c0314030b001d429103a00070302c00400d884450000300710031604040325041c4070700d141c50305001100c0f182c0400ea03488150300d81443d07c4100823030b0622207001d4a0324034101115202c0098007003071a406d01103444040700c6510003100c0011010440945c0c0801c0401c2420302d240605020400c01c000e00100404811411014000030214007440d01209a234800c13101031200e10840000e102e00c103541032140e110210505401800c102c0d090a0001c2d02020b2a0a0381045003500407001c03404075515540b203090300380141c6040340c13032000701c0346409480080540001d8001c00d14103140d441c001e60042c051031003458156500c51503103a9800740140d8032108903112603000c241d0713520720800280b0050b0004c0382c0650481e40360314110140c0f182c000314000400901490041845900c140c154410024481e5006242410100020b07810650064 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 421838839 1250 421837589 421837627
    0x507090c080106090923090106030302120909060907090b041520030306130f020a080f1f0510050c01060e06032401051c2108070206040b0103151509020903010605090c03010b 76
    0x10105a60f021b092200c8046c0542c42001203d110b0740a4a000041d01364101c002c0d40a0000303450707004103414000645501d000d0b0070f0141c0c08102070500906598031208080c0c0d1542082c0c02c04904402da140c01d003001107030442600a44460054807440000600117030b8103840e4003000d01040c1c00740d0f15080407040100c5c60b60b00701b00040071004808544850b00c1d10002040f14000399070750043c0e04030704404141d104020b02d010100050312001c2c08582c291420b4148800c0c01c2c8405244003c119082c490410001c1003809907400800f1000095641410020109410f01c14255883c03a041c1c1508400c815008030403549035411503504840447d1141401f03101464151020400105510841f00e00200326182ca2a8006064142980c07284010354540c0340c1a603441c00150b078050703c01f40003400104005a03200130001c2807440542804500c0750034010300d0035801d41c83da40040c0105a008035400c180746c1024429a40100b40c11507210a89003010340010b1260b00c818000c2074080c503000117040112100c146401c2c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 421840089 1250 421838839 421838891
    0x90604030f060b18061f02190c061704171b031605060606130b03090c0a080102270d120323010503010e120a0f090506071406090303010b12061c0507090c0801060909 72
    0x40e00000c000327407a200860036501d018190100f060305c045103144046840d2064851a0711401e006020034010352044043d4001c1d04480300300006400030128200c1041c006050038440064602ca6041c1c07c3e4582103051400082038140904400e0000c070200440c1c0040b50022140d81c1d60503580d41c1c1d21401c2d8076604011100c1a0304e41c0040c010000054088015030040107000c80c9503410313140400c4a011410580d40b080d421081d840381c000c6c1070007000700e003104003030600110890030000745101c0c40b124200c0c065094189508460a0268010003860400303004190325001903101a15010581c842108014040d04240700c007041100741c0140c81c11400b0340042c9025000041160f6228940c0d4035102c003c03580c1282d400703e103900800c0045606807000005990590f483c040615040c2801c0401d01c0e0380d1250014036142d4480790241940c1c0c0142c404074030b21501c0c18002d401500086041406480695603220880800c201d80e074001040456441942d803016103101c4900450b280c401d41c42841c441c0e401040700303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 421841339 1250 421840089 421840123
    0x1050f0a0320040e06090c010c0c0b03100e09070509090c09040b07090b0f04060f020a0b01090905010207020406080d0f0e180405010f0f020a0f020114010902090604030f060b18061f02 80
    0x54400050b0001171301c0d038424007060086407200b1800800450320844d0319a0028143c021007201130102c6245c0703402840d80902040500403030f803a0368440b0411f05000c142c1f0740c0b0000ea0030818041c407083c10a203003d5948080c1c0c2030011700d040140d2602094038a90000c0019010903650804100f00754803030310101c401480c0c40012281c80c0c01090b1000c6002c1d5000d841243c0115a4103080000c07064008106008482c0c0c0203500988140e04c4c3c0766108000d4201c500c1c00b16120b5501300441c000690711481000017400403a002005007050703040001d0f22890007041840c0500105107041040d986d0748040020b901c48681c040a02c041d00c617403800e107001d0032050010300805800d0640c10b07608800c25501604852a0594501c00100c0662038180d0032130710f6284e407140c2644040f0700140000e400d2a00202400c07240500228941640da80f203000c15029850401c80e2510746500704c0b0701042c900001c1030320078601100b584e456641441c0c00007070400560400401070a4440c902d9806085001388800b440382000e01078 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 421842589 1250 421841339 421841351
    0x80a020a14010c0f02010e07170124030b1003080f0a110a0b1f120809031603060203090c010306120210090f06050415020c06070b190e030a02010501050f0a032004 71
    0x201d6029109107030015000070650701d00391110324814000d52810042c00c2000d01045c5040c49411150450f28003c0903c96640724105c0c152a4002c00ea0201d5204160901c082c503094110310b01074a0302407001c1d02e0f514011103018400e00200d1500e00446d0b00c3c7c10b00390382341c03a6507071203143c1ca040da1a905c0446518400c0e014415120003071096482c85148642007101c54a0100c8541d5650b0007440d002134000d007104013000501400c000741190f402401108401011645000000d191a00c1c030f504264000721420340d008410f001c0c284100b0401801720305000d08041c0040760616210176401c200c20fa002901c104140c0f00580b0702c85000788112400380c09d040b00032000a544442014000f94800c1c4100c400f01c401803246421000c0c030106000c0e5039202d00400a610b08003254076028485880946048101e003a0603480e6070f8406a81d100d240c00aa5050000e0740d21000340c240c000e401c44605902150295121a441807440da64860020094980c0413a20b52503d070a4541c507014072410788884a0303002443d201c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 421843839 1250 421842589 421842623
    0x130b030406110d1b0302040f2c0907090f090b040f0c1a07110301090f0b10050604061205060102160b0a050702030a0b1b07030822060c080106090e04050703080a020a 72
    0x1070882c2c1c80c1001561501342c40340d07900000c114100c3c8100d10401c4034508443e0001d1019401900da94504031042d1521124241003040030b0720184c0e4816a100c80a03503000c007a08001d402c1460142c203a043e0380303000041180c4000b84d12165074800009000810040240e0760000401020322081005080c1c11101e45402d124040c08040280d1720146050750129000700c001141032905000d009000d690200c0d00700f00c1e9020b650b13240010100094490541d80c1c000140114668480102030002440551354203041c455030700c2800000c4620190002c0c0c1150491605000510314101c02c0344211661482070a5a56014400440c0c1500604400940c03600600700c00340244040d90503002e02403040c3c681c4000e920262000e84403482e02c110640240841e180b000000c980c05080b25408440c61a491441c500642d82070b602c1008680c87d100740100030410000044c0b094640c031039a5640680644010403e184c1001e4985603990440c0784001412214009072a0a51310f100388007419909512403407980311400341d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 421845089 1250 421843839 421843841
    0x60103140a0507030f020c1002030403110a0804030c06030209030601051201061a0c0c0a140603071b05060103030e03030c1002070c1a12070512062e021006050105130b030406110d 78
    0x583d082d10001341000145d80a01d0190710131203a081c00d50310001e01c010740c0190b00320006034200404c04c0c2e040c0700c04501840c81003a010f00c4010b24a9201e046819503840c00c51618802180030343e0012020076205000c6a040f41e00c00056541c191802201c3c2c2c0002120140d4145000d001ca42e001441e40e4003511010345622941c6101818012030044103403103216080c0780600414210910034141e81c001152001d414908001e001035030000414a4030354000c00000e0400407909001501c2214103600103001041403691141c13071a20000c3d421009140b800b2100c80400f5620b100514034003c2c4643c0c000b0301c4100b00541c0c07003d0f2000400024000300c0c1e035019140408107507070300030340c50054060840c8070024150360300c1081250740030019540c050840b5103841c0e0602c40d00c2054a03c4580c040794020346425140c00059800440806c1107500509100500106c241e041e5201580100e060140038800b40e04d010411050980c01d80780382a070001d850341d03910b0a208025200c1e85558011032080042c48100034a46 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 421846339 1250 421845089 421845091
    0x22515020c06060a090e07140613060f0806011407060f0204050a06110609010207031e090305061303090e04050303071107051008012d120303021b0705011421060103140a05 75
    0x10407159880d010b591881741c2415512201a8006160820003050001c0c2c10003500610451401508881c10302000582c00503100181c2d411a5001c590719a402281351035000c402180d008400f0300c1c1804480001c0c24500c4098007801c000100b04036100e8490100141303081c3d059800504009000c00f41041d510074001d003041c41c020054140034007413400011403440e014021211a29410780e214a4138040d0402d2001c0160102d5200f5400c001c0c0702d0304000701180c800c01c856400b40103408030b000a0000c103880c0180c40c50005a04c25010354150b0b0781040042030021054039401465420704203411800008034506243da41d42181d5800400040342460550703000003454143e841d0b01c0c0003040440000e118070f107100480d07c0f241e1020780f0041300c41030140888004000c0368080c441d040250070901d03418502170024540701c00c55003860340440340800140d82e120240500320361003520491701c1c1000e02c1c1e8600f225002070300f402862404500010850070b034400e50044065407401d080f510750b2800d00302401005000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 421847589 1250 421846339 421846351
    0x3150e030910032c100e030f0f070c1403010b030111190215040302061503012901030207020603150906010c080d0510090912140405030709050c070c12020112022515020c06 75
    0xc1100c03161780714111648078604620305400003c5003011b107125042e42c40e691040d208607035907079401d02003040020300c0090100c0141c020a0f526a40c0c2c1c80640c42414210340c4030514a070300c6a030500b00d04c1415401d03840c0850f0309030b1221501d001c000b040030040c280e02d0000d166031a0000221308904000a040d80810070038060309840b050304400358060000c050a84403c8015580106c2611f004000a03d00e0403041440504040c14090309001c11a00040c515070000c803002c40f105030801030411a1807800001301a4071050900301000c940c26103480d00103440c001c2030b00e4050496602c80126400c1c10509108000510000b41c003448504040c1c90301c1b965083c910004c105c0880c40080b6001029010441601c00b03552003d00248021403400c0056805460090540000d1620801003540810740180710303180908115030a481d401d04e0300380700040500030071012003121148180100e44a41400781c1c5030290305504511070319a48102130506429040801c841c08024a20000394207400c1c803800724469100d88 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 421848839 1250 421847589 421847593
    0x5060306100803090d060617010219020601300602070609020a05060a02150a02040f030f03020c010e06030412031d0c130203040c05100507080a050403150e030910032c 73
    0x7840d20004901d600034940a8800305400a1003610301c0f9007018401403065600079400410840c0c0d86840ca0300b4000284948110a6500002c40c800c240380d0b609240041c1740481d2000344281d61429000522400030698181c05c2d0300a0003000341d1000160681c130712100303071b0800c60031592040c1c90725104008280c030080032401521103000000702c03458a40300f921407a10054000d0040c44400380300704181d180c00140001c460326400d100c0400e042c42c822921380061442061401d8080c0003a04010349096091800a81004654414414070f51952015250070503803120200a10718450700040e009482c54a1920340207114200240010120000740000d10b1401038403140900010341441c60141d11040710301030202d2040001c10002810010312100c442699460030505101d642e503240300d036a502180f0400000b030000305e000d000303000d01c030904030182c01d010f4a020000803212250807901d038069259494403078003041d58403600d0980030f0b41204007130b8000c2030310400c408402c2203055003803103204507170038503840c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 421850089 1250 421848839 421848841
    0xf06050c0f0d110f120f2a070819031205040206090411180f0d03140d02030702031806070f030f0909020c01050106020c18060d020d140601051005070b0103060905031b0105060306 78
    0x20000c90010312400b500d80309a440c141040b5969645940b01c101311301031111144885002e03e50b02818842c0786031f40c580015001561038a102185008842c070203012403000000201c00020341c20181501c019a23300c0c1010469544a000044c481e016081c4a0798009084c0b6021100c3c0d052000014543d080d0447c00c0c041d007420384401804150345000034641c0e0041982c542c00d6010a0140704000044544403030214908801141801e0580e00151100c0016903c003040c00d40081d0303000e015000c2e1100c0180c1c1d0203818880e880d2601c04084440c0640501071250240500070300a208804078005003c00d13580940d901c001c4940242d000300000d2003650014082d481c02c1d014940707000180d040c91b002d03030707000e20989541342d0074100520f080c140682260306c0201c0e00000390010b2200c0c0c2d884c5c0040000540074041d00e40c940030500202c61102d521200820004020800005a19200c11815a600584002a031080fa07140007840c40c1b00e0500400e001d9199070903a0258441c05400152240005034251101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 421851339 1250 421850089 421850113
    0x3070c050d1701050904020303160b0604050c0903150a1b0e030115050303040b22030605040b070203130603020d0f020f04030c05090c04060c02042d060e010f06050c0f0d11 75
    0x1540c03120990b01c20071684804010001c600d003002040d900503000400741d030324060b4409400d1040311a811422601d08010104004aa160038842c0c19480550240050b241c0005800042d81320f141c0e10b42c0d241103001100c0c02240c08842d41d0b52026070001c40c000300014013030740343c104050711410140f41d540b4447d60034029039200401c89441d010003108c801038011400c0030704096225040f50401258040c1002d020f1441080050054803070000a601416000940d81040d040c16194004020401815988104000011a110301d00c1600c115034181ca00182c9506c1c00c0f4200d1008bd150980888045500200300480900480300042041b2071054034192070480d0f8a00034000305000031115504110824441001900e0041c00d541c5101c610042000400d0031190000d4201034013501c081041030f841120119804c0740d03903841213001400c06141c51400703540c9090341503070003820300c0d015030350801c80d01094450040340c08000c1801182c0c03d041c151a1070807892003000b4081c88890121056510881032801a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 421852589 1250 421851339 421851347
    0x411030f030d0b190611100204030c08150405071e030203030c03131403030910031404060f0f050412141902060601030605010302190318050f030a20062a03070c050d 72
    0x7412080395499644c2d49000380c1684d081e075a91480c10001e024014559091100903c0200069489802e240c42c801303003003414092500102c107140c8100742030108180008901c00017500e40444104564103151100000c0751010440c1140d40300035054403001c50801140800030010788817403400f10664081566942c0c07003d0b1000b048000007160590003c0108481c02d01306801c415520f40390a06000c200c014060f420044000412501955080e540303c0303c0704803421540c041c1080c0324070b110030140b0940c1441d03100da00e006015840020f00348058021650b1851000000341c4d41002c20403503a00b603504984050181d211502254002e000034500140440c044d8003034803c0d5200814a0703016026052046403040c1c1c02031a04e0001d401d64290403012003c00030354100608424002d801d405141c0394008032101405821001008001c42c0c101c04440d442d955100103145d641c03100101440c1d1640450301035025501e484003048091341c50600001700201c16030088070050510703110b0030403158166035500c0e00311 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 421853839 1250 421852589 421852609
    0x1d06010215040b0f0a020f0d061e1a03040516030f02030c09091b0109080703030509090f04030c08030606160b0f011a07031202160c030b1303080703050411030f030d0b 73
    0xf8401a04400829040319460b90010740c0690401001450071074a414903000310342082103110400c9841c0e201c28010714039440c040041801081c12580d140a0400008134182c0810021845c85d0180200000303046c00320801038245000c0d400000400f1840d100e05201006000709075040e4000d200d440b400d0000d5050000d680ca1103500918045c02c648400502d41549042c26058050304104c140784001c58514001e0100f14015440390315420f80e5807141c50300788185130303100900c005100000b002c20440440c1d0040d00c1000032542c0300c1c100e0359595444100280c0b407400360a07042048011220000300810211040d103d000f070784400c0044c2a1030ba0703240c44030707041101d08024134286058140321410001e4010100c03588c0c20602a100036041030011846000c602e031544406560181c2c0c50141042400180e0910980102ca510070420070f110040d1070281400318080c06030010955510001002d02030281680c46001000805803265022125207140e92504a40811020300340340888003c95458052030701 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 421855089 1250 421853839 421853843
    0x1605090c0406030b0f040501080708010f02041d0c07082a06012904030501020a0e01170903070f02030a0209090607091212050a02070f030305040e0f100306050601091d0601021504 78
    0x4207207810b0030304034110080c00304140d116810508040203a00329a07a18001c41d4043d0100d5001402803030700e0014060700352418080d100c1d402c0703031041006028413009000942c00c1c424603402d100d195611400c00241d203600c03c408001c2c024610108900500c10041001d1151070285c4c507400f0201c4500c444500c68075504203101300b038100f4490030701d00144095200d0502107049060702107903042039640e4403041d00faa40010100342c0000e0032200340340d08542c0c000595415142c00c4007034440082c0b420300908c640d2441000e4001d0071503c0003002c0c0804540c0c00704010302c2c025601501e403540a007008070009a94500c281d48460209800d440086508519140c001e954680c000c926100e0b081e42c1ca420a80e41684908000341c1140620007000c55140c10307180183c4010f610a98405036901d184c160b201c0840b500240ca01d100044203c81071020798454159080e003903075040000001d55440f1b560050355051002d5005100380e90704801c0c000e10300400c00d403459200704820780a40703100810341030064800c0d503021100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 421856339 1250 421855089 421855111
    0x80a090311090f0726010906030c0609080d0e0d020607051e010209010e060a020a020d080c060a0203061e01091508060a0504050108101a150c0f120a050f040e09160509 73
    0x81c1e400d803203209000b60745507020386090044140030083d40c850307585c00d0300031011481e2656410003c101d071208900c4000c3c5040d10b01038a03980d00744641540c42d13941c01e8000b54200b08074542c05005580e1140c182503281036008061030382c5c80038145000c0b510f4074a8200d41e8006d401e081001911000b106008a42c00c1c0e0390141d4503094403541001c208400b03034024002e00382c110301c58074051100584520b80640d803400e001e00314607601c60342c5000d0000d2070401c00400b00c9603200e0040c8140843c40c2c6461410205d00e441aa02e102400c0740c1c4803004a880f00c91070b81c8842d5500b098003410440300d90300b0050580c0074100c01d0382c1c46581951604244001e4820a105828060744150030f0140280103680c0302c5884000f0701c16411440943c2d440005041c011002400260740c0d80003d1f0301c006076201004900480d0f0801d4014281b0301d8501454400350303001c3c002001303060000c0010203c110303640c18011140503240380960307034403541011111a540d640800e45062000175401e80f000c200c9203405240716208101c6103103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 421857589 1250 421856339 421856341
    0x110c030717040f03030903050f0d0e0d0614180f030f030403181802030604050901050709061404051906020d02010209060d23070e03010c140f090a03080a090311090f 72
    0x2907400340ca050360001c5468010014040421005040c0c40520001c50083d030b20400d920b41903052190512a100840d88401e034000440940b80d6600100d020343c000d03070112071503201e510090401d000601408101c502400da03442081242e205001d181c1d550320607240c102202d42c1424240b031442c0e500c0c411941800e0400c40140005400030b4850500c6014020010001405440e601c3c1c2000d06441c00304082c20030165008400c1108030f041c603100b1103038030021200090159061265019100c4016400b03400100204059020300781c0452a00f140c00520740501124242e0850b417048100442c454000d9a005004814400f0b403482d1050090f1034154100504081c0b0f4520801d4041d001070500c0d1036072010134549515141050384110304064440c50f0f898690000390042030040508503211134018800348030a190f4030080030490003003a51180105610840e5480f40b0302d10005d04000717410350005107400d200180781e6150341e91005265086a10403a0420001c41d681c904010040d2003c840902100e15554 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 421858839 1250 421857589 421857593
    0xf0105090613080d02030f0106030e03090a030201050c01060503070e04052b0c031106040b0901060504090807020d0c0305070b07030806090601121a28060c050a060504030905040618110c0307 83
    0x20040814080c072a43c8030b030b4a040f4884000c071040c1e130412146001d06c5080b00307004000310740e0540183e154288840029502d0000d0340d00001d20703107685502001e4100880401c05c3c8402c20000d40c809005000c1c010111003030707240d40c0e2140041d0304208640482d220f0044800d129603030560354010342d03e4042412603031501e5402c80003013214016020002541003180503c040140210305000580c01a400303010241e07031600c4c03d00450303030940d452640010f000702d00c5c2420f248086500c1c00300340d440c140c0d03045a0345031401040c1c1c01c01c00c0c0c03e00c12540bc082e29500800d0381c0095002c080784020075501d44251a035031aa075442d0020804120310864825020501d0140c401c50360020b40d60104120240110a4580d030f031a01d00045250014500e442e140181a104280b5076000041603060005200c103160a08004000d907407229261812000003c00e2140ca07100400c0405d4012129400940000b41c001c06c03031269581505594000380c1185504c1040c03070310303018134800040141203618101841c1b0045190400072707 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 421860089 1250 421858839 421858861
    0x201060f1a0f0307030b010e030c03030d0e150108060a050106030b0a180f061401080a1116060603020405040f0209100305071404090f030816090315020f0702030d110f01050906 77
    0x403002814103500400642202e0b0780d0800245000d015542d800007024103100d000034006009524040e40f00781d0094032040300c41e640000c00c80e01c00c980100c201040d1151051103091a10180c0218074280300844800031074506000a1041c0c46a107038103500f8000c81e42d80c0c0da0260200c0301c00d542829005048031078144101c0140050000c4101490800014860382c5000c1c143d080340e107590824003814181d003054031b05540e40f201903107400402c03080d0100b105010158050300d040c8240c10b84583d8405100301141c081c0511a0701120046070082c0050101d85030520388100b205403075100c100d10499030781000c18140c0f9031356032a0f0f1013034941c07040c0181620b50078501c495180400109880d603101d5120040000010130400d0002e180c2882610303070040300c2c20810b03042100104820001c0c01003204800d82003002c56042e0261821322540d01100581d40c070700c003440c00035180c42208406500751265807860340c040bc0d0300000303100a902d00712040d14100c1c0c4401014070b099483c217803001d07203d950080380420081030035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 421861339 1250 421860089 421860119
    0xb0621061c120f02032a010e0303090a02221e050c07030804201305010f0506070804060807030f09200409031e1e020c010e01030608100b04020d0608010f0c0201060f 72
    0x55004036424552035100f000f051340884080001486e240c040e180146000034082c1d881c0740c040c841c024600354503000f2030303403943d075210307244041d22840a1480603508040034007110002d00708034000601100c14100c0c481d10038103101d00560400c49181600040090a54006540d0740c00d600d983e034201c0b113490b2034a462240b8242418005002d4529550041a070f036500e0f2061180c41c8031001700426203614003409554110811352003d401910100440c00000394480e0480d400c2c1c1d030240c14075510070345a060044004180c41c0555214003841c1142d0381d018407501e064003043c2d400000c3c01d0890141c15540c140f1013556495400100800c03a000950781121003140b07540746404d41245011413040c0100601c424003a00144100d401603000740401c0c003110b507401174480515503428242400707000d2a00380707416546c0a0310b42d41361141c0c9948045205c00c035540d64046803c4854001001e024260f200d40c8204e00800988141103040c0c1e252400e00140280180104022600105032210350940740c80c4400f10711007a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 421862589 1250 421861339 421861367
    0x7021b132703080402030f0d020307060c02011409030909060a0b041202030f01020307050406090e010b030411040e0f0304090b0405090a121107030f030e1504090b0621061c12 76
    0x81c07075240350401c0e00360145141d18180d010343e4500702103050074014141007028410030000250082c5914500341900041140c00407a8090700c0080d2520007c08124010030324a0b101034507603050401400f6001e4030000c0942000c0703004564034491615108100280c0034082d00c10b00d203e42600384810002840640b10003200140090141c80d116240062520700326801240c0d00404520045070a110560b80811743d0790203070880300010240d0754101364070011140402800188044240685401c0f540c072950050450820203008031038030041d10100554894005004191485203080650f440c1c0b1300d418018240030f294000064629080700740c5030b40601c0340c81c41c280e40c414413408001c0365810320020030804008601a0307100540d03001a80c6002451150140411886102048002c526400d0701070708983c1283d1902c0c00003c2d1800c0d004002c55140d02038400030180040500024440340a55600300f54400da0b02101e80c1c1c080000010082c1e898820070400140148883c42c21084446008038135081641c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 421863839 1250 421862589 421862621
    0xd050a080a0309140c030307020405090139020a02150901051c02040906090507080601080924090d11070608060d080c1f0902092703030f07021b13 64
    0x10015296015140d001d00450720000303a90352521401c2c4001044400000c01811001e0101e80c5012000a942c90103951070203845603940c0d001044180409520410350390181220103a55030001088030101c4412024100441e1408000300381c02c807620101d6100c1744d60f0740c001c18a00d01c2d031880d80c03a21009a0010342d41941800780030481c210038802c100020030786004001c0c1c4003507562400c125003d000e441065116210460a003001d10240c645c00c0503d01ea4041801c1c41d1521242e07407000703e030919040e031301c01c5162042e01c14018103d01e0040d10303040e40e51003102403e084660380306c107890049900c502c021032884d901790421803051090b1392092000035001900100700101540503070b103031440258060300f001071445d030000070020380703e400e44000c1c2d508450010702c00704411440d44d0003041c1024030060000600d202d0300e031082c4101d911a81ca94142160b8284116501d0b40760210000c5d06100e81a40c40002510a06040e80c6194803843c20141502d04068a50380501c0201d41d0220040c0c51040e04400c5c0503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 421865089 1250 421863839 421863853
    0x304080d11030405010905010f0911130f090f050f0309010207090c020304050a060c0203010b06180112020c030c06042f0103020c250e010f060801061124330d05 70
    0x140e01c04005107000e1400f0354000034a450b00c518202d401c44400201c00710040b802e281c000000304405c00e1140308102015200c070410444e420310000000e0200c104001c4070203280003015024440c080f0b000c250703454803d608442c60011040c44443c1d0328005c1050082c0143c4c8101018080e8058540088000801900459060a03141c1c0002451102c4c9a04804002408442900103600e0240103130f41c940c0c2402d403069403511044a40d1202d40c00f0303103500302506119600b905200e00d13107500d60407910010001e2041d030784c440005500c5140c47e200150b40079a54200095604c0340485141d12590740d100c00403c0000b4480c0d008030700190040d403ca8001109980101041c0c8a24140324060306007031700310b11070101e0202d5810207071050308078101a004041c489854450901a207604000301c05c2c15604642400d540b454800c9090790f26107440b8090284450f41d09031140380d5030038801103555000c0c2e0800c541d8030742c6c50b41c0c4c44041007515544524014900000c280d0b04d0180c1d13403c00f8a1103040e154011400e035685 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 421866339 1250 421865089 421865111
    0x7020618060706020a0201150528092c010b01020303150118090b1203090d021c05100c08092406031005150f090f07052b140109110304080d 61
    0xd50b00041c00554019400081c040f00603642071054046c1083c800c2c2d800d60f0b0071410b010101e11a03018200d0911050064800340200c01f0101f0a001d000403c200442886440c00e948915081d035a401a1480e820304281803020001c800180034515070614180d0085040d03680784640b2101da40340518903581441159001000310303402c810303644009003003140004910700810b0320070f010f05981c0200780300146030400d220b41000381d42d660b1304111301960115080c1002c0750000d5a41c200d64400701000910620414290b024101c0480d00200c44881182e01e800c1c0c503a43d03464001c01d880307107410070f2510044040240456034442c0d20b003007219004a070150444070004020a058421580103860351004607807035440b240c2c0e161500b2202c1c0c0000100a840d4000c26003894141d040c02d040303001d00050240440031440300703d50a461401c402d5a500c11811031881c2d0105040090000c1418642c40e80c452482c0c4000443c0f020300c0343c000e01040b08545c3d070005245a072180c84001c11034000c4010201e020382c03180c2c0d07840c130 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 421867589 1250 421866339 421866349
    0x1b0f0501063c030516060806030a03021f180b04020a090614090c0c030a030501030b070f0906050f190c0219120b090c0301091a100501210e01020d0207060b03070b07020618 75
    0x2170301507183c000382c03d0810b041039009441540c0050525209501002068001039030100300700f0981500c41c00d050902018803460385000d1300382505245000140641d0040038400d061030650302581c0242c42541d002603c40c01082d00740d80302030041c0c0c458ac150300703020007003941090081640d020307a06a40c9581844141d6031007038110b038401c0d2102e500080d00c0340018001e01240b415001c6d00901142400c801c5424040005450380255114003800e10030045190081b1279240f030210b035006140c42c070840914103003046001d4080d0700420810b03070041d2a0381c0740e41c0c2030700c803103030001582a03628445100d803900410b0782d280710540400800c001000e009010700454961000d000b41e602191080305104070012255858109a10004101c42400c14020b4002c1080c1d07604806030b05c2a00410b900380c01c59102200a0380c001500351881072403c60342c03000403c4503401c04268040c10580340300c1d01c014415544500300b016580c290901404a88040810144c4010324040340249004000d510900c40146840000a4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 421868839 1250 421867589 421867603
    0xa200d0209060d29011509060c03020c0907120c020a0804120c0509070302090909010b0a0e040206190201060f050a0e06010c051e010507121505060a1b0f0501063c0305 73
    0x440901c0113a2148044010713080303803403809002d000403000382402c042440100804044d11840042c011400803900070716109000b0404101c50240c107401c1d407030130034001c01040d041409500d10341841c6011110490ba51000c00c01c2600581c101c0c0d807440c28542003403084010340e07020b18422141c8040000780020103840d80d0705502d1081125440043c3c8928183c0c0070b0002e079070001464484070380d00d41554880c1c10f80e035800300c1c10151000d03000040380642d1f41c1e10210f5031034030487e0101d0340c4030f0301d911500017492581500039405450b0030f00c104102d019030b43c00501c0901e8085018034140b06540c90300080140d4425007010b201e95000c5c8040300c01000c0c0541e0194403a000d1a0443c0075544d45650400080c01c1d0000d812484038070f9030090801490000c3c0d0100b1311032282e140030f2540700d9040018840321061040104000280d0341064002070110f0074608551701521103d0122425420403070001070120402a00042d288800c61040c1c3c0c03940800b5050046902c200c401203415030440240c0400851010401c1c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 421870089 1250 421868839 421868873
    0xd0807031d1c08240d02060d0518010221070e0d29040b070c11040e061b0c120c0709020a0302130806160c0c080a03020a200d0209060d 59
    0x5031060025003250303920b8030a401c031209801d00030b1480a109001c1400445500860b10f01109001280b00c070100107200da10b48048043d43c8440049082030f503480c241d030301ca14021142416112840140b00042500382e0041c552a01c09070008100c810319000c00d292040c030341c040c98078a805905010b03410009014510654400d40d1054400c1040882030384a00303c4003042c040e040f40e0558614034140d643d1510710b1600525140030412442c0b4002c08210080f14000e1032840000c2c002c0c010000603156a640d2440308860904001c01d0400c80c06112803800b0048030301d105102e8005e0002c614101c814014a5800415a8a1248155a400207102c002840136207a070803e07a50300940c1e5520562030840c0104101c0d00b1100c41c0d40c004606100f5518080700003240807520038280200b940e10b0500b062000d85d1029030000c401d0f40149200c2c20101980866100131b518407900c10070000c10f071841003650303541200149554101c41e01510030405031812202e0551f108ea4000d09010080100d039564130b8810100c2d40c58 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 421871339 1250 421870089 421870093
    0x312040807170109111e0406080a02130c09050111030706050124021209040b03030f07081201060206040b181009150b01180302090402010c0f05030a031a030d0807031d 73
    0x42407001285040034401e200d90400000d02c05507075075031120340c1074545205d06548903200000c0c100402003207001c2c200c01541c41c003e100300030b6155500080c0303451f035080c40ca00300e1081440c03958031521441c0741d20500c41300703940035540c440c003da050030015501c090501c28a580c4900c4140f050100150480c05000d010f00344240841e0b4400740d40d8098500c000c1c0c14980c014007590082c0d131080d5041d05400c02a1f880c07d01e0100d60104102280340c02107403c520030811003500c00d20002a80e5405c2c4201440100104044882c0b0091075a036111812038580d517050304e000b0410700c28540030650038000260756150301c8158406a07009440c0348240b81c0100d600175030301280c8845000c0c40c0b407001111148034280f0011002e00700b0703401840c09048500f00c0e8410a02000384201c28000c003160940e44101900e24040b6404038005c490081d80e03040c0140d1b03940040c080c1100007820f01e4244031103050400100b02038040040c0c01025910030f0305209485d0300400038524410983d450784558a0300002904d542d00313139180c001c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 421872589 1250 421871339 421871353
    0x120a0e1c0e0901050d11060306011404031101110f03040b030411031b0301110a120e1903080105090703020f0a031a0d08030a18050a0605060d1505060a150e0f03120408 73
    0x20510040e00c0050f40554400e1034042c80005c041940321120401c90b90f011510140d580d40c401005807074010400d0010031440f480418003104108004e10411941d2500b40c03140300901e22216401076540c5511b00528105400a000811070882070b170000d10b810074885c540c001046d10820000c00d19050750380f45100d54500c0c008a0107951805c0071300c00e1400c2400000720722454203040c00000760803400e15814038085c03a40c0d00c40345440349440074007010702c503549070f41040c17580c19000c1e04009021000c280110b40c418007413503020415041c024030844120b02140042c0d40d00303080c0340c454260001d002c4080e07500c9005030100a407051598549029520b00d034400c0b1b0080c0d849050044000c01207402c0c007464039021007001800c040100348005460380b00315034006004141c995441001c1094400c0e0b030701004003241c0c501080040c5c010ba854111900c503000c140e80404007680eaa18500da110064102198017003150785a1412840c100300d40c0000c69500050111070701000d02074541d0703250380d00c994081152600042c0f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 421873839 1250 421872589 421872617
    0x40c0302091206090714040f0203010b0d0e0d141b0f031b070506191e0e031c140a200102030402091005091801090c2702120a0e1c 57
    0x1c1480052202c82800500340d614000c48155920080350090202802d16612103421a5072250007030740080b008840255240c1d65603d20401290f088031003560010b81c00d0880000207c1e0780004c5200302a8a2680e0f015a422000b14500e5540d52100c03001e01b02c00d004990001031020b0b0100001e05024040d130303000316511a0840703500321080615610060054216110400c10faa441d001620129002d10360200b1501c3d0a0b010151100550704100d4803030840d00400b480200b903000002012407090a9081d981d100c020290603000c1484c0d03400f0f8150102d000ca08000300705850300400b4200321045410903508a0011000503c0100000030302550141c0d0004101f00450420003030003608007603036044100f4668201000a80e007248010551342440900c0081d8080280c42500300e0b000054100006000d000e03240c0482d01d03410b201d0031161010964682c500481c03c61260b108840810b680300c48482c2ca1502c60b00118006014941d01403c2188034080c0210307030524141614045062094a450000c0001d0b1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 421875089 1250 421873839 421873849
    0xc09150411250f080a020715121b020601091d0601170118080906130b0d0608010605120705060306041103090f0607110309010c02010908070b09150c0714040902040c030209 75
    0x140641d051250140c40600005510f140350741144960025440d43c44444108080b490b00c8605c4d880411440382e00080d800005401040000c1400340e0030700705012192101881062461518400400580c06100108a185e07c00c0d0b01c07203a5a1400341d2615400407940d6103101d0710b0808281c000380b030b402440d4120449101000d1080303603d03210401e04019152081da880341e4607140280c040c014000c420014000c04036503c15680d4801500480c50090386030100d8481400003000c80d4050b24082d5841d203040800c2c980b070b1011100c0c42d0240c45500405040b41400c0a103c81600701510443d002030b00c8907840032820b0003540103180719541400042160b8000e40c044545400009888101031045050038014609030110031070b030070300c80282090240c481071440100c074200c00c142e100c1ea01d04e004000000c14503d1409004082c415000c8594050b00d41e1488980440e500c2109400040c0d5400883d0800001c0398052500d40030040027800010603454030b802003000e9034210030303106000a5001030002503600e04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 421876339 1250 421875089 421875127
    0x1020408120c0c0a050603010e1b0a12050601141e09030a0302160b120406051b13230904031209050102210a0506031f0b040204030303090b0705030403020c09150411 72
    0x8079004e2452910b42804aa801e110601840940102030400a2092034002540c0760001c0707449000c1c0f55540c50b040400074080043c20500700030003800c00f008503010f0762190200014400c8041c1c4c00368a080b01601032080112902084090342c000c00f4807868041356018801c44d24014007179005001c1009501058111101042e0441c1035010780c00e1003801c04040c4038440503a130140c2e0050300000d4580303500c0400d07054007604d0b4801a03016040006c0e8075410312010400c40044561006003e204103202c07501041d814981c1103c2c203a0031180301800100445d1107030394803a11803108114000380024140e21500e003607a02c0f29004040203c541c020002124850030b5440c1e81c080950001005141400c000103525200c00c50711003844040000c84d10026021158007000d01102b0050086644a03644c0c42e01802520700c2000030340b40c01c0c14030000a5043ca0043c4c04a03441164154003804c0380d10140310411482c03175000342c400c01842e000f04038225003546491242008400c45030b000d06480340a0441141110b0350 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 421877589 1250 421876339 421876363
    0x2040c0809060f100909050c030607050d0623010e24130509060f04111201170d0809030a140c0618010608010915051509130218060108040f030201020408120c 69
    0x10054100030152034130550380000d490b030700203020900c40c400d41003007460113055904c0154180030300800c0c01081c5030060700826a0010105041c000295100c001c104404410362441aa00d03154000c0c0300b4141d0700c030702189689034500808448988045d6040400303140f00103403e581044500140a46090b6a40d506120080004481c03982051802c10003040c1c449410f07207500c03030040782c66101c0412205450000c0d04c004400180016030150380d510307607140d5110203090342054035005000d40d260f0030900c9107070b060b403240100388015031400c4c040040860301c15800d413a03195100c510034010200b000d8014068076000c3d0f0401503034828107822101080742101d0711030b40b180003142e141402901c00a1410042c4030f0200b0f52a20f800201561340e191400345100708080d0607540700100004003c0b501d17040010b00e080c42c50081d2001460807000c4900c0c40e000b08070549005000c1280d00001500094031003901d078034018801c0c8000750510303580e40d807500e1130414101e0303008100590100c2e48104850080015001407030b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 421878839 1250 421877589 421877611
    0xa0201050f060906030a030f020c04020a020a060b0a0501091e0b12071413061b1a01030b06220b030109080c0706020c0402041d0c0715140a09020a050f010c02040c080906 74
    0x4c21301c840003035542c0d5003086000382405208407100760028000d20407680c4111001c0c2c4195551640c00d00000d468025281d0f0440d0080c0c5844640b00e65414007065080a4900c10784038206520300b8220440f00d041201c0150528581010740007088a0b843e0700080c00341d5400240c1004c9181c1000703000500f142c5200580100d00c1c01c0700b0700c07042a1111381d40343c06030100c400c2400d1605c00c0810012980d5020101c0c03d00241c41841d5079082d5501083c4500030b5103048030f0040c0302c003819a88441040000d101541c00c41541d804042c03a503600d200d04a240c1c0000d0301c8000040c0001290703d0a81c2c2c400d0b140f0b0f0032074920a51a904010310030402103805000c510f42c2e910048800f140341c43d0030141c2700c0c40d1809154031014a003400f0100052080710304101150039039a04007401e800380d4100b801410000c0c02d82c0240e4444090031400100c0da448601e8001c210b4055070007401320340fa60f0308110074801c0e072034100c03071406c2e04210003170b01a2030260f282c40c4545440c2c0d010a50314031001d850020700b0f40707261441c0030307215a06407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 421880089 1250 421878839 421878841
    0x14010504020603070c0201030e0607090617072307021801081e19030203070501050a020414010e030a0605060612010906090c05160206030604020403060216060c03020f07080c0f030a0201050f0609 85
    0x50b5220720860b9800112030411141c0f2030352900048000380407101803421944580d00c103201e80c1c2500800f103c81100c0c480d9849007081700300031350054145c1c44d0076a1440042032840f2804090075201c0030010300002c002c9001d01d81010119000101c21801c1d4640c2180000400300040c0100c0a051004080c5004414164009001e006080640e01c80040144d514040001c0040c3c81c200341c424011511402d41100080c446800c00030501da00950180c03040003440e007480582d40f84294024020121120802009003589030303c180ca031079000e014000c0c4000e078001000c0005511522070660b900e801303010700c01d04c00603c8504043c22601200d4a004a0806211090007501054501078140d11141a419110340751240c0300d040c08540079000f5604010407460000c550b0300c4810440900d8401da0500428061000020400b000e500321701ca480148c901400d401c10200c0c0c007107140302006182001a040840c0c1c400c841984c1480d0450304407035054130050b5141e1061101c10108461900e4000c48100c0300e031401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 421881339 1250 421880089 421880093
    0x20070f03021606051603110f010b0a050916200304030302100c05090a29030a051006090602101107140a030e03060c030105120a020a0b040608011502030715061a0714010504 75
    0x607602850701d41420306074440300d17654200761103000c200c58014a410304a840d004034841d0818080d0002c044018028131018000080c0f40c03a02ca010a8003541104459803410080c000c0c0c211813500031030040b5814644d92903031400803448100000c0c40110b010b540038141003240c02076035074156400c1003036a400f005000d114669507941c0e8000a90200c980c03260004204a0703403054400c0100e00036403084c0c01019004001c02403140c0c003a0b040680b094008000140e032454a0720310645040445011780700059001d4503200300442000d82c444022040d18120752410042c0a545e10050500c21420407a0742c1e030880020b8404158002c2880700741410118090042407a0400700b264035408140f03e01e03032040c412502d41c8007a0403014800c0d4081150058264084107844803058600b039031007132151b00c1c0040c540c130f4000210030300d511000d0016822203a001d9440d11626450343c550107650f003125000e0466940070001581c207291503480e0020802c40400c84c0c0c4900c0c40d41081c0c1d030300790041b00403008039904040c10040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 421882589 1250 421881339 421881347
    0xc0f061e0f050717040b0403031115061014030a0b03070b0a0807050a03020d290a0f0e0c130603063003031e020d0504020901120c030620070f03021606 66
    0x640c1d5146850310035201d16031030403d00ea050380010a05400d201000801240c510000310003801524041c1d194100b02201c02d010700e41e5181c0d8a9042c411030090b240020608515029005403401426864800b0032010703002d4044900f68416103143d070109650385000c403810300b000e01286c4000d10140d44228100001e11401902d000d5004000c402000000102001c07501d0283c5c0c16541c510009590800c2081a00e044141750f800250203c03c00f02e5030344d00d01004443c5000c22085080c0d5010041d1044141d10300000c0f00014140a400c004524170148525021166000c030140b00402490394040741780b91900a09415404a0031440510704000b0f0705101042c84c50f0307010084041d9810310700003030f134904601c98a600b40c12003200120901b0340002040c1201d140305404c110300681c000c0380e29583d9a40d035160041030124428600412201a41c002040400d0031079201c1100a00341207061104107000d20030910555001c200f080310800b141040d460249941042031010308401c095154000d00d04041c0090 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 421883839 1250 421882589 421882607
    0x311030313080d06121109011403070b07080910020604110108150904080d02070b04060b04050f0c0a02010b0406120c0806060102031b0a02180a05060d1218030c0f061e 73
    0x6000340500086903c4401907941c0480b00500c60310f9600f000d4014540741100000d2900200c151081180781e0011450807200e019540c01080001c000342140c2d07107003603c00f604a420001003500c1616060041c080355441d1031b00003021402e90b0360702400140c509840d01025000c0d203000c80504210b104010810468200001007040307100c22160f07140d45a0301c605e485920340c4110861100e88500110701d03032081180000b0014092481090140b10f801a000244421510216202140c0382e9030721011079441d811000040482d401c1510012400d9034400000c01c0a844940e4044a00651690040020f000340c500646000d07000960141c402401d264000135524000d4202a80001152a50f00d0801b454108510300c1060740c0640101c441c408402804021144201c40b81c90a00b0b04040c0029603a00d0f2580400d00c8032644005881500d0000040c103c44440c8403038a9180e15030a071220101c04079a180130040020f1603089a034810123801c1c0a8014407040300c429140e4031204c2c1c400070b803804039600305a0603 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 421885089 1250 421883839 421883843
    0x617061e040b1008030d0e06091606081302041d1009050c010f0302072307060806010f080405161e090605030a1704150509150a1e05071704030311030313 67
    0x2e503460302c4006880a00b410345500c6050244000980c09000150603000f03200c000b0f00302c030b007998240c1e900d40b64241e843c0d00184809442c4520003035412700442c3d0042c40002c0c0c0240300c100940c80c0300d1142d0790101d001c88070520511400058400800d540b104020401c1c1c0701103840401c030034000f00507580e45403542d03460004e4005d418011565502d1249504c2a030555030110b0708034040e042c6202c00d407004070b000c44407040c04d918014000c0075000704116005411142c065003040e594090034000c1e19404a8401d000500304031098083c540120070401d5074520030340c0250102110700c0400f410000031681c89c1c030341543e1000d5034490522608100b680c5d0040342c40034416800802490304048080034544d454425604000030119240b1540341c0c002d64003001821090205448050a07900426407a00c018002c040031a0001203444880c1d041900c41003056080c14807550034010308203025541e404103203040da00c0c138441e00c00902140c104241540280161800c0784100040c52440c1030003400c0140b0400c8007280 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 421886339 1250 421885089 421885103
    0xc180f0e07060f111b090c07150209040f140a0510030302071406090d0b06010306330201020c030f0d060f0b072901080d03150f061107090617061e04 65
    0x440a0703d4050381e40f000d0380c803501d042640d1181c0d0b104000d641d003815030703201d501e400f4624480000c0e00058004044540494014000356040303910155024041c1d0700074800d0503002915160903000110701401181c40d0b02d00f144042800300d182292101e01190001071944400034620003040020980101e20301d81903c9003009901c2081d00c440010511034442d1100b10b0340c020403a0b07800c5105102c25280da00b400307040309a90500640d603407078101a01004d8808425035030041c003402601001008804a58025001c1e40000b6080c017400900b054216048401c0c2035800c42400100446000070b41d12400003c0d080f9000c8100c141c50034202e406106000341c100007808a0f98828483c40d14000d040140320070380806030300117400c03980c444208503224100003001d080801d080402c800200101803c5000544080056010040e4034041040f01c0301510001c0344040c03400340c02d20215001036180120780c041c0052a41c04842c10240c048440e24014009103805106114211146400c02840c8c88143e003007500851 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 421887589 1250 421886339 421886357
    0xf0901081e0f091b011b0f1707030e0402040806190905030418180203101e0c0225030b062707030608010c090b03010b030c070c180f0e0706 61
    0x14076524070740303001008a040d0911410401c2425290a4140d0b4428000c1c0340903500207600620340410303030596841101c0d001c100000076280c00e0700140d50402a19034042c1310722030704201c2c15442d2002c1c801e401c5100c20610142c00145402415005049008980c2e01502c046184c246070241d000e4503900c0c0501810700b641c140d42c0745400c002d80c0d00d030403039918290800252540d556840b050b140740190200c2f01c25900d40d0801012600d15480d5058481c2041d03009000381c000d60755100d4200c0028105a0588090340e084009510601c00b101c0c4510b40d40d20f411600107000c4242c507848569070120203d90f610f42c1c0d40192410500014085403c1c2c44c2d003200040c0c03006420040000ca1041c20403003800204407140920204000d081039047d0481c0003100c20480081041d0000d0660841d02080d8034020f00100742010001003010002060095a1128000144508240131640c4010401c08103900026004070610030140e00e880480c890a1035208000500b0400e000059021a80794201c500c40d540034840e1003d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 421888839 1250 421887589 421887601
    0x60f04020315010e070801150f030c09090608030310150509010e0f060a0c02100c1a10050333060d0201120b04020c060f0901050f1303050412050c0111030f090108 71
    0xb048814484060100038035a101e00001d00100421100c05002070240400000c004071110074000300c1c0c4500d40d4809070100706600058000d8030102c00144100a100d503400284401e0504c6840040e00036140510340d2400c1141c9003100e80c50b51350308101048001c80e2020b101e042d8003d0100c82c031200c1d0a0800e401300e202000005040481000c0074603070001000151500e91643c44281c85403024821681c20503400116801218000039803040140398560344513007884000ca610b00800d51000300b0f501d07881612a03d0740003090420842c411405003070490082c40c08802d510303100b030902210400022004051a0103000194101400301d00681032200e145a02511811640c000004100d4042c0c42076644615420003140d4403e0304507080d1280c0b2000c4808240c6800060041a0040e5102200d041e180d0b241e00207582c1c03a50700f03000790440501070b0030000015076074060b041c0030041d240503101820045080600140050208001c010107681003007061341c00c51b4040400352100c0300003e190007040c6540361f03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 421890089 1250 421888839 421888843
    0xd05060105190807052a010f02031b070c0801020a0f1205040c030624061206120309030b150301050c04030201080f0408030a0e0c0d050303040320060703021c1d0d08010305060f040203 80
    0xe1110082c0e074107541111694901e104106c210700c0040b810303000300003929280c148134040340819540304c01040700c204400840c1d111104082c1803c54040c0c6c07a012041691703081c0765800c80e400900d41030041844690b051161303d41007054800200304540081c4120b107003540e1500141103140c000102201e6071409259002066401c401d48810081c004202e02140c540d20003805041c01140b0840115090880201d42c0d04007642110b42c42a6050f20740703008035130071513036417106061005202e420004001d200561481e03400f4043c46004081844040e690f550450000424605009203041a0390a080b81448000354554048950060125030009500317402c036051103041c1442010501e51142113540d16600f804004801503014500c00c0d00e44100c01860f10b046044040c1c4103080354060380d00050002040503009800402c1400c0300d281000740c80c00341c0082008215072043c200312502e24803080d9420020082000817160041d082d007040b0110390b140d60f035200c1e03540700020726403070407015040045402c540381 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 421891339 1250 421890089 421890097
    0x60812031f030b1b04080319051207081909020f0108150901150f0c03050a050a09180e010b012c030c03061f0b0408030d05060a09110d0506010519080705 67
    0x106058914050b41d0341c0c28191800e40f000d551800403008042c102c400410580b00c00c80341142d5144000d5420800d880c09140c64460940c4841001e01204002d500f05010712107a14520402d070503192600e040c20188400200c8a0000c070110b01414902450400541d4403d1042c21074402e00346071094840d6502c81a000c2c0b0000541c0105802800e0320300046921140807137200e11403c2d0681e10240314502d0140110f03031001c2041d10180200d032041040d081c10a00c600002e0010480398245500e4007030340c3d00414410f6220070040990203e540d001d03409480c0d807081c082d04c0e104010918000c03000302030b240c60900c00d40d503c074580800300c041c102c040b4080c41e0b1024081411131081c0203059840c80d01d0402c1d6407221a44c5c18074554401010749407000300d80001410161416103840c5001181441c03049840d07800148000381c06140c0c4020b050000090100c001c2c0200810349001c1e1004c1511429050004401c3e910043d0201b41407010a01c004400f0600c2170941486001061414403d152680d01003540e481c81 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 421892589 1250 421891339 421891381
    0x703051e0c0a050a05063603130803132702090406090e0d110a0b22060c120b240f221502060f1303030608030c150a06081203 55
    0x500142d01003442000300380109150b00030401d5407000d55801100407900601600400314103c80c49022002c0c00d01c03c10303d140d95442c85a81280e00e0041300b0071084600900c590b0001c0040d030b1001401c240c1c20305d030920b81c0c40300801c1c1d200780c01074181310030351100380c480c5e04240039500440350f01281d01039450b529508510020b051410b42000003040c55044030f40c8400115142c500841c1d4030701c145056a480004600d28001d03000020314042c0e03200c05000c0700b0b428290300c0691a5003503107040f4801c0030458910807400d285a82e51900e958200c4041c076200c040d03850441c2e00782c1c0314024284c0440d502d03510941a020b0708044c094ac1d10396803207001c114480c000340030348109044018620b003060441100300712960000da5031030034002500e0210004040340e440c40100d034044c0080420101050900500740c00c0b200c00079100381408501c60740c84100007031440d001201a0140ca80c0071101c1c02041c40c001444054100032302e010b00f4000c90b401c01004030390314050080301c140904030000c006900440c050034014118070b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 421893839 1250 421892589 421892593
    0x25020c06041706010605210a1410080d14040303080403180e0601030b09040201090312170a050609010602191104140906010314010212060d0303021e071203020703051e0c 74
    0x780c80b1640041c0691040710700304250b2007a0000421030340d0082c0141c80445000300450302001c082c11140e1028000040c1a44140a4480740c14440b19840c40c08410b00c144003404604084628104025141800c02140708042c08840b5000300c43c0000540112403d403500360278144441e0711545000c8901d00d41d83d1034040c642748120032020808590781d6080d54000c0d03074240c0c0d06025a0015804102402ea82528000d000c502a4042003000440615031001601600e0a20261308000090242001c20040320121440ca541e9010440549809141d41d8050714240c03000340f1580e81c0f070301503d062940c2212405840c1c03405034010001c00340c2d1650400040c6e40e00159403407030142072000c0031035940c0c4002c7c00101d03040c50344032001140ca02c0e8140f0942d10151a01200c0318000d4031650148511041d05560690406400f00085144160a01200c81c1401c07a5450019a40d455500b00503880b0071000d260941018010004080400d510200380c400c0c60360350b082a08c01d082c1516801c419a8400c1d250001114 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 421895089 1250 421893839 421893847
    0x6170112030e1012062319050d0506090d0c0c0e130204090f1a06030c2205040b010311150306010f02010b030607030c0e040203010b041707091802130525020c06 70
    0x40f55001006070646440203009200040e1502e0044e0582c4240c2803405c4a0b02c8000ca04140c038516044215000b54040c4000303060249480d440800c00300400008291f40c01d900c201c00b408800c03901000712071004441454201c0c40008696035111060a45101d00e0300507101910114510b001154017840314282e000380b080040403c64030b070480a6910018041d202600d1214a4074082c40d80402218420880240a00310310f100920410420811086042c48014285c1583c0d008a4500d03100302030045014a6000d980e941c514078042220001c4040c0c0c080c000c280c4445109984191641620340041302420200c0702d241d8801000c0307005088032401c1c95403522403441840003240e01544003070900c80803070340c580000d00105418002030380300c203105141440208000400c1004242400c001c1c030300b400340b0240d4400c19600d54000060322303c3d08040c56060040409403008503d880744042138104400403043c412440c005588002e00c86407050b441c946045100800d002c440e00c01e110b2240c01c607100500103519 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 421896339 1250 421895089 421895119
    0x609091903030c0e03010c141c050a1d030c030d0b0310060e010501030b150301030305160b01081b0d050604140f062d010e0a020d020d05090c030706170112030e 70
    0x20341001800708000c204c20900400003130606000354250343c0c0b02900d902e0040413092250580540c04660031000207414505021114107141c08ad01d4045c400d0b9039404180300000c1d034400c03d05080d080c01c0c10211a481000075504015021054400d40c0c400700c580000c0c5000c80501181c14003214411f0b05080a00d040c0c00414840aa4442d0905a40c1c080c0d0b42040960f10072814003444a82c802c40c001100c90b01031004000081c400e0300142961942c45900450038402551071451102081e00541c01d50b402400c59001c1c01c1303810001c080a0f05000301c41030720307444510b602e90580b903c5d00074002919110000e19502081c402c1086404000700101040703030b415282082001c8100440c1081443c0000d501009585d8a0481c00c4959410b9a010365010b440c1a15108407881c02075102070140707041d40e5002d00220341c001d00d052150a100750340802c0030b004c4460030a000c050601e1055002502032107640c5220740b0f5880d0f107512030181074806590541808200904042d224548082080760b40300703840c1b402c07000c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 421897589 1250 421896339 421896341
    0x40e060a090302060c2a16060215101212030209030f0a050c010c0b011202040f090602070b0a0e0c09090c0301051008060709150c030c05061f0e0103020603060909190303 74
    0x8464001e601351581521a80c80b01d10b4a0b04c00c6685c0c00a504019a0785501003040080d034411245608204a810a11703482e541c031051451715521000158010300b0480c5248090820b50550181c003031b80c0b54260a03810314000000c2900100b0020f05120010f05101041030302980c112100e162008088410001c0c0340c1c0460f550781c40c03846101b203405018000440b03030694040c20401000030741c07044480200e0f07800d02c1c4010200301e103101800c0c0d130300076102c940d00e154a0700c0ca403107000704090103a4005a502c0011b402c0c01c6088050180034045c400e890000c0301024503001248401c060700e002c507800a001e8640541d42c1c2e152003000312406505510381001e0004e07010810840f13004036404082990a1507440b840c0c1a00c01d070b0810320460303c40d00c0d0090300040400e0301c65000084064030906100300320800035250541f60640c00c645144100c414010301f5644000c081c80043c0080a0040c40b010b4030b5030566012a605020161030940141c0a0300040b482c3e1200511031808400c0c150b44c61440c2400710303814010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 421898839 1250 421897589 421897601
    0x519060807090e030304051c0c020a060f0f020d14130314061b040807050d03120c020c042708250803070e040509071e0b1b010605011b020906040e060a 66
    0x40d1000340380035803c0124030004000c1d281725580200c041d010f203403070202d041020740400d802c00404000d02d1101d03550069585400c00d4008d04101c0c1c0d261200c1061081001c0c21072800700088001395440000d840c403010764003c4a4000d00011755681b2501d40600500000440307105400c000c10520003240e094803c450006105071054281620642c40d24110240800091040d805141020b810101040c00681130040009695510910b80030007915501500b9100702d03150711881800503044880e480d281d9113014020300e0103410562189042c00f0203d00301032404d2001003180180302d24001b00d0007070480300b8483c100c0044111105044040c0c40c82038585012194004c440810200d000d6281c004154280751058901c61032201000340755281c2410b40042260380351b40100950700c0c25001010403008111000780c100d14001550300d60410450500403401e403800e13038010504000044800c134036840200424603803003c0c0c054855007000c0e100c980204024010302c8820302c10030321409041c0007100345c03154408 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 421900089 1250 421898839 421898849
    0xf0f0905060c070803010603111b0d1e0503010905040521040911071a040804050a0b03010f141f0306030c03031d1e0609040902220b0604060f030519060807 68
    0xe01e81640d200e15092842d800b4503140601018018401809a28000e0344516500d07284000c82c0d504002c041e240c19a00e54405c8030340d48280340c0149815020300c1e82c00144903e06103083c0c0b24840949030341b03464006c1060205202d0300c9030722515140824140b00c424003250180c0500303c58034042d11207076200c0e4011a03910511900714034a15014907050a00c2c602c03016540b000c0d500c0031045188000b19040500006030103042503c1c440b000b04400205a6102c0c04400300500003081d01c50340300e6151010780380307108026520402090134200f90454240da100fa0080c400324582800aa81c01f414200d8101c00409094200901603001c8640110501d500000d40391000340d01402c02ca06d001031000300b40601e11642d0803d019440000000341580340c40e0040148c0814180904000703001c004540006400c840240003610b076a101c2045002c0001c06a4001d010448400361036492506103070880040000d02c41c03280000070503580d0004a2210f20f50b0b01c0541030491400c0e1400d1041e5902c401100d43ca0704c40760311070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 421901339 1250 421900089 421900093
    0xf0d09210809071202010c2909010b030114090703030c0c032003010f060f060c1a01030f140d051c1b1e03110f070203030f0a020703020f010507020a17010f0f0905 71
    0x40004c5512403140d804905542c1a500c1480c050b446980d142c0000590300c485220b0f24007581c00608070050f50480c0b0903c682100000840c44490400c2403500711144600c0c0c01d00200145001c108000400050800449074940741c03094220180b820030000040301a0401052242140c540c0c0b42c0c4101a16100d1109020440081000c0c0141e859844100c821911800071100d6110001304126801280281c104600520000e850078809607401118200c098008507446001d01c41c00006201003007801070380c07a00100c001000e250804110142141c080d01d2482007284040403148082d240300790700325207030000b41d142881102c2862071602800d41030f02150180300000701070100702d02083c440c3c0218104c106031403096a01e0005222410135081d44140400c2c1d80500c000c0044040d00c0c445000108009541c0c0d81c040c0400d9415803040021101ea00c008075410031070240445400350352003080c2c4000321802c01e0383c040001c0003910581405003081503512008240f4022070b00a46142680000105ca880b840c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 421902589 1250 421901339 421901353
    0x609090c0e071d0406091b090b030f011214060708240a05280605090307050d08030604091106040f0f0e011d090c060301090b0112020f0d09210809 64
    0x14010003140d808440c080002803035211420405040b10811248691001d000410780945072842c000a5680c3c3d498050887c850384078403900350356803009280015155880040340707141031907807100e402e0b0313841070007041e60b5503841030011400c00103180726240c185030b40310007a2240e9140901d005803626074100c0c1c010750046110b02c801003075249200c00c1e450000200500b40c034440c1d4189002d008101c102801c2c1920701c502d111065090182c14401200c00400017070b170700c7c940d40320300d40001d05003010769603031190340101d41c80880c0c0b00005048205a81e802031051364001204100350a1030740b62402e10702080c1da0002c80004001c41d0000c9604220310941da004111404c1d0383d603880003107450100007481940002120f480c4080e0303003e1488802280c10410203021240c1c030b01e03000d20000e05103a0080c1d002d040c4075644c460b000241035030000381d405c0d80c280c8500d0f42142031070401c4d10900014030510a0745003820387d0300e0700300c141000b64520000d440015286030b0030300c1c3e1280c05d8a02611080d0306840c079101501c241d034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 421903839 1250 421902589 421902599
    0xf0c030f0e03191b0503160501060b040518150a120b01050904120807020309093c180106171501140618030316060b180c1801120609090c 60
    0x40302c0d6035050f21502d101400901c880d0131a248814003041a803080310b1542e282c00450b504001030700c0059a08031204494043c9450803d00b1154141d000d441101c0c400c2c0400c00c1241d03120040001207440101c8061010f42d90000000b02c00306610039807603480381d102000840c0105042c502e50701400e110350900003d0fa6247c0b01007003070a5008544c010075140010b140500850310420b0466001404d41c011241042c80310030000d0144c2c00204c91198010400c1b1a813004440f60490f1140001d010f20180141660007524403540300200061610300900d810b01c002c010051382c254400b000402002e041d00e410700081401c00764036403202d00d400740c00d8403400500106045620408840140a0081505180182900303c1500604c012042c460f8540800c1c005d203180da6030312407856601e01e481400d000804100480c1040444003d5110140e02215200d0030805002c1001040312086038003403044044400c84800100e802e030817407074420032205045c003800142c0700d910343d003040c40c81c1d611070a01040f800741c81d1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 421905089 1250 421903839 421903843
    0xc12030d180803010b0a170906160e01080103031d03011d0f03250c0e040311060c130308030a09200114031306091704030c0807060905220f0c030f0e 65
    0x1d0300030708001000c00c01013044010010082081c3c82440c2815440340040340a0800881804c60743e907100b03a080340c4100030400410000300e0064030241d05103d000807903040e000a20000b0140002030a201e032501e00c030b4050200421103a980001c2c02070003801070340100c071114000054486030001c0d00c0c0c8140354a01d044004040281d840352038505200f4075203a000074480d40d81e0a82c9101007510700039895140410442280001caa104500075201e440c100050140300b185801001016240d00d030f40b05100c40855400b0310040101100e407c048425140d440c5c080080e0003c0c04126002031032032451400c0e0569040885e05102e400c040241c88104441058401011080c401215009000c10702071100000151855014503070045c06500c0c8150860300103154841e141e4421341040c0e036011340070001004001d004002100180078240380448500c0d290001207001c5d03403800c2e045402100c41d215840e092011040c0d0004017072054060341442030000449018006260f40c21300c2e102080d00380340211840c02e0700 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 421906339 1250 421905089 421905131
    0x2030d080105060a1206090c02240c09040203100b04080d090b090d02121c0315080a0c0e1b07030507050c0409150e0f060906090715050d09050c12030d 66
    0x14024500e03014911508a6041e101c0441c054034495407180c000ca1300c3c081b0b42c4223010070403040f50014610b21407000213844145148540709071041003030000b00060600e030740058662340c00082d40e015807a40c49a81004403055056003081d65034a40200c1c1c000790245000441d21402440e40d00c1b0aa0001e4407024004958800d0485403900b0408020125005080a101d41400c0040740d405883c1d511514010400707541c1810340ca0a000280c850007443c03101441610140c0007840c070381e4020101d041c007a58a034036400346a44034481100c228440042c810164001c0002001c802400b461941d070209458050065003100d0070a841900c509851014142414811004095084003580558282e00180344010b00111490f115450042d250003a03a10101086494007544205016004a01d081d180b1a841c5c030003540c2c484100120408650108a0f811204803111001c0c0c140e8003107204c0d0044d062180c41c10f0a90500030303410809038034200315000f8011010341301c070100340caa060009103480002240100c1d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 421907589 1250 421906339 421906349
    0x203040b0912010e010c030501050a05030c0f0d021c08040906050402031005090a0b1c05010b061611010504051909050702120306040203130b011212051908060102031b01020702030d0801 81
    0x8100011409807a21030121180c1d441c1c2c1000100b21886000006400d4542c10003022001c00d03210401030286180c400c00b8500600700c10750040917400311406c0020122840d4800d06070142c200400044155221840e01500c2240481d514034003440c4d15142c5040d4960140c40341e10b02c150302c0c0c0100468170b0703c0e090085030b0040b141e1a140c04a080e04010070000c60725000b501800f506965040100d6070754841c5210798419100d043c3c07003222880c2c058140380e400d503800c40314a188220010014444403251030040e0310100c3da0042c000d0495400c1700c4c030040e0b8861080e5003007594040542c0c6610031100641c6400c40b030544104c00001d2100b0384681c00140da88200003031110300b04404c240001641404e05a01035644841451405881003c5c1610b60300300802084c4c10030302a5010403000d450600070f00891024079030502d072070400c0c40d01c03182c000c003a004580d00314008400c2000d481701251079a0310070002d66800300ca104060400788018004458002d60000408174001c1c041d03003208807662401a07400504940d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 421908839 1250 421907589 421907609
    0xf090b04030f050c1002040302040b010c02090c07081e03040515070f1d15120f161d06030108010b03060a050702280c06030b01080a0902130e0f0a080415020304 70
    0x5299076905444000e40a40c00d18104801070018801d04142000f9009003111074160050307889003503005000c1900e0b10342c2c26103410f004035040e0301c1300103881d241c00e41a03008582403c0d46e83c0340d0000b4501810720b84100442000d09041034003c4c03518000191000318000c9208600312140e201c1841c2200c48240c200315030f444081900d40c5510300b01d40e4004d640c0f1040050a0344840810051301000249840002d0340ba454000b1601042ca070f505c136030700c1810640e0891a00300d0a00844d01d0403581c0700b8107043d0807540c080d040100000071800c5886045905c0315080b04010021902c941c2c5600751240244803a402c0da910030310a21010401c06403680c4621400b54800354042d11407a02c6510307a0824205440340507540301110301c0c6100011842e5034807414054a080c0d60040f42c454107040006050881c080d0589601c07901d417400000040c1d440d0b0540b0b02e11601c03501000704401d140118600d0034081840d49540f150f0140e41d0070a420001804c0040081c1c56078850900c1240300f04540c200d9a0b80901d000d02000340b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 421910089 1250 421908839 421908841
    0xe0607030b0d080c030714010b0d0206160218100b070209041212060e1914010e1302040501030b06030f030a02210c010c0c0c0504110f070809030703050307060f090b 72
    0x1244a90030001c200720000c1c14051003a1203d540e49a020340c007958030324003160004100c0f04100030170b81a1050700c07002003200901940b50101c3c0001c0d40701c4120320000740318441c0000e480c0c03454007011a43d082155001464036810190080c000b00340d40c0e07003c90316403420403e074150119204a460f401d031003a13150081c1584049956650319845d0048499103441d0030b0041030031018420701e1690240300090b02130080344100c1800e2144101e0980502070701c0b0608140d007001c085844070303028402d002e4112000c180c9114807617240c82c1007896401e1407036107001e0b400c07504040000c400c2c442c1003c1c07030314002c41007035085440d9034015981c4075840c0c0c05404000001038101c540030111218101c040c1240085010344150701c0c0c12030452515085690380040d000208080e10b800754240850f451140300100700a440034029070725054000001441058107900810b24040303000c0091001120966544000c0074003140c00740350b00d07410030300d40d20782202d403084a00e41c0c18000c016075020640e0207000d2140303922468100d41 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 421911339 1250 421910089 421910101
    0x2904050924100b0703030207050105060a03120806011101020c060108060c091003110d050112020108060301021801141905070c0f12060506010e040c0f031134060c030f0507030e06 78
    0x2407480142c4541114100b4120220300000c50b0740040c15824840c1e24016a50303505483d096003981c0380100780900c10100341d8400c001003158600c2c52054010107113040b0260340d880fa001600c408101d00c44d6030500350310100700112510790018546045e44e014804403159a070f512032a1030385078405d03610060340200c00c8a00d2340c40790a000c0e4104145040461000500380080d201d407130390444100360b2005030b00002140c4400155608135640c01d070441070030ba00075840c004442040186400860890350b0400c10b4044560903816401c0060b1880c4c9121100408031140312290018200d0b0805401a1080c801102c0000340980c20b25000800310344030344801d0410303440c4545480c40100001400e19050040140420120b942c55100c0d400140c031103521034250003000740704028101c0b03003145407002c1420b0041204243d415a0100a01611b0141614022132020b040c0ca1000c2c0c04400c841009200c24101604000309541580103c00800c0d000704003004aa0b41e041c4d011001d03501c01a01c0208103800c90008521 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 421912589 1250 421911339 421911403
    0x9150303050a1404030f210c120f0504030602040344070f0b010f06020d05040807050f01051e0406110307020f04020309031c0b190b0a1229040509 64
    0x210550348882c00c0c3e800c0c03641c0e80d10340c2100b1380e0180720211f030040c0c0200c141142d5080952014203150583d482e000c01e001e040c5035a421300540d002c02c1c6083c280002c1050300040a8414401c4030042e60740060150344071552417a280d100d504071038200b9030b0050070594550f05d4110040030740c0b40d4100c03481ca2007081100e8264071403200c07607440980b055175405c800b080070001282c07070301081c0c900070030160001d102d42518148009041003a013681c01030810908010400208a00240039415100100c5109100880c080f006075210b1054419440c4d21344d201d241c40608443c0701c1c0028108651054443e41034000c050300c1516128490210001d52001c030300d2507443d5031401d040e80619840b1405100b1680b070304444072616048840085448401d4986418004000b803c080c003100c000d09000d0207070b4600103070829007004120f0103100000d0080050251080d540b44019070001c1d81d4030440850780c0c00b01da003010034880300f801c080003401034051f604013400b1032030a900000712491034001c404040c001080d10304120130 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 421913839 1250 421912589 421912607
    0x202b020f0616110f06210705040f1403010e06040308090c010809030a0c03020c031603061103040507180213080d030c14040b13050303030f0f010801020a0816090b1309150303050a 78
    0x150060b03603210b4401465145c07580208001443d0144a1604100201c220b00e4800c1004200c2e074100041800100403c206204000e020b56181c0c070302c41c581088003200820300514030320f0001d00d010700c42c0c1018001816000186980140c052200341d507000080383c030054070039800030b4500c0c0b290303580104900f420040c499662408400d10a1064031400d07081c02c00000d142c00c0d00501c9102030a101d0100410400c0400d200e03144c0041c8444140c54110b2505460741500c0d0045c41c45150380399254840c08a5540141c2e0341203480700c07400c1c2c2454181c502d0b00c400025030341c0c0d0007040e45031000ca442d265501000300d000344901c5c2043c8c0320b070f80105441d00c1e0400350082015000800000c8003441e4143d008a082d40c1d0910145100744c00c07090f40c00c19145401c030400118950180d000501591042040c1100c0940c460011540841003c68040c203000140400b21012000d07170703010031201c44000c180420641c000760700d40c0c001c6880c203410600c1030b90100441007a80407154440140410000c000391007025020b40c03142 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 421915089 1250 421913839 421913873
    0x240c050a020618040f0902030c150403211101060f05060702180f09070b0a0e010c050a12021b0a05100305100909030903120c202b020f0616 61
    0x940c405200d41e5000c50312a400a401911403107201a001c0c031200d00b042d101d035904003c11080d040c1b21117841c0d500400e84402400e0b074807500504c001d03c0c0f00711011681c04119401103038449401d0560348665405ca01d07a201c01d00c011000090a19100c4008420050084d281900c20410f5140d00c0180303010100115540031007402ca810002c10081501c9480320000110301c9500d0310b410001503803401204140c24004280c22542d000354090010100345079210940342645031080c02e0003d0844c0e40760810742d1800e15a218020300b10890703030212009003603000c29484c0240d1118280d103c2805600d10800c240507015010300c46e0440d074054a8070b41828865007040d900709011000f045440b1f5200d100a400b40c400b44141600407404400003041048085041c044450103035190010340348205555502041c0c0700c945442030008514400d84041d035990b0484040c5c4014110072442d01c08a1711190740d20140c403400d20a91180524202103206401e241080701e1410300280c81403114842d442e03540c032000311481044 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 421916339 1250 421915089 421915093
    0x150b040b0a031101021c0207060336020f0607150b0135100608041515090614030c0306040b070c02120a0b0108011a0603090a0b011509240c05 62
    0x2191215072218060540034500441d05042d10ba80034100181c83d1403a139030030f204540d5408199034055981d010880200341c1e015441c01050701855001c0c001d801c031201301d01008034100b0003803c495000e014aa444004244203a44550341400400200800c50140e220003034100d04201000a1200c900c43d84001c3d0303104070506150800c1c00d140c01028001000c504003184200c0070001e40035100c0c40c00844001d5000000c040c82c0c0c8a1a400c018006010180282000f00301c0340741441d03c08404141074100c003c1031032020040d280c059a4807030002000e09014844c2102ca0079030030f6018040c40c200840c9080d0543e1018000703211580b5030344d03903100c24064018411401c000a49580c500142e4508499007000cdd0f0311803000b000b80d0140780c2084003102c001030f0f11003034007a85410381c80d8984a0b40c40d21000420401107407040d890307503160454142821000c030780050a244d48480003180701e003020718403040c0900403595030003180d98503414208200d0b0104250f1901ca1104481e9403a540b5228a294240c9070b489801 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 421917589 1250 421916339 421916351
    0x302040b1c1401180317100b0c01020403140714211203041a100b0721090f0605090105030103080d09021806150f0a180f080307060501050409150b04 65
    0x10001c0c98000010021501c02c01c010341c20b20141142400b0302e05204042d01c030000650303806950007801c4000412424200d0601c944000b84000070311096004c011700d0000b000320380d210315a8030520f000f0b40c818001283c6058440c140701d03080020010340c5078103a034055040425910004420841c014504518803410302100b42c100220715001880b07201081d017014007c0580b80d0900307180110300000e94980f40044500c054080001c6148000f021504171081803010075a626410700340030900b840c03124002180c981c2101901040703654084031040446031603942d04848540c4840044400784508110540000c4042c0700520114040304018269151a101c0000c0ca44c0f0203030b40400e404004000b0b00c1c02c1001001c4041252904010000d942440760344c00c40c05150401d81c58101c410ba00a0001e58001c103c2c0041c28240108207400b0268082c040001c0d42d01c143c507035503600c1280d990380154412500c00c0c4c1000c00010309824035004015400b64000d507807035200c0d21aa01194002c02210380801e41c816140e203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 421918839 1250 421917589 421917619
    0x3090909100e0705010e040b030a060c1107080703140f03030403180302100309020a06050a2001110c03071e0510091e14150705030109050606270102250302040b 70
    0x1c441c50310306454207805810f03624505000940b4050510030400c0c044c90602d04400390940e40800d0691045501c81800104104d04c020202d03204400c58808516a118002e804200d03a1400030301202160700c03078029580001142c5042030703100c4440860b0045194018000325001078010612101c14a0501c030003407110702d9594000880380d0001c0120301c0c0100e5583d20310712080d82800543c240c0640500d0900751b140c401400701c0200246c1d40c0c1070440c4842c0d800030031500b08620782904620f01c40950040d4281c2c64061603600c8540301d51001004403081c080091580300d10420100e00d9400194000010349894400c04420501800041d00122800e190b80849905d02c80d00311003510480d030307024444150881c02c81001d09481c21040c40d03501d5508004080030048440e51010403241902e12040b030228064a5000c040307002c900440108180204441c010200d52a06600170200400c0c826400c8450301c1410700d0301406400c02c1c99101c0340d001c2204241c18809800d054009201404011b401c62215110306 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 421920089 1250 421918839 421918841
    0x160803010b0901030c2a020f060301081015030305030708090f0d1d060f1b010f1122050312090a0b0f031f0b07020d0f060507230304050309090910 64
    0x340c104060000c07020441005950385071242002020b040d0801ca1185902a904500b03051070b00c0000402d070302d020704920011912100e0f402801d0302400b0301a16200c0d40c4458606840302005c13802201c40924048021000303003010500241103d42540364030349981c031201e1040303406450080001a05100740210703080100410000c102c03e84649507288140c1c5513a0030000c401c072044450809200340020710188041000f440e0860f50001c040d091440e401e081c2c4409001d01409079040d95404152600c004010011a0300c0d00518038506100803000c81d40f606108243d840343c00f940a80c540660042c100028400381c0726000f4050400018035500c2c0013aa00c000034602c9512160002c0502d44003c001d0080e0391015400c034140c69040d444114040d030703051090150060040d05c1010b840f41c00d0070000b803001e012003543c0701d5242c43c0e005203040c005440c0042019010b0b1110050035400d81a0910709002c2241c103000681c2d000e42e5000015614040303440c0108040c0e0b000c007500c000421300409018541400b49 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 421921339 1250 421920089 421920091
    0x60203040206090a030302031c0e06070f18031a0604020c0a2a090207030212040b09090a091a06030601050114180604080a05060f070504150309111201051f080601030305160803 77
    0x101f54019a80c40002c0c4078081110365014001000c4142010b409414103140410440da00c428a0320384000c1d003c0d01800c04407184403078440c8920300b0310043d88002c0184840002c200b05040e1400c0206c443c5c40d19464140000c9210b040350401c3c05811400c0c004d00000c4100450101241e804011040101c0f80040e03410003000d06944040c80706a4000307807610405406004408c5c010300709005060815180010b960b81a1040d032554a1103003c0b03190008040004a80c04248595003041c20200e05100c0291818100d17407003607450621070f125081c000500342d880780580448400c16030400c20301b8246032580307100103a01c92650381350348070030144000708130030030100180b1000602a0006081b02d0030720b4220750382c03200b80260200d42008010041400160240600b521920348580740014482c2801d040c40900010071f140320690100300b586c02c800e481481508914090202640100158188411001d200204c030f0321400d03c054021000403c00f00e8050009400b015440900c6010421141e0791201e1181d40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 421922589 1250 421921339 421921343
    0xa080f031b060105090403030f0204180c030b0604120b09010603050313140603072007030819030b0a03020a03022b0b091e0c040207061812120c0c060203040206090a03 73
    0x4004120a000703410006441d030100300341031000d004036504000100d0351013a00244050289910b442c071034010546603a04031001041460f8200000d04d044d0a40751028050030010701d400a4101001c00009140c0710044504a81c2450540014903404e0f0395030301140c0d24000e200040c0c0d5560f41c8000800300e10305100500d007000d1040700c854002c6007800036161415480307824a03402402c0600800c4001c5820000c0300702e94a00080000c40d5005160000610780192908014030030744002c1070500b0b800c880062406450981070301c0510081c02100c1c00e200e1002c4a030f00c000b03540710a20903c10409030415071081e060b00c00c030040c0e14002541c048440081c414103000300c11107021558108001500b5014031000800d032100c168101c9440c000502200e60b550b994282a0348143d500003405d00030824950701188980d9800b808464100305241010005030003220b0001003c80c1c0e04c1d80c110808044180324040e0000083e0b15101c803500d01d151100b9009410090049810900c100801e41035070b81c5105038800214 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 421923839 1250 421922589 421922593
    0x4050d110d08120c0a050901110a170c0706020f0c06030408071b05040b120c011d1f020d021c0e06090402070507090b0139150501030317040807020d020a080f 69
    0x44001c0e8540d04400004e1240740c04d90342c24010118a180c0c4001103c5818009207401501c0d54080c0c08890b080034820a401801901c14026a1403d03070340840c007074130058010205580303155664500580e1588186141c0b01840d410200d000d02d5985482c45c044d6400901840301035080403191f996151101082030f0a08014480d4680100000d1038240a01d01c1c0e200420b840c200b88188608858541d504041820203062004101140d43d05a006510032203203044d00074518620b509104041298200103000d00f000140100713030031000c503a40006181101d0f000d030041000442c0c060302400322040c00c00440e00d143d00c0a410451120b4554a81c000ba248003030142000e490b00c240341c00c09880031039444228440c1400040b0034080c050408644960310b80c1013030303102c1c0115045030142e0f10202c1d0003d000c8004090380c602110003100049640d01982c1a20702c00c0c0c6a8607074141c51403205044182c2e080f94001d001d2481003002c500107003030001c6440f04840c07000d00b107200900e45440c5c0041c280840208401c400b5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 421925089 1250 421923839 421923847
    0x3030207080106150c060c050c0307030e190303050f09010513090c081807060813020d051f151403072102090a06030305120c0c060411040516020304050d110d08 70
    0x10081c00c0c89200001c104800c69000d000f03140b0400540a02400320380034000d1955103031001521800b40741150580300081c400d40b40d03103050340d160140200c0083c5001c0c0b401540c0403082215805400304e120700c192601912003508201c81d680041d441a4446075920b0704218081c4500310700c03490314010f0310024200c246e1002c00c10141c010700c0200108002031001c03208100e0b41540340d03c1450042080c4043d03a071603150000c080c0d500c03a05041144030f0752420013034110341c403000000c00b403140c0400e00342c0134181440d43c00d800400010048009680d0703584940c101d588007808003000390303111100c2c0a02c000301c0041c080d1f5103a10381c0c03940c102203490018071020300a020a41044401c5103050301da501c2d0300005d0103004000d49800d503100100140541d410181105c06047d0110f02c44801400664804503582400ca884610f401d19000c03104e072860584041c0541d00309008500d05803d071110710704c0617024135802076042a1801040000303200704c0c3c01059802104840c42c1140b03a4507040d80d0074030958040e40d00c40c0e0751 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 421926339 1250 421925089 421925099
    0x61407170a0f030b0306190b030c09040c05010f0c052d01091103010e0114010b030408040b0403030314070201200a0c0602031003020109060f0207270e0610050d051011120103030207 79
    0x1a0b412803084da501c69009513040042654405451282001090000085600030000800d20340710b421a030017a4810000341c1040104140126828260750080e0307100a041e46800c1c40607a02d0300300440008150703401030000380880c001d48220447c006000c80c00181d1007512068003003802c5668a03036007039074480d00140320b400d410300782402000614009800208581456540c41c81044541030250021035900003002c581480001070607200070740704080746160350302c1d81e0b441c01500508040080303580e0014200b0008031102e0041c42980c190401103003200210360070a60303008180398402e00c1d6100034440c462a1881c0030454601c05544030f202c4d4000d00c850710908500000d030200559030b00400401c104d42d04129282d96010a10070100c0e42c54591003c030303004d021003c85402890003841403490f10700c1c010324051841400910540100700e01c2085804c141e84031024081c5200818070045c0c81e503441155040c64020055110710b05111141c404141801c0c1c1e800011043c0c9102030b481640181c1c415801804 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 421927589 1250 421926339 421926341
    0x702011401051215070203130603150603090506040b040201121404050606030d0212180409030503100506090f091e04030903050d0801140f0a052205060a061407170a0f03 74
    0x201400c81292110b800041810a00340e4442e44c03010748420050781003001c50060307802001034410a00619000300a641c0d01d552000780101000b41465038060181000090200d01900c50100c065030030002a00203035449482d01002c411b80900101c1c100300c03429043c140e40200380d100b0a00c0542c140541e281440c241810501d02d841c0000c0c3c9050b01c0f030703000b610f500c540ea00d80004007450710b006418501c0c0d840d0005a600f22000c025030010642c0c000d030034003590004140d8040c000f144104061000d00d4201c2c0c0c0c030381e0300f400410300903400d1640e044044402500d00c0c17854101d6160b580201e840c0004584048251a02441c4001c20354084011544201e002d004000702401822441c43c0a03140000741503140041507010340307010b14416030180540f420010078944481d0f8407072014100c050030b1a050742a1801008804004001c11706440916040100b440c6103001203404048a565a0b90f040c00f94920348054001c030740c0400d808441d0200594410500c0e01c3c48a00070b441500039940f220200b51600b03820183c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 421928839 1250 421927589 421927591
    0x501030507171f15020604030f0e090c120a0615030f06050d03170c0a140f0d0c0503011805010503030307031116050c0a080a0f0b0a020d02070602040f1d0a0c140307020114 75
    0x80130144042812070301c1544c0020b01c40d41c0302c1d8042c0390000e410b061204064030f10082101c03a01c0d42040541c1c0400080f526080c0042032074440003c900207041ea6400c03410011a0494028945001202485050310500c40d401156032000d5411000603c03d80d100c0004440c0e041b050b4048001c141080503550450020503203950f031094260130040d141a868020040405440d291074a20341c26022903d030316124240029600c3e00401c5004c100204500c00c0005400ca800920821440ca5006410b51140300514010b540c100c0e14043d00131410340d101e201e0b017070780609884d03061b21038148030600071100c1142ca030340c40c50078030903028130050302c006101c500510178107154035000502d680d1b00c00c03824200090441549035811541048940400c1d0303c1c1e14908201a108070b07090248102d0000c1118014080d6680c020001c0326042800301150b950b483c07181d0080003207404010004105040c002400b01003150308110a003080310324080100d003640850a00f001d030001ea41000060f903640900300c88040801c4101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 421930089 1250 421928839 421928849
    0xa020c030322051e010309150212040c09140114030a0213050a06240c080c071806061b030c0309030206040e1506160303020705010e06070f03050a020703090501030507171f 75
    0xc1111320038045080c000d154120b00c4224109666902081c0502030154003042212100041c291750310700d4030086298540000381e406441021204400041c03082c59480313416055007a2500c2e20240380c0c43c21710b588184144450100c0e4160083e00860380051f5a41600483d01903030620002405080c054015000c8460796000301c0002c014010700c0c61203040c41030f0312801d040e84480c503180c2031501c618130b004c045a000703242403001d00784542107001ca002c0c101c4030903c011a001d13041c010030a0b030380d0715101150a282a903101688404240c1211000300380b20300c00303c83d1828003d0800b00c0c03000b0703500e074041040340e8059030000704048003400c140802d6298241611040380e02c11201c240c240240780a520306c0d00340c0d01020050034981e00040b0326040120a412410516180c035094070030394034294101400054000c140e18000a26043c0007030395000c2d041c8240e84070943c0581c0d413200394605000056004100180c540c0052002c82c441400500da040000c00b407003891400360802040c40076245240200c03605804c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 421931339 1250 421930089 421930099
    0xd020103510311040b3c040c0801050907030e1509100902011409030703080403030e01020607090b04091d060a020408070608060f040203071106040c050120060406020a020c03032205 79
    0x810070200c1c1d42c3c0e0741c100610480031180021103500b400005241086100e1080c20802d20103c82920500d4201080c1135401c46506010300810f60301d9000c1104031400e003030012021454100040c40346040000b082944107a0605000855001b2620380c207241c5010500e03400d007844000d404120303c030401800141d400e917901800c2803000c03080660010384003002d0303144c40a50b08080030410000301d5404006d0a00190b03002100c1d295550307221b00b40201000c910744150350140c8200e001003200d05101ea007a24088410410111741020b051070600b1016000c1d89221400d81c810020f04000707220801d00900b40143c0c004500165260b1034083c905007000351540c0240f05120060081240070380310b8180480e00203604a42c0140d40341d95180040e101e034442030380c400c00c003803199804000820107945420000e0390001d80394815611103107120751003e4500c2803050710254000740f000ca00060621b4018181082040c0140c41c01030800b000400d285401140d104503003201d144454005906601c0212800761a080d11 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 421932589 1250 421931339 421931501
    0x1309240c0e061801030c0e0406090b1215010e07110d0206101a07020f06040b131a070809040b030c180a050c0a091811040b0d0e010b0d020103 62
    0x32006025283c6800d03003030501d80c45041d800ea04610070f00706080c400500034020054162a00f01c1103001703203114071013240500d410324400c01d010000050ac6000c4486000c81c031540a03800c1a4148000c0c040c050704800510141030b1148480220610103074042a22941c01044203140607a0150b00c1c680c01c60388500618001440e24800005c0c00070111900e50303805071207519504d0f601c40d0100c1c00314803440e44041c84102e03022a442e1b00036803a40e4408803c41c0c15050010900c211310b004000c0c2070344140304000b01400c00030048810141003030341024a00800090540e0080b6601101003032282030b0540074084100300341410499644c1d441d02c521034010000d070030382c1d5041951003600038005400c01e000e02010781c1c0ca80c00000c048458190800c820002c10000039a40729652041c841142d80c001e030140c0803150742410b004120340007052180c41d03010400200040180501c070b400660051015070718090200220940c0905e84010340d02c1403000e40758419102060045400f000740300c400803150102081510010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 421933839 1250 421932589 421932607
    0xc05031906081e07170d030b010f080103060e0a0501020a03090501050108010c1719020f0a03230105061b01020307050406020d0f020604080f07120801050103060b03061309240c0e06 79
    0x25000c1c1e0041210704604030a48031a543c1d5031038018258004221010442c0400c04610000704101080070030705c0c2c80c1804074200c1980156140007044400c04001740d4050010808101c01d600907450b058540da00342c841c42d8809841d41801d9034021084500800d856214610030003109102d43c50042804000820988440b404014080c2c3c0145e4011014014800e0100d00e0307001542d003819059207084001107541c0d5950203030f4084d00340c00920701100804e160a000340ca01140090000c000349006009003561030b0309140800076140c002e0007040d00303284003c22100800390400d02c015805694140c0b80c86482e070341380c004020701e00042c11240300204a00403031803032030280d00019201d801951220255032545c5112201540500075900040c05000c5c1c226078202260707070001142c9040c0ca0080e641400015118114807645100955109410901010300c0c0171600510780d01074901d280c071031800e10546041c40b1902e0618401402c403d00c4200c2e998210075409560001900c2d02105025111541024103503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 421935089 1250 421933839 421933843
    0x4080a03081f03110909061006050a050903070e150a03080f03070e031510060207050f06070302012c0c01170a1a04090606090609020c03190903060c0503190608 70
    0x140001001d20203100003107412142c0b455441041c200450040d40340842d5241400007020184002040c0903001120120700c03040401300c1c50030301c1000c40c1030f0f040d44010318001080311503912401e400002c0000502654020ba03506005890041a4607200c01265042952a081c1c1400717428107000c1c42501803403410000036030a2815149440d6403200b042d40c40380d440c040c05496000e12180c120390306016100402403d9501a45d105004068401d1f60000d40f0ba180c0405076a2920b0a001c4c4030340c0f0804807036000342c03189850f600400e5080d220f4400444d000c10340300600c110b505558200c0c45096101503901c04e00d103840802110300209001d10f000c016103450140c0344124030b41c01410f0004010b84490165031b200e060480461354590010780100255072071401c00500412490081015840c1003a0740001d4014460003a076080703a400c28041e6242c0880400e00118400e140c1c20218180011420000080b898902c42c0001c40241c9840d0117540c2d281402d80b2000c0360540d20701e4620010304d0400709100302000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 421936339 1250 421935089 421935103
    0x100e010f0e0f061207020606030105010b0409020c010b1210050702070f030f03230904150312050a03060315050105090709080304051e030d0e0909010c0210050402040b0901080c0112020408 82
    0x10a041c542160000c500100d8010104071407190382014002542452549103419807900c1a000da03070030380e0f2603500c40d00101400d0750001e01c600f00b04070b02c084c0000c1c01100d1459000340352006102c4000201d801c160404140d100c0c1c24044245a039401c92640807170324070311074020140c2c4109148050300c582810800180540540c60101074a5056418051802c040c007030200e07000107400c10011056030f081000040ca070294040b07208039025038184528841109102e01d46d00c82a240e00800c9007416003450b401c200c0720342e00800054001c1544926001001c5004209003d0f040000c9000114145d810801030104801015000c10b00b00020748504004882004c010340301030300e02c111410782d048032580e03001c4c0440d46608049241d250203070082c1d00c1030030b0f90464150704010500b6101c8000d00d940d1a111036003294540c080950144c1c12054031600400050350095034028401000010207900040101c0d2241c50246c22600c2da651050701880815a00b00c04400c9503620782e1740041d8a003604000c8110b03120f6413 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 421937589 1250 421936339 421936367
    0x38030702120708090306040c080c0405010b180a1e0608060d03120b0f040237080a050408040305030c0c03011d0c0f0d0b04050a0b062b020627100e01 65
    0x4020409104003d01041258800c520040854901d400c3c20300340072901e1b05481c031400e4070610039006030740d0f0340382403602034207048803000c425241c00e0198518596030240314842c407099000e9140d00000c2880c0100001a49010312003007601440d445c03e00c0f602600c02c45c0c014080c0d13849000d440181c900080c3d0302c190001030b4280c41042c0842c4083c1e034130700031409036074100f200564403034000701c2d5078114500b020003045100c4401980074000c2800400c044602200d1070464035001400c0100014049403541d000780e60405d2055071110f185c91703900d4880604540280c203129107590015400c502c442c0c070f024014024000250440480710304c0c3c04050752503580d648034180c81c2c041c900e11031080080c0d6885d80034000541d138110a40080f02d00c1c051800c503403199501002242c009201801041a034188144880130040520340e9555035001e1a00480a11059a007001c070383c410800c0003070090030907140440a0315584a1440309685140341410081d407240700b0800c1b0410825060a02d0316181c1e030000802800c0c01d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 421938839 1250 421937589 421937623
    0x60406050a0f06182703031b05161106070b040506040b0907050d03030f0605030d180b090a050f04090203030a0207080601091b110a1a180a0308150a38030702 69
    0x140488090340321070210b64000a04980a14000916030107400500d03c20140c52300b4038050804041c019a03d50003400c0e440551003040c1c805200c0055036080d440248844004d000700d04000d0a5900e2040710f2700300300c0c2c00300c8454211000f440100140c2d6400c8541020003030700949095414500410104040044007800f095250070f0442a1290154481800741002905071404000d00030009003c0300d801141140510005000000700c00c24940140c40c40c0b010010300b900d16942c5000100942d190540c1c0352580c0c80751f69440302000683e0b0410081c00201d2041d0090f010003031504140604051050780880703145030401e00d00c1e207070020640c2003401600a01e428000c0081e4030306100286042c5104100a0080c0d100c0300d00c0c0400e0000c03a441241c0b240721910300b442072200c8a145825107404443c00d008001c2045000032540b01c1e0303505409664bd4203001750001010550300d00007270b4110006460304034081103000d4858104203261070300d10780c01c541016840c180365041c02c500007550f511084006061607 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 421940089 1250 421938839 421938851
    0x170708011a160206161203021c050a0b0a0905060f0103020f0a0c05070f1e0b07051b0d020405010b0a1701140d0201140a0306090b01020d020613050f060406050a0f0618 73
    0xc1d0a0121045291074000c0e12450321500c5c0c5080000c2d40904030441540c6a103160324040e0000340c42030003250303254400c1104103102c107a4025102c9000c1c1401500140e600d0785c4400058449468070364054008080654001c2410705000085c0304a07012a890903a04144c01004418a1000c00304200c0d85000254507010070742d0380e41828404d080402c0c40d00142c84500c0e80c0d0b5000030f080980002400c100604800c648600701c1c3d075900078207480d8803527040300070300d10b8200641022403d8541a00d13200310440103000004030035000c2d4000f07400c4410076000242c2801d80440d4409040368080f0704020980d000150a180c1541090500040440b914a11b41d20a00a90001b1011a4402e1044203d090304d601c689544a07401d0f4140600a00300502800103210b03d0211040800e600c00500c1d000d603031483e50064921a2100050b82c07102100b032040583d01407003100807034a044002040721a02c00c9000714030000e0681010329142c000d481603040d00c00702140c2041c00620000003014040d6034040b020840c000f0340 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 421941339 1250 421940089 421940107
    0x31a0d0b040f020603040302010b180405060718080a030507110d02130506040216060525140c0a0803010e1b0909060f210a05151b0c07030b0106170708011a 68
    0x1c42094030000350804c4010040c032080540540040b82245001c54914001c1910742c00f50342181402214054000d510400104810302c0c080d00319607200d5480581a1401d450311028030600c0c10176465003c4000550008650050041d548241200030302e00b2165400506035540004030745079601442000c14030f90f96000f1070745035540c3d641214480c20201c01c14500000c42c45c10010b0049c80c044410211f80100341f840a01d0706e118008007040101450f4070384509080054a034008981c002001c170070b40c0ca10903548400701040e682c501440c0200300e0302c280126180307000c211300440341a040e126035000c3c203824043c4501715641d041149a0288040e100b400070380c0c80d22030000c0c0c5072140800c000510b00800e28000100550040768005105004a0485036094003c0390f002180200c21a1400901c0b422042c41c04030003181d8a004001c0900d141003103544840d12500c64001800080c0c0c05031000c10416200800307030f41d007505407580e40030245003040c202a40c50000c1d103108d42d291881ba50002140b00040c0d09803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 421942446 1107 421941339 421941353
    0x5011a0603151305181b01020705040f0f15080d0801140105030601020a12050711060c0a0b06030109060204260601060c030c030e0402031501031a0d0b04 67
    0xd28642d503a0902840a10707800440580c00001400318018610050280c80c0c0a014030003040c0c15089a0607030300d240b40c000800312071101c0c68003491054a90b41c0c0c010600b0380c211002900c0c0880d00000000e041801003140c80c407152482c41c5006083c4400030820030350401941d01d41c004075840c00c0e09440e000c1e03031644024402c0c3c4001c0c0c1e41300d80e100c007107039403140c00659003024041c0100c442c24000c503960b81c07455a0f40f032140c000006101040000c00d00250349011541404150340701c5181018401150380c441e01e814401030300428480c0c0c04501940c60940c800b03581f140e004a021902c564503001c490883c0c0d145280742d07070101c00d10307004841a4100b001c20441d0480d07640c1c1e01c80820b0030300aa42d040d910300040c0384055043c01b840403000401a12a0b000461007a080c04a1007040303038100c28000350441d00d44492180a032000e140740c0000300e441d20011303140d44541088005146070b0392440c00c0b00e = true := by decide +kernel

theorem cover : BRFrame.Cov 421762589 421942446 := by
  have h0 := BRFrame.cov_init 421762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 421762589 ≤ n) (h2 : n < 421942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
