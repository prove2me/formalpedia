-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4378
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:25:39.1449+00:00
-- url     : https://prove2.me/submissions/453698c9-e35c-4645-b160-9e2af49ab469

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 787230215 ≤ n < 787410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 787231465 1250 787230215 787230233
    0x1030f081c06090b1005031e150a0305010e2116020d05010e060a050c09090a0504030c050607050a020d03060501050a031d0d09031b05060f090d08040305100c030501080a060f0207 78
    0x41c0c0300f6200c01141000c0800180f1225a104c2e17403807a0f09000c1e06104011100d80038505542e0aa00d00040c2e260080d10f508c0c00980d40389a1200007142c000c0d1b84e030800403050120542007521600035110403200d00c19500084505048052802e001a2000c200a9510300c110a202141022760004001131014401039891500f103511a4803807021580042d020814014aa807240c254003d020140081c64a514440056500c00d8001d26403080642d0b5100030800389841041c4810f0b445900200700c1c3c80034280504082c0541c0c01c0800c0480c014403901c006200e84a100e80104030840c0c00603140c0504041e20080140c02400031403a19a00805036003004030703510f01040118042460403a250801ca03a070031418501030f911200b000481c2c0a401d010820006a00e4200403204080c000e10f98140d1607519100001e5410300c181480030b012a50080b8020013070240c00305111002d4441d5000400403404103107405d4055540912403143c880e04107070703616404900e05070012201401c1e14100141741804594500440c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 787232715 1250 787231465 787231469
    0x6030e03090604030b0f06030c010e010305042607050c030102040501081503011b0c021516020111070509011403060601110c040f0b1002010c2606041e0c110c0901030f081c06 76
    0x2c0400175828840c00070300d200c180c150000c40c180d0251044052820004c3c0400e140344181d24101030b601c100203000d00003403542d641c54044440c121401c500404003030316916500221000d071094041c200349010580380505c01c840807a04181c49000301c0c0d0ba87d0f806c15152440240c0c05854040d501e030044d00707070235015000c3c2c140c0a041d0b1035240c10090445034014001c442030306c1500c07a00060310801c2031510399000c4540380700301e051382460407055900f80780010700c2c1420002d41c015500903c4c401c0c00412070412100100307081e030000b50200c80117940d8580044138070750318560100703906402140c40307080b0034109034000c0441211142d03408684e45c00359001060000760501180b400607551001303503107101c50307110205d070550346240300342c182c03414120045002200801500c43c92103540da5803500d800300104201c000107400c044190400042000136806407401e542c50310854014051040004810309e48031100a0584e60445412205201ca0796115402c9900c40c80441130260804407083d80c424101d4020080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 787233965 1250 787232715 787232723
    0x40809032b0306081207030c0b01060306060e06182b140f065a0109020f160303060305160f0b0f19030204090906022503050406030e0309060403 63
    0x2824005040455141c09940030100405082c00801c000071180066050800d82580150704d07941c2e80d45180541d000c80d2142c00040003110f25500001d0708540650200b4221044c50300c07680404010181044003e22450072054200c9141c440301c00c00a00b4090340c04d44c0304840840c0740ea26250140c10b0001101c0540d00011100e207241d482d2550600541406103a112459180082c041420060340e002681210b050380c0e0401c000090f8021072442e030092274038100b07501807680c104511800c00b0f102d618800c27403206805280d482506000140c860444d04c01c032040c41c000030031814107010310000c180a05580c000000d40c1003588641c800320124200b0f1000000c40c1c2c50490a1030f00542c81c7c41d1180301c43d200980c3c86075160010500c100172280d10100100e4a050000100c1764504c140c80a80c180c000303004a4100c0c009151906207404100b103115801800c4140309400c48518450107414880802c818080e03001700080c2c0305000c00c20525000341c101c981c03001c070140242c0381080c00502c0400d0f2503170402d070b101792 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 787235215 1250 787233965 787234003
    0x6120b060a0801090609120f1e03142e0503100e03040302150a03060602060c04060c05070e0a0f050604050114220c0e040c0e0916030609090302070f060806130504080903 74
    0x400100a4000011040c1f6040c0138982d00da0880307002c0d1400260f03001f800b042000403034848006500c698400404a0440380191501d0f04001c401c80c031464240c1011510380d01c0003d4400d00c3c024489400200440d04010003c0c074000510001c07001c06811508a80702c0c40d40b00c140808001603903408200d51252548030130b100c0d00c40542050007800e81e41503034007001c00d41d0400001d10203594000c45c2140c00b03032485800d004850310b41e6403405500d0301d4900d1784100100c0514000380701c04a01d06070418440072a804600b4495502c1302c0b0304002c1260001c0c81803403400e03035606c40805160b08119604a195050402d002c443d21118272070580180c6001c458080002000080b018070a80340500c200faa000010740b80a0100d200c4000201d0100b10300a0907021180100d181820415480780d0424405000e0b038000078000e2540d04d140107580d50006024212130369212000c0030031890310840d011803143d00020603110140c940003400c0300007811b01410030365084204100e880d855407000c0162000c0c0d210303020104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 787236465 1250 787235215 787235231
    0x18032503120b060d05041b0602060727030210050f0409090b010b090904060e010e100504051908070305131e030b0a020705030306122e06050406120b060a08010906 71
    0x508120150140c0c4094034078150100c1c1094030344600307a4030201302d40b010010b465101d0b4100740303084915076090010120001c280104505501040a500603c0340e0744680b031500207000000404204890b002c03103c04036096030100007600d04500c00c40d13001da02d507003031851600a88a0b0200ca0540c06508201716450302d030041340c0c08100c11000d20328010a29107040c0c505008240001034040c010151014110fa61900e03180104044c00b903200c0c54096900408560800c05400340a0011303101c129800e6415004841e50b10b04000c05082e18540702542c031550540c5061150740d02a030346a0010380c42075581c103500c14004650030400060180200d41c00e003400c1c0078039900d1440e1480220400816414031a8014040003001440000940390000c02c100d03050215807110022507490489805131000703010724050042c0210145495407408884526081441915190018002950141d1150550070520301c8880c07004603107004002e81e000071004062003104c90780c0d00e00d02c60a55040716030640f4103581d50b0045c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 787237715 1250 787236465 787236467
    0xf030a02100203071b020f030a0609020f0d05120a09090f020c010608070609030633060f14030a15034716050702060304060603030e0405040b18032503 66
    0x1c0841044084095156140038200181100343d07000040440c805401090340840d50340c445210312000003c2d04035403840e24581441409040785001c1a4020900c2c00011078081c01c2c07140d5051002a0407d0041885c92480300315150141c2c00b2001441c10042516004a281846070103400e0500007020405a2180e025450081c21282c0c19800314486d5402400108a00758000070a4400c480e008003001481112504001818260900141280c01d14591090030311b100c5010f66441506c1c510340d90792440390603d400507540405130040031115200144000703020003069800170b0701d5004070347c414180f5841d030341d80e80d21241496143c4c0c0015068805400c50000450f100d401c081401c0d501e00b11001100013580c0e1282c01c00001402400041d81d0b03000c5c440d00c0e0980968221140b903a40030340600d03540d15090812074020702181c00110005a10900c0030203440c41d250061f240038503004030403184192a0441c4000b05424180700d6080d0500050007004c45104c942903210040405084038403084507581d00d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 787238965 1250 787237715 787237723
    0xc021314040803010e1008210c0706030905070f180513050d0519030911010e0109030b010308040e0708040203070e0709050d0b15030304080703060b0406050910030210022116050f030a02 81
    0x300507080406c0c01d076001c010312000015400b40e11040c030118515100480482501c96105001034290140b00f007440004281c0d9040d888000101e01486c03e8841c0c540c0c596685220800f030a00c60100d0070074207030036100703034034401507102139040100395040009002c41c940d140c2c2c0c2030000d4242d0180c0400c1000c070750440844566401100030441c186402c20a0300d2a0303940d41e494144120041a0400c40403201d0390400b640110355020156803c0404140e044d80d681c60494001c1c0d002e40515852064800085010607005190f481d01496004001c4c214047c14055064424803000300b03c1010040c0e42000003a2a444855048992030b01500c0215400d280c50000003401d402120792040c0a54410002004081804280901600c0d800040403c04202050009010300328075000990b00180c80c3c1d05220307081028903d6041240c0c0709132850702014101132000e90300d441120040817030350a03020915281a1041310000e204031156900360b544084c81035215071780f400b559100c10700d200b54000070798440d060350104 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 787240215 1250 787238965 787238971
    0x7390f03030f09030c0b0a0209030601030c0302010f141605030f0d05040c06091512020f0c01090303050c0f0a0503090f0102121e0103080414010e09090c09090d0c021314040803010e 79
    0x5003d01180c4207503a00108245074100000c1c0c1120310000c00701710465001d8044074040d420040c105c801d103503184c0c01d11080000881c8000c82c04a10b0291004c1a554002c060205007030444543c0182021103500000310020040002101c10b404208000300100d9680c102910300c42110000000b86480d04ec64540c0c103501285e0000e60500922803002c0000415109184640d5180d500e0141c40c2e840d0500c03540302c068010110300c030b00c1d1a00e0110b51411240d00561190000d14042d560a006a4580082c41c070103510501030062040710080090744003003030154005503040549039003243c1c030344801c480280e400c82c8c0105400c03203d181d20a00c280200183c2008003524803e01081c0e810500b545140e850460500c500c0c03040e030106e820001541c1100742e0144000c829a20070290080201d0b162449440d80c45417084203007030307114400711800f00713100510000d04c00460307030240e4617910001c40c002e400b044440300074281940d039070585a01d0041c40421001e101640079501c214041c0344c50f541003203c0018480002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 787241465 1250 787240215 787240241
    0x901031b03200c0309130908070f031209081603090302090a15150f0e1906080a0608011b1803050d090302120a1214071b1a0307390f0303 60
    0x500840c54114400304c01c86115403c11600640f0741e0703035002180b0000c0d00c0e000c400640083e1001c9058014046610503814070107101c1e90710810b0450074443c1040844d0540500a403030f401041c0460014201040382c1031101d00d000c0c4c101001101e5403940051400d44044500b0860652a8190106002ca103403201e0310241c1f155010700804c00005e10320060403d20b1005040041105400f1003c3c05612582c03074032141081c850780044129600c0d1032010f40a59400e03642c08111514105001a0010040c41490803980d411040b201b04410f54600444800444130380c00b03c100040710f40c0c0040011410071035003125000301e0b00c1d0341030b02c0c1c0d00c0c42c0108180951003c0e40d69145070002d036854000200000c100c0d08191440341419160070310401c2c0d48070180c0c082c5510040900078800741c403001340c0b0110f0071104101c541074010921500024814482030703001c2502c40102080ca000307000060500c0541b14821403541c081812402c43c54070074501a80548043c2094a00c481d030030000506140d454000c5100c0c1100c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 787242715 1250 787241465 787241467
    0x70509190302010e100c0209062806020c180423070305070513060b0912010b04020c1b060705100c170a14010b0f040308071a04080c071a030c0901031b0320 68
    0x381d0400341c071b28803003208020b100b03581007000a00320355156a107000c05000740c1000d0780801c8031040c0260210445901525026103d81c1d4004882460603116032421500b00f04075040e200c0c3c8480e900d035094442100000241c6445080030380001ca90100b0035840118011002400d0b03081ca00000e0020444061080c4094541081e0301403082d44040d408407550341406483c507503268400007040d0360041504451450740b1500004417141140700000c1c54920120861101c0098015030508000c085e11445500402503040340c41f8403107440010b540009424049070400e03440240b0080c0e2804000e41088a41d019010395590001c1080c441402d10140584841c1e5a580d28214000b25038100780e01482c0b100810404000403034804110030301003a0740b42c44200046c203200c103041514262084d500000c07030300349161141050010700b240080d083e9031010b500b4200141e1864031907050140d40303070f441440000d05041e00d501e01014100100d4403d07210940083c1d600080445450302d0b148041a00e01d5003074032030090 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 787243965 1250 787242715 787242739
    0x50c10020d0f03022104020d08180102070504050f040308041506030605150102160b090a0b070305120f01032303120901050117012c100903080a14070f08070509190302010e 75
    0x600d1002c0c172404a82403564400c841d80d501d20010b8400c61040700000c2060001040920307180040c00600c41414400360250741c415038442d4123000403100c044034054400c0e407444001c00c0209000e402d0550308203004000071507186482c4801c400540341c407940100c0f07030144c2e10002c11602c4640c0301c401d10b0480300d0910260000c415014403a200c100d0490140b00c0d624440010900e0456039240c009200800400c000036458442034203010342a9046041d281201a0001d00011040b8a94646040c1644d074409000420b1031000380c1241044560a02c01200c1d51004000380b120f1807403040d1400d841004818000300700da6040c00f4140250741c03614915518143c1c1400b0421041c03420004c10200c4032081204e000c0c24500c00040310070300c1c2240544001b8070052500e80a0010b0641c4640d0440c49202158000d103d9003118004180002c1c40845490b000682400b8500c0c549910400d09a40c00c6451894824281400f400025001d10403499804042c0d144528080085581002d000e015410f021518103106503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 787245215 1250 787243965 787243987
    0xf060904170c0111091507052a210d0f0e0f01020102090a03080a090b0c06060f030708071707061407030e06070f031d03010e0c0d050c10020d0f0302 65
    0x548058001003030441101180000160140240e5149141000013440b04034903921490b50385611007030310305000e0f0303169111780d00817501200101c4800755801801403d81d25840b03950345041e0552108014011000c142c0c004c3c8081d03646000c5428102052601d544034401e08000f030703070726002c001d01c1680c0c24881c008420718611a0450303070b14048030750161450640c00d4507103030040b40280300d132218456101d10702c02d201105126117000540811364060b1500c040050306c504030403c5500594022041030303409500050307180c0c100714914130041c80016003110b014030b807145091402d02c0055003207840c0000303004001e0000d129041000034002c2501d41440114611424481c0d121885000005000c1c0840c8000300100d1307469450880312201d421540d2041c2459151074002d080134814180b14112111403024185c3c18a41841000100d41d032510080684a0811003801040300305407205231242c1c054150f140185032158050350071240c40d194060005d400014201400b540c840680070410181305000050180c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 787246465 1250 787245215 787245229
    0x3070212070f0b03010e06010201090b130204150611010f02040f051909060b071203060e180c1002151003030203031306020c0a0606050a060e0d0f020d051507080f06 72
    0x5a40580e441034500e03601104040c9003800a62141c007100401d4440007460003c1d03100514140c42c128030b880140da881c2c0e40e00490a076403000501502c4201007001052070107001e840440c02c4c0074409007001c01d403c01a01403441407440305174069004500388099240001f1020320031954801c214130821400e0a003020640d401001e41030103540c0c0650a01507218901441000c80a4018080c1440a00550b501c0d03116490307051300300c1c0b40200d80a1400311401e403581c500a0207040c00381d403075204484829035907800001000180d40401c600381c5000d0a8a0a416500c91060810015103c2d800514900c01c414840e11941c00d402456032042850000c02400040e9011040340c0e0400c0780382012000c060700c9400c020000344544803a0140c0c0d0f100d000b4601c020003a035500040c007150000c98104440ea56121002d0340c00100021010303900190b481030100004a0f043c102886050001d0001c1420072605d94a0519040700c03502c1c001e910100c1402081b0306558002a0141d00c00d40d00c450b01c10a5061a8000ca068 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 787247715 1250 787246465 787246477
    0x8100908030c092115070f0212030601170a0b0906030a0c0303030c090e190c020d090909170403060203010918021809210705010605150d02130512030903060109050903 73
    0x60005801c5403e55514a180c0b41e407100d4210840007030141a110b8140d481c050420f0030300d00900e4134000140203d000c2c11543c1e0030764280e600580000d030740002c520030850384024034003418402d1020304001c0220405402c03500c511100b4600050450203001000f0054a004121900c03030750240301000009030005c1c807000102e035810b050110f4100d1031100141d82c002c400f60854060a05078904006c1214103081c03605090303810800c1c0422080b224a002241c542018051440c04a03501410400005030703a90310008200e4003031003201c0010500442c0c00d90341035001d03030703c00c0d5072094011005102400203449000d9032038034500c6c11450b60f0b19865000c90291516040c036091603049000010f0000d40781030003403440722000c0800c0c0c1348070790f48400880e1050b41c01150017070342c503580380c00c201085508001c07010001a00a00800a0400d52016141c101941c4a40840c0c4043c102e03000000a0b951540304d8541580c0b0701e51809161500c40207024940740c208140d00100c0b40500303003020301034000000710440b65 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 787248965 1250 787247715 787247731
    0x10f080d090b090117040b1609300614071101061a18060301080f100504080702090c0c060406020909131110030605060a030606110304050901091e150810090803 70
    0x7032a6282900181e034500c200f03000740020b10000000f04000c2000341c01f125441454142004078114050107011200b20780140601d445102c0960640404210420340c1d01c0281040441042c4500c4140c1d92404241c5071482807080c001220300090002d0160851802031010550b034000f000300e03c0c5001c040004021000108180004001803128540280010032400b071400140120b69a5651008210364602c2030007800700301801107226222810b0360303034014580250f80110010741491015020401c001c2d80103440752a0741072007041400d040c00f10910003680300720301522005882d203070803201348076101a00428900d0070700c51131044a070020b2410081030119440030340d40412450583c020a5008180302c1c2c1200d0b9101e43d01141003603203268960444020344e40282c0c2d07110048540d40e80100e81d240031318082c1d50fa05c0a40d100043c4405421644040035180d210507040c02c203410251180e00c1128100305403034800b074020f01c1007400903030010440d81d0020301d0501c2d0104040d1409840b260b0300c80c000585408 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 787250215 1250 787248965 787248967
    0x15080d030228021608210906070c0b0a0311031302011b0b0408072a030303180b0a0203011e1203030b04110a02070e060f03100209150c030d270605040821010f080d090b 73
    0x1a47c6a00c901041d1151180c0c46540365440640320040c08100d50000700e40c4030002070500c2260040c2ca4810341c15039009501c0401801d9480c0c0c4107500664440c0c00780d40002881c1561041e03203001042c17440e00c13140d014600800c50180d135800c883c00c2c5401c1920400c056000342d00440d501e480500b011070301d4003c0c100da0300b52800003184980d054403100000c0d0b060501510705401c0400703102000d4410781c0218101e9561000390402000d21139444100000c4911078410444149040c810120340241c01002240d10000c0c000141c10302c120b07106e40e08581001d0304042c01a07200890900501c4039140c8141c1c3c1111084072034810102200d0700013581c84400c8101040d0290700030035003c910f03880d05a10348000400b0840129203c641024200b592074024024a904541c10700340107041440341c000c401054400300007217680e000300303082e01d50302c3c05400c0c041c008940740300040007100325101c0c0d0051440b030000850764018803103503d070040780c2c01001c200c0d8000d020543c2200f0316510007030380c0000c0100c04858144001c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 787251465 1250 787250215 787250227
    0x61d0c01120608030c07171f0b030c04180302150c0a050d14180c010c020f0402091f0903020a05090106020a14120706020702030115080d03022802160821 67
    0x1c00c040c046503440b01c9080d04c40804e83e030313082034008194201604c1c00810f0074050003201d030700b18030b0361408800ca9514070300c841440601c4200f2016013003602030207005070032a2054000c8001007801c403002c044212100c200111400ba04056047c09885000031100715501c28074200840a442688a00401e081c280400012800c45401d800d812416540c4048200c0d1a150301d003410000c1e004006142e4541054003551450681035030042c0e500061180e009001c241150400100740002540400806a071141540c136040c41070080a0a60307020740d24070f0f80d03a16000c5038a107105000e05449035803c03141c81908070b0030050000c20350000700c0007080d507006408c0010103d000002c10b410a03e44000240c880c800004034501800000e800030305441e4400d80080050402c000c00140c0382034128010060036070060046c014103244660044c049040800d00d11460f0f18200401704203242259413041009604160007614110500034800c00091003a1009491301032070360006403070048895048040031000110f24 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 787252715 1250 787251465 787251497
    0x71b06080a152d08151e0702030a0c060b100e150403020d02090414030708031603050712111612020f060f37050619210206190804061d0c01 61
    0x51000500d0113800381ca0640201044012004008036580110140e0300c0201180b81d1030f8982425100f060f40e503001e10306001c3c20392402c4903801402e0ba400c0c0e1725651542035596456464451000b103000c183d45620112140c00e405001090350180341601d00d245050208002688400c10040c88099049400e520555243d1600c500c580b03d44202c002954071000c5840010400203100440c0100130842415080859610048080d00c80c22180040000c1c079a5072080042035054020310400c030b084425143c2401c2c0c03183c1d0f0b84d07690301050300c105a500145003d4102034254051211008071111500a0b01861034000360380c2c000000003030061500d00819440041d0403c1e403042450760310b81c09550049108206640a00c005440103643c0144244041781d5484188402800d414088500c40c01040355045490800304082c03549009090740c000c5030402c224181031640e9144004042915150014a8107080c2080011503045107481755040540001c0048a904000740e4030b40040000d2800312520300101d05 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 787253965 1250 787252715 787252799
    0x61b0c0a0602092b0c051c17190507110901260304180203040611130306020306041104060207061b020f13091b03021306031106071b06080a15 62
    0x211640c1c0e03003206215010b01e103503401915413071640c010144290000e80340c20400c410070428886030701500c06080c6514000902e103a00414403d50071290301c90a20034840080b143d011344602d280360000d080010360200300081c00d0070b540076106003a200c010f900d44c18100501c3c00310b034462006201000308070414031441c2404104450107400c4084140241c00d40e030319941350107504107841c00c450041c1400d2201d000d14203070340705540c103201c01c1801c0c00c40700504c6c517290b000084d400540007e0b041604c1c0c1c0302ca1400b18000000034802014954005c000540c54400024141c690001c024000c0400c00f01c00d60002d6541e01c1c0d2017014000044515110318506280507400420200d507005100d4560008500c0b90b60340300402c6c8000301c900a071580409038011080740811146c007404000e00031b5079881400e0b041810074601070640188101d444981a80c1058031214a00d14141d000c180000d1042041003142d1149005200c070341071070380c881400014249910303503071600100720921005c00341c4d042407140302c020608 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 787255215 1250 787253965 787253989
    0xc07080d110c010e1e01020c0d050d02060c031b0d090204050103050f1506030319140705010501150c0b04060209060f1b06090a0309050d2102061b0c0a060209 69
    0x2004840024211a6000d481650701060110740c074050301c02e0b000101c3d40079a000089500b00240b80202d50fa52802d84125440440e6004504500c21500e070007105860704800000100d000300000c1c0040c50513854004e151000c001c0440022038018014003a41e0001c030021040d0181507104031603150480b0394080c0005061204019502c542000c4c0004140039000c80d21440000810050303c45944041c0284c0c050b0303000070f499058055000300240d1040ba07000c11000c11080c039040c42c1007004604c9a02000c91030780c201e81010340301a5901c0c80100101c1c07640c078144076280c00315420055641649a120706044182c0100080c0141c0c1d00012802d0040d41c9040c12900144401084603840d5801894102034004001c80c07220054401c0e02c1c08a03804103400682450502d51565072903000a003000c080c0000802c1c0a00101d41c85105c0e00003851742d6000401c004035100c8015402001c0918155030744020026901e030780b286031242c0c06c212901c0d20f45408115200c4151304813401503503545911010900c070007150 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 787256465 1250 787255215 787255229
    0xe0c030c090306070e0a061803060513080c0c0a060c0209190b0a12021503190c0525020a092f04030b0f07171311040f050903040518100302060c07 64
    0x74040000313080e0031107041600480c042d1600c0000350f4540d003050703503403910a018014a06031403100800c0021500c3e00059070200c48422421405189541d50000c00c0d000103a4002d0b80e6000000302410307904020494000511181c80c0c9546800c3c2d0b81e4004c0ae1090354050300c00703c24202c102c040c00a100c0181e8011100b600d1016110b01411641c60420f02c4848800c018100d10a006083c031907a040c03928402039900807403440342081e0f00f10799009403810041c4001c0d901c00060100502200074030700440d0501d0400b1100c1c201020061180742e02c10070510300055005100c43c90304c0c080340c031072030791160811341642c0c890780000c0707040e22800030302100c5414082d55200402011010301080707c2c0804441c030701d41c09224030f52a0400100f50b0414400301070007085442b26640584070079244082a0710840e0b200002d1401380000608030003c0d1400000c2c0d4100316001000ca5000090820032820514030350b5400c6240e400c6540c074541031120782c01c02e43d03198910000e84240d07070105805040000c244005e0000b0205 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 787257715 1250 787256465 787256473
    0x19050717070318080304030611040522140a050f1b0a0c0f0501060906050102070602010c080406111201030b07020c0307030203190813080c0a050316180906060e09070f0e0c030c0903 79
    0x4d6070280c039a4903030090000b2545542002400190200c96030251819a04014150000c400400884d4040000a14000028551200308001e5041000109603000c1c244043e4041178524160480e4400884080c1900040340d030140c004544180747c03c81551640c460601d8020740d0007003e800c210345030004201000d0f001e9460600300040c030307140c240d100f80c04031402a0255180d955440c08140e00322111010b520000c01c2c0c01e130300041d0002d0600c3d444000659002440c05003490301d1181c1d1001c4048098004540440c800d400344514182c0400c1810300340042200202440c40c10756001c40d441d8140c03091107a522126401c0200304201c82d40b4141c40300a1084c070305200c600c9a8400e41ca540d076440c00c117042c0e4011400040086028100401c070805c3c0d00a1511240343d00c0c0b07142408090081019202e003820060343d900300764000811b03d01402c2e005000c40244c0d074106040414143d4203001c415440403030006d042c071800304110110081020307070003c154000c164032036a03803558201241c400c601080da4907000d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 787258965 1250 787257715 787257719
    0x11040306020c01051e07080703020d020d0c11100b130e2416090e06010e011103041409060a08071502030723060106051e0d020d060b19050717070318 65
    0x34154404c42c4110501d80082c1c000c418050450a001c2c2c500b590b928002a05a00014070418000e400620f000103045800528040406612404440641c0c00d0140040e200b0790915000303041c10000c148003e0100d0400b04007403510100016100391090f00b0b1705580907102d2070000c02460081c451110840e203c0c0e880703201c1c0c808040394a070340c030020126048001d5103100f00c05030318401d119080710002e4480704400e885031600c03a00e005603062030180345903a042004815090300340c40320508c0a400141940032000c4008890b4900b0050401c100801e0340d4024811888204407100c2c001a40504490091087d80d1222001540490540c4141c1e4000f9102e4101801d03004011072549102407891709501c0c081e00e1581c1d0300d5410403074261141d0f019120b9810b1030400c80c640b00d820000000c000105000d8030041c03800d0312801c0c248086c0c401590003407080d0031002ca003c41000d000550f07207112808492408a00c1c0008981e03400d1000f8048510301e4603150004a404401c050040e00f4100742442c50106500c8000c2d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 787260215 1250 787258965 787258987
    0xf090a090b0903130e0c0306120c060f0d24030f060f0c11010c0e0f10020703231e0a0b040f020d1b05040608070506031f03051005061e041104030602 65
    0xe0300061503008000070300c120018a08038000c05c018000d80910300c5261441e20351004100401c031846075200071600800884000564843d030003041200d42e403041e96502c80e8004614681202e01c3c41c140c5180c0c0a24409440d000f00c1005110407090ba80d102c61034000401090a285004160000c440d801803442c00300c8080c10f03070340c1000600d43c00c140c112009120f95583d0030400c44a021a245815400464450340200645040c4903480e0030002d00c0d1045810b11583d071349a0f002d401c802020500070184010f0700b0500070120a0003a00c41c0141041802a844a91007045641c1c64141d14005400541020007080c1007040020740311000a4004101800310402d5007400641d0f41b00d90b4542c0c02001e01844000a0181010300880d0210303000d10014200706807420082c042603500052062210b1000314450301e03003000a00e890200510700030002041d0015a000c10423044810140041d03205996484205190f114040711418500c4020f840101c1c524070800d00d20349407400340d50802080c5038000300d503a507400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 787261465 1250 787260215 787260217
    0x111303060f0605010c0507030b0615030f100b030f0c070807150b01031a0108060f061b0309091b033903061005072307031e0b0106020c0f090a090b0903 66
    0xd001c110701e0400440359120010b44007101c8504c1c000b000340d000454208081603204000c607501110240c44000d1a4040b00c288000325070003125040000b4013060309100c0408107034084076024107008601e00703285041c194908840138200801c2400415030019030b4208202c801000d55405551003050310b4400c41c0071001443c0038010802c040e80c0064034100342030310314418031006403e0340c1006848440075030711480140010320014440035500700000300000e200310010070b6118000403071010081e5488603d50800c014000901402681204510303980c1c0012a01c9400308503608046440c0301d5005c0c5902c11201c00c100915452540106100d40d048000d4004010000a40c8110011681e0700241c13580d60364181c27001e000f2410060800d10400740d002c0741c000078150120b0441c50340d203801c503110555070b075661a504150800030001c252060308600c1041050000b07429000d801d00e40041d00c0c3c00c0c4a1039011418414042051521036400a80420b11782c040ca43c0c0300f04c90158101540c10510300d010700700703141e43e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 787262715 1250 787261465 787261481
    0x61b070f0303120c0f0f0302252402031b0904060305010203011214060108070e040f080a0f0f03060e1603060806011217030705040b0f210108070b0708040911130306 72
    0x1484c10b190410802922621411102440c0343e2241c003a0000201411030007904400c1401c1101c00041240c005107103a601c1d098130f4005e00c02c0f02c200840c0c0138000c4404a4180e888042c12900c1401401802802c4034002c80c1d0100640c805250107495810300b00014001d85082d9002030625403000002140c07130244440258800c074090302040c80003140c11840b11782e82c0c8500744078251700303500800818450b04040c00c4803242c001d07000d00344e14104040c0c0350300c0b10380c52070380524583c00c041001803c040380300710b070405c3c03403648510040d0608009085c03608155071030200c030042440d840210b070041c200700068040da012102404114040703034082d40e120a0980120804100191810071680e907040c1c1c0300c20040f5084038840c5055079200780c20f05280c103400b000203130400040711401c404217011030413050003210345c030002c4005000c00118003940343c101280c1c188001c54010030034a2208104210100310741130216002c55000c03200014410402c01d45c005603074090700d180c8206980a0101c00410312405800840d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 787263965 1250 787262715 787262747
    0x190501020d09031101050a02160602070518070e0f0103020d06030b04051203071e0e0603100f080c151b03070302060a050601030501030f061a131a010c02061b070f0303 73
    0xa9000c4100d0090b2411041484001e0000480310000c4c4032075441800603001c03401d40c0c2d00444000c4503014000800e010596001035005911500c01000f19141034812a10603110010b244552420044030003000c81c1d0070b103580c1d140540c0c041c55440030142d02c2581103c001c00048070042181e01c1c0c5034900340c0600001030f202a12984070340400c190141c1d203800102e90140c0d11a495050100021080c001c54810508420b0b0040c41382d00300340c1040c107442c0d550042d40708100400c03448824604240c40d5602a00040d0410181c50b0301504620507251200e029982901d10310010f0503803a80450910340030910608084c40a40d8003010800c1c0d0109900000c041d40a410300510500c003654480004404640c000d10002d071aa030503841c640350226603075500680c040b0440c0e000c3da03a5445007c1d404290296480608581815a140700c1c4000c0c0c0f9907034090a008030a001d103031136030266036143c001075114050b00c01254510010059010540c8508105035001410141d04a008150707890401031710080307807803507140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 787265215 1250 787263965 787263973
    0x192007051e0108011a0d11070c0603020f0d05060a050d03050d0c08070e010f0e0415170102090a0b0315220b090103150e03090a03061b08010513020c0c19050102 70
    0x14200348645000001c0380384069441c011203030f10b407400b4180c440d0485500d003054840f08000c1c4d074034290700b0b03402241a01042d00080d51780d070746442d1500b0807101810781d100360101031050180120030945041154007440d00c241010806445d81e40009000d51156402268801480071701402010341201c00381c00c1000c0346a1080100b40903101c0241c803030700c204480d040001008001d841200350700803d000507940e0403916001c00041c84000c0232404480c039201100b114440401401c200008403c0c1181d065518040300a50802c082c640106138242c419001c0c10310b00c4a0044000380351038856280e16144850014440007e0f02e03c03211144112490a034034807207019042a4240c115400c01200c030078103e0f503200400b90610b24241c58890000c118203080e00105000810402d11590b0341c030700d12a030245010350300000e20b0800c140c1807003000c0300c0c03404400001d00149000400a5690742079001450049803600565035401502000f410002c1d003425803640b0003c00700c04450401d100075039a501340c50b420f03001c031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 787266465 1250 787265215 787265239
    0xe01020726040501020d050c10051510030b0f0f0105162913020f030111120a06081204060e0a0e040506041e020310111e0d0b0f0619200705 61
    0x4001c0c07a2065004540c09603001000b82500c5034030500040c505040c1020607034405c648000208403c0d0b40c015980ba541d61901406408128500964100300d042280d0408211103c03c0d540030460301c0342900550303482442210383c60031032a40180f08443c50b0f14080442141c60540901e403203016080881c11040760540c41e101d00c0d080404050038070074011941208044803141d0a0740c00c00516000c82c0e00a01d4055489a194031143d000c064081c0c811a04050b034030403d2071810f6403046007160301a6015031840e40c0803250a040c06500507046034165519072500b03050101e0b41d40d022a00d8a8100c7d8450744100d404d071400c020a105000c1106401144a00100e440b503403201400b62524940c050f0000c3c0d4150030201d002400e503411507002d00d0320038503021b0516041c10f01921110f181e00070000a03002d0301120020303030007161510600c104d8444a100f25081c10301070500001286d1070b8080d201d0001f19480c0c2c1e01016050309030050105110048990440782690692400741c0d50b02c51802d40700f414060319074000c0e2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 787267715 1250 787266465 787266533
    0x6030b030a0515060d0c060c030210060323190b09010b040603080f1323031023150301150e0c040308030103080309010906060602030d060b180d06150e040219080318040e010207 77
    0x101c03011260401c040074403605002096181000703070303800e0501c507d10412408910800c453f10500b0320250003404034001d203281c103030301890a41d030340b14030b825114600c2c00d801403000801c41030660b841000c5a605039501c1d00300c2c03008803010f42303641030300400c1e1038020f1198507205514a4003245a0084d41c2039095070302c40d01c04609180161205004c2c0002244a20803080803d007c2c1846240c0e80001e00201014101c04441c0220742140c1c072100000800c4040d0080603c01e14119030f98503038104014410b141d24003843c5807141c620320302060100900d58000000031400a12094103d40d14090304a03000f0003445580d614040e56981c40300b289003042c6030410100045030740048059a9245041c1050030008104400c100421060007400c2129200d580700f0501c0310b075003e01e8140781d01420b00004106c25034141401048000800c44045e4801d0029016081c40161004003c0d40c0c0440c0c60b00f00300785903040800002038050524040d0881c1d69610225515080c4180c02c40c184490460020344044240002c41c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 787268965 1250 787267715 787267721
    0x60e07030f02030d03150b090316031a0f0618281b0c0503160c180b09090f0703030e130504120809030a050f0a09050d0c06030b030a0515060d0c060c030210 68
    0x86c42c082405018001003004081348401041090780080c01d45001403081c00e030a81000103113030820fa030341c4480d821020321a07110100c802c5820507100c1202d941c1524094001502ca000300620204440f030b0b5100205c0ca10441385034010980300320102c0101c51209042c049a0000c2c00d2154002c610b01000d4882168984d02624030a841c15800102552500303a00e047c200c1c20a0009000c11182403080280004005040f4490040a21010040400c050040c2c80c10400700e4000a088900c40350460300c2c1e00c00e21200b00040b4074046030350500300743c1c082001d000d000076411560003a1540c2003134180b03802c204c00c1100b0044202c0c0450340c0f130340326040981c0b07802d11416580d004000001002c07503400c0140350345600d1500042c040d82d4032036107410401c03c2d071100c01081041c4541c0104980441e1100402c0c000c080e018002e010550400358000c08005925807903540c0d0300c0813001004c40080148001280b42034445140c4511440d82050301034800c03590720400148400540c0c10107a0050295602407219210a80 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 787270215 1250 787268965 787268981
    0x1a04060f0e0a060c050903030d1b03020306090a050c0c011103011d010510030b0a09020c03070c14241b0d0206090a03210e0d050a12020c0d0c060e07030f02030d03 71
    0x15008050852056550f00002e01025400c0c5041c0b2200380300d00400390b981080100356003200514040b50182111003000710303640449840e401407500500030401c10b6141e19022582c0007000910100e0f0b541c507030400c1ba50787d034130030424101055400d2518468908048000460480e040c034051040d203d0003030600c03140801001e0290a5001c0f04a15089140c10300c00e801065200000034009103506540c1c40d03200080fa031002c60500380075040071510301e0a1100029082d0000c003111002d0100201c6130400045c00c181c0f426148a026040c095200340d55000c81c0000c0d9003c030490401c1c0c40303807071074401c06000d40d565000c1c0403054010301c94800000c155540105001d00c1896160b1954440011900c0f000101c000e07460284400e41540ca03491140010f0040200c4051000707551035007503850791091401801c3c0340c201d412215585004100c0394403c0c4c280003036400500485450000d031400007601e082c00280801c90400c4400d4450804080140904c81c03d45c409400e00c00c07801c5030058000e6000c160140e803806 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 787271465 1250 787270215 787270241
    0x3030f0b0a0b121012030c0309080a0b180606130e070f08060115020102180f010507052a010e03071a040b0c030315090f010302060903070b120108071d01050d0f1a04060f 74
    0x80407002134080c02a181c4054071a0170812780564486100e24900b202000c0c1c280d44c0107031020240520134201c00e00342035001141a0150105103480d2011a440c400456100458941d4510100f000700006000c481e001e007038810101c2103165640d0601e140d84030340a00071403100180e556100100b042c014401c903a101401203030b00a41c021500c400304001e12000214584c1807108c100700d004009502800038030308072850882e00520051080540d0212042503007030300390500504809a0f09580d40c00200d4801b2107800840207480c1150060006490340101d9100360100e01001c03070214007000020000d580704d02c082101c2072950124203c1046501c03001510b0131501c40c20514014400b50501000a01c0d0300200a0115408070740d03903900101c00d0f40d0248042c0080c480c0b09500604c0450304c240501802413000c080750700c0314035031081e0700200303000e0040c40f82d2032080c0c200d4503841701002400c0c82000300250b00801441c3d580b0400c21071a0403d081c4c1114120748031468484c01d03901c00607042c450204e1a0341c00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 787272715 1250 787271465 787271489
    0x1106040b0105060f1917071103030f0a0608030d0c030b0906180702030f130e060d17031f0801050403082d04050109050717060a0c050703030f0b0a0b1210 67
    0x42c1500b4031009a020b520101003503e0100410115445070300b43c00800c1d80190380c0d406450305603016a000021a0181c00c400c10001480340904040b03400005607034000058240348000c5495410f05500181404e5014000074000403078101c407000041d034080c466001072a1001d1000c0c8a03413408007c000c0000311019613100d0384051181400c15a00c01c2c881c0e0344890980101d916180d12514401455085152100d121400307144d024001c00c0c48003084141c00031819500100c01c02010350311a0000c055410390108110008000500c10014102110520486c860030365507810751a1081c2a0181200311016404181d0020100d441e403084200048181c400300c0d031948041c0f4a0b15203014020050250040c0c0383e640d00c400618002c07442c24810080200380f030400d17104440840c48a421304000d001440495510f01d04010510120742003011525074980c1880c00099018020340c00780020103000424a0b005040800042080c020000c010080b080036052941039903070303d2148413400c07414140100c5041141c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 787273965 1250 787272715 787272719
    0x18190f060f0906080615160201020f0303070207030b1015110c150301050d0c0801050c071217130311060f0601180f051c060509030a080105120c150d0906020a1106040b01 74
    0x481100265000280240085225958503081ba0043d4100f00c1001c00190584034041c03045603010011200f01c2e841d514041c1d81035140c800030203500c42004d848040c20708240080003a41c0001516085005002e982681031820740070001d0081005200411010052180c041c40e0b510034a84010038510201c45804520300c0d40c0c0c2020103102c0500312010f000c4540c81d0507141c010688000070301030a0310503400040110b803950001e0904480313448100840c24140314203443c401000213048010150300c003080e070300c0144100c0b9440c50105d030074104e08800141140502c5080c0004040001702c40381c0250001d0f80d030041c1520038016040d20740c0e00d082c03060080a1007401000c11280c24102c440e00145000c42658840c0312038161202d00995404840001607504005942412940c01c040d078517000d010151080e414021480c0501d913507800141640d2442518040d9030101d0f1102094100c8604003950807003401905503915009010f5003100507003c011a07482080c54111000015020f4840ca81101ea00c440c564 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 787275215 1250 787273965 787273967
    0x12032101330e060d020c01050403142104031101090501050921090f0406030b0702010f060b040b0307032a08010e0a0c1421070c0c09020406020a020618190f060f0906 72
    0x2140580e201c50b00020f003402003590340c5000d032016100751081b040c0049031798030309490028207a4580c94245401c0d03450030301840303680d1342c00381e4024005651611941d00c401c0d215810156a490050240e508842d820140c0344002c110f030640000d405000007904071011510300a0046000c0303420343c040800550ba0610010007a4503203035040c1c00c80c03044040c1001841548a898241148500b100c00c0e0015039182d1a440c0c0c1c0d02800c0d07206a000600c5201883da0405060110002d200d21026001e0401c05890344208070310b0650032440a08030159030200304012807104a800382100000340303d1054908200000519081c000b80122040710b03010f0345c2c44143c440300c0401d1421241c1c001c00d5002d4501c105003082850b0340e050341c24072203020b003400da122303907031b00000d107103801000040340b80c10204080340148400c11035150005a0503481e240c1c121025516540360b07003520a00800e02c11943c40d4081c4602d2048520900400c0441c800d88948006990541d504c903003040e100006440300341400100041e000304026 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 787276465 1250 787275215 787275227
    0x1b0611161a190b06040305010e160f0e0f07030e01050907030b06180f07050705070e04140a1211100218100309021c03020c1336021203210133 62
    0x48000203000c241060307183d455423401c40e00d192106034902d03071040d58510601c0d0b070401d5443e0020031174403010314255130503c0d0180b000c050f40640f0700c41c411240000803442c0d140c0a40c2101200c000c240d00200302903e0200c40c103d91b540340b9880706503249060107000c82d58904104c1c0014100103200c00a504450b10303003c0b041e18180c0e0000b440300003089814420003001800500c00c2d08024045c600c1d034000d450800d41000e13206240d01e40b4403040c2c01d5005010301d000081c4c10b02e00c00c0c0401c5540341000c446070302c010010141401010321036041c072184001400601059411f94502c1c15400540d4141180c04e10841e055089907041d110181d4400c120300304041200c119915008015803080c4140d0740c4602c5803e000c10785c0310b0148500340e10b000c1c0d02c0342d980c003a01d50031301d400032030700c065440100c8800544d2a40b00801c130f22120b0b05004e402140c01803180145502c0400071030382401e0741a009102d4003015808030040401003801941040c101d03000b441c0200341800340d11b10001150001e04410480c410342d4041c3c0390 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 787277715 1250 787276465 787276481
    0xd1107020a030f0f060c0e0108090109030206010510140408031b03070c090f0912081602010b280302030a0b0a0c14160201020106082406030106061b0611161a19 70
    0x8640084e01c22000082860141d03955100540e1a454103050b20800050700313481e00100342600c03580c54010824003181e800a407040c1150020340341c8020307207400031100325904030720024403017055240020001040b4900200600c0c02e40840d2260111040c01c801041382c480c41821005012220742d0b9005221450a5502c0040e41e03113a62500001c2c41040c40c0e0b5030b0707041707004011400d0b008a0050700402040d014005030b89192404144020403c080207003000a072505084112480100700c6c410403404d484100c06445000f85800408603074071044503140040000c43c048920300d16103410580c050301d0701805403040c0c65940c44074202d62403c2000c20002c00c282216200c2d020b0781150340b140030000c0d288000b40a0b50300200504803010b5000d0840340c000000e11b2001401140c042e83c035060f010001c1320b501404c01c00201e0401c95000750b0541d00350804002405460b1099545140001042b4269160001c24909801d00c83c2c110f5120b1840040e0000c020240100c3e40300f1008030004000d030001c246160b105c1f0075 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 787278965 1250 787277715 787277723
    0x1a1e0d1404052b20030c01061203030b040c05180d120203090102150105031e12040b0a030e010902010801090c0507081801081609060e031c050d1107020a030f 69
    0x1a90006180c000304001905650a0307445420050200202a03007002510701024a5020000e80c3c2860361240100b59a100c440740c11901c01c01002c0f210103d880c10b1040310820744000c0024040207496141101046078810b5044001c241b400c0c411026905040c055081600480d440d61070500d4400c085400c035076018420341d1940101c160b006100041d01c401207422800708150b0007182c90784040000a1724042c000c4407901a181c2c000f03c01003200d564000717a02c51f81c40c41a104559075842c007070030209181400498040100c002c006c04c0115002c1d510b400030340101d0240d03030381c1030000e1500e0403278403402c03a02c0045000e800a0702800050045d06095000003030340107850300d840d524103205600c0707004283d0802e9103080425603030b00000322000d69000441d00c0d007205001c1c1809078420303940309010380860707280c2c42954280481400341011568003840301585400030050900c41c1440b103400000d060750310090442107643d2501100c01c941c111690180d071640360380907081440840c00c644400d10f100d003402d00c0c225 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 787280215 1250 787278965 787278971
    0x901050c0417010f0c0f030b0a121b08121c05090a1709091504063c18050a0c0c0807020d020301320c0307170603120a08011a1e0d 57
    0x1080305105803241700400340a03503980c100c2e40405e600006041e2946c0f954158440d4850210500c02d02c0740d070f0360202c40440e5001d0b0007060707210540c9000c030010321001d40c440c810601566001c0c0c02d5400c40380c0c0041214115a0b003c00040c00188614070044800a4825400551001c0c04440005101001c00101c03410308450b8a810450000d0010304110001c40c3e4203404240d5010b40c07a60300f81801c3c003400024000103800800c1603007200d06516503808240c099200c0c118144980243c4020f001000c030405442510140b410186145014501404094420607441440c1c180546000740c07080700c4c1d81d0482580a200b05d8540000d58080001040c01c00d403003660f065590320030140000302d00200244c18050528000224400444020000c00e40010841c2e03990400800c1084400f039800101c2d0340c400000400200340b01d48551010a140080300d425010b040c0200185047250a40c002e00064100c440c224200c0e0001c6500b0b850030b240c94040c2c0001807060400020601d1508040710300600000c4038030ba2400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 787281465 1250 787280215 787280231
    0xc02120115080d110d0c08091206060a0f120b0a060902160308070203070b01180e1002091c210c080412110103140703020706021c140901050c041701 65
    0x14508480e0484071000711501c20000400c1103080c140b14190310711049041480311107011044580e04e40f10889032460402c40955020b90170000369005490710700901600202c20418801d100d00c1e030b286004d0b03410300d200d1b00240c080000c24800070113a0806441c0c51426884110105541d0800c0c540c43c050304181400f1780711440842e200c1c1c2d184c80640744207003250309244c1403203a01d428090710700d05000d442d28085420402220340800c49211200c0d0441b2020010070000d03410320a034400040100c03401502850045a054030004a0107401400c40c51400311000707030807260400c000480c0c041038060024030300b10203200c401203405400d044212401c03110b4100803000a000e69500e03240344d8040d130004180100356240601c240b100d94200f20703c02e60340c2800c08002510380024040c0210000a140310101500000c0d039904000300340c1c041d52000f03210804241504c200407148000688616050000e10041c0000003a103410014040c0314060028207420515043c10280da51044564601061200b0b640358444 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 787282715 1250 787281465 787281499
    0x61101021e030106090b04050913030c0510151d0403200a05060106030f021e0f04030c03060501060206090303070c0b040819030c020f01020703050d020a180902071a090a030c02 77
    0x120110740e00000c10259901e605000c0090321481240d00008a001030030b004c00d00813603e84076180b542100a010050660466070328080360340f800c403c24014a81d005800410031068030f56048004030a04001242d40b10988a0807136501e0700654440a50642c10001d01240200e40034035004000c500c3c52601d28081d0822030001039160108580c3e0449070355014070010807600d03074184501c4c030120b9041e0030150b1800038500c03909003000c0c1ca55607000d140b240c80068001c00c0200002d08880c01541c0c8201e010014a54a003056401010244102009409080006102002c2c040100c0b845142107880e60240c0f0303c00c5450300d400141000707100302e07610042044820380350b080394040c10f0040344040c1d6010841c8074080d10009c0c200780d012868151140c1c0184507010000760000c09464038940705003001078079064001000ca031101200e0022900c080065000850340a00540040044a01518916042e20004904911042c070102c400d194190007089240000910891034003001d10700080414804030407546c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 787283965 1250 787282715 787282747
    0x90114180d05490509101e0806060304120e060d020d060e28021614071a0415030902030f0f0c150301050105071401060906092406110102 60
    0x8401d8a0981c030020180d10020103a18100680418100c980000450f6148442c0d800c1981081040f41010b08648068607951281e015100d02c15002420440003a00300340b4042c2c002d0f051521210705403c13111a5079012940903842c80381c025a07010340300d07510b55030b40c1e611401070310035274429004100007145d040e02000355111000342c181f0081c0c0c10350040c5d44001c0415168200c48496212040e0358210104200d0110644800c03940d6a0031405c1c22001607070414405200244103070300d6400102030100c48010240084034540c10010301d6107000700d8011075180c014041034120044a1207004071410042403005c4602814001c107080d0b82c9044c08a20301c40c07203500080c00c1c52241e007401c01803a481030000f50a4011304100c44070a16406451512100b681d01c00146068407050141c1414441d000a05030108010891000c0c2081155002003051030384410b1100050500b901c1200b10440c20034100c49030201d02c040491076011598580340500c0d40c603025043d01c220000304202d49440d5400d21590603130f500300c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 787285215 1250 787283965 787283989
    0xe010917281a0f090609061303090b07080705060a020702100507061806020904180f0209040302070b0f09090603011802040b06070c03140d0c0302060f130618110609011418 75
    0xb668111a0b07190030700c010b0260680080c03c081e1a0352111041c0320300000c0c0030074000c5c1c0101c8200251800022141170544101c05130b0352260480b020002415418000084042d010765841403058800c1502e4803000201640a0040c010754407000c031800c044202030060004100d428800e401c0800e011b0316415003034140625840e07007500d403517400044c4e03c0701c540350603c07e02c074440301d8080011400c4115900c3d81c5001c00d05400c1c0003405070741e440011070281030003000014018049040510f64070101558031207500e801101c2c815015000365400b10f2903c0ca01805035040c0c0e00080d5507054013082d80b6800304800307810300e4043c0c1500240200190f1011542682414000e0341c040c01c00e481c1003581501c4414500302e40e50280070100a401091b84000940c04205141c00001c203400014207a11941c916855448030780400a001c01d14201380281003601d40d03082c0c0c40c48203008480c21210400180140415407249600103800070b10701d5415403084254000c094500141e07042681d00d0400107400100b141040c0c90 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 787286465 1250 787285215 787285253
    0x5010f1e0c02030d140d111204210906021c0e10020615060702100302030c0d0f1a01030606050a030e0304050d0507090f1e0207021305070e01091728 65
    0x9030141c0015400c08110a1503042e1041c5005c0762660078100d0341c000e80c0e02807062203410f042d880b1000010b0f01012441560090081d40001a41c181010f03d09010700342c0311412145008003030040c413503070100e000c3d07055030702101c1458001d003440c40d100d840c41c8071940c1d10885604052094411000c0724a0f229986003111501180d00280041e007804401485041d01070003810388280001c2282c1030040c1c0b82e0310260340140056007000340e00c07500e801480554a00658029490061031322116031080f170000d0b0012000c40300101c44085482c0c0541c40110300791035585c013906011a10030404960440d12a500030106800c2d03000c00d07603081c5030b2034400003003121040c01003e9882d540300e44c3c401c0c08440198440c3c441d841951282c208012100080c441e85500d01840b000c503c61540414114117544400103014114101c0c2c010800540c079121101070185074468010f9400181034081c04a5009845105803a0409220303004081e99102c2c1c889070300d50850350246101410351601c8171800040c41ea8031203078010080c1d03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 787287715 1250 787286465 787286477
    0x50304050f06013816060509010603050a0b09101524020304050d020303130801020c100603030e0f0409060c1e050c0615130c021b030303240d02180603010c08090705010f1e 75
    0x140d030900105a84004d0661b08560345043c0d40bc0002500025078025069070140a2a50359503409160609101a440d03620900c10b00702012400040e02c42c60404081c1d07201e440c5070a0300115169112041e02a5407065500541e100300410b120600e80706000c1d44d486840101200d28044502c0e0a01582c0801c59005c1b0310a6900030801c0c40c3e0011042c0140040d6403c0301204000c11480c40c0c40081522079618a103600620780040644555196500516080c0f81c11102c140f00c070300c1c1aa10000c00d0580034600001146185454200c04a44110111040e200310103000703040170b48a042d0b01600410111000e90703030180a030ba507070200056250061000a46103038028220350054500700c904541c100c0380600c1c0c4a03410801c10808504070b00d05864184401340461300401010304400329000c013420100c041d40c00743c84030880e0010200c0103000a446404160f0081c4048100050180e03800e410035148007507160802481405954071070303810100c0d10804c510b4401000190040c8103204920451a00e400241d2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 787288965 1250 787287715 787287757
    0x61203070206181f09061209050d080601090609050d080315031509060106080115030f0204120c050a0801020a17071806080f0903090d0f170406050304050f060138 71
    0x81c1c90441320303041d040203500f0035290006410f0000d001c1243c50045a05214a142c07101550310f456612000d04030303520400302c95034248000710281c88100100e4445000410f03414001ca11035108040860440720090240c60b480c52540d6208051a08011300c0c500100c0d00c0b4000c0780c00281d40070494003102841841003a007260518800c0c6600b4541d050700888240203104004001c0e104a00c0c00c40300010105250000c0c90958080110001e44100d602001600b01540110000d109038881c0d8901266000c94a004406980da1042401d0b4054901508040340001034a82ca030000002c034101d40c41031040c500b184d01d0020b200b280100d400b6154002c1d5000400600401c841140c160b0341c030b150000700301c070015030074607100c1c0c000500c1070f01441c20010809250b13014140104108607a610074200d0040600c03540b01c60b25820001d1440d041205e05441503c184c0100b5a4110404240c60341a0341d44d4941e40d51000300004100d40b8403650750000103c9001c01e0a52800607e40036202404c50001e0035410250144 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 787290215 1250 787288965 787288969
    0x30c060806030c1309150c0e010305130507030803070921050c03071505211f09050f13110307140f03060c0301510503070806120307020618 61
    0x40010030182c001e5206031245801582c401c421414000014a00840c0c503001e28540030704580440381781d60044034240814144095004441524038000a036001c2025a41e03950a007000d8220f039080191468026203005c0c0301048030b6500860b400310840c00e04c3c01c0c01c65900c2c031040e41001c42c50303880c0c1120002e20102010400006000c21084000300714010303c940c5003089140e4602e42d0401e4160b10600600261002006030701561620104102d110007420034909005103505980003141c400d05407a42202d00810001818854070b4041c45101e41d44030115582c1c110440c0e8982c842e9842520050005807c0c1c9145a804110301c00c050a005000e40d5800d01208060024038076840300c10a100fa0890410004070f0b4240006885c111020200d20000d544a4001300c4c2403000300040d01289400812007044d010f07000112043c66400e004801e0100c12080040c400322507501003514884000707401c500200389186050b0a08442c404030043c283c03860418903070b001038000c1e800f41c00078400000009c40c40035264 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 787291465 1250 787290215 787290227
    0x302040b0909060601050a030f06080c09010509190c03020705011506081302031002070c0f06020303040b0c0a120c0e0415080f010b060304120e2107050a0f0e0916030c06 74
    0x40c000e8907201100e007003079444152510002013256040290114001c007115100c0c1d0003643d4800c45c0b076502040825203440140b9101e6800c0e1082a014ae0b00c2030000244608010300207500c0741288001e08411b80c00e044040340094100e41c0b034600700b095000d02018021803000e100d80021040c0310205440b84500d03100c40070b80f112800910110310489075104020240e2400b0980b0442c26852207001643c0303600510f0804580a0a03030812680d0714940d5401003507407a0004011405140a0341100101e0f42d10241c000c2c0c0e55118a03a8480e0008601c0c604554040754079800400121050b81000088040101c01080469504101d0000300c210760803000c001a401c18000703c8401070fa003800a10240030a000030404920001e4002030140e8103c0d020201312602c24200c030030102100a00c1d06100141c6000d0701c0403c8040c0d2450b0041d103015030040000c3c00c0c0307001400c040c120b43c2c0c0e4003104000701303141c00c86201c0345180061041e03819000b000300c18a0020740044000003e10f11803074800002c141002e0005040d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 787292715 1250 787291465 787291481
    0x3070f02031c0f090804061106060406030f230f010b190506030105012303070c061a0a120503040e04030302040609120f15091a240d11012106030204 65
    0x2507400c10003a4140091800e10940c06070001d4120214050802c0da5103070004081400c0060401540468041030040c1d0024444078910484070483c1c03a1503c4890822089601600c001081820354900a01c00a0940416a08030351020011203480b01c841032880b03428107102940b00210741c0d5480c0f507a14034910f018013084980080000034007a84074185400314055100c103014040c144489030742c465021900032441c4c405203107105040e4544a0510041c00380114203c440119031080c00d03c0142d00c40e0303100e0100094050840208180c04092805544282d441409001559a80030030030000c140c0b0b01807100042c0c06180301c2d40e0300503550791410100424444154001040c02e503804001000410b807181140c3c001c554100104031401003111100d24001c01001074010081450520000b04c03060024500d94401c0403024041e940019480b5080c14000e03d04c03600c0c03235034000c100e81f01401c0400e000c003110074100a018123043c0890401d91081d4020700071050407564071035072505010300031818a801680f003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 787293965 1250 787292715 787292717
    0x10615090801150e0405190c06030501122f03060103080306031e07060f0504180f1a0d060b190f030516060c0308070201021b01050f06010507080d11040f0b03070f 71
    0xf200e010844201e4900c45904d110380f114211800f004907050180a0052030000ca20b505401c2c40344403110300c0d05840049080c070600000c43d2810000040741e00112400390760095022480540c03c000d0040d1015000e0b040c0e6140c0c40b2986502c010340c00c0c0c2030710100b2540d0301071401800b0780c545074645101054541181c810003111080307940c08400d5031506d0300141e00004d507151401c04443c204003401003201d0901841d4800400f05650a0074404500c29aa101c071200081a02040c030000801949040b00051251f05242e04000580c200802103440d5910030b1002c044020907840203030080303100d50130441280790071003001d20b0490102042048400c00260240c00000700038404518030f81100038100e01a1000301405000c4210b0008800a200303504807041030740d2240d4520040032201a00600811007241c00e401c441204c0c4020a40e02c3d8007a00a4401c4c583e444210545020340c00f20001003d8688242000101c10307051001050104070300c842302c0c01501f98101000c1e201d1030400e400070000c0d034941ca4148 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 787295215 1250 787293965 787293971
    0xf0a02030d0e220906020d0504020f0603090c0108250215011d0606030901060504060b0406090b090d020616083402090a0b03030d090b090d14090f060c010615090801 72
    0x34000c2d880740454081da0340000c19000c110421080040b8004e000c0c2d00318024482e42c40000d605540c0120341c2d1103d0700950080d15010509015001070125910042d544504643c0c00814503e455620954801d6031082140485201002c00c074002e4486244080130342e900541c11400060340300808810406004003803401c0340301c2c48091205102c1c000380001500c014040c420000001d10000030075048400104005003042100740e40c1c8800350b4059801c42d002e00c1000850480c03001074103901004c2916079091004280d42c440070300316401c101469104c0c8000340f4001c502c440d048001310708550b0150800980c064480040d0710b5220000844400482c844040d201040618100168440c510800e922201c066000154084018002407031400740300301c0b680106040420100800c00180f451900405c14841151129045c854054544607000540009441d800b0710220180d450f2102d00c900c101d500290115203002408007005003035480340d8000760300c00d004055880d0840c0b80d0003002c010040010000030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 787296465 1250 787295215 787295237
    0x70c09060e100b0301030b1806010602100c05040f050d051002030f060925050327030705151303030c0e130b130902060313170c0105070f110d1d030f0a02030d 69
    0x29000d02041c000501744404510025000d012108c41e020700902c02c0404440031981e551070025611050561840c01c810700b8003580007450b0340034406460640700b1007007a0014213820141032103031000760701006452620409985404616881c40114010100b800711414180b07071040c00d010b40b011003d40101000b081c039401004590428900980b99034400b450856a83d40341c0b50700c006940b50210070101e402c0040ca55129149410005c001d003811480b800948101104902c45088420f10031902c61062600c040c42070350000b4420f41c82920136040c1420072000407420600450451104900f41181c40780e071300c80402c10345290141c1010b0003404a02404e22614003640d01003202c601002d44201140c0504910b01c004100920201d684141c640c554025114150000032501038a415503a09000c14034402d54400e40604c107600950303452060100905c05007443c0d040c00c031303100540303420041c015481050f4820403603502441000d04c0d8840e1b0100921410005004050400303485102d03200500c1030411031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 787297715 1250 787296465 787296479
    0xd0809030a1d041d01051509011701060b04090c031103150402030c0909040c031403091f120f0c021605090115020c0301051e100f1703070c09060e10 65
    0x129008107240d071504000c0001e00c03000310041018040c2d84568054100a510714030760012204068407510610024005601c450f5800070b035010412480b660080908801407014403040000c03442001c01030720000622a50325a0100c0c1541c009070050f0742080d40701c1400e4038000c2d40c1070240c00152015401c41a11750b0801201c50a960401c00306c1c0070340910b0300070000541e0103210700e082c4c2e401c0c01c6001e018071545103001c0c64002800503840c0404c0b501e800120b41e901640072000401c1d00e2581c030002d0800301e20b441e0721031070203c40342117402540317410418405040344245600b0700540d410481c00380804501d164000300c019080041c42440341005604a6004101c150b03650521141119249070f10380401c2000304801b2800d01003c0404030b9019030038442030000b000304c001104501c1400580303081e005a100c10014a03650b548602c40c0101d1040c0c004814030040c2d042d0758908612450b04021286006a9075039080c1061000e40d011100103031faa1a0704000c1080034a41e265031052402c050180d0341403c1541c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 787298965 1250 787297715 787297717
    0x1e08071403010905030d02120106080103021e040b0d081309150e070909150e240f12070e010e060a08100c0c02060c0607020c0402070302190501090b0f090d080903 71
    0x1003000310038111582900e85649003948101c000d1a040010b4aa07200a00e0001c01c01a501c4641c00c090784101c14800010300d1882605402d040e83e500030031440400c1441603915030503a5941c1c80c082d52040da1a02010074540d03681c0042090f4502c240c01d03054a0300c103007078041604880340d6840004560f0411000386000021109034006982e2801d46013001621235540440e041480e5400280b4603901e0715842c404c64410000013102201c0d0b001c144d901d40c5d45d8416240940200b0b070136000041052496000740e82d1860039150321208420083c0602405601c9001041c1c98403c0550110300a18a00707401031080c003280021841c1e1140c81658040032407807900007620780c0c0c0e401c800c3c0195183c1341d0b0b030302a801056100d00494014150010900783d120341801c065a521088240d0701140544240524811141028000e0301d466540540107403000030200100ea403d0352400e0101101e0315540c410f081d9001802e001c2d260b9009030030760042a41d851420f00e186510b001d031208065024004548108245564000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 787300215 1250 787298965 787298969
    0x222050d081c1508031306030c0c0f051f1d1603110604090e0609060a0e0d0e0402131707050a030b071b020603130b130503121003020306101e0807 64
    0x244200302e0090382802d00200030700d801004610307046450800041c200c02c0000c0034201108690040030181aa124811f600301c0700d09881070030100781240b01920102c2c0000c0300c01c41e90a800340c0c013034440001d41e114109465407030035000072051a540c0c03d14020803254070744082215403500402010f02e0680140400085041807100030b000003d0140c42030b405482d00003da40040c0100c82d024801001a5108141c5074a01102ea0308007601ca0381d000517140f0115401107582d2501d0700005071402c000e69803070465140d4100050250003035001c001c4951110000140b00c03005088007030800c5080709141418900301003655004502c124090071080c4085890a511b0641015550501c07286056035841901c01900c6280000b80d4800c5021040001110909003840080340c0702e2918081d2984d02c0c204140c042c4076643d080500030303600034011600e4042c0008403042c0c0103c6111042e01c5110754941c006403400004482403103484c01c0f61403041149002202c0c8041e40004448120703c4550b0030302c00110341e03540b10341c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 787301465 1250 787300215 787300237
    0xe060105090d03170a020a02010b030c060406030b0105071b03120809060106260103050c03070519090c11010f0c03050a09030c020906010909110702011e0804020112020d0222050d08 79
    0x4940b640d420140a10a13030100c000790f0b09030a1800b460a082000700035080040c2860240d4241454403100b407502240c140300b10317075004041604190518004078000c004d0700e8150380c103111003003103c0e50101c2e9403031300b40c113801680b90020316454a04500d824200342c2601c0b503035030091290702018441619004541a41034500600d460030080088107511400d5180e098000e1004074072490020041c85408542d13005030280503011615402e941d18107000050b80001d00d48103c05071522418451000150420103807070159252a0641101c1100124211107040c07601c9001e4680d2030014041003074050164540c0500f240c030003001000380c642c0b805030682178030b960028829a0041c00003011680910604009828450020015001c17820800c006d83d40c89284241d004c52070f0b54980e04c3e20900c43e50a05001c03900c1d140e48022150701c41e45c0c015116628a40016085984c0a100b0b0303404061261000e010312401c1c0e0b810341c0b40b078206080c0d05003107945100d801503030049502d0821440894441c40c100c034094001c03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 787302715 1250 787301465 787301479
    0x90303080c0a0e04090b0601030e0d02030f0a0201060321021027140102120105120d093b0a0f060602151305070308040317030f0a021806041805010e06010509 69
    0x4460304682983c04600310f5a03010b86060303551800d00500005035807003400203807401c2001c009100c045035174542d0b5403946880142c1c0304019041c2600c41e018054030801d5014000030941c1920b80d5a41091560500d034035101c480d080008610030315034108984a2842c009580800c100d11401d002071129000781620951305c0f002c0785c04042c04001410352078114420111000310f440751000083c3d1544840300303104251041304552086003940002152460b1b0250203611503041081c40c1c00180411070440300b900980f45101c2d0440a40c444480041950700c8100712a1404034615010300b0644c1144c490940c141c1900c0e240050920441d9000900c1c06400403040e6800c07000c075a11500c442240c2200c04800405074002c3c20000030420080902400640e8458a2140441560a8a907910500040301c4c60700e090400d000229201c91466070051400c161864101c0300e070b43d4a0100482c400e584141e0110107842000c03500041c036441140319240c09404101d94035005414014002003041c0179900001e441410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 787303965 1250 787302715 787302727
    0x30f0507050c12070f0509100312050708040f0524090114190c0209090123040510050702100c020304080c04020c0f0703031d03150c0309010204090509030d0b01090303080c 75
    0x81000702203440008180400310050f4000c40354031410300c0e100b01c8503420440b0301c006c0f42500d0481000c40c4944890101e0740d00a83c42c1d902c0e9240040324042821081c01410401c030408500d40c180204040d0110310050700c00589080244104420201c0c9081140c0301004031a5941000000c111001c1010900e080a88840b44c05002c161070322540b107413800703010f203401c0e460007010390020104e4043e02e0003141c0d4141d96507142c1c40c09034280c0d80c3e802d9041000f5281c0f248010301043c5449841500b040c06401220340c41b0301d00e0030441084034010388540c0096445a070030b1074082c0c02a40100498001d041c4042c40c00e0034035040045580701030f00d0340042c1c0310301e0300801c0ea0808604200b2007050195030f04170403241e0043d62414040c0c00c03001c2a40a40300084181d100060040c2400607101d0a4004407202d400d8803075035554907a8105401c080d0120803155020400001d181000c2d00030b0600030300c001409160340e1440807050f9422074400d451203505000c412081040441c0e04028025401409400e040350b40351 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 787305215 1250 787303965 787303973
    0x8070e010e03011d120f070f0f0b09011a03071d04020409021c0b0606040605030a151706091b0108010603020f07020405041b0b030105030a1511030103081e0304030f0507 74
    0xc2400d0307a11903055881c1070611307184a05110b1100c010b1035a024241c1c2c034504e2581500a605120315658807014910401032000056039201e000101140110381c496004000744d9903148846c071007960260b0b601c2c2c2d15000d210201080000d8040300001c1e01b01c009000382c83c507065500c00b4444881c100301e10042d2010001034159110303030b04040580c42e402080308044154480285c1130a15240100742c40000c1e60b14000781c150b0414000326000e44000c1d45500d81580e80c1da160820242082a1200b41801c0c904d403000201c80044000710360101321100c02801075840d1440348149401611965000e0311103115000350026604240034a055600c51319025a5800708010f203090240304112000b500503142004202c140001148484280221424400d4080b030340c5c0d00e844180360100b8000d05500d030700702a0301640001d202c01104169540d0360380d00414004e00c1400442100c1d082607200395000e20000400c80d200350310001c1c0c6140b0b442c6107088480d0450810361401451465281c1d202e83c00c0c0240022040140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 787306465 1250 787305215 787305227
    0x3090c0503010e07150c0c05100c120f080a060501080112051f0506030d09030c1e150503070915170c0c070f050103060b0412020409150203330108070e01 67
    0x19150240003402445255000213644a1862013000660882046100d200e01d21440c04401210f400c24810744046040004108091152164000502550606800025150581c62811542c060311003009018103060040c0c8817040080200018501d0158140600c2c1c0c0c005e81c0d56815030780d10b524415102c0c6000e24003289041204a40c154030130b03103001c02c042c2147d1401c0d0040c6210700000d805591515112801c142c408000901008051110780e500a00084605144001c0300000749406181c0944da28160005500703a050381c0c07900000c0f000000c12540710b810000580090000142c06090704051000c020404c000c500006221044250041510030046074140c42102c81d2071000e8a207041d80c1d40c0e40e40070859a03a4803c540c08039003400e00014403403600005440449084002d0302c10b42c4641d640c2000003e02040310120307044801c140702000c4001051010314802c20162100314100c8110708118203810001a5007986401d901c108140c81e6a40c0c00b0000039044405070410000c0056032400581d05 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 787307715 1250 787306465 787306469
    0x50418030e06270f09090d050d09060501090204051503040b01030201120b041404060e0f0709020f1204030e1309080a12060b0703031506050f070b34021c0f03090c 71
    0x12440e000b00908400c2401a003044240d144110b83c04e9004803202400d220182c0c208072040d0501e03802c00350030400c030b240c0290000c062050560400044440c00b95503000b0885401381c2240ca00743e50f01107018005030409040320441c54401c600081d003549421f03510030744010014000281000028901508200e03515000f42840c440e0040c002d12014420030f618010801c4100e030f06440305820141d45845190010549007110070121020700005c070b007001d245601961210100101c0391804000c05011040c0824020b80250b201ea6030b1100d4140b0741e0400c0051020880d050785101600e81a01500020580350403034518081c9070802141c2c42040d60909002010150304c020340800d000144002015815032100d9516850300c004650802e8442300200c816008950001005980400c07041001c2203181a806a00000382c0905150003d203c1c52203000d040081140541010061076210071100e8050182000c5c0303002e6660303864099102c61600400a08078800090705155507104240c0a100c24510b6000c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 787308965 1250 787307715 787307737
    0x209030318010c1e06050a020a09060513080d0c0c06020123060a08100c11060615070519030e1206071b03050c030a0e010906020c032d1b0406050418030e06 68
    0x10140780e01210320000900c1300181128064a1308000421240e544e1003546c04288140c0d54220100f41064001da4859025481054003200c0f01600041e03070800030480241c4c4c1d080341d40d544000c6604580741036600007003141c00440540e414040d4450b20162101c800102d000c04421103150790361506030204221003030b42c0d0018541c9000e1034001b0101030030590041c0303000d4010b65680c5801d82a125100b580c43c1c0b45d0590344164800c010350001d032910703403d8030f000d000f02c5400354080d40d00c190420440b1503508c1504403001c034041140c0c041600c0c02da180c11090070800c0320940002c0c00451404100c0188052000b10490800c0a46406c200c82454030410545001801201c00c4070364494103050040c028010103030010340055000b00001c10483d201191380b03805803c01070700400c6212200d40b00440c4075a840b040d85c6020080e042144080c044040000816004a4682c1480401080300c2408280c0f48282c018034080c600340040c000c0f41c1d4040602141c102071f010b140040e9002078200000e44036104000c0303d81 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 787310215 1250 787308965 787308983
    0x90903021f091a152d12011a0406150f1103070614010e07090b07080315060d05041103190602070c0e010305030307030f090b07231209060108010209030318010c 70
    0x108009a949000c0350158490340d6030104c0c0d040c2d12400b041342c8601719900c0340080600d008001d0030300c0c07030018041036401c22008202003000b0120501490031228800840040340040d081d41e144541060f00c100000f420010fa0701300d10040404801800d2007100a46003004c1003020404094201002d205580b07203668044c0702844080180020241c10030700a003c0e4500c203204200c08030710b8040c0545000d0003201c2c03240d0034243c02e2040e103860b541c0d00d54000074031421181d01015001500c540e92100108244002d48100083c10b003010b01346042c511720420b20b500c0c06580b0980c58002010b801d14500c215469220784d01580d2401240341c00940303020700d0b9001030390545040e400402000008401303035205040550b401c110700680440000c054031512500900703144c0a407000f00c0c1000348a01441e1442d01c0038190036038281102d9614010042c2e100018900548890605110603400706006590050a510009500305800c5d0800241ca80c462031100c0800010700b000700344902d0340a00c40e044800340e0091002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 787311465 1250 787310215 787310243
    0x6061014120a0c0804171305101205160c150f0c1205090105040c030b06040e0f010606030501080706020303160908011119031a0d02040b0904030315090903021f09 71
    0xc1002410140e4400c10180d0900c2480c43c41e861054085074441c0d60445200006118000010a02c0390b01055440c5510390680030042105c0d102c9403c0700480a10b555a52503920100e4040e039011108040d10419148501140c0302180d144c2c030180b184059500300c0c0d112403500400c00144c0c0010950300500e604a1030a040703a501143d90404520124a5903004013404a69600d240c039a080b1601143c1c000d0000c40091001d0000c190300402060f032008000c0c10000c0c060b103d80742e2741842d18080c6546043c140c3e454000c284142070703060143c0c60051001c080100130440c2050000b03512804010301c203c1c905001c1c1070328220140d10900c2c40100800c180c0c00200500101c0c0b820f815410352002924174252a6140502c804080c0b082c0309102c0c4041e264005d007000c0740140003c008048000c0d400c1aa40b060300e458942e2410350b42c07034040b01e001d14480c3d00c0006580d040110520342c8084a603200702c2d021498800e12401081d000f161000e5808000c83c8484642107400d494040100310200020b400c240c1e86c00c500b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 787312715 1250 787311465 787311487
    0x50f0c0c18040507080c010c0305070305120c180409020609190f080a030807080402220902090901060e181923010c02010f11070b0a240320010206061014 67
    0x7125008500a409540711a40c85224541d0358015101e0424001a8480040004644180041e002383c1c0c1c420310b8028542a400d4480c11104030066410f841d00880014420b0081d40e40a0129007207414282d038140400c00d840e4000a069000f01180b1034021044070414000403031020000001400141c074010381e4075900c1e080c806540d4000100105d010403003281c0414400d500a0020718440c3c2c0d401000d446d10024a820200d40d0000d0300c062a6550589692030000162344424032a442030040341d00004070036141c401810100c0b40302810141c05951489e4000000c0c0d0004181c0703010140305280e111640e80801d2400004282c9103065046081c00c0d884550b41c0e012006400140c1da4008a900920960340003842003c100e4002450302d076072a400c10091840006c0d0b560141d258051f0102c1400160744003401d6034521240074800a51041c075000302d00610400400b448030007000b00e100903840c05120440030000c0e6179000040c02241c454600300070040c0c141e42c86440130000b00b508469010303454100070a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 787313965 1250 787312715 787312759
    0x105030a0209040615052a0606190b07030c020307050405010509131703040b04111c140106050a0e01080105071d1e030304060f14030f0f040c09110a0e0d0201050f0c0c 73
    0x7c504034417102d5001c843c10041345082251050340980340a0f00c1e2502044a1980161541014110041e4000030000c20100c042c00c61640030383c0310300d081c042c80740c0704160411284e60026072007285001c00512850325450803c40d8814481c80e05c0c5500b0000b1030400210741402842500800d410001c2044100011072000d07030b00032031203000d035030b0104003c2204200d0410b5203010407401c4e039517066065402252a4040c0b80302c50360380000001440f87c0d11107012600000080c3c000c1130a801c650001041098424454a0351181241c0b60485000c0c41070102c08c220b50380c10703880c007078450501c08410418803a0300c41e1182c4810480101242d688950710007001c1c00800403d02550082001c0c4c5001c520002e041404880c410300845454500700c0d07480c043c1d901040480a803040c0c50581d00c49034003003200300d514172400c044d012403800d489803610b07504a80100300200b94001c85015816070451400182d0300841035a0384a0020310020742c99007102c1880601e080784030100a54842000070941140111443e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 787315215 1250 787313965 787313977
    0xa02031207030e0613030f0f170f0103030206070e030309040b01020c04060f0906060215040b1e04060b0a09180201030b0d02060f0406170106090311130e0c03100b0105030a020904061505 81
    0xc025103850385c0c1d4112070160410b04403003020300410194400240454031980e081c5407141c1d100d0405030141b14590841100c1e070f00702268500c1d000030f40d40380140117058040011a500c240b252409903101c40c500008280c590084140c1a800b494988504c415542e0080c000b0f00740c1c1420142080082d50755900303c6800004991003403030705891400d0720100b0001d202155518031400601c4d90003050b038030f0b650385104c1294030080c1003034402540c100c0340d02c0702041c0940e103107800b86e0300034500451b030082000b00704602c1b440c95520503034040346402003440c19491b41031540450303650242000181400003c002c034488080140c2c0c020340c401e20000e102d40781c030f5840e480074005035241e5645420641001c503900f070203010007e0080401280d0440c1d0308200103100111045010701e0080c08407105810580c103480700707032038016900c80c52a8001ca40300303802900342042840203000c1c05981c140310b0f41e404180003801c0c5110250401e2203950300010051080d4413245c201c0402441f802030100c802c0700c2e0b183d9004200343c02c55 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 787316465 1250 787315215 787315241
    0x6050109080307081606021b0d0905061218210409180503040306020a0e12011d0102031e090102040312080a060503070b0a0f02100c020d030f050c0f0a0203120703 71
    0x3840000c504030300d0000544800d2640200c00c1440d1004071600c44124102d035410403642d440d000c12241e1220444c1079110000b0150684c014102d10110303d0303001e4100e0005401c4030303005042c02c3c081035070320003084030b0000e4000622403844842d00d181000000c0c202041290a41006644803141c5101390f51914018811216904010805855042044e1600b0503c8d03c0c0c014000760b006000070310114800703a005044400c070905004200c1c14101001c80c1c242d0302c00c1010407089940d500d182050103034021445580000444000b145107150030030901c1d0303074100b80242c545a400c1c1000005003113284254103c4000d950442104078807080341e48401000100c0840b1800032242c10040300140d2410300042d61402c0e266600602814030070f442404a400c03459221642d4214400d0841d4240584c00178452007407002401d0f40a407100802100307016040d00c001e04618042a07141400b0030000d0135081c0e0039644140005144161340e039000342c2c812032442c05800000a101070744403052051030b54240e0b10480360f4102c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 787317715 1250 787316465 787316477
    0x12023405011103060117101805040b1b0a180801090b0105100c0f03080403180806061c0210050c030f19090602010221180106031406130c030b04080f0a03060501 70
    0x800b20480800e404152002400706950303805d19000c1c10740840d0031a038400c01a200c08030000e90b94111400c40604400c0e0b20140460396501404140500311070880e80c004550b601c000d000c2c00d60001c210700799104000c0b0442c1001a803600c0f000d2401a06c1104900522100f4024008a41182089502707140d007842010702c110009082c00e080c40d4007500400340c000d908000100c030703504020f1320182e907450302c02032044081160b4a0440c0881c00c603040d000c80080c01d0200024001441d0200605c01d9101130040d511584c41c1c1e4410010b8016922542c20002c1e1403001e2070b040fa01c0382120604c0c00c0c514010807002030f02c0d628001c50110720302041040303000054000c5a0307444040c50b0b900c2000381e080344640d90031825800c1510403030b0700301440325050854103c204003100450040c0c1407464542112065042211a812820b0008080440801070f0940000140b0818161403245903644c1400301d0b61031100170485000c1000007018400705105940c0c81c0300d10340101c01d0341c5181a420060040641c3d000f942c0c00f20b21 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 787318965 1250 787317715 787317731
    0x12306030f03030a0506040b0d0311010606050c0c0d0212030412110109060e040507020c030a050307021906090315021e1b0601050609040906061a031503030304031202340501 76
    0x14001400181c1120020059851a1a910b405802501005042582061f201d2441c1034203074440c24614140d044c040d5454503626070030179601c14203584a0750703c0300303003008011700020103112400316502c1ca0104003107800045242c210710101d80c1151802c0e00c0c0c9070282c080460b0002d0b14031070311140802d1180c81100f0912107583d60b13130015900790501c1e0150b4000540c044050981906069001075000340117801198440043c1900003485e08800030703c12a420b0f000401e9103070444c20310521a620f50100003280c280894205203008020642d50720014101c0d422090358981c0c0c04480e581120040c0a1201650004246145684a0a80c400c0304210390706994441420115070011540c24141d50700144010310b0315080308100806040d40c00d0040d118240d40d60302c00500c0000302d80016018180e40101291649018079007070034410b800d036210500170382040003080006644080c0038200300a010000689403040304000742c00c41401c4060001c0c910207140980c3c00703011010041080741d40e118800070700c090740d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 787320215 1250 787318965 787318969
    0x4180908030c071e08032403030d0b04060f0605120a150308030106020d090302150904110c010507120507050d180b010602010218011803030c2f04050a200a11012306 72
    0x11308202c40140c40a602400815201c2d4034030315080418440031001d03d50100303103200002c2d0540e84500606c0065079960003c601e003d0810780200b0004007001841101c0107451305c44080c20521554624a95088641002806000700c03603100285024490344460542074407864507941e198420300622015109801510705001c0c880da000c9003e40b0750140c0000c0403a41c1080418040e03405c51006140d015445210881c0084000c0c0054411f507600c83c40040b446003410381003c0c0030004000741481c0c2c514101002c0111894101d421148100b03180b000004011988941200d03050b20800801401222010700000c1d800d075054004e4400c3d1614042040b080b50070440041d07030b030445140c1c010b002c4800c00b60002c0010034081c007039403e1124082c4512805a40d20349003410003041d1400951841c2c4960701c0300d030002c3c0c0c0c145407103000d910a80c42001045401101c54600004948000d0011895200020041609403042c8a0f1600300c1980c2d8009000c250107516140300040d82c409045001440301000150541c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 787321465 1250 787320215 787320263
    0x90708250905100603230a0b12030a020c01050d020708032a0a080a0c020f12040303200c190f120b0c040e0f1f17060c090604180908030c07 61
    0x5005030024690820325142045d8040c001c80780603280c040c04005690440f0307801d000a524841c000e000d40018074860490308100c036440f0198103500f5140e0041c01021190749c1c00060202445100b400d00c280c60300358101c0880041e120b04400202004008000d1003804204c513040d41045484002a030850b0035014444119140500010b07480082c010710f002c94a621410352040300d000c80d5074415141d01d0050300711520b02c0c3c6402c5220703480c0c0e071200005040090603400b00c010f411451150000100b4070480c244070955403501d040c1c07111306c21250b1001c044c0c4141550030584009041d504038808400c0c1d03032400340c2d1106241c1034000341c0310a403000c400552071160f00003c503004d031101120003210300d488120a594540d0401007040c100200c5000d034001ca8060400e2400f4010003000d01080700003050121424203100f000f50003080070603410f000d01186540e0300d80544080d5658414a44001c111283c0c031500070740001c19000d42003110010600900200c3c100085c54418000c1c001010400110b10005d5a8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 787322715 1250 787321465 787321471
    0xe060606090f010305040c03050a120e03190b06030129010207090212010e04060609050c0304060c080603300d15060e01081b120a020d20070b090708250905 68
    0x3200d2059039100c0b80c103600980c06950007600602c1034000c030715140d64038a8076200d0a9a401d41300568002103003080680d1100e1547c2d40c0000680142640d10030504c9502190343c00080028a803034411000118540c809602c4103071200c0d400210401d62118a903400d00221213800910343c0180600007020842c001c00d4002c07180721400125030b2010507032a2a0f400210010080d2044486645a2000141100b40c034061280a00080c048890356428036282c0b01c4215607010802d42c0034004603000700a056500031a0305030454030700c03218407600344083c452001d201c07a920000c03140301c0c55008603008907002800d6015040c00318880c0c140724400d5440307a005681103148203e403c0e0015408070005100695158a041c881c0c6041d20ac0b554140244c030110f034410684100c41001c0b102c0e50114030465903007014004c07401030312514014400b1511840202181502c15880090044144100403440602c800c000401c001d142200548051080a2070368140026504070001c0303100b041e2540105460829206840c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 787323965 1250 787322715 787322719
    0x9061d010e071b1202030a0314090c0402030a060f0e0a140c030703020f04150c05060105040903021b030f0316060b010e0d0312022b0e0a02130b030a060f0e06060609 72
    0x821640c50001c00c95661103c0300080100702000007011001407440410745003001415005552112400c090040403103610a039840000700d84403040c0300800704041a00d40c800c000a4401503a03d41e03514a1034800351007694000b41c4114820761002455150301e0b0011805080e9000d0300384030707500d07044001d985640b00944220542034410008a4a160b0099005041d10358002001e00d003841d0b03407401e082035000440c00c100c90201d05150190741c01c201c41481058050201203908105500154400a648034122002010207a0050001013181d41d0100080c1589094242c21640d842d0100c071032080000203407582c11100f440c108082900a50b010340301400b5400e10107807403007a4010341a1801c4915410b400483e07004140e00b00007120280c1a8071244802461091180802c155818441c1504584945400d030b2440d8004070211001a07603002d01680ca40c081001002c65451200070001e07003024540b5400910007072901700d0060451880e6009101184966000d4518540c1c6a106010552080c000705039 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 787325215 1250 787323965 787323989
    0xb09010f09200406170609010e070620030c0106031a060f060d2c0d110d170c28170402011413030f050a0209010b070807020f0102010f0609061d01 64
    0x4010600c550754903510746001400811120360301c07860381c540342c208409410f02d1783d00000c6c200800e0030b4003405411500b5400c00c0c020122340f40382c0800104100351045d80d800e403c075036078a00c0031981c0d03d040043d40c006110900080100d540d80385010104000761454a01c030700a030780c00018040d841c0400c1b80004440c400381a0302d01e082411203c880040034040003840c88058404203260315241607a84071945d0345825001000a4000e4890241041e01d4112529000f41d01c000201c83e405507000c001100000d039400320182031501e5000303484802d40150881c01c80503105017110003103403128038042042c4910840d01c0d01c1040200e00e08510060000854010b40840c464009003070000500d08001c3c2200302810702c183c4049a01c80d5500c1880c11714101c000e8916520822200741585841031049006003021400d81c2c1c03408002e661103040c40d0240140291081e40440340d0f81340d0300d134005c0d081016214220f1004001c5c1d55150700d1120028521801500705a05510146007504024404c00c42c1c10b9846014ac62 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 787326465 1250 787325215 787325243
    0x120e03040306091509050d17010b0f16120c0b0702010b090c0c251706090c04050402040902090a06170a080d0b12101415091302040213030b09010f09 65
    0xa84000c02041340c041d160055040756840062040100382842403000d04103141441c94001c0c0101041824011898062001001802418022920920800c100050700c60001003521016030181e254003402d1640a10040e07000130b6405080900c0030740c0f088100d0045501c2c1c0700e401b2802c030f40b029180603410141810110304130503655805000700d44280c00884048840da41d0200304041c8140516a000c05962442440000c0340b850903505402c0c0c501c1d004000301c2ca482042d1503682c500c1108900d01481d55040800e00395210342d00841c01954001d80306130024100f41440388000c0c24540704001c0c40359140350304200c0003440415240300081d003051002d424000402c410350000d11100401e181c2c807030f2001e04090601d1a0900188500e0b030320600700080d40d00380341c465003c0c25a6009021260205d440f1801c0c444646da03151115800c081080a1501021981c1c07004c58020710520066507403100d00082c00100f0805031981c21445600719400a00c200c04031013100605440c100e080c0203080d101c483e060 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 787327715 1250 787326465 787326473
    0x2070c0f0503032a0106092a0516031209080d0f18020f06040e0702061602030403020a0915270b04020421051912200c101716120e030403 60
    0x10803003003480c51240500c03e07032072031000c45085801b2980b24240c1c0940380e140407e00e89802284e0f0320703880e10400f410040744294a50b0004c0051055804010786002c40d03034140da09241c030628511241104501c02000b0780e0400741000c410540043d13001050050030719500400c8410741d400b0740800040d50045200c042c542030707403c00c1500015040d115410210510001509018140300c5a015480d1900504003030306001013030900c2d501007540740005540c0200f20820068032040440030440700e502c030f00010745040003045031400d0071150f4010401e07111949814520245511820016030390072803020060056840288020f034012481481e040c54444e014140c000724011004004862140058604040d464803502e00302c8542084140c485002c42c640c011801600007a9480d01215951410740c3c0b400d60121600f035031403500c2546640a8480c01d02d0300e22806000f20f00c294040c221610580c51149450900174000342c004184140001c1c00b10003045080791881d1040b0130300c550900001c4c524060075034403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 787328965 1250 787327715 787327747
    0x4090317090714270f04150219030b010c050a23061e1e15130203040c090b21010209032b08071101020304031e1b1205070c080102070c0f050303 63
    0x504036444008100002c60f004c1c240140441c40340c20400d0040159003042d060500c01d1465140b8801c0c00c0510420042c08103120828240c010188070389000b140762202040101d501c9083c418000705240716000c40013080045014180c21410b031803c2554146084040401d0f9807684155000e030031011032142241064241100d285034048800041824140705088100e940044202e4055821a81d8442030380010300e4240724840804800c20b0302175045040070f480d44c91048100b4860009401e80d215104a201d89035000503040f500c0512001614040c40028200d010b9400f070031800c1c5c031a00540f20103034401e240c11011b0090101000b41e81403811003034100151420b25003d4111810f01c00100c0100c806210240002d41c4194803d68945c2c101101060410700c1440c0d03100c0c202ea080c0088040c10314000c1103113481d503211807900021200d40c1b45280320415a194480e060010b01585852440807a1030700d0150020980f00d8415106d0100c20342e41da112164228445002da03951580040100c00c406140101c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 787330215 1250 787328965 787328989
    0x130b0412410f040807030302070e011d0711030c01021905040e0f1003080409020a0f0e15070218011e09020f040b130f0f030308060d0203120307050904090317090714 72
    0x103403494501100304050303954005034800041360744098401d10415a050000d03170010a1040d80340c448950400c1072420201d40004140009480391100003090b884c80b40d84072103c041904000d82c1c4e5038081c0003800314043d500030784181d0f004004c040f001030030b2a4481c034116000c4540d036920704051611a01c0902004070741c00341c03a4001d08a0ba03128080046202d42c4010401004658001070b561914460060301e043e03000070f40c403018070103031180d80e41a940364607441d811080c8041c011076a031401c851000864a5180084814440c150b950010409200720030b00c00b640781500796415182159541100c40c181c0c03141c0048118645800e00c420800400c0c0c40700135003010030141c06509447c40c0c68400002c540c6001c0e9009540c151074840081080c1a00301e1400340d0424030580d0104100103554010a85e5105800e039041d050020000010310000c0c81442551a00031004100303102d80f802c0b606008054a81c0036807071410010000012a440c0c000006040d4120350400c800c0c0101c41205204008080c0f0480d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 787331465 1250 787330215 787330337
    0xb0a1517160f1d15030405010f11190c0b040528020109030b180f100b01020304050603060f06070501060602011a030d0918020c031204030f020321130b0412 68
    0x841e2050303409030f94801130028182840101141c0b24a49800d01c2829141071441a0300d22600c1d00005000014280c1d0844252214036071146549104070841100c01e11440320000d052482c05505010400ca8081602083d022000780c08810564451204040c07000407000000d022400d0a0000c100007042d5042140c0c0c0401040d40343c10402d0507000401e8200f081245c042c80ca1600301d03680b8850440f089200b401c014032400c2c13004604203410031000c038610744005000700c2d110307032030a011010080d51010111405a50301000034090141d444002a000c3c003410001c0300800c4007001e540103214200040c180f40b00007205e0741e440d040c00f450800305943c905169009000704035002c00404110600c100020008a1880d00500c0031a18060900624200c035010341042190020000f00c50340745500220010012000e00809015484080141040007000351000f0040000e0400300310a00902c0e040c9130401c10b0040d19500d003085e0b4820b00304444207100c034105a0405034440d91070789684004035800c901703540d00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 787332715 1250 787331465 787331507
    0x50a060e0d0312050403030c030507020c0a0e0603031303030201060e150f01030923070e0601051309050c0d0c0e040e01020a3e1e0309060406030b0a1517160f 69
    0x1001140000344c0e0011a02680841c0d00e8199070f844595262046950107889407000d03241c102c0c070003400107682c2403291042e000000c0480020a14680d018011141008890300e00c920003155a8900a80604100d209212400094800040031109103080608400c440140101c04a039001e000660080004082c2a030b105411041807400051003200202c0071084c2044c010105546840301d240c40611009040f94100300007030020000002541d56484183d80c100b46000ca1141e603400d6659059018120581c01a00c0c00c159040740b50a810240b00c59410409803400c0c400c00000c4104d0500340e01c240003040c800200110039014003510007091070f19002c4101c402c0c1400410347e00c0840a050111103242c0c50842d040001c8490301c80f00849a100550410b000141d820034104000007103241c045e82c0301d00c070245274844103108525078910010201400001088d10019091503000500c81840711141001c03a4405401199071f50551030130a425601c66039850442e01500220100c441c903150003c910004c1e0a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 787333965 1250 787332715 787332737
    0x60c140c0a0f05040e0109020d0f0323120711060726072c0a0314010e0607021608010e07030f14030a0e011e08042301110d0501050a060e0d03 62
    0x240d1081141c00500021000e5402c45082c030b0100300031203481d41d175007040704e070314000700c8500584a12011000c1c80f0b4104040014030501c82c241644d48005040980c0c820780300c10103520076910f0002001d0440b43d08072604482180e42d41145c141ca0074580e203651800c503680054000740172a403154002c80e180700803401942ea800500b40303900c40c20000d03003074581e80b021540340c04149442c080b1444403c0c40d0300c00140501ca070360440d500d0200300244200d0001500c03003c503808103441ca1040035041150740760074203021034265144c0710030025100c0c000903801c1115900c1e42c000010324100305024400c2c2c9040d021010f80b000601d55641e0044480c0c07804011924800c0e41c0070310403580751003800a440e040e040743d101c04401c2e1500d9030005102020034166040010b001030024107000d58410b2086911690200581d001400f403a00070050342a10320540c4100d0750700740426000c112010300040c141000f26180e00307001c0741e601c0b03d0811542e2030040c010345001810048e40c0814926000d045241c80038000d04040110134 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 787335215 1250 787333965 787333969
    0x3030c020f15360c01081b09040212090601080d0309050304090b01030902092a040b031302011e020f2107060f180602090307050609010210090c0e04200604060c140c 72
    0x40f12038050082d4a208441d030a283c0c1100c20300281d000d000e4240f90100311403620011140d403400d14038010000f4490045403200c625211a070440b8200b04002800142c0341c0b51071072400395620001d01600c1c0c00380c00b42d12003081c07402c4c0c00307401424809076001c00903604103401c1000c444001c1ca02540154105a1074030651400358031194015401034134070b400d001d103000141c045007142030305104091243d2190100400c110b0140030400303907500500d1686884550f80c00b503000498048003610000700761148010380c0001c03842d40010304450b203000d4030020707180298401c10001200506c44c002c840703480300040142c1000503d80742c2c400f0b071000500c0300000039500c0b5400c103142d40420221100311841e650001d0311a45506d000c000c0300005020440d880b42c42c028842c80002e40700d05d680303030300c0104203904d0b01550400c003c0403480c008003400a400d0315820610385820300395181d807801400040c960a8000b4103c403d400c16104071002d581d607903180c03e4034604843d91501e5651403441c0c80822140511310042c4134070b03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 787336465 1250 787335215 787335271
    0x13020f1b03120f0f0907060f0c060605030105070f140405010f111c08040201030f06052b141c14160311060c0c0d09030f0605090307060507020303010303030c020f15 72
    0x603111400d001001d840c101c0c05000013040050b0000010b40e00c042420808203521003a10320542c01c1500d0030102c60200c62900c04007603d0035030401a4103500b04010040030301c0c0d0002344146440042e0742c50021581d00301815240e1807041d405100d0008040103103000c2d8090103148101c0d10788040b0b0301107981180110400011082c590306041000840c240284030656074540030302d040e0810188000c000c5a0314040c0050000d145070801c0301140310a164200f00d08581c1840d88800c60ba400000060100d80302071102034030303040c11203498611003801c0802c0502a038828102294944194400c1c603140c400c180b8484840742c1114038003101048014071005003101d4047c02818010070a0040164440c110408101c0c100706070300c501d080400c2030700e0b00104003142c01c4112400f51560825000116900d070201365a0440c03050460150070a070901050105041e400001917040768003995041041460f003140481e00c0d5588203d2848045e44038044402c442e0340900c0395036410947c0e01c0140c8c00210068000c694803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 787337715 1250 787336465 787336471
    0x3102106180b07052109070302030f060604110a080705070809100c150e0304030233031e13020405070306050d06020c0c030123040503072013020f1b0312 67
    0x18034000c0d041c0a000c011418015a41100c0f890418500701403c078034001600481d120000c0d003010411901290440000388001009150003034103a800420b10703101d01603607030a02035a2041c025490001925018980f80c01030307807911400c583c0c40040d0b035201d54070115540c1d0071201060344e8074502005941cad007070798802c0e80ba5100e9000729184d000b84507000d0300705031180448450b54580360300d0910501e241100740120488003601c0d4100c0380e01031450a00e40c0d01e036907000880d02803c9917030142c0307444030865809a58003031841500f81501d243c082c9020281400c00310b8105488054540c0c00e2403014500601d41501700076800b030941d240c00200e03c0d03518400542e0032040080161225540000c0c2280d004030b090108451100f0305400901403400360a052100b0416640c81c841502006400481e082003001d00c202c030b254540000700c81281d4800c421042419222600c0c61503c00c002c85034405181080c00d00070380e030030405d0b030420f540e0500055241d448035644000310f034a0510b00042081108103d050820070f40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 787338965 1250 787337715 787337741
    0x130020c0a05010506010e01020c0909010906020301080304143a1e0507090b0d0318050d121d210123180c03030f0f0d1d010c030203102106 61
    0x281ca000700c1c00c1aa007168009440241001099141c50302c0ca40d0300041c2008001e0700980c4d070510550390380c01e2200d00500c006000140014000000080d00c844000094400c0c1e40c20882c09a4148500c1c1040042103240500350968100e10400004000c51047c000c18911404d803540c0c84014076029a41c80041b03292046141d518240c03603c81c520140b0508010840243c12641c000b088003d5606000032101b0300c0800004040020b54204190100e1600041d8030080c403002d00810505429072030a0209440400b0280c00000e4208200700f00c01d03004410b040d100c030700020f041c8240303500a44440016008401c3c0d80d58030650340f02c0c0c901c414852010b42424808004480007606281010702201c9444050214000610f510280c01504a82e4000c0216012440d06040c604e5548100c0100010b0600450b0749012080c0d180501103120303e42c00884415a044007074000308149403000c20f01b94200c5c08151206d480140c13004809020711424543c5412011082c0511402140c00303565540e41518821702e4040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 787340215 1250 787338965 787338973
    0x28090e011428090c050d0203162c061311120a020403020f0603040b06010c02010e120f0f1908030a1503141c05090f130603060e06070306050130020c 65
    0xc2c08448601840302c82e600c1e040d04144411011038592808040240c09100d100d0080303030110008544d410010360b0300c0d80f44003e840c3c070083d84c0e507144120b00c0c00514182200d00d9041d0096804005a0b0000301e0f188600d8004007941c0c0c20700b0311210004014603a140d848070b220101001901c0400410b10724580c0324641d098005a80e0f14198414030081d10102e00d580c5001d18014000d000000d0701ca41d43c0c0d01e9100c8003c0c48c20300e98503015400100d6040c204a4105508210340158074510b440e00403641c100030048400407180f141ca14500b04507903686506402c4400020f488501800040c0b2002c0150b800040d00140440c1c1d10791294a48202141550300403554405100901014440c050000384018840004111030b9040420b07000f82c075070b01c02c07108081c0c42030b0384c10796500c0301598500070074143e55407040d07604001c191307220b01d024002042c400d505c03604e607482948005403285220303000300c000380c85060703603140c50300c01042001444c0d112444400301c9030b4040600000030302d12000c1c4050f00010320300c00c00070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 787341465 1250 787340215 787340251
    0x12040e1308040b16060e01140c07050c090c0a09052211090a27050411130e0f010204063f0e241014060903030702060304030306030228090e0114 63
    0x255084403409084054140d04118800c10108e10071440076a008a039024155902d0641c3d140490400744511103070703544046a1014821200743d0400a031810707140c91b03140d001c0c441c0d4403441007000349031102246c200a4071400f8071000403089a42c100d0001c105602c020b080c1800b1585000541c0e085882d000003103852068401039062009940d8072050701064180b040000b81015190103c0d1400c04040150040c40c6da140d10032040074040d801440d40204032010703200290b0306180c0070360103035103c1d100e0030002842c0826603451896038024012035401222500d0080301245240b00990b1103d4801c070210700684e00d98041c038030801c042c45044103142c21103408007446592a1000f64005002501503110280080014000c03002e0341003c40382c103c0402c65806882d46035500001780346114030400290010ba01105000805425400c41d4082c2c038400c5401446000b104204d206602c030b40d00d20011a4113440100c1004158040d5101c00559400320b07001045d1200c40030300030807003820103881c15480042d001c032407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 787342715 1250 787341465 787341473
    0xd0903020307170406050d022b1d032107110f060f010909020f13090c0b0702090c070506012102030d110715090302060a0c05060f04020312040e1308040b16 68
    0x2c040f243c08080c020702420941032078001810ba019804410880c0341e40002c0701c02195074041e0700c01000070340301342c21080c5048854100c4000341880416140a40c10000741603110440080281e900c0125516403039812000f20841c940c800c0d41001d0320b0780080c000d010441c0200c05a060190314005c038038000041420342845030382c244c0c4440e8141d208100041c5804551001030741e61525503c100300c42260491b2401c42c1900b4600e00900100c07070300800d20610b54800280e0100440d002c0c0550314001c9034a0703c940e5580207102d4100340b180c1040140150010001400840110510006002c00080c5000064403c030350110346440000100a400704003e900e000029000400c02d03040946140302c2c4a04106004031400742248070b036400700074070901d4045064103140703200d072f404103440a03080000c80b80c20341402020000c00e400203a409038003d00482c0303030f94482c1c0720350030003180c007201d19001440a50342d42c0e0f03903101807a515182c0310450354042d0402002440078090405011603840d4110a424107603c64a8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 787343965 1250 787342715 787342733
    0x13020c030301090b011e050313170706060f05030a0b0a18061d1605010221220e070810051e19140405011401081003021306060e0405041e0203030d0903020307 69
    0x80c0c061b80801541c1c000c9482c5a0040580b034220210314203840c0e100075140307880a182ca08a04448501c000045001804d1003003e030044000c4a1035007100c80c00081d2213000749600c9a60821014000380f90b2000400c0100c1d4242e80803150707440112086004440c05c550702d14056070f1030070040b4265142041c041e0420385105004032010501446070581d6960701d0100041c1d1152518882c0c5110050b454144124501d141d00490340445031720520034201e01001c03d40c0c00408000390041000c68440c56001500850084070300c10701503d0a01c4d900034000b0716000400c1440701d14815001511610b00048102a84500114011503a5100d040307e0703000e81040c440505038100f14189a1056080600403c5401d00740c0040d2420802c081c039080e410b69030303005101c400b1070100e0b500094200f401407070765850800c4182d200d00250781075642c481c1d44244001041000ba11000d40c2d004d00044903484000c0c00080c1c030350b100c16056520281c242e9003045c820f010032070100c614081e02580517803c0010318074104136440c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 787345215 1250 787343965 787343987
    0x1060603021206030604021e0409080c01060815010f051012050c0a1d0f010f050c06010b270f30010c0f020304031212020c06072a02090613020c030301090b01 69
    0x44d008202c42c0c902600000e079610340e941343c90351100c2c1149041c411251120713048001d85541100da01a074440d41035606e0341c0200700912404640b4000c2407a845055100c55884034100d030300c1b641c18103603200c0c180400c00448032100c1c82c0c1c0005009622200c1400034a0304e014892054078540821910741181140140004090b921101c55601c03511400041070303551b086140d40c2c100428030b05181d14544480e8140d4a1f407103000c9207500184101c100000d10700d102c4000604e14440804104040003035401e6895200340001c0303160b03541c0510307400007841040c1004504c00241c0d0f281c4213400704182c44038039044d45e041d82c0582404401a51241e60807071380369803c00e02e2031050385554802189400e1940e150005c4143c4074035014803c000f00300840351030750301071034054071200389060050f103e41d814030b220040e01002a4050074001440790507280f48045406001000d03803da005807000c0c0d50340d030707455041291040340c030091110203503070030300c07003d03080840420107140079165103c030008070001407000241401c0c07602 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 787346465 1250 787345215 787345219
    0xb07050c0a06142a040306023403030f021204080a0c0209040c080c010801050603041401110408060a050711030d0e010227100f020d050903010e010203042607080409020a09080d12051807030f0507050301060603021206 94
    0x4100810403602504125073f4001c2d002a001c544230301c0380d00c20484045c1d951040c0070b50700c0801078041c0801d005030056090b04503100c0ca000c440d200520400152003000b001d00c20240d0007001840010040344d4021020030f424101c20000182d180c40d400122180c40c0c2254000d104030b90b0050003003001c40d84042c40b8894200c5c6445c205100700c402d201041030743da0312a0316074803011710f03807110030088590340c003501542c00e001400350911007040440500b000c400e00c00d80c08080d11401c00300c850300220f1070265107810500c03190703076010305281920780340306841580c4062900c0d505903507a1902c1d056034640a1001d14021361048406803003d131020354094181c2e8128441490510804105071400038404e0380c1203e045803655500980c890504c42d8040d610058550f000380040e00441105c0212181c0c00039070190b8840f42103800300441e80303031188419200082c2000c00b5100da0300c072800c24070224803420300c0210890300c280c0456030029141c80c0846e082d40c03070070307881000401e0b004554914070500e81402181d01100c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 787347715 1250 787346465 787346467
    0x6050a050c0a110709060902120601030c020607030903021c0e10110a0f02010c0b010311120304051509060c030406030b1c0b07050c0a06142a040306023403030f02 71
    0x10840c55846070780701c1c0c16540c50a0250815483c018148103220030001419503510800c0784560381c0071010b000e980244c007079681c25103440780003075030543c000d216110000c0310b03e50080180d5030fa030b04d9040c0c0040c00d00714003d40a500c1940f80c0d03281002145000d010807140c0594601414499403401e01141d1084090740b50305100000b900c01c0d1070150006608080c49070030040c0500185080c0c00141c1e020341150034040d1210001c100048144104d80071040c410400035180c04901000380214680c60380030341d00650303502501d54003110256181c40006422000c0d4001c158510742424001c0c0c1a00d9030703101d58024400710362105100391365072031b2000040c0803a141303654401c801103030207594070303c15079000420410034014045201d00e0380d01010010443e0705070f1321200030800118100403801006404448420f0f007203600445500711a80038120114448070700c42d44071f6082c42e0039952508065001490103000601c00c5084030300d5076000c1c1c542420500191520b50001080b00c4d4180102541d1030186410074043c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 787348965 1250 787347715 787347721
    0xd05030a02070e0c03241c0c06090302090606070317010e06030d08070e0405090102040f06090e0606040302060a030b0d0c12030f03060b041205010e2401050109050120150c0706050a05 80
    0x110001c1100d512041d1440040a691401c691428111000400c902e40000c01606008a2410200c1c1807c1a2a00504c02a0383d01d50303035030320b00712001440381c00003d41200c454008200d641c1004005000705c1c5100713092281000500448094140209a01084d10550140c0038131100741000c0c004034241c112185006692881c0580c40a0051404d8142944c010b6a507000050a100000c1d810f50700604054264000290f0796110001c110314607600030128000e41c44004908070f032800f40111801c41e036015001e2428050451010b9004113268806190405440c1e444140020900009200905180104040c1804007030034004c0011402416203014581703840c0c024070202d141c9405440c1120301c141c013420b5140d0b45520700a8003500c0e52081700442440b40300c089103030306401094185075a141010824141307070f03a80d00c01166103194600c241d50109400e26107208000c0720006420801c01ca0b04004c44000303680e8000800c15500302115a00e0001d00045006020406140103040e00b040710385070240402d003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 787350215 1250 787348965 787348981
    0x60513111905010c0507091b140a02060103120e04111206041a190b1b0d05210603150f1f080c01050c12040902040504111215040b0d05030a02070e 64
    0x81e0039405882d041c4107241c0110000c21904101e1140a00f44a071170074840a000d861300d030f426002525101d0004102c10204000d40e143c114415034601e40c43e1503000300400d0b4603684a1110150302080c60804001c90044040304603180d502450030043ea00c181010f541c0d0b10390032141d9038070340381c00303004684240e04066040000c89030191000c50100c00490f240c11102d0b030920a03118100c0e02d55444011902c9000c1040c0080300812554039a088540d44291008030031822070840d060320a20525400045800e49040700803409a1281d9503c100050f0454102c02c890503803118000000b2500c0b041b000494600700921442e00b131903139075075141030040440e1110742040e80c030360b80304e40910401e54100000854101c41942042001801a040c040c46203070765a5100c098901c041d611078003580380660708001614001440f8607003114140310300102c071400c0300c0e15031800000802d92040e10280c1e00030744401c200030740b541d10810316800030f51090703000b175a4408640d1000ba00305560703640302d40f00096103042048040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 787351465 1250 787350215 787350259
    0xc120c0a150b0306041106070605040c06020c01020622240b0a091107120c020a0303020f0607050a0e010f0908160806071b060b0117010602030711031b0d050a06051311 73
    0x6640302d424a000c050801b000b103501401001400340042d03041505000612004140c00d8050303030000c0e401d0f04c030791500080043e69141c0c07080d5101e001c01d202941204140e0384848507245070311403052800180c005034081c2d5210306480c800b58407403c503560701d10a2954a02d4804074100040c041c00340f09000b50300e8944081030242c05003100250006286c00ac107049242e104640300c900c1154024100180300391282402941d4282d8510880120300c58040403602e050f014009440180302a692000310481c5a0700c011100c50700c0c04007000c020b0003100080400c860400b4042c5031817124060207002a40d510f003041c2c59182c040c015080358144007400b51a9883c07294140c0d40f41d14920341000d40071031a001e480700102e419503504400302070241322050002c1400c59000c07005001c0680075454100307105005104064660007510b42d4200596034101510046040c0415482d412038010810307a221088a61100419200c0860b001c1508010f10380c043c0c0c0c100326140c012007010501c161240c410300310109941d0310794 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 787352715 1250 787351465 787351471
    0x309010503040206122e0e011e0e15031b03120708070b15030c01030e03030106032304120807020303040f330c030e030f040b0c120c0a150b0306 63
    0x1000380000c001400c2d9110001250106180f802c44a50246808a5a20010200010017031032020100800c04410501e00e140d10302a1903584000240603440c00c0040e42e15268010030602500701200800140a180d032600c6603c104e04003028a11940710010030103007800210618220516450004210151000a0a541e00c086182e1009a4404083c107068203d40180a0020a031840c1e0204102c804644041d50f076440d11003d40071075002040300401541551503410204c81d40303134014401004168402e0300426052000040e07448800103005200c415032100403a42500c4890f10280c466003503c1e4460700b190f40c0200b861000c1d5042d17043c141e60302e0412000101015181414001081c18040c06a00c0c11001c004c40d0040c6000302c082c00b001482024100070541000460f1410206440e440c0020080303580185032214203901d024207000c0e0b090300d2a0070070005110103104110201006c0860100204001c5126000a0406c5904c1e031034086a69036000514054407402c0c0004201a81c600092043e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 787353965 1250 787352715 787352717
    0x1206041a040f050307030504050a23010e1207120b0f090601060333030501510608040b06040e0a51150603090c0909080315010e03030901 60
    0x42501c0303a0801440402c21120054003d000000c0e0b0541019000401401159400e0310304017a030603a03d640d1030544520503501e04918100c007282005541d0b20800800c1104440100385502c80c20221581501d000c010360040781e0810501091401800381416542d544024411041c1c03101d894481c91712900c88c0810b01c210400c0c16120f40160045a064092a020760000c1601c595410f100704004d00c00000d96034401030350194681452060008010305101705041e5803200140c0c002503100c008212015107290f80d210381054414442840100b03000c001c07070014a10355441800f1420a070030022901840a03101c240b0491410f074070101e0412020030000f550035000000d4000c0032280d0001c17082410000510100904003460103490020b441000c1d050014021601c4030340d44101d186011402c403010b28406800e2001b903d401048003d00c070790000c0761024400c1e12600300325a031b90510b8a058600b0210101d690705004402c02c00101c80351a0b0800e808142444c181c1004640310012903140c0c8100405c40d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 787355215 1250 787353965 787354013
    0x11b0c030201020d0f021803030c070e090a050118050c030a0b010e0414010203010b070b0f01061b0309050316080c181603060b0d02120c032401180f05120604 69
    0x40c03600030360584a503c480c610090221900700c5a00344000d50190f60924403d0030b450901909078100042076650694004000f408118108a00402c00c0e00000706880560300c22803e40a000a00a024181c2c00342841d4009071144c44561130224200002294114040e034415644913010480b00c0491904444000f100c0c1d1f001c9849a0401004503107541004820941c000000010a034450b50000d010003401101400216207503d15503440303460f028400e07a00010f0180452201d500884000c01080768821301f0040255907550000c281850700d48606078120211207081049400000d0081c008800c008880c102c590002c3d110012086a0000c1d1600d05a0051044007a2000c1c2c002d500072401f6200b089035481c1c030340c43c200d41c00401943c003500d81010300c4030002c0042580350740d000c4196402070581032207104010000440341640412100c1d5961304102e420701061941c1000254400058109044c80000c020f081200b40300c1255900d102ca4034155120208010105805412448126907024910 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 787356465 1250 787355215 787355237
    0x1202070f050717151504110706150905071e0f0e0306040f06060e1003080a03091a060102070611071a120106090e18100b01090f0e0f09011b 61
    0x203014122110001080340c03042c020b020507295065080425081c1c410700848164490380044c0d110000400d0341e03804100107000c0c4c0c1700782003403505400c400c0283c40202584d03030400d0b10f144c90f5401918000990381c481103040c0b1000780400240b901401d54801f203a0b05240d0740d030050480d02200c500c3c0b02d00c0032032020060460340d41155107104910080e0f50f160010b0407a2800d00f00b074141034440c246056002c5880916068000520805d40000d29100b4640c40c80e12003441c81c6142c0b1003c0040d0b2007034252a007015501c1f0240c000194018800c2c41006070918604041880c00c90006446c0c15800c1e000502849500048201a210f0004181741554860324020f0000c0314005038480c20345c003400c10038000da08282000402c00c9640110201c003201c000c0007011105071507590410403070f0740f4170840a05050b0401d404560081d0800d4119003400f45062403c01c400700c0c6e584200810030311254100c0c4882d5440b000070b003c811010394145c542c008561800811060840103404166521704000b0702051113050090 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 787357715 1250 787356465 787356473
    0xe0405060609030703030302030a14160c0302150a15080705060706021c39091e0503010c0c02041109030c090408091801030312060e013005030901080a0b01120207 71
    0x5a4801c42d602a00f219003141d201d18016001e9003040b650010602d1424800092207a01d04080c140140b1044809494027550032608903500303001500c0a0303055105101c1d41a510403041607115214402000700040c00503410000320100b503989900042103a400307440140300c2c079901c1700708036200310340d01110041e902d5000d00014130304004004c506804545c82d00050069010500182130300944030042c2c80031038113500701c543c10080e109170b285002c00142c000070244061250084034a01d601d9047c041203102540d2540001d003940c1084100f03000145580340c2a1085040c90b0040c25a0910420602e0b0b0404c0d00c06d03c0441d40e40c44c80c420000303204019400c003041c20b00500404a908821018007142041c60800140c41031481d0288003c0740022884041003500b15440d10400c810303030788800f811402692908100e00400901c0c41005801c2c50203a1140041c82c038803251556601e98403e6002c0d503244c410801c009044070100030600a0079500381f011132040e981c2e00100c803840300380c1c03c46401a100c51550034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 787358965 1250 787357715 787357717
    0x200d0c060e121b0109330501030807140a02120d0f0203030103120c02010909050907050a170607260a0b010f050c0d121404050a0b060f090c360406150e04050606 70
    0x780078110703030000100c1e40d00e80c6c02a4004070440e9143e0000d80103002508510240489509200c00390503c80d050205c14006000c460086040082c488102c440c00c10360341e000607555100c01500c1c1003441d800b820740124955042500204802d8a60014500307541c910784502c0500402e080040d4100050b0f0354941c03045a01810403140607103024202000103103400000666108032070b020f03040c4100260071000903124020705400c1403680b6180c025003103949440c803007036856066900403080c155440b15079101007041000c62081c41200c0d4030b0804070340d01c0e042d00009414111034190082c00c01404100c40042c4101c0002d10459502c1645400807900304501c0b14840106900342c40725484000f004140000d00c00000343d4221040c1c095080c071826070700c1c3d141c06c0008404083e00d07a40c1c1c0000380b40700000c0b103c54846025200c0540d0103c410582e10854020714803503155440903100c2d03c140d070001850590705141c0b141c24050020b11131000395030301c0030700400340c400c02d443c009851145880c1d0303000030100e80b0390710 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 787360215 1250 787358965 787358981
    0x30706020d140103050f060114130f181b050d0314030705040b0c010c1403011a0d0f05011d0105031b040c1e02010b240901200d0c060e121b01 62
    0x1141d039842d5940c4903d0856110a6903800d07003540c0d44500c900120300c044081600f55401c04c4010065041d5081a841480180000642410320a1756a440c8803910010340340f41200103c0c0700d0b0a0640e8001c2c20784ac074441e83d101e803d8000c98090030101580000080c0c02c10501442421002034040d16075494400c115054480c5070000001c00d80081946440c0c0f2605400c0701259072215129010340b0303014010350007400d002c00d200e00c02e411046004080d64900103100240000c06d03242d4800300700c00c48540d01020a444082c1d004480c9411005074100382141c100004c81d0141800700d015040081c10000d481c00d000300003481e95403090380d0310f09200707107054054522803c80065401c0d6035910000e038040080e000303103003141d111b83c00f91000c01078000c040d0440340c524007001740c6c40c10002410664540300465103400c402c0030400c7c0d41e84d4441c0344400500303010000c0304003060f419076910b441c075040f520b428014ac54001c0d034017a0311540100c0b008030b034160f90501038aa00200040c03603900101c408000c0e0714007500c0d5813 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 787361465 1250 787360215 787360241
    0x715030e0f0a02030d0522061d030604020f01050904060b03040813271e0e010606090b0405090106050f040b041217130b0c030d0509100c090e0c03103303090302030706020d 75
    0x520000110b1f2074000c0c100d00d0760341c98050027100c1465000c1041c1a21040c0440f40203500040a20f00000700e580510003a0005504c060070000720f607609e880884c480d80e030043d1804d0700d2984d0007107071400344643d100800c0c40180c8102030110f07a004491a2600355001c800556001409031281c0746507458000a805001c86103d4000e01407250b01c0700190554002c10046c091100010600103000c44c0350306408081b034080342c4001d040c010181c8c0ca414000c445039089514a802040310800c00020a40500009807001d01210042007400310094039044c08400511491a80360113070611441c92442c900001c0b074001c80702c0404000d582c3d0307038802c0101c0f4154402c2004944000749803000b07004200c0f400140c034446c400a4500300700010807440900345c40c15400d9120b1100b4804088000030194081040a90f40140300070400701d0107141c13540b1540c042c04081c0012011804a40e480b068a0400c004102c001412a24141007006d0895501d00944900c21144081c20007500028001440f000540c001d00900c481 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 787362715 1250 787361465 787361527
    0x40507050c03070f060b121203060f13020904060e061c0201030e2a220f06031208060a050a0f0e4813170715030e0f0a02030d05 56
    0xa29001c0f054244040c0b0990700c1030311b000d1a2881504003a07000000b07820409004010754820524010885c0d4070041c00345800516102d4840225240c01c01442c80282e450b0201680781e158550601c421100c25130302c0384009010100910111703445a6031025a0000c1c0c1d0100b170f01d02b1111500060b070251040c0911455244202110800b4484140c2280b1403c0c0127505014280441440108000c2503100703c000e002080d1454401e002c00e02055100000d40e8480203070215080d0b5607522159007000d000380303161012800310000c110345407500314460000740004a0326029481d0500281c2c44001816000d00c01c4100c080c580850841d41c24980d4080c0700025461051359000304115070303462585c8030029445550703136442c0c1400c1030044011040c0d42e030340c0d2148807000740b4141c40c0c400768881109605030f60044030700a03000081840f400440100340d10300c24580703000c600c1420622056140c01c1c041d03070141104e42c1000300c0ba640142e80114503540c21109030320300b050300c54051040d40c045504003443da100c1c81e140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 787363965 1250 787362715 787362727
    0xf01180201051c09200411090901060807170103080306010206071d0609010512100e1003030c020d0204021308210309060112021309050a1103010b030a0204050703020c0303090106090e0703030e040507050c03 90
    0x2c6003085c0488110003074401744100e440c19406032204e4092604120f501541e820018000b036441180d8055004121b443c1519280400e0a6201340500c42a0000c1e203c080e0000100006541c04211050700640c841c9803e0000d800381154070b00300c03200c52881aa00c10100020b41a409078810402d03590004d0320510303426001c0c10070402c59200042c180c0314001d0342c00c210b5000103400440e1003520710b0489402d500e0b83d11210000c5c0d030030041501420102240d02980c00e104120038400091104c070086c156400051000b0340c41d940c162882d600c2d07110390030151080300b00704000c90039002140080c1101c402c1200700d0100d43c0c0601c002480400a807292444040c40c11141e43d040c040001226101c3c00c2c00740d8007070170003816074005140c00e035001041003603059032051001c9001810701d81e2019911100524005040c80003000d0a07a0450f803058a100e41c2c569102d100a00410065215002820707a01c10002c0024910395640a040740d074660805601c00caa542d80091a000c1c0207038120b0390854444400c0d6540c0320 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 787365215 1250 787363965 787364003
    0xf18080609060615030a1d1006060207080327010207080307050a110a05030c01080712090f0203070905060d12140f070506010603020c0a0609050712050f01180201051c09 74
    0x10604550030080c612681003c5109400c00f0040c1142500b4186500c52942d41d038001004040c104000400d00c21001e03d443c503101c1118284400305400451120100340545402c6000b0314082260b00801126042040b840302002034034205000b980300c0b114405204180850b00607400d011710b036400604a400006400810403c000c966007501d02c0c400c1d28100800543c09040c801d200e031850188030307010303030114014a100e50b014030102a840111803a054100307584413200407040c1c410700b100c111104405550107e0441c6014071420010300440ea104001610300348000940003a13040314094090701e01c3c0d030480b4003541d1145591200024480c0c07061551003d0403070740c0f6545036220b40001e5540d40a043d00105d03c06200b8000c96500720340e120b000f82052031075504c480000708160442100c90b0321580c0c00c0015081c0c10000c030442c01e580500d01a0541a2403200081d00799860451104e032411020151000140e8003e400c0d918000c1c0b5806414a5080700f05509030001c0c10240800351011111205a40e40700b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 787366465 1250 787365215 787365223
    0xc09040c1502030c1b0f0405040c1a21090d1b0c0e0126061b0d230a06050a03030f021f0b0411040b04090509030d110406031109100f1808 60
    0xc50381c20f00c21140c0404503107071030980c1085040d01480c6c0c491262081d50200386041e400454000d40141c8170ba01710310741e81e80c003586171410181021000215010130181244690791000111000380c01a0350490340c500340300055101d80e600d00e902411300621030303107000c0d8080c102078110b40c9031540003011741092615411149171394082403148103c609200d83c100e2040c00ca21858922020b241680104a5601c4d1180401ca60b8240780b613460146020a000400300304266000720190620b104038904052207150ba1120340c3d01e032000b0014842182401001c1003642ca0300d1540c03200303c9405141c51242200d2400e000ca08208003a80200800a0101902a0104180d030f00c40c06028404980810140e0208400c51440d80103901c01d00720854014881042850b400c1e402c4154800c0c5402c0540e8a4081144010005c50b040e448110b8501c600c0480c091089079010302c912510780c083c1d40200c5041000c1100050242d500204010040001c5054200006800350340d21a02c1718078000e803420302480d11801d6090790707 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 787367715 1250 787366465 787366477
    0x103021c050604051509031908060630010f0e04080310260f011515020703020a0938040b030106080a05010f0c0c050a24020f0304050c010503090c09040c150203 70
    0x1114091700c01207030145400201f100c0031000e1507440daa620140c240c3c1c00343d070301c030800070403241d046002000601d000720155076002d460040308038450310180014200c0004074440c1600070240c842c1d46031005002c62941d04840c15440f030f41c0213040655075076030712105403c0d0070650b82c0f0010002001c0c090602580f51540c098481614008049581482c10074000350700b40d07001c1b5200f204a0410000e814410008403644a103a81151401120640341c0e40354045807000302c3c9544020041682c0303506a40c02c050441200c03007101080300c0c000600802c40000d40d8260103100c07040144c8569a0303901d640d880c03a2400c2d0001c0008142c0b00c01559251441814001d010705504c0110f8034400b4070700085202103e000c1c0b001c80241681007401407540c1101039803241c0209070440601d0443c0e018281d00da40805060b40010b010905208408a8882c103040c81c106191001e5030343c415043c02030610820446200001c1e072141100c01c02c444202454846052000078200182c02003010100c4594101404075000002058 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 787368965 1250 787367715 787367743
    0x1f03060f0323010b100503060a03050303160f030c1403040620090a05190605071505040f03020c1e1e03100902031209130b030c03011401050a0f030b0103021c05060405 73
    0x1041020100610f0884070710b8100da0b0340c859500190461110720440c051548041c02820742440d80b5102e484540c5107420481d4180300380404641c01081d650703070221907424a1613460400f4402030072802d5000d8061401207102c0e0752010b50100000d02440802d40214a800c194540c100000c01c0205d40118101c1d4042141d10340500b41e21781d00051541410041403850b01280081c420b00982411000c5030b055005c0c40064a40c03860100d10007640c85900c0c41a107000d03a00c0390088000034038482c07801030b0402c07699402944c4500d4000d0b0100394101d05070801e034403821000b01d52142040341750000003001c44508456868040c070a80c0e0180880c48c4c410b131b001c200094022011150070000c00030f442c0c9811b00c6403142d401c3d0000d901d1a992100080c242d0482c01c2d602900a095481400d81c25000c03e0864100f07a500b11100000f03500108118100080b000000d08421440101000c0c11074441145114040c4030082c0581e1640c44244005000c4202c49408182c1c00b1003980c486003440e0405030354810400e51590 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 787370215 1250 787368965 787369013
    0x10180605031510030c2307240501060206180309130e2a0414130605100513050115090f120203070324141504091416091a1f03060f03 58
    0x24155141c1d0906c017a2511010b0a525200c2940d0701c0f001d11006204816107144003602e40b4844101c10703802101d018003000d9004061922f403030b2a8520b4000450780c21011305400070820305255803a2000c1c1d50210040444d130119110914002c814a0482c160b6001640300c1a14160015a60340a000075416000215024800d403aa902002481600b050312180210b80f03201d07001800240158000703070f038044010540400c40960340c0012640c45091444a0150303940e413080103101d110310801e020301c2e0700314961410030416400d1003914403800c0164020020a0203500c42004211340d0708005070b002071548000f54a0600901082700110302840510348d5071294100b5050000d854403d0121500c200750b1609440e031448641402d00000307201c5180c0907107001a218000508501c420808410001d07004207010452603e0000e81004444a10b41444030201d40182040029503c405c1c1040c66445c050700c041d290104108420307002030409900c1000c82c02c40302c40000007444100c031150225154811860 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 787371465 1250 787370215 787370237
    0x209040606022a0d02090901090308090d4d010b04090c0b0310150905030f070305030406080a06050a0603050a1a0a0b09061308070510180605031510030c 67
    0x2e980fa00e00c0c0703e0142d01c10100340c001070608090910802c00d606080a400c40038a6060350f008141100f07811168003160b42e445441c640c040542c003c40141c0d114190030007805034041c0c403660040034800c04d1218086540401c1c2120f92844820505000000ca440e58496281b4281d4002c45c07851803018030843c500d00d500e0400c0c0b43c3c0060a0030300078200c525a001002901030b505042c0b05c5000c0341c00152551384e40d0008103a001c51510290303058480c030001c0944890102520700020103281c45860fa40e4081c854100040c1000000d00000c180e40503500c05040241d00e0741c2e074081c900c00003410107038851503005083c03080c00250142c0642c032483c02200101c000f800000900039400709126055918550031624103082001400f400c00050a004ca00c0141120710341540001c004074020569080b07250706404c040c004000c145400503080c481d240c102d0504844c200c09004c0c3c4160207040c00d204a00c1403081c00030002c0c0c09038044086401d5814401800c1c44507108000030700400414500200001141d080340300d1f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 787372715 1250 787371465 787371467
    0x1e19050607180e190e0a0320010219030b030a050d1805011803020f0301020d0504140609190b04020f04020c06010906060e03060c0a0c080a02030a080f040f02011107180209040606 78
    0x188105880b90b041c20544280c803140713544d51451402c3c16440c494699114405203483d00240880001140213559030107100c0700e0f400214800c4042010000c1e80b5a10400c405d0050b502418000701c201c4245007000500c640c00b40d00407034100032050030010800d00600c2a0b200d82070340c01c8182e2245001400540010464441005403000c0a9005500103041141d03481000180703880b0301e01095030741000d4009030810f00041c01d0f6070180c81c001e9404a407121205140141d40000c00c105655000050f5001042600d1340001500100c25030840040c00c0e9a00c040001019911080c220316039100300900700315564040010001e4840310b003800303030183d92801d10100045242c45000e05024502c0018003078a071540700c3c03102e144819031000703130a00d0a2100c1d5000c030601081c20040a0010740e40c880c2c000d140c1d190303038a407001003012900410070031030b60782d0702010700000c5200c10400007a07050342800d2813100c16102000c00b6140c41c0442e8003d404800d10030140003815201a000ba0071403480584050103a00e403107a01c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 787373965 1250 787372715 787372757
    0x2030c0601090b01020a140118030302120609070923060318010c0e01050a03180c0602030c0c0a2402010b1e090f07051903090804120b1006021e19050607 67
    0x744540141c0c003041800d4040381002c0c0f441249031f50300f407000044075014013140804181c0801425000310360301149801f2420800101964099001c65411401c4c2c0740008028101040d640100d00301180044031100084040c07403100ba0402070000c012584038503102610341c2008840c041e40c04d002d035003820000c80c541e5006980820384428140c48003418012904822001440c1a1000400909503012480003007a54800c41001074042d5601455440d403551480074640407010040704e001301142501041752000107151401101c196940c80c0c1084044540d08a015100a00c0d0705a40180c060a030360802d81a10007581000307010903560345881c2d80c2c44007040c2411000c1242c100020a00801c21095090456a01d1160070181e60a0000b51034920b40c0b100702041c0c22070780183c0c10070182907c80c80d00744503d096030164801c031240000c0355a40d04061000391609400648004c0c110030014942035160710601c02d03021040c01c0c03036200d8422038515052156440c0015112070000c03541490402a40310900384d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 787375215 1250 787373965 787373981
    0xd0905100c3606050c0d0c05070603023007031d030a1119060510080c150a11010509071502060f01030f240e0d030e07050d020301060b0a02030c060109 66
    0x1860b24a5042d2811050b0700e0b0a4100404101104030511181d41c4003046407038101020746900d9807115202c8008248441c5440d40c0701c0c0c218001d0241039050b50707000800000d154403d0310098074002da02c0d0182ca41c1c0d030305900e0705059154003503800314102c80c0c0c602d40346144100d4030070695030358280200b444091002001d215a0342801003d81c004001c8000841d0260550302003a400c01d00442c1d12882c02c1c1840c18101040c0d940c070803101507494000f403210780c0e2200c42101016100da5400360038054031680c0050f0200e408071070610908000811410305141c0204803d41010b00440c000b0b20841c9400041d680d1200428003d060052580c150204112840062032500c2035006182e00360440e400e40e2a103180d0040aa50211035950300040100c01c039811200211700075985010010964007400d0340380380d0800031a074080504144c50201048490400011400215001651b0108040103640082405016103410185250100003160200c0540c000010148500460103440032a6240c0a0040c1556042 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 787376465 1250 787375215 787375217
    0x250611090f0420030702010608070f1503050606040906030501091203060e01140303070f0b07080610141605060c0a030b0406050609060c1c0507050601081504031d04020d0905100c 78
    0x3000107855581040d81c40018060340c00e180e8a0703180701d0070755800f8074076500803030b5810f006035156403041219040c20000c1001502048601c14040c9040507002c2d0f100f01d0b408100c04003019120f20100d01c2c644c581e40100ca000e826000002e12132681c0301d0604070302809804a08444680e840d8a501c3d4209101e44180810b0300c4003901101c289910304000d880c115400d074024250b26000820801001074801c80340004507500c40d40b928509403400c1d1030043c103015001400c00c0c5c090741291510000c0580d01510f0000b951400801958444056055050071170b40868001081c92284074244401c40700d200010786800901950b007441045603480900081e1101d900c07980e6000081030207841d01c5454850080c00201c880c2c0401c89401001410f04843c02142d034120030008510001b40030300c00e0020902c41580581103207002803550846056020380100c100810140802c41028001c80d0701c15074030300b2508000c0000420079512810008000030040c021520104d603d8492120b070b0340c107003002d1405030180c03001c45 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 787377715 1250 787376465 787376479
    0xd230403140f120a1b0804031b03120603141b060301360203070e1906050304031e050d06090902010c030302130f1202010807020f2125061109 62
    0x1800803500390390300550050014040b09114044049605089840c816040c8002c04510840c2d03040d5200800c4091501c19010895440c04010109411962260203507007008021096901035080807945a02000e803000d42c40d0b03003040c0340041407080c0202c0100884901d041070301d02d81441c0e61103c0c03160380c40384040260402414001040070b8040481c0c80803500c3c07540d040200c01200c54022040b1001c1039401c0c40030210358080188000f0075404049c1c41d141c620f00741d590a00990440809508050b0341d849230004001340080000d0402d845000380d035000c2104242c04001c03100d64080043e0064112250030300c1d032503203400c4000844903000d01612064275010785900300c40000b2070300e0881c040d50003880c0c50b40c400540c06a0000d05a08001c0400000309080240b0049030b0041d44001401d04501500550442d0310000240c00104004200c01d420382400041000c9100c50010031b08009028140207500d140541c010780c2c1c082c0c024110010140c16210750020002200d400e40c0c903a4150284860706a00120 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 787378965 1250 787377715 787377737
    0x415031203020913140910060e0a2408010501030b060a0b03061e0307061d06030106090e040515040f0c090e030405040b190b120703050f0c0304020409080d230403 71
    0x4002c0e801400020805443d0301c1e250700c44000120180c4844081d00c4a100310680c04004089000780450360000704038541c00d0021924084181000c003501030007108602d542c483c180c142078011210b1480400c204140070141503503079840300d035009200034031065924020003030002d011032411040c090705440400c0016400c40d1184014408030b560791040d80880051000411402541d0401c500300040103a96561003500408079101d110101c00c0d4210309000321402c1c801445210b405c0200e403019113551115202550740d9509040b0b141100c0c160110640d260700794107100600030a0540ba249145c041d800d142c000507501d80c541421034012a102c446550428001804186084c0e00a41c0d00c1c102d00070418295104c5c1d0a07000f40c42d1401c16400403910f2400000c0200c000f06440002c1a8001c0c40f03401d04211074038044e040c000c02800e0080000a175440008001804c5543d294041c040c8240c20160254440003003c402c54010886407840403680c401443c030004448041c01041445541d1681e100a9241 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 787380215 1250 787378965 787378967
    0x80c010c0f020d020a15020c0a030503070f1104140403170103170a091503060602070e010b0a05030606270102070909021804080f161106030403200c09041104150312 72
    0x80c8002070700302e900c5103007405903002507074400c0d44c03100c043e06101c481d6500218130103c01a28040300c040d5280c0c05500c2120040001c1400401034841460300440c2c1c0c2103030740d91145000c0c03940005c60120b0715405850151440000c1180000c854030540c400c0e110300c1010321415010500300482440010114103041c8444d4042a07800d40103010340220608000820075102c1c4071500d10010011801e5001a607950400c008580c2d0400045000300060040140c0d99418004242e40c540705178001d9105018000020510645a94084072800b08010340b50700d810103442c24010303a104164500c218014800c04038089020000d602c1740c00710f100e0b4010640080e0184000c507032136410a000b48203459200091100d201038100b4000100a2400092500304101d96145010346081041d42c6046000340014010080000d4100780c01081e00f80005401c84940140704103010720700000c4441d80c60700141d00005000030010100d4550f00b40c00c00486062003000b0600e0350f0100c01c01014400a020350000c245190707496 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 787381465 1250 787380215 787380233
    0x314010902160213051e0c040501140d1401050405090c0901030209040201030e1f0c09050105160611040905061f122309060a061505070303020c010204030209090304030c080c010c 78
    0xd102581014420565243c000449007482c00b180c01e04c0c500d446104100e8031a14415080d80701c20030020030800e00c1e080c402028201801a4081d4a05000000c9501140000507409a42807004501414810310007425010400034000b842005c0c0168107002c081340d690000810031303250040020300012070350780c03942c0c00f008440c5802500c103030306140e40d0304414610721078280405e08620301e81140d441034140c41d10b02d484088400b8650301341e0030040842418411a0707442421104030109038200c40718010702c2410120002d1041000c0e003090710000040c00540c815040e00114401e003400c442030701142c0f913800014041c1c2c41c00101d0020000340c040550722102c5c6650f43c00301d140b041b822000c00301046940311042101140581d5440c5440e4061000c019480c1404d019000140c5003502052042e40d06c0d07180e0140a600030180c00070103242d004034501d1030b074210940c182c0d001950001e003400c0c41400e00d0402c1a45a90160005075003405240b040071400c800c0000e02c1170107902e81030b03403200b07001e80032034840f8080c1c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 787382715 1250 787381465 787381477
    0x203120114040c1103161707030c031d09010e0a0f02180f0418020d112d1002030d1d0d09061e0c020603091009060f0c0c150b032a100314010902 63
    0x140308012600110042547c003d0807010340700b0740700d10740750013480d0401401d0b000420711012882c02d140c01d031201c029200d205226044800c0c01c0842c0000b07868030705014000e02201030010314003a00c082014220841140f40f10044a00151170340380c0b035441d203d002c1c00f081e9246003c020400950700d82105005040003215a90710300e0141040720800001180054000604900d659078a12040c000d1071134a04620f05910007005000c50b8001e40c400000e5002039142c2c040c0608030552543c1d5010410402030b400d022050ba02000385003034800015175648042c2041d0074500400000030000080130f02c802d92280c3c14419202c030715441340c8045050650800203164070041c01c1d02140c3c040d55542c46a258028050103080c0f5114400c0880d99400081e142000c54807860f03801d4040000c480c180e400032402d156000803218420180110700e103050f80c4040f0349002c44800802101c1c0e4074100c1030f4a900d180c01140845d103d402203881000d10280107200310300b6101483e03000011400b6500041200b0001a401044 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 787383965 1250 787382715 787382723
    0x70905211518060126060f1801060f0f0306140c180d0501050f0103050c0a1a1e0304060c020d0f1d03070b18040c180608070203120114040c110316 64
    0x6a00c03401c08043c02c000082c1d111403282e800d40d080c01c10080a00905c43d15684d03a45000420f158500414032500c1e811010b03040c10010078003541d598400100a42195010b420320082131506a681c407031580030381448602c01a03801c14904210030348502905141140205031483c01c40d070a0101c00e543c01c01c41d00c48940c0320158030410b0103411000088081c003406d8400c02c40070301c01c80c0d03440d85141880b5041141c4281d05c28450740754040c090200ca40c0f1101e268403129840300703c03035480720005c0d8800409543c02d00004c9581c14408000c0000304003a031707000b20040c40032540c01d55814488540302510700c06410bc2d101d402103071115900c1c130704040021a80d0550000001e04882c0655503810113411070341c0c4019040800103100500581c0c0f40e0600d03014100194049260480203061313014999011b4400c20301a800030012008045a003c030b10070020754002401802901e081c81d41d482c1c001450105a0740c18581c026814040e01c6281e8a002c0c0f4a81d8214a8074007010f1490150400648080205000c034211 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 787385215 1250 787383965 787383991
    0x21507031409130501080105091c09092301030f0c0e060105031906091112010b0a08010506070f02151908040c090b060c0708030c150103051f090b0709052115 69
    0x360b680683c1c0c0030b61030080407003000001302e9040081c8014213010380d2041d007500785400340b8202c0036110340c000c1d00c1707004903400140002001a06ca84004140303a018224041035a07911100120911480c101000366840c03041e0210f0f214699a002200c403007210883c4c4040c046107007031001400740c0d6415000b0f084040550100010100c8d1646c201c0012181801c5c018000150007003a100004140701040c50302410000500750b0804007072a400500701081402010300990001c15000c041005083c62088856030080062034080382d000342d0306646800001c00711601e150320b01c003d03580d680d010717032a41030145801c036200340101030a200210010b1300c0c9060700d21340c002c0d404000f0000700c2401032021901508168000e15615404950907614080035514200345031203080e03004000041e030000b0740c0c01070f0020030011944c8082104068400034803008602801c216654010000d05075849441d1034140c5104840307210413404442070300c40c91010620703d003025a500a150321101c132000d000c4840d0380060300700555 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 787386465 1250 787385215 787385239
    0x50a030509030c190614090d020f0a0905072c030d081e2410090510140c06071209050604110d0203070f08010b100507030e0a090c020a021507031409 65
    0xf18440701c0072108000d0303c84407007a1080c07045641c806c5419407810961066142801030080000b1714208804c2c40091084c03500300c22a1000e52904020080100944c90781005541b070042c03800b800030ba521020740c9460510001240c2400750300c8400318030444202500401600c1641803064032108405409242c055112000311410900c410610038481c00c0b885d0410040c3c1d5842c001e03004c05074402441c00341c0c45410f001e0221400242d00103134035021100c0c2281d000e00c14451802003952441542c0d85115008000000c0c00e11080c1c0c40000c40e03174005c18a0b96295110041d940103180c3c111000c80138014519001000030502182c403040c01d003006034030f0081c1340410a4405600081c9018119407240b06502c200080c01c10440d03400380b08070700c0076003015039070a41c403140a600700030441d1260b00f1004050100002d006401500e0b20300303050b009860444420804ca03040c10070f02a40e02c4100c1035040384503d01e00c890400c100c0140302c00703617640903a060321010b001e040c122400c070b01c41b03400401025410100030644 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 787387715 1250 787386465 787386469
    0xf0606050f0d054c0b0f07060f0f020a0e030c06090f040b04050f0a0c0801060c0b071e05040306060b070f0b0903070807060605030f061b0f16030327050a030509030c 72
    0x480c0e03000041035200c4c22403100c1c154580c0704150711100e01c1c09042e02c03444002000202141422128840905501e150b502c42c66481c00c8030003001d220320b00c01041791608030020f03404285a4000e0102c1c0425031140304041c1182c00030155075402c0c060003180c0050050040070041d05021580810345080104080303003084162002ca001c03140708071040404609a5000d03c40494002e00c2108419100c0386855032040d814071101420340b4203200c5008101900c100000b0349020300c181c14000351009d4a45100c810a01c07185002050ba8006020648546182900010345203140c03c0c11108900e5000899202c0221180c90301907250300b000f40314102c41d0004018982c001501c2400030224a407050b41d00040081c108414140b9203403056205054a40c00107040c040009810401503070b41b04240e55082d070390307441c120301c0c082d60354000d4640110b004600d42d807102c020150035030008041d602c5601c010511485141032081940c0d8102e19000d0100d070801c1e082200840d12503402040a2030b0050116904058a800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 787388965 1250 787387715 787387771
    0x6041404061509050a08150711150c1309060302030705040e0307140604061b1d010203041d1803040609051903050609010b130b010e210706030f0606050f0d05 69
    0x10850001d03c861405001c40e00d41011400b000d02600b130020110112030285843c0c0350707070f00504100d0901641e49808290071008000c901c070406201400300c0d03040d040031800022142c022207103400007002d654401082504a0f40f01c0c1c80c04480c0c000f4005c100682c07524091000030301100070888402d00042152002050300da44025000704c24440050465140c0313401d00c94222601c10b803a28a0b1040240d08140300d040d8050a103e03100f01d8400c02d080c00c1080c00100503071840c4502c0e400400004424142c80e148051303504070301c41c03107514440404814020706000280e2a44954001c11001c0b888001040c4441e01309824028260541e40c1001c5010a40b0790b229149004000c0341c0301c034151380d1640030102840c100ba80d111038554104440078000214414006000d01103c1900b26015511107001864160703c00d503000c070081c03c0810141c0744401e40701e800081c00303812000d560003082070408000081c0d1600c600202e413113010000c02e6841c103004d03000c0101000b030310003c1d0000b011450181101c000801d640c207 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 787390215 1250 787388965 787388999
    0x17010b060a0c03080f06011e02031e09040606021207080a03020d0608010c0f08100308160204060f0e010806010b0301060c03020724090b12041205040909151a0604140406 74
    0x502c81954801c003502d0010a000002414034103149040f50a000f41660058040340c000900c0d0006202c10200e1010700328914092414811542442034500c1a09903195000800d501901038406220843c2c403078805aa840740c51602d6078222400c00c2200c98045090b1101810781034602c0e2402500e407201d18040c00c4161003040c2c00c01106c40c0d64840b505030356150080f1800103035a00d507003803644580c40c02e81400100f641d018403026060320703000200700620048495811902e9035004004014403616010415501005802401407503444000007040d400c900141d028101c07480e441c00d80340b6681c240300c01212440c002660490641c404d404001c2032001e45504200e181c0b241c1064091907101c00e04000520110a5070303c608803070300c4100441d440200808451326401038110512100d1b2400c0403000b16503522031640010300c1549816002c900300044142c11040d0302c0485241401408440300c0031808019141120b242c2c00041000100301c1d050414100070f2845c94002d0002480a81c3d506070682c40d0b10a40d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 787391465 1250 787390215 787390217
    0x30812100518150409081902030d09050705131a010c140a110a0504020f191e03060303030e0312010e060312030c04090e070305030d02090a080d21140117010b060a 71
    0x350104040703918225095000202c0481e01444107905c01d488250701031141002d941000741c200c804100c009402002210101070510004200d1000306082c9661a00140d00131248203062850100448010502507040e15064501c00e00004144841c01944c00d0129254120707900c0c5452401900d600c8814401c0c0440c603030040040d14040740c01801046026902a086988954414050311030202180020382c0c2000007030ba101070503e14400e10307080e00c3d158000350078903c40020742d5203942c00f01e580c1600314004481c0300340c40038080c1c109071036521601e900411031242c0c60030174103800400c0001c510300c10396900440007500b40c0c2c0740c10301c1080310141254011103000340510000181008661654462a0800c1e0b802c10090142941903990305922072184041095803150003040c11503d075500e54180800508040080707900688034450040e006e11588092245202c030f047c520003890035614000c0b04080e6481026002540e800d12110b4407944030b48420801e501d40d0381d4010080c058032100003e203015425 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 787392715 1250 787391465 787391509
    0x3040c1701141b03150418080a0206150f04050601030219110d0908060a200313060f020a050d181209150201200703020f0d0c050606030102040308121005 67
    0x70b80410444038160243c001010000800d1144a00103e0842540e812074061000b100e40810380300c0010b40904a10881142e00c0300041c1061350401c500e040042000c40724a40981d0707900e560301034005006114241311260803158512400c24685020b0b8041580110141001403c00030540941108035070300c40d009070007150440342e0500d8911410010a1040c070b41601c0c0c060070340c2d410000a03c2e182c3c4800380c010f214458440d06000c21543d017407105921208581d2a04580741e00e40408800d181206140c0c0956490785081260b803480221402142d042c3c80b203036110760b0300d880780e070018a038020011200ca4840c0c4c0b01c0040c0516000031910b0548100c210304680c0c501c0c081c5818140e52140360707484103100d9001d41e81b6014000c40700502968484c03e0030400050318035100c07246d07410141d040650300000c60aa6004102c1c2c8900540d4000d8041c0450500480888090742e0341d0780c1c2418200d102d14000680011014080e803052010540c82c0d0301d07440306650034040611559080030409e50090f03481030015000c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 787393965 1250 787392715 787392731
    0x5030c0a0c02130513030809280f0f03080a0f1a010e01030204050406090c02060f011508072601210209131b030b070e03010c140f04050a03050c15030c090603040c1701 73
    0x940a0249900a905000500403004038008601170f45085980318107a0509c0701070600d4140503048048038102900000b8944221245150040c00c20108032a07413511207140c440d0800c080d903224030800800207500010003551443e80c03001034401c500c004106504040d02000042060f88031802010003c003100c210200e09401401000f9003042002401000da407410702004010310700c4104642a80884036040405942e20b62020441b401d0130403104c41e000b403074141c0f01d40c801c00b417807080d941604036117001c042000f62250003c41e10807030a10121010398081032a1011907400c07070001590300446442139681020180c0000c560f803282141562007904d6401c50f08080204035074000e030381428840740c11030080101200f6420090410008070005c415401030124460f417050250604132005001e008140054040e5280392203a61b6400c0401ea41e8080d100724400c00400d0502003040d039010f940b85844407401c14801a00344252500300803c1522510001a40000c002441a940310900c0c6001800403c9441c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 787395215 1250 787393965 787393967
    0x130207050106050d0506040b18030c07030c06031a100e0901081b061606050406020d060e04060c0203040602120f04090f09300305060406050913030201060605030c0a0c0213051303 78
    0x180342d5803180d401158940c0c00000002c00c0071400035445540907040554584500d52503408087e4a01590f04d20361100142c120006400081c0c2c11080701e101cac603205188151100001c82c1510000c0404607460f01c101405882c0e1490f00301040714803e03035107240c10a6401210703c00224800020303805015584c106140c604603800004030f9401000005950b1700c0d241041c3c4414a51050740c40d02c1d009460710b82d4a1010a0402c00e15804807404880710034010310075640c070b90407103401e05403044d00e089604c075241070250801240040192001c484e080c0d00502184400801c514806074420f0011090301502040301240d43e02c00c1340309000341042e1540d40051440c0181c544034600b03546100205200400380c1d40d5800c400741301600f24012960281c64042481d40b41c40000c40c02030b064607044580e02600070000c02c25880c02560909040fa4043d0b4028020315645240079107141c030040e982d1b215600e02c1000811625405502c0705213402c2c1c4080c100b20b2610410014400803280c0a40d481c07481c2c549007080071400c0c9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 787396465 1250 787395215 787395221
    0xa140d1a151009050402090f03060a06051801081e1216020f0a05240d0509010504302010020408160509160234150f050309010b1302070501 61
    0x10342010b82e1001e0968070310a00181000b1064881e031480f450700084da980540d2680f410b041c00141d009011211941400a00d400140100340201c0d40213080a0b010403000b1000b26541504032045200540103202051700303440000f14002140310b0f40d6224940f1015802c0c00c1000051011054800400394246013910400440851034034286204d43c090030818803269503184503103030141046a001580700c07007803401302209900403000705140c041c0ca00801c002d203450f01900094415403040d07008600e0080c4001c0307040482c410707a2091210204d002404620954012940e600203a4100100c0e807014016040c461460081005500c101c00380d0041010000e1b0b030b00402c00340101c0144041240d40d13032410100030a902082c010003040001002c0ca00c142002ca00900c84100d6000c0d01d111125113400138403011a80c82802040029110b185d05400042d5081090f10070581c60000c5030350356a40c003a402d03041196503810161001075155030760718034180c4a41d1040780d1034040da03954180241c1c54850303a0910600b1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 787397715 1250 787396465 787396501
    0x91005040f140a05150f011e0509090114040602070c150804060203061c050f0609030901020307060c05040f060806091b0d0504031e1205070e0d06051f0b030a0b06090a140d1a 76
    0x7001c039071580b00941c0580e0341c0c1e000c041950340649000d410364bd07500e1003041c050144444241344500019091106001039500102150380c000c04000351541d60760550307950407030100c0d00c9000010301e0a00200700090784c550011500b103180141100b00b0040078003007428070b00e45034141c216102d0b0700400f40c4102e1940709001c020783c003040b42e5010710f0402d41032400103500c174030800100602080e6500c0d00100102e0296007680e01411a0b580440481515250090144481030307501500c14203181d0002242c501c82d19940c262100e15408e11142428403c8000c2000b1b404041d0044041c40071040446006180e8841284407640f40ea9803181d00300c0201c15200002c5440103054881007050741054400c0640b140c10b40440c005070301080000f1a41d940ca080346500c2000d400c4810903880c0304450003d180030211005d0b602851125000b0040d001c1c03824200078240c4580203680ea0040018034003086900e000340f04003410310401600300c4810388150ba444086960103c0828200c812168060207900c0540300710080e4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 787398965 1250 787397715 787397729
    0x50a0b0c100204151115092b0e0609120f0d1e0906140f0a0f031a0906060901030e03070516120c03110324091005040f140a05150f01 58
    0x110f0a410942c0e1035110f882101c0703416040c042e60a2603200214000c03c488100000d14100041c25800c001602548800e071040104420001031a81c4811242c00c00c1c0b544107142240c2c0d02c1d04c50010942c0002d0007842c2d00090b40300765004005940c44044000140100d44408680102a00c000907246d20058048108034050003000356880b050016040e801039000030030b81d9200d0400b0517071080651030046c80780c031444040d007981c0344000c40e0200c4c2c826004119802102400d40703050180c14031500001d0b08a12902c1d0140341e00c2501900825400d0070044001c1120b01010308d0013017240c56082003a9481d5a104000c1203641d0f5105018680e03050301000640005026110f50140070844107803280300041c42079010140c44004400f0813908d09582c100924a1003124402c008072950900c5e00c1143d0350007070216045020747c0500c1e010807075000d03d14400c071803095070f010f601a201540b594071403502628918029800500c0b4034805e41c000305200f082400c4041d0321088962a80740b41c00d1000000c4c075134043e0300c6a9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 787400215 1250 787398965 787398967
    0x10207020d02190f061e0315151205010b030a050912030406152402010b01021204140301090b010b1c050f1602070b130e1605071506050a0b0c1002 64
    0x60050740c070914841c0406804542080d0002915801000141500c1d0b010004020014400055054004c0e6040e5103008074080406104a00c0354800c0e0159036010740d00e004032002c902402e206c0c4804c0c2c03042c009480610391412040000f8412095411110203801c038080241000c820403002600314054070b0b03404a1042c0c080c05035840c3c06940f80f0f4041c00007620040032070743c0721000a2040715541003184018115a062103641071084d04009040c101c00b03e9241e0b00550034920044815400012a2000030f03450300907013443c1c14504210040301c000c00040c8036903d5502e6480d54408690380c0d2071414082d10441480682d2118030808070484114540c1c5034141c03003801e282c204000c190000460039405022250641c4071903242ca0710403130400720940c2121800440c0464480d00c030385000c2400f2803d54030f481c1c01003030481e242e03040202450700b05000c2d101c001400070004c3d00000703036146062220701039001102103109522000001c660014a03000b594000101041e401d101d00d000300043d00c48200e03111021 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 787401465 1250 787400215 787400227
    0xc1e0c0d0c0e130b070c050106090b0303040302040905010617070e0702010b1e01031b0f0206010b0309071a070f0812060109050f010309030e130e0610060801060e12010c200102 77
    0x285a0022070b032280754a5010b00c2d40001d05000303141891a0034580e4416140191458100406400800144029a115031a1090100b0480018428030301d000200600640c249840d581c00c00002d001006401c80e100c0d520b4020010b074086d80142c240268042d447d014003600ba09180c8003102d8000010154011681041800041925004045052040480825581d000c00f00d0010717400b0340050f68074600c1402c540c2d0800c42800c0e500c034401c116440d05a070300380c4d00baa0740d8884d5482040d020a80341e0258a801080040203c80345404802007609900c010060904069446a0740c113254080e03005d580740e5900207803c0c0e400c4900070707500d261b2040003404c00c0440d1500700b0004ca1404207100a103e818503996040361011f06d070044107040c2d00310314020900101d2101c02d0490301d000d0903c0c4880070040344292808140c40010104902c400d940c1e250b640d0700103e030318003d0304403807000114107803e4010441e1042c428030440300703001c0c88454800903110030340040e0110030f210003142040d00c5080c0c4248d105000f2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 787402715 1250 787401465 787401473
    0xc0a05061302030d0e132406092903070c051e100f050907050603060409060f020d1803050a14040305010903080609070f0c02090a2a1416030c03050c1e0c0d 68
    0x203944040d40f00510000b9074014044600c0d154018617a940c06805d4480070f500080f050341c002035031000d0300c0e16034400d12190304407625030030b20000250744ac2d4013405000b800001c0da086d1155040d508140d0007201190005109980844980611942808410341058407820360090386c60188807150400c0072001c01c49850b050010381d40300c01180c0078551041500001141c10782d52181c00800038142c0084041000d0f980e41d008900080d40086000c12a003418160703e50100c000c01031070f0034aaa41c040c2c86140c5080c0050741c04940c0c0a0901c3e5402010701c40610000c000302d042442a54101403194403001c40c6030810320200414004002c004004208000c403d5212040d80700c502007849035415540300c041500c0390300d10130b400b40110102c500c080b001c404c036621410404040780260b43d242c09488542c9449550f100000a40c811002800e04104440c00c1c1c1d0300000e031003046128001d5001e0310b4154203219032400b0680c10201058504034400401d0018110009000d02c030740307480e4040403921001002e115a41e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 787403965 1250 787402715 787402729
    0x51806040204051f0f050906220903020102210402120304180506121207120e09060d060f020c0d140a170702030705030a03020714070303140c0a05061302030d0e 70
    0x9014903111800b00750503000c82e040310000f43c4036044d244401c4980750b13085840941c180b4428a8400c05810010440e04c0c10441041000b030100051048003580e8450395140203040c2242048003159400c001020b04004190302108541448070307428036641c1001e00400c81c112111031030b2456180c000704000c11aa0008202a80c00710100c400d0106840d652400043c0c0780c0030064098800314040d10300104910351114001f08110307881400030000809081004480c002d11001989070440c0050700416030307514140840300c401d00d2048601040c18050800f184041c2d03000b050001c2400d5100d10901800541c005c400d220010301da0009050800038456401416406001c03500003500c41050080303007500e4400d000300c6443e40d41000842c0d50390100c6060041c000d6120a500703407450701e80014201008540420f80408482e01595035240342074403810040d4082d8000e03d007003a12440385c54681000581c080c0b04803440b40c0c0318800c141d00c060f19140140350801c00b0a40d281c1013040303602c8d82d220a0f1030380d0f044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 787405215 1250 787403965 787403971
    0x606010e010c06061e1701050403020c2b05060603070b0f03071110021c1b14030a06030c030f061407170a0e0102130f0b0406090512010209090405010b04051806 70
    0x407a042e541100e00c2e0400400511590b002918080c19802002d44c000011aa00b081150040054080204401c0100e00d00b2a9015500100144c1042060780740b540340481c2030900012a08440351034102c1c06010900e081d12001004860740d4101504001c0c1e07a10f02030200d00010582941040c4c41d01044040e50a40f500c4014050b40034410204240616560208401c81003550026411036442c0440e009000601010900b000f20641c103084455030103020311075071101d101c01c080c0c980140041c407034801c11006800c020b0104200f40c0d50748100001007034410090900460142946036001d044a0034510b00b920345070b8050341110360140c01400000c541c44105004501000715015241d80c49154040f0040c00402d425103d10f58004107907240c061041c100080121158202c00c01e00c2d06507603412428250190b8800c00c00441c0305180704011609000c44800c03000702d01c07400010300d440c0d56400002c0e084101a03d0030b80d0641c1d0358040b0040ca605240c81501c0d0801170452403500c2d2681c0002c41d1945d9501d0007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 787406465 1250 787405215 787405217
    0x11a01091a030a09050d020303061f2c060d050109050a050603030403110d1406070207060305310807050303011a042d051e0301150b1e12040c0509090606010e01 70
    0xe1004421380c0c4a15201540441a036108070b80c410b10084d03581c1c2041d50350703a11031201012203a814240012000402c2002602c94400900c402501e507000c089901110580011003100c0c0440b0350395402c4002d05018060200018281d4100f0600c10101e40300180700d900610b180005202042da00002a40d0440380c1c0310b4011034070030095030081001095148c20040c41044000d81c01e000500e0042078851180419508861803c0d40e1024220203036001560219113400c0011080b174110341e240c405061008540d920b0b85410146c06590380307403455002280654864002100610010200750203031110400854030071400c0c2401d0050300740c0b110300010361a00070040c29400da1442c08840d811403600030300001340401500ca800103182c3c10304481c2d100c01d071442540780c200d0445048040080342c205440c0d28035401c0f03090a00daa60709e882d001c0350f90580d001e00c00c1c0042c0503511001c00f8114180384070368030a0303200b84541072808003030011510002d002c0001c00c1d000081003002e02d99001c2040010742400f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 787407715 1250 787406465 787406467
    0x40e07030b071809051509060a260f0102031f0311010503060d230f1b01210623040e0c01141201150e0d0b040b100b0c011a01091a 57
    0x15600d042e9a80741921110700f11402600200007600348031548014071602d00e0a145190100c51300713041003060101212202c2d80103014100501691415086882e02066484624041040444020307883c04c1c851504211403603400004212198100e000b0102d008403021105c180c0b01d0303085560301180007160405860420101100183d4980d40c5d9580010ba4076402003103150740c1c05182d030307a42500a0a03014800825200d6100034904800c000034230120828003039222003036044050b0004546251151980407501565060b4424400e250362103844011724404140d0344051320812090f2042400c1d00b06410310442c540781d0b103000b40040c00708010383d1103402460401c1004044401c0c01c1140e0144100c010046840320001284200b00d9450f600c1c0403040359213456090000182c00c01c0500c002c140401010082d0031b0b80400c0020341c0700001282c101c0950041700d0405a11003240103503a4200c414080c036142c1d10780484a4a182c0c071204140350604081c6810442503040041121004009c600d14440e0480 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 787408965 1250 787407715 787407721
    0x307050d120b130501031209030f02040b041508010516050c0d0f120c05031905100308030a0209280e0603250806010f090507050306090402040c0c05070902120105040e07030b 76
    0x122640440c8461000400c83d2203080010520340c8003c14090008490f0030044000c61100c19024070446c200700e950082c50440ba1020700e0b03080c0b101074080440c8540e04286c40e030803132182105115180c60060040c0c100001407030301c4d11b188802e6983c59030448003010700c082041f48004c1b1500c0400c0003030b9100b559080c184c1d1800402c2c20222003000762091b824080616100941d9080b40d4040020b41c054160400d003400e204e4035211007a000c80c1c0b800c1d91500608070071800c0070000651500e024661040c10340368014200b0441c4804182c1e449c0c075202e08441c40a00140706036600c8400c1c038211101a022900e030700c0e600c9190141c0441d5136201103040c2c0c40c10b00d01040d01d0b8000c13860100d05242e0042c0002105a444950f59003000107150001806606180c0e0f040030001019070340300340c0a8a20a4400403c2c1c54983c0d180e40d001d000c000e110700700110040008040c1140d012407410000722006001e030080040e130343d42003201e0754038034004180c000501c43c80c180a980c20b802c1500082150a41c1c2c0c00a04a0f00661 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 787410071 1106 787408965 787408997
    0x11b14030c061005012307050a080403150c091701090c0e16030522152a11030f2a0c04060905040c1e050d0b040201030c020307050d 58
    0x201d9814048201d50b101412103041d06d46810a040c0c03070914580c40d118149401000c00341c5c0c2c0766400040c108100415a9031f480d6514100b00e10030801c008408000400c0c1940714401c0509020404007001034400e020741c803048450303034060040f019056441c00007070701c60742041740c1c4010144400502101c0b0345000c0d000f03030fa209091200000b401c07440a221600e0700b081304010269080c0041c1d00d1000d03a1240d15109071140d110040d12090103402005804071940d000480146040090707402c00f4015145e000000d4aa0000d686c644168850011480b01b8091605030803030005014060925000c011a000c1001a40608299403d004440d1180400c0c001c1d03510664004206480b00711041146500e16100840180c00c400c8110245039550000502c00032101c0ca425502464181c041c8030840d0703018412603c0500090028508100c641c0c0ca502d51241c81d10b140081c14010301e042c03114449 = true := by decide +kernel

theorem cover : BRFrame.Cov 787230215 787410071 := by
  have h0 := BRFrame.cov_init 787230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 787230215 ≤ n) (h2 : n < 787410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
