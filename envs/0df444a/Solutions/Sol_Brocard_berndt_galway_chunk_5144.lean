-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5144
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:53:39.972144+00:00
-- url     : https://prove2.me/submissions/c626d573-6b06-488d-a836-a00a42cc0357

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 925000000 ≤ n < 925179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 925001250 1250 925000000 925000003
    0x9040606030605060d0504081e2805040b09030c060418061d0609061f030e12030709150212120106030506040501061b020103140c1207050307090320031f0e 68
    0x103d10070240e000f80180503000301400a0740000f83e0092040348030341e24003540444400710946148100b003c03084004203d100320225156401d8202c1c0a0043c0c1407000355030080b200030024840c50046030186000428080c1a0352800c202c02c0ca80403400814107511036450303146092400380c1c840c4403000e5550800c000001c0400c207203840d600c40c408504000c0c02980d596202805401c1d070300500f007180c02c4485102400c810001e0101c10000da00c1c001d03030300810054003c5000a2426588200743c09514100b0010710030400e4001071000200c2c0d6519041c549204c2d081e800503030402024078408800b1800005082c0e0b45804503c892a0503030300a6101006030b038031500240411910240200004a003045840c0310640c2c50600b40c03803901c03920501d00411130020245110900d0381341501e01c00d40d900004902c0350000c415450280f5400101c0b0b03e4802c0c154a00648007d1072002103200150100b1040034444400c0e520f40e0000c030544041c040c040b15041540c0505408003c9504941802040c1c41c1403500030301e6840 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 925002500 1250 925001250 925001261
    0xb03031917042f04051f1a180a09060303050d050c07030f030b06040f15020c01081b28090906060e0109212a05040c08130501110d020904060603 63
    0x4220883c108005241e050f40b1165841e1041e1000740f03000b40100f5840b8640e03480c0a00c0f48182200d0b0000030004007451000442407895802641c0074044116000418140c440d050b28995180001050203080900f000f0510b0495150441d0030424100b040c04814190070900400c08176441d540200080c0ea1040b681c090103019261000b00015428a0910718041c0309402a06040e00002c01c601c0c505075481810a07984a115449a0301d44100c444003c44407580521513030040550a0070141810b00d4115005220b185844141e0400300f00e001c95440842d07100140707075019404440000d2513915560440203801140340d0b01c61030382c10030f007002c0c004102c091007801d0f1030420b2030040c1c44070740045e0b090040c1c0202e907180d06900d00d00c101d00191000800301d014280c02c054030921032496550240c035051159420540181c11448c0100d00b000e0008210950024149030711420486001d58503480346e260160141801c1e10540150100108503028000c400340e004008041080310100314203a5a908283d05031403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 925003750 1250 925002500 925002503
    0x7080c0102220302091b040914040501050c070b011a07080d091103010e1b040b040219030f0b0a1403010e0d0e0109080105070e010f03180308010e0a1a12010b0303191704 74
    0x4100004a82c400641901000e050b10f86c1d0074006041c103072181110300c201c900284d05041549506006d0006100c8288643c6070000240300e0340724581541520381d50314641d4180304419110040c40f14541d1243c0e91101500d901c3d0b80d00a003280e03030b52580e01020f44050018608151060f4001d080354840e10b241c14440c24031340d00484405001424038109c0d40c4520100840b40281e0000d468541d510020ba489100810204421a0b0b680700200c49a81000302259a40411307850703920702d40060412a56101d62000702220704401611100341c100c0c00119026202c400e00e04c1c040c41c0304641b0b014420642005000010381c00030780e00c8000c041d03a2203d6403405e0312426200d46010440d4022101d40030352244111200c5001142008202c40d4000e03c496640d8500c2c2c1c1400768000740003003006000d1307945501c04a0340c20030703810b4000303101000b10183c10314a00441d620342984610000580c4510740758082d0081d07082e81c4401001d41c6d0f120102940380c080e1004a0000079000941c07141c130300031a003501e1400c00c1c03800384e0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 925005000 1250 925003750 925003759
    0x61804020f040e0a02030f160618090b04020c0a030f0212092112160c080a15150803030906090c180703020304060f0c0f12110f07060207080c0102220302 67
    0x5880c03800c10b01000340034100c00740310b841c011801e03101c4c0940c408000b40d55180764200e005254907032040188010050301078005508101d01d0100064042d5015400b0005550b103000000890204103c0041d0091084070f214000c1c0c0d0040400c10340030302d40c0200340c00f03910744010380a607100180300c50900241d61041c0b1207003562080b4208030440c152820741c0b08040803030f0356020845100070b50305460300074107400c4021000100f054890164040080e46181c130317001452002c00418048030b942c1c1d210180b041241c02c1081c191565419900d68030000e05403414000d02d000000e8981d40e00b0010b10304c0c0d80340c80c1d0440300c0300305902c0f44840080d00d50904034100b150844000008042a44070060304034040d62021300305491240e15680400030401082c0710b11806480c0f0340c1c0300d161504094410144c80e9400392000d004105180c560f05958188000d022210040100304295669544e1803500384024010a1400340c0300c42e902055510b981c80c415070040c00b1580f041103000d034207480c4000036080d11f0900b502000b50030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 925006250 1250 925005000 925005019
    0x12080f0307022a0f090115080c0f270f060307210c020a2f0f030307120908101107020103020d060510050406090f06090e0901022106180402 61
    0x442104405150851110310503120b080d00c82c05440c84078a1072020440c9038902d940440214107252611a41074904404d540c55141c0e5851320b0010400d8035a40e04014080c0304203200040e408101c0f403001c403083d85c40c41c03a10f01d685901d210881c9104203400c6415000807117490650040c1a17142c40034a01c05506401480756240d681d4400c1c00710380070900e00800c100603190707003070491140c0324460003100d080c60480d600400310540d480c2451649080d01042d008100b000c000000303124540c08400c00820190244d429090345221034012074070b1881101800b07000401e806032404d85180e070050001044515040844016200350340c4074104594051119035842c0700304004013001940030b500640740818414000080d00790f550030100703481100405401d4005540010103000660308245110003170120803c42820031382c181100034100c00054001d001268201000151410100750115551100ca0042e1003c80c180300c1c16000f503040c030742500c2c520702c112210030813922941d8500092901c01e0782c004006012 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 925007500 1250 925006250 925006267
    0x30b1e01290f0702090a050708061225030c06020a170a05071104090b0c09040f05130f0c0b07030c0b09031314030309030f060103060e0a120e27040c1208 67
    0xc0a5010815a5408003401c0c06014007680c0d8561000f1b01c2500f5032180821140340c5810b00a0000000030003580c880c503485207580001c03003400901e0011000c5a245041c642c240c0c86031000c0700300d0401d0b074002001e000d600c0202064055000c07509860f04c03481203031036090795148000220b207540986661b02000076024000500810382d40d081c072540c100c4000d040010050700c152030740c455000381252006000c2d040001c038000d490030944140406103440040401250070401c0c0c0303544c0440d60700040545400804100d490600200f0704288004004410056907200c40924018102507100c500c1551040d02c800001181c1d0680841241c0002d0742c81004403860b94180b0700845c0419107840c050355050b10091107010b581b03441c2004140041e284a10041c98958514601441500c000030401d0300541c1080360044005541003804c40098449400c000aa900c00304006c2000d2300101b00b20034450402e118240d4440c00480b801140c06540524400141540c8078080c079181c0c00f245907402406118100000e18 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 925008750 1250 925007500 925007579
    0x1090522021303120309021e0303030112020109080601060806031203060607030c150914120a140702150f070b010f0f0e1504050108061014091f030b1e01 67
    0x1d00020b40c0403042c1011030722615800401240034010401007035442c143ea13002e5241c4401950f6044014442ca101c0407400d041c0170907100d00040c800c09195222000b51101168001d250315005040342004440c05583d44ea5402450540150740a0780a070180507182944140c40008484c89003e000c0c002501c1c0000980d0201c0b40c4508054056400c0d0304280d4280941c201507020b0080700780d00035240b5501825900c0c10041c2131244412044050300c004000c600611600240e1a460100741030f1500c0391140040c0c00400d81d01c002030b825800072104000f45041c2502100b4010b07181c1507000340511034441ea203a00d40710349400d456008810307042c100143c01b005003403a9030b40d800c1d41c040003158032520324407c004c1c04541507400c280c0107402c80745c0000c0b080000c2c4010a05803003008140294000b100d00484001150403620050700a2070105060b40c80054405148101c1000460b40104a400075143c4440d412010880100e4a9202c81c041c00c000003c3c1242070b12520480d940200b4880c440c803003654605403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 925010000 1250 925008750 925008757
    0xc021806011403010f1809020a030201140906030f0901050709050102070504020a0212070321020f03060904030e0d08030a0c230a02190b060f22020c0c0a090b0109052202 74
    0x100e0400c041c0742c01001100c030840001c1c0d03009143c50220625100c0c2440301440c040380202244a014516155100c40960390b8440160112502800c2002c41040c803070306201d585118059141d500540b000007801080010406494407450300b80c002008292600701044807840240d102d114010390010a041c03240b85042d84c010003002032240116029054040ca00741030b0340c2c10110301500031656040d8200e000540502200780e010b003440c0d031f0446c40c20001120040d110b01010304a10300450500700050f0030907010742d03040e44100c50001c0080510801c9443e200034141e1080b82c1c008511801c09481010703140c0690303092a0403144012141d600506811189a0281c010305e10007402c5100b9004550401100c409031403908501401e0885000d01c0d0070740600400b1201303014820301812142e204d0760b001051622080101c3c0e200c980025135112580600c0901e04091506810f82c01642c2e8800001e02e008150300a06035040e007a01c0da085a02d07030702c07010041515540c0d910420f1400b8490078a100840c0141e005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 925011250 1250 925010000 925010011
    0xd0e040207121d1f09081207060c050d020304060515010c080d09062a0306170d0c03020705060d06210519030c06090305090a090204081218032a010c0218 67
    0x910700001003007002401c51014409150709088004e04400d984940c1300020001401000004114030310140080c0040c2e4450760034050555603841003000c00c0c40f441201120701c0f5043e104403e41d103d040c40d017440002410281e072802d1001d4100c810815155000754103074030000350414901420a47c5001e1508003909150340100d607042c0c0c1d00c10801c090820900340e40c00558850360300d00702c00d000300d8120203022110b071500039625800311100c801030700280018074200400442d140010101419180503803614001c0c1e0007065000713501040440743d1140f2a03008404a2b00308059583d01c4912300714554400c040007001c00b801e140c10845100283d5201d840d10222514401c0c584811030080581b660780484200213400c0340014030015020000c0e1402d82c0fa520040c02c91608110700e400d00d0405a255948030707141a2440072017000c00d852001102030000b212138140c02a095a0420781c80e80b00000655150707036086803003400110300110b0139501c6055160b49043c2c0c00b80c03d888100c00908000e0307100180c020b11 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 925012500 1250 925011250 925011287
    0x1b0303070803190c02030c0c0d15020a140c0f0606040c050301120f0506070c05160f061209060617061f060e041d010e0d053f010303020d0e04020712 65
    0xc400b9071045284c8100c00d20004c09034041c6480c2d41510300b8480c10041140851486112448a404040b80350828484100d03041001c0050340c0310000795082d650700c03541c2500204107a4010624400c03020300403584480c10030381b04040c1d80c100c0d03a40c94200000c80311080c2c80140040c00a1006020315600811710040140c0160f00d0f50107201840c2d55a140380c440d003211602d00060952905500b04407040040f44202100000c060710828206100021110755034840d000821140030010183c1c0300d40c0d50701c1041c141d50000c1052044544a50704440080506100c0201030703c0b03500c0c002620380c051181c6000f1074110750304140c0205450108200e49800d034011a0781d07881a910302a072450030120030400141015280000714014119414072130a10198289900620008201c0c035000300a0504a001d5a034000d8140e6540c46203101000f19484c0031003100d80c0003d40400ca00102c203168000540440c0400c181d940c40c500c00d22180b05020903030082050051001c0b030014000300401c0c0c013418030f060080240e2003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 925013750 1250 925012500 925012531
    0x12a05120103061a09160e0d02090408071407060c020d1106191407031b1403040f050301050a0c080406090213020409061a041a0f071208091b0303070803 67
    0x80800680c6000703a004039035080ea690001102000c004580e5610020122014807251500b0051030000c11103507031001003045001d0b1a0441d003641c42403a600c4540e600a07000a049141614004401d41c0c40f401d001e460600800c41c00301035403080012030009489481c1d4038903580a40c0c0f41d0900802e03644401007151640540c802013117440c0ca90001600d924844089800e2070040030882c0503120b100a601031303200318081000b000d004290410010460110b14a00c805100c0351036040282035003084221820181c000020b00003004000480c0340416944214020491500e80304036940455440581e124003007203480c00001c020401c00c0e4031244800380080c00040705414a40c1131301c0100d0744690085607005a0b6201c06100e042c40c9080514919000c1002c1c2c0f0f80b606003080d05040c41d000e03c42421500076400010b0f603001040103401075a20082d8003443c03500c045412401c000e403800701c0440700c40e1280c4c0300d004858521950807200002e44408040c0c091450700314991034010301d6900050a113183d0b03a1584 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 925015000 1250 925013750 925013767
    0x30f061112160311091810081c080606030420010c020303130905310501090605180c03150619080a0308060a0f15050a020f071511012a05 60
    0x1d5182a00c00c544205405103041e4503128054101d485020703046040d28824001e0381d5481d1150086010fa203035202c0480e49459984201e55440d00070740c0d0f0041001e0b4052190617901c0940311000e000a9940c05840d100c1103540d8820070300503603000c00c41d00903003a400001c0c0744003844040c610a6109158042c94544503803044c2c0e07000300345554081c5008400f1000107a10400c50b080d400d2040707540142182c9220880450440b5180301e010961141c0e03172400811140140c02004000d610003000d0681c401c005004a00d89040500d07040c07101c0d070048a69034000c100414145140204e16520b02c0300c041c12140c1c0054580744280a05080c805916000921101e400410703448010490400f0303252007955400d2440c5481c10a0080700341141e4400690280504000d000191403015070821000451038115160001c03654100d182c801c02c0640846c540c01001d001149294880152401c05a00c540792402010030421120f8200c4495100051b2500070f40c0c5840d1050040714140080580200d24255051180c0e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 925016250 1250 925015000 925015027
    0x30c030c021807120f021c0b0d0605010f05040507031509051905010306020a020d020a05060c0f19080f160c0b0402010306150801060f030905030a0e03010609110c0705030601030f0611 80
    0x20b543d610042002c4041d0248011079a025031428120381a40c19428400c0c40141018158188088400140d49803003000e005038585015800034160071000a00c4196910b010580c0c101100b8000e1600a500b820000744005009000700900380601c000d400503400c3c6001031a07130080c80050722015030140e0b0b000c42c3c10203500e900d000c2d250103580240380040c1d0741d010700e15010340b40881c60003813607096400c460841004030308080381e015403185420f00d0031582e03030000442d0f5140c1b03072007141204801700e40c1d501440c2c054a0717408801d1520500800034600d01039251041001407180303000041c1400210840340c0400080c1098828940007441030501150480e00d500142800100d136824080002c1d66410040004d00e600102a02c50007515043c1006102c03840e03110b0640b20b100f01030310300081c41a24448042d0b00c2d1025405034004040c0090b04104048600354209625400842050202e01c14010080750030711780400c0b0301f4100c2e58007440320616214a503450701e014040000002039544018460114030105 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 925017500 1250 925016250 925016299
    0xb06090c04092903060609010902030726060102010605060f0405010c05030c010230010f05040207051608100e0f0d0c1a180f01050f070c0507030c03060203010503120304030c030c02 79
    0xd003d00002c0c02c0d030480340c2070445402041a601c0c845d6002000b40070858550813050740c1940c45103080542d41c1c1d52642d1040d550301660420321901c0102c460150b032964561190154040c0400341d0090200c5541c4a0400c100c03406160101c004a12040008214a60040c4d0282452a1050b010b480c102030b4201c0125007242c12400c4800003243d80d0312070b84490002480d58001c200f200702c5240311065410081000040700311809014000d907030000b0120203120003040355103400c90050f1441881d86413501c100c26102e28035031034252050303801c01e0121040101d001c6442c800c1880e600009000520700ca0300c0488000c00072041c1915000340141001964843d91407803644101c0da90089401e450034110358281c5040c20394400721580703900d00410f000b4039070018800395400c90316a180000880b0700a040850030248954030080596800110000c20001280c0146041358400c070182c0303140e410b03040320ba00003610040350010006280b001001c8000b0b4000c0710841c100b180054080600c0340c40300c00c00400c0c400f0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 925018750 1250 925017500 925017521
    0x30905011d060708070b09010203040b0a09140f011a1203090d17040e010509070f0c0b070314250804030f1d03010e0f1b0102030306100e03060c0706060608040b06090c0409 75
    0x9000150f90046c03081756100d043c0c102030350030000c51851506440710001604041d059003041501c444690091003400882c400354140207074282c62254071311002c0103000700351102441e00f4541d41c03810b05010600d40703001503585010f1300e80e01441c581111081000b42c0b081030b0201c115400c0b2413640e2007940020050000d00041e1462583e18132039541018204a4604002882c1004000c03a21105003c0d070356010b40e0f0080d80980c0310039040c02540b200182640508045840c400380740c5510800c00c02004400c03134640b200110a404c48a400000e6003008070f42c00c01c400c440140104050460704100d9921400061040c901003108512000c02c1c0d1500103801d451a207503104e03040e5402401124039010043c05440c0004c42d18094002c940c81013140040c0d07d90000500c0e1720b21412280c3c2c840e9100901074200505e440c00c008003a241c8900c1c268a021480c0e41010401340c03031040c074245003c24950301541da85400340d50000da009401d9550a030421550700f038001d04406030407400344000100d801d03083c0a4854241c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 925020000 1250 925018750 925018763
    0x11151c09080c0325050c010327050601140a0303020303070c0204150305061504060f1a130308031f0f03020f0f04050a0605041103010b090d05010e12041809030905011d0607 75
    0x910140583d0f200c400c81c84c2c1521340d0328102d440ca50f100011400100540321007002c0c280802c403d201420700400181c80c01e0400c3e04010000c101c0c883c1044004140c0d03e040e40d1001e03042011010485041c0040034501d070000034096441040484c0031980100340d80e40301316100a2005c90109801100268510030341d500c1103d80e64040c4c0140103881c05901160802d076403003a2803c010b00b5103040c00d00c12560500e449070312442020070f640c01c00d04104001c115429503909a886c92402c540c0c91400d00600d5104546030a201814500d210070300d85010820700007210f80e00009407100ca07042d5000c102202c0034007155150b22000c045102c00d6242c460307004182c400d010142e0001222850300c01880103480e160100512010800c00050109a84c00000d486c0f4075402961002444143d6141c094010000c1d2101210184070344c21842c98054180030062042e20500d000c10400c0c2d503410003001081c4c0c0c440583c02000b24140c10b0041c070007035114099000d00303044445118090032040501280a940c0003400c107a40d00c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 925021250 1250 925020000 925020007
    0x1503030d06051309110409020d0b07020d080723090303190801050f2d06040b0f09010f110a080a051b030c0c090103030c021509040e070311151c09080c03 67
    0x1075142c1800850310f24401c910042c0145502580d80004800b41c070320503107224540c1c4d803600c0000d54031030000204040b98454160b0260b82440c1201a41e690b88078800c41c40050803090006402500c9a1031a03810342442c00000c5501ca611403103501c1c02a00704900068241c0700500034540c2818a070260340c100d000c141c0d1148070300c5505080911110b501203030340c201d000340c50b030b070000d0b186400ba01c14171221140c441c3d1886002002a00000480c07501c81e6a1102e04040e0002c00c0101305049070000a0181950913204e0900d00b000414040d41c40482004081c01c080d0002560540460300450042c840b1800d1441e00c1468420b800c4146030713100fa00c1c480036201035803001c514082c0041e810450360032020400c903100c401d15031450b0740080c0a4841d450000b402910404c004e0b146d070310300340e1054031071460f4010001d0080a03203c5104d40e90f6507100d0320007651a00b000084000c91420404255107143c00c890841a203070913034022203003009010701d405a0f0f01ca942d42d9100a40860400e202800141440101940c1d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 925022500 1250 925021250 925021259
    0x50f0c010f0c1b08091c0b0405030d0b041109130f15080f06090d050a05070605011805180c1912050a0c0f05010e1e040e010c02100b060a081503030d06 66
    0x8000026840e5041a94000f1940d0080f07286801520080384007161110114510b000b1001c4d5a000d4001d4014000b4410405203c104580440a8580d050750064200001c1c1d400008201c1560640442c0d00c512510812084099092a454078110400f11102c0400c0220040c58440101d40f500740c00300c03410301001e44050100314400d010040c00348800740020195418200f0781540c9401030000344d0400e20400003254407805009201752821795801040801166075101d400e030000e002041c5100040a16060001e441040158103440060f0007110003804241510400d21624000d00580402c0c0d61000400020340c00c15040f4405c5603080c45080a858081418a40344640085d2900b100f408030501350824000c0707990150010f14030000403682075580c4a49022000d006140204040340c005003408408024200150007554400c0d4580d82110040040880c10f0303412208076044469000f4806c20446207001d10443c5403e800081582c81402e02900c002c0c002450365201d21550040e0f1901d8840800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 925023750 1250 925022500 925022507
    0x32c0a1203030f020a0806101e0f020114040c1e050a090b031b031005040602160804140109050d02150c0f1501080a2109120c08060c040e0601050f0c010f0c 68
    0x3d0500203886025800d1601c0c075280944000001404ca50050b040a000d940406200d41601d055207090103094141410303c228004040c4e800781e0a4032130156007801c01c41d0b925070b8000350791184582e07001302001545604140000704d148045841e240180107032610f01182550b1990a00001043d14807070005080d1403650a15060044180c1c80300d0010325111048180d03034901003210350741c1000303070f02001070103a07100d00d86840207025800515103001109080ca9003088060b00c014001e444285500d47d000d850001c0045030300001500039660042a0162a100142896002070300c0e494268132100c0d00f41100c42c0280d0b4685508210130452591021250310303042d00484003403034050112240a01503240b6592118095400c06c290300f40b0004180300c81405500c0d1280445401500f4100e14000b281e10460500e400b4a01490003004d205008010110b0229108042103070112040842e8a0545a03101d10056903550480720f51008141c0080280c401d5052007841401141a10b4140c009841e150406004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 925025000 1250 925023750 925023761
    0x609070e060d0c121415100b1c0c030b102d0f0f02120703030603050c101e050d0516090608090304090908090306090d030e0703032c0a120303 62
    0x340d0240c2c1207990400045810076000c1402e440c0074070b400010f03040080c6000e40810300c00040400c2d0b90301a003000e0081c51041c4407001400360b0f806081c003032041c0e6200c08240620b403007071a84003072402c111034009411000d1281c00148007a03109003000105403651308c006c40c000342d154665410000e05004442168000c180c200c0c0000c110184610f603c2140c220b440c040d0034050003e240d401401540d42c0c000341d10740d00c00c00030316250201046219440d03100070302d00a4040c1c00540021201c9010300000b0041c00d0420114400c004441c036035451324607091340400d00703141c4640c04040301e0030440200400784100115000d01b80c06040e00950744e510030f80034410014074513121600480104090242403159420000081c0d41c00e58495010010703000fa550314090349030703100d020f40c01505805801d042155121011030200100c840310b840074010601280b07807003610340c403890000601140840d000c50070500b4004810350310000700000d0705000a0240070005070881c04c0e9611250f800840404500c0c2011340c1400740 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 925026250 1250 925025000 925025011
    0x603190213091406090d1e0804020a05130e010501090507210b03030403030e1008250504120b04140a0209162708120910030207290709122307080609070e 67
    0x1c10320704400780c0e10b4082c10f00218041d5004201d801001309e01503684442c2450001d10005101188000800c5100805041c0f507022101681d40b03004d00014950030039000d09807140d405591104580c42001c09080000c0000041d000c01795a51903520f0b0801d61070400040000e94041d8403040586104901003040c032041e01e040110800c00050148003c03520036030103400b0340c2d6400441c0c5580003403410404417120f0182c0d0b1b00007031b00386440f01e400c1c000b4485580c400c03500036070050808020406804220580c1c0b034120100003500b00019400081d030000c0350480d80d850710700881ca00a080f0f200c03105044110101c0020301e1010010303a140040048090801454080a100e40758031820441c01c1c0c00092078a1042c41600e01c1032640010b9044100700c8005881000d20400500a20740c00546d04c081c02c03e8110201c1e20240480d041d10b0010546a03d0b104540f000c050740010304900fa05820100e05d940c0c1035072001f1043c190b104600e80403964510038030102c0d11980720040184070080c90000c4520340984041c0c079 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 925027500 1250 925026250 925026257
    0x50405060a0e0c0f100c170903070f060509090612160609050a0620160b0304060b0d05060a200a02011401050d170a120501090902090603190213091406090d 68
    0xf504030054a98819a0b0400c513411141e4140810740d0800641307030520b00f9103000f0000710185005103c5150503201401e0281416401c440340d0a8071942c10440c0c0f105240200070201d4014000044680703441380d4a603901c044094100d1040c000100ca00c1881e0601015008218201040e814080a40e011483c5801804201c130741200091510502824005404c1880c4640700801030702d401002500700003401025204041c4000c281d0360b03070b1520034000c1d0015a022151281401401440380c036208030030040c1c440c2c100e00500f44c1611050f4a9034001c0208080300001d005400e10b641820030403040240007409115000850b010790521820b42103800160007580c4242c40303100d402700c0032401400c42100790007007940c0300542d202600b0700c0695064600840b01d06030b15003000c0004c50600309030307041414141c3c42540c090b01561200400c058840c0718181c1011200d07107800403140701525016000d40100e424502002034003061648541182c000111300605065100c02c09010b140c520411513406541d05915 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 925028750 1250 925027500 925027513
    0x1150801141f0303121506180e060109170c100201090302070518040311011107060b01120b03030a140f1201050a08120301150201020c060a06050111031e030415050405060a0e 76
    0x100b09003142600d400080c00308101c2080311440038501e41d02882c1424074100c1c1d0007030400c0d0f4440000304105c40c0300031a1500400488000100d8411181001c0e020f100146c44040c0c001e4102003405600b403040101d12040751040c56410015529100030f2410201070540c004502c0545a00740a850001d041d405a404bc03400303900c0d4244060340c040d442d10b400c01e0f41441c0c03602c000880c924500f405031123842c8070520281d100051150801c40d495100c25104c00c000c0c1c0380c1c0400700b41c0884140741100c0010010640641003000070045842c0f10340c0400071003400c41c4000c1d50078441d00c01a8540980c000c2083c050364801140b005015915201c1e42450041800000818828440d80c40781d05030703400188980715049219068038030000d0700070340654401c26000e1088401d54034000b1004000f5150078419240810380100c1c440d10701d00c101004503842240c00140510868003003d551714002d6000900035030ba149824200c45d2202e596034000c00b03000f1806100100f4460411019030001c40e10a045002200d03880360 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 925030000 1250 925028750 925028791
    0x150105060901030b030a0507060207150f14130e040506180607020d0e010e1002060a0b0f010804020607060b060a02030d1a0f121204061d030705031506030115080114 72
    0x31000c46485810078640070980c002c5640120b840c02e9000c0d030700282180a030090101d902640040d044044581324a0011107101e05070398282d03135420400b01d0190000d0a2030544100d0b9030040300080c40344110206003024000e070342d2141090075250580301201c003030b0400d1045c072210310140c020740d04913604520050141418030f41406035032182480500800e0000d21079051507582c1c019070b107016400380e01400c3d4592100300c0c0384000752605030803240011401d203003064154060074510003402202c94181c451880c0360701d9640810055402c400c8045840a8440c102c0c40b80940340e0001411441c01d00da0000c40c0c4070904042884103a42001d00000c0d4000c1085403418000e544a004501c0d065000380d84041d5000c1000c80c001c1e0600c0301c2c40c04ca892a0400c0003030300182d07103036009001011143c018600d80d180d5265070420103882d07807038500c102075150740002d0345940321300031504c015600043c008000052038503014a81c01c075907054961284089940d20100c8a15243d1803202c0ba90b408241101000d81d02101e1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 925031250 1250 925030000 925030009
    0x25140c0d0f080409020d1d0303010501120b03011b0504030b0a0203040809011d1207050a1a03180304030215210708150402070209180708010c0903032717150105 70
    0x4900040c111040744000c81c41400501c5040b00c0103001481d40555075002d20a95042c0603108020004a10300303040d2200100005011050f01c0c16640d05a40302c0312114220300b07081e0060601000110703410755845441c00420652200e080c0b241070b00f15103d00791a0b6245082502204000800303802042d4010000c000020318a40b0440710f11110900304991710351010b821010540300c0d41e6600726005510340b50a09d180c941d0003d84201198000c6039610581507d407115880c035000221080c01911400f800440c40054001c0d0f031042e103a119003400c81c0c1c00c141d0b813070700011340c10345842e0b10750481c4880000d00025245a6082c4866813000017041500702030400349c00c000c0610800401002d00d0130030740c2c03000d140799030350741d4048bd42d00d140c0040c820040b03410088010407044840300d603020740034401c101c0001400401806003081c40c071010784890401d05d18540301540c000403404420390043c8102e86200c0c030b0003601c1081c1c40014243e1701c1a41c45c083d41308001007519100f4981c281400c1c505178800104800e944 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 925032500 1250 925031250 925031269
    0xd0c08060a02190c050c0a08030d0b040908070f02120114190207030f031e020706060510020a0b0f06060408010f0615020102092b0c080a020906101e0525140c 69
    0x21a458408120704042c2041d901b840303140e8180d180c0c04410340784002410305c0000013511881c181d080e410000440c0c60020041141c01c010701c020a4140b0030310520020891015103120701d140090080e0264000054015084414a07a1400c0d4481482010f0040030780c83c9111100035101c182804611389103564801503c94207018100314105600c0350340000c4c0510100d692801c1c4202b20040564650350285407490103807031103004e840e01070102d6820b0400498400215541c000340c03c42910003058644201d1103040e00401058142c008400b0000068207500920840385001340201d80050800d043c1641c0b14a080c10490032101107a00600c0748140d0ba5444c0d10421152028a0b0309181e46502c1d80c1c8651b888651414901400361064004005882c03a00880c2200a045c0b0072214240c16596900c2000401e0990802000002c0d5403200380a1203460903040180d00ca22550410318100500d20b0b8444c1c9442d00b00480c80d0f04241d07100b00307e0300100301d0041030800f45d00340548040c010540518020828079207 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 925033750 1250 925032500 925032547
    0x712110d090605031816080102210c07030503070507020604060305061801140f0409020d03050301060810030c06081f060216090501053a0b150d05100207110d0c08060a02 74
    0x18040c40c0400a03000c0100311306d940d00109500c0307451102c0d030b0b1034640f14000d401c44504a4061190607000b461080300e0030308594400c05105090509040c5d290714100c41907003004054030103021080000c440941d40e00006000200701c9079030082a24509401031100700c0303072440003c410214a050060082036800039200d0003000c0c00f0b482090002404400040240c44c4010000c0d401010b0706001205055011307008605856441d01c2c0ca40807901d074400703217800320382691202600002580f8014840c00d40306110203a0410001e0f585540c1c0d4a0a41d580021840c44652058000d80c4c44628400101c0c6d8040a080f4003c1a40b12010407442d13140034041290100d0007812a100401c0c45100f1840c04070701080001c18003d07108a0180c0850302c40c0c074203182c1d006000d580604040ca80c005c08040c85291a4010004050340000980100004041c6100103908120011110302d07142c00c0b14007440d07032510090100d81070b000342c840d11107403840c01c0300c03031030511101401000d109801004224110085a8000241403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 925035000 1250 925033750 925033771
    0x100c0305190e0409210c0206040302060706230601110601120f0201050f040603050a0f230603010b0409120f1b0b0c0c06130b1f030204110712110d09060503 68
    0x40061507003190409001c918090740b2070324105880b4180050010740f2110380034110421308002506000981d100304413404003c0d407000c070800040c00182800030142c205140301e0310340810030001d450303010a0766010320055210201140010001c41e5030780038524540c40c04401025140710350400710020703030f80b8102c4c06000d840398488e04447c0c401c59100e0421107800c050400002d50712542c0f10180180540826140c000b410303400d00c15840985840c0f84180c044407841c21517080824008180454034000005140e194555030301c521145494175180200d0302ca0320301c2100f1409811540c5132010302400c0742c0d498800b040081c0034a00c0c8082640309220110941d801101d0944640d071341884118991040c06c00f820b4240c042c00c42800344806903411401c3c8050300c12001281141d81d400070300b00340c80b1080700011402a1704c403002080541003a27809031000c07071001c154040c50f10a0640301c0030207005403944030f81d00050352810040c0840b2802c1c01074810900442c640701002c42c0c90940003c04600001e007090107078 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 925036250 1250 925035000 925035037
    0x90204030213021e040807051f050d05060121090213020301060f03020f0d0e030c1e030a1103070203120c060108010b090a020c070302030f0304080f03090a061101090818100c0305 78
    0x3200044d10010701d400702c1500554941e150720303844d5101e1a15100d62400381c000640390404501c4840c0c86045550040e555050501c1401c00740c04d405410050903031f030f050103c018100441d04503083c40401014104007404101c1100501c188020100a486400846441400140002507200041c0e80716200685405030311000c0540c0d50441074451000c1c90008680385c03084000c03890303401101402c08000143c080d240481082c02d6009030404810900e02900d41041194420031801070140014404c0030b04c080b01e0920089030b010914100c1e261a090551500105000c1016141081a0f901410350040280560300b9424042201940c018140d10300341e6802140f1188486010003400000750b0700101240d1003800c0b035410168403039000e07005801c0c50b8002c10b26050004040041110100c550103070203010114600141160f8084440006038060754890704d07498003140d181000351030794101a000c401c116003500c40801504d08188000c800c24401c00345a10000b1070b4010381a02d60700c8075103541c51000f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 925037500 1250 925036250 925036267
    0x200304051804111f030f150b0d06150903020a0609030809090a0f2909010b030a050403020708070602010b01110a020f0906030111160204051f140a030203012409020403021302 76
    0x3c00c0507507400d04036000340c01d05900d140110304c00c0840b052441410303202002100c1401802000351003600354a42d1180100000404c480ea80340001414200c61030080000e095450b140c0c0078203401038a40c8014009514494184294904280030b0f034000d20b01414820500f40c0742d0356a0365514052040c0d0180700c3c4c104000007138071009558200b00284070849504000980c100e01d558080c0300d5100c07090440c05081d160340c41c0d919040090405059842940000d0b08550381c484159004d401d00134011170860140766030019100c5810448500030742030b03e800201c0c145c24414001440030a055124011075801b28000318096204ca41540717032815400d4034080700654811011070b0140c80812006011480001013100c1d02002094038522050300c2140c0c14025620303080c010004070344a800e44118036401500703040140c03000d800c1d0784656150b00980400106640c07a0002400c40e42e00101e403411031b94841e600344500541c00301040d805403640344411800c0c6819500410754018152144010140d8001801d44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 925038750 1250 925037500 925037513
    0x1502120a0c0807030207180b03060406091a010f0302100318060f02160803040b101a0309150f04050609010c0e011b1407210f020409020a0305010c200304051804 70
    0x1080c1d6000041265142c000b407a0095640761030784215803010104902e006400f052500580d8001c81b0020003c12141d02c448d11007200403c464102100c0d03a401644c85003c40c140e9920a15008101c3e241c0740220051850041c81100c1101d858a03404140c40d004032400e0410482c422241e103590860380c00281c18030b00341141d000a00c00c282c230000c50f0302948640c1c8030800c62284015403146200d40452800d5442d105482c014103506401400e22064010740304010305920580990f82c030000a10443d00042100c61140a101c007041d03c0001912441800308000e11034100a46a0040a4030008001c542c0e403444c80202100a807050142c1003081d44000d0381c80143c1200101c84603180c000e050b40c03d60f002001c00641d030b030f02150b200d12001c16811900d001d002508102c1c50450041c1c002da41c0c8080c4c80025400c00c002868a10300403a804107100303070007202050007482109002c000c140c0300c1000c410000c42c0756a50b2f401549805810310b900801051181d91a8810b21914040c1c299840900c607840c0c41c903040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 925040000 1250 925038750 925038767
    0xc0a140d060b040b0702180609071d0a03140d0e0f0103090507080709020a0807020c2101021207051e0f1210080f010b010905061317030d060306090b011502120a 70
    0x840100c2c0c0402c0114000b001c4200400707150380300f2035004102c18000ca41c1954601c800b103c4d01603004003940d0008280c2c40c00391341096180c5241030440c0000ea06804006050600c546c0c1094070044092691107080c01410040c2180801c01405c00c4ca21100503170000802c0e451000744254101910307a07011174204002044000041c1821500350b80b041d60b25803048c1c1d80203400001c1d1400004024034081494039001140c45941c191018140b605169000086080c00140b0050641c050f903500704a80c58118000c18144c0d8020080369441664510000030081c0b200c6000c1c032840c8180c8503040000c3c1c82440030f01411605014001c402c4c0b500560345102100420700071a170b201d00518007900a01d0104054190711500c1d107041d0988544a150b80c941c1c050201d0703030040c0d0380c41c01f2150503000030500441401990240c80c42020344116843c2010401c004007c1d5a440c0d40125000c5803600d038100100001c41e0300150141c05420504c080701000c40307034001c1d513444041c48031444e1910002104141035100b682c08 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 925041250 1250 925040000 925040009
    0xe0a050d0b07030c051206060918130b07210c1809020a020601091b031a0d1b090b0102030307030c020a0204110307032711120a03080406050c0a140d06 66
    0x31a40150302038208001c015a08440b2500028a4400d03c144064011410385554180d031980301c10055503031600307201495214440301e603400624411142c090844a207101d91141045502a4100302c04c2460030b00300080001d4a05003d00031610780e0000c21940c0c06440b002001c41200c008a0745014121041d10f4000c9894240c0700410f401800c04988022260010100095240d00715a580daaa8007145c60442d4040c00c1d20b042e100000c2c111744200540f00e600403000c2002d401940980c1d045101c07000503649980031000300c40703e9281c9988542150302844044004100c41d5005010302010000003d40324413004101805050b80c680303010803000d100b0480c205506a0160042110610140c03c6503039941003150380d440004e04148190220003200082e0f40b60f4000e00c1c2c101300c00702180c41ea0b60200b00c8120200c4298012480c03111540c4091030801805203118020785802d49a410141007407415550000c0c00860554001c0014006140c0e001050700900c43d0801c0c02c0316113800722801c1000242506601 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 925042500 1250 925041250 925041259
    0x9240108100218060a050c0c10080403112505032a0907050702100903120c020112020901110703060905060c03060d0308130c030c210b06090403020709090c05010306090216030e0a05 79
    0x5c1d0802220740240041c0a00c02c140c03000c4480d0507148104101c00700105001001c0011070100215000a0007003401d1809072191006948021081e1246007101c0001c0e422001c000000c0b591080110b814240129004044854641501c586400d110244181c003603010b104c0c0146490400038034680c0c4583e081e168000e50040c0320b19050001c0318402056030580340004e42e032410a181c110075219019100300d01082d941030b1649070f80079100288510094200d61001818002c1c818410204440244140e401952041c00001780d001e9407400c03d140f50007070060011206a10400034407000d0340e907041e501c0320340f00c1c0d1618060350b50303956801481c80c559224900c003c1c14056030a00110400c006009140c0950f980c010030032424540016603401c481002c290f0103032100d40200c0114078a410101e903040c0d071007400b03801164a513668a24850381240e100705000d03501750841d0304c814046980c2c58007924009002e544810741c18200300e038400e000007611001004090100c05118140700d500c454101d44014074000300b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 925043750 1250 925042500 925042507
    0x601050a0801020f0a0f1403040b2517130b09101404080418021b0d080a09020d0b040c0b04151803030e040b130c0207090c0801081c0311030924010810021806 69
    0x1800c010200d600751102f080c11040d003400c0c44a03a101e628844205e81e00255190200191001a84508541c0181030803105c60940c0801c40c0c0071400b0782c0411405065104020000480040500012620507403101c2035110314500c14403011850f114281c80c140c4403401d5100c4140d80207485010001e1203000002c001e213031002004418901000300740341e280440c9a88540c0010b80d2080c86810840d810810000d600110105880300440c009400456000c3d2241d4000104291200501c0d1041d0300151b12a0030680301140c051080c02d5400106035107101103031707400c440040d41503503400f40541c000c13620b11038095907070740341a14076640d65107241005020301a14104800308100c00021344071000c500402012600384444604003500c6044034a041780c00710b01c00341c81c082d1004a02e03001d8000c0c1c1900b0030410543c94201a101508181e00114081c050000c010722208811400c2410044901c2000c01003d030b80e40d00040080c09400b103105070710844510b0f070041c0e030f0b017a10f8034104210f140c4441c0a10341082010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 925045000 1250 925043750 925043753
    0x140f06092701020d060b070213020a092709050304080d0513060806030a08040b090f0f03030403230105010e010617070f0f050d0509070f0b160204050a020d050403020601050a0801020f0a0f140304 85
    0x220001c0441324000d0740c44009e23400c0b5005801c4140c0c862040b400740003171744620301008000d441a1b00c07a041c940d44004010300c0e5181108115042c3c42c59003e050310349400008041081210812941010602c10309007a82010119801c2c049048020b200d498203002c0b20100140803981d0900500807820380c03100078591525220b922045a540082c4649070060240c41c00456440c030300301c914405c4103003006005500d00340c01e641d15a81090000e03490f06206015003002040c44180030f00820740601101c0501040f0b540c0b400c48024104811842130b039041510110900021944c4007444009504c81c504280b8096850034808540c18403590199a044134a01014828000720102d02c00048902d1100104401a100d10540b103940c0314903212910b0960303194402800608103900302030ba1002c405d10005052501400d030b2801603a80407a811001038215000610452130100e6600010f00080c070021410400c0294103100b10f84203104411007404420b007644902244500458400c0b0004801c4041c0c403070615 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 925046250 1250 925045000 925045019
    0x1020a17130602011104140102160305100501380906031501080c0c1015180e0609070f050609040219020d030606051603081504140f06092701020d06 65
    0x9007808011400003484001040c03481400b4104402c1103910041c0e252900d4030161140031841100340c2d5041d40128800481c0038540401920011802071001c0e2000b500481034007030031180705801076005403000914201c503da5400ba070140b40344d9641c661201e035032101400309411901070040d849521000c00002c01106800e00030132105405400e07219504107445152004645002e1310079802650351002142e00c0781c5000a400c11000104c1c2c0d08402c442054032150740b000203440c0c0c81240f48480d900c80040403c031380400c0107400d60002c58080602812424040c0c010b008442500c81c491188801045558843d078482c0e040700c101c103d02148861750000c0303855010351074488041502002c03919016000401a000f801103903145072111890680341100e5580650390040058006c2148540c010003004541e02d0354030480c520300f0810b0b0420b11413403600e65038061031504000c100500500809003844000189080000609810f5440c0001403448020100740280910302c404a00f2504004002602402 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 925047500 1250 925046250 925046257
    0xd0c03172703130e250c06021204030207061812080d0518070e0103121209120518030703050d0518090f16090b0904020904060306020f040806151c0201020a17 69
    0x10380e800c903c001140e440d610030a4420302103c0500035400580d01c481c040104080c21218026441e06207000030400035180c16080b40c00a103507100e202000d4009000c141a010400f0b00010a406c0c940540410503c81030340381030304960310418032100c443c0f016900811850005850704401d22510401c441d10781035020740200e59041000c0302050003030310008070320100c0d405a42d505036600310300d0380044103940360b02c12130b03c00030b0417103404110580d00d8034844002100f075403071031440c0d012507900e003038517178010035411403001041450041c0320381d12440080000541c08104445131210034107103240c035440080401600710b02060340c0a41e010414004014041c07010900d0300d0701440821111031481c00f082401603802800311b000d034040141c003d1014503000c0c90281c00030b1010403000350000c5250b0b541c0c0e0740c415040e03030421282501c40c1200403805002140003005050f034003000e1180070090540040c1c000c00e24907140e0094240005540c200f1035030940e402040f5120645034003800c0b090b01c038560506080407030380 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 925048750 1250 925047500 925047517
    0x607020c12100f320403110f070b0307020d020109150b01050706150e0f0423100609020c0c01050703050901121d0d08010f180c090503030f09030d0c03172703 69
    0x620000c80981540c1035040038144e003904094214000e403110384003910081c410407054000e51082170024456880140603503002019072071002622802c0140c000303801c00a803510304108580c0740600b0780c2c000c40da5100d82c104007108851000640740d2250340c0101d60b60300c00e42202500d00c81c142926842c3e640514010101102d030721408150103501e848202c50105c4200b82c801411680122541c08008003080300980d41c41d02d240030407905810a14080c940c01d5400d9584812070099011440c410441d809000c032003c8aa002d02c2c095240c00383c1039030003a0150180101140c100b01c5a440da000030381c003082d413010b40242c48103052250510300050040350b03508048021180040c3c01d00340009004021049a081a6460724104e0b0108012102036480100036020780c80c41001a80040000c1c45d440600c000c0101d041c0000c3c40d50f030342d94201c0060601c0c00c41c114000c5020081e00007488401b02e40e01c1031242c251194103008454041e201c1404601c1031125281130541c2c1e1040c80c071807074685080004002d00c0d041 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 925050000 1250 925048750 925048781
    0xd0c0b040f0e15040b0105091c110303040f06030c0201023907050a1e120c061d0f040e0708011e0b06040311010c0303060b0703051b0607020c12100f 65
    0x5480e011100c182c01d8050b104108440b10b61140b4900e24601904960814103040c50024103214400d00000d14a882c0c140b02c510890203201c000e44148038886600101d000b205038003c600d403600e01421007000700c2451180c80c0c00c05a550040c4000e42d8400c1d0115104510381d01b0381c07204088003981d41c5a05e0b18814808201c44d40211461110010301c000c40c480040b9075004064030085407900c20b00072240c0c10031070360820301301d050343c07001007000d004244450441d14003810a001c2820705101c000b130030a044003c903480b840710818104590aa884c0d20302903500f030301c003503801041d80861600550301d4810950040e04171542401403441142c0b64101c619120030803041c000344003100151050200e548103a00000d41010050150301010323502036803013800f255110b0325002441e555a11301041c09600711640807400581c0c006401c0d14a05807004a640346000040007410850a0020000c1d554220a00f02c50b80183d0a0300079803480c041c0207000e00740384d50003840d0043c441c65920001d028000d000000005e0480d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 925051250 1250 925050000 925050029
    0x180f012705181618050d0c09020c0705100c050a15150b0306010f0801050d0f0c1716090b031c110f031b06010605090616060213050103051e0c090d0c0b04 67
    0x124880e454602d0442840035040e100681070000303100b940111207109491f0024120800a014851131006280201c100406855a80e04110422200580d001d10b8807042001c690080c3c00407400202e64400099400107500c407086180034403c0380540701011041c030104108041c0090346480100c01180b148100b43d90b89008194010416544003000780203c070740028070b030841c0c071000600d01e51070001d1036030044101c401d50720b51300d148200c141d03014075058161907000501d1840b00701402c1e0b000034003c0c22a0035070900180c050840441c3c2d407422549000107018048100f0903084501448211502c41400000d881c800940e010645035030358004500c501c140c030400c42c3e0400300300c0b03004203003e81610b020b65903070303031030185141c0070841e02da00103007580100d82d00c80c420400005100752006041c104d005240301c2921032304d85000501110320090401e04900650134001500ca1034611b0600e07844407042490a48540c80140810080f03d60084002c6c494070034114040f80083c251001342040784c404c038407074a61 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 925052500 1250 925051250 925051291
    0x8010e130302060a0c270302090c07020616060f0e030909070215010308070206120109090515070f050705071e090b03010605010e0105030901150902180f01270518 71
    0x462540c680e80940107070019008601903e5140e041001882010320300352a5103036182501e03103014643c0d95241100300c0c20a0604000f1824031b1040c0300d41c0300041e0f5841c0741c240643c1e6000b0400c0c034400d005142400c24140e5070314200304503e9500440c1e2004006204005e024503d400e1555203038400000b25105e07d5050002031003680c400200d581c41190a1248003139142d285584071026a0403202d0100d81c001c00a1041a81226101002500910f00f8610204001040d8101182000340c490510320303000c0e607440f00308021766070800540700700a1054038280703688440c241003880c00c0402c80d8218050582c0c0c0707030814032181e6044880e038000b900c0c1100ca0420034541d24038101422142d06108944c00700310540448406503000e01e001d19032101206002240d01491031448102e0b041d142d4001076070665001c103403410200903880c5608405c15003580e0181c01064041e0010f0a01d0010708400f2002624980721034124049007000c0e08010040030380070a155400b400d0888003051000c642900c60480303841c590070b0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 925053750 1250 925052500 925052521
    0x9120f0c0924060c0a050102030a06060e01020606010503060d02030a060507110706031802011d090a1e0216080a2c1f08011a210610110d080712020a08010e 68
    0x901802c1d40d008940a020840140000354004d8280a022402914200f6011170700a00082d80f0410400c000005c54600b01800900007050410303100d4110b5220387c08101840c0d0f0030404907600103204588030185020340b880001e14094013220000c100a080c0300500c400c280d0010944c0030020f0100c0141c8840da521141c044088802c54030aa00b15444003107001405540184010042c045805a16074000301081012400f044010394450030101c3da1003c0c19800481075038179407500da2043d40710a501d0184050200d001c851001d035805820480d0000d00714201038001c1100314070120400c03e40702010114a0f46621390a481041954011003180d0f602c2022928600c00400d0001d207903440c0c0407110303401c1ca65507a525000100f61030a00290801541d2040b060050707070340f2900e8940310314040451403c0c1b010b0140c1c850001c05000d05004144c804020b0000c4040350003440304886203400c040d5980e9002d412900f10075020341c12051907200080500b080381e8010384c01d42c16904030071400b00c4a80c56001981 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 925055000 1250 925053750 925053781
    0x304140910060c0201030905012a110a080d0603020a092408031b0c1216062c01030f180309080f070e100504060f090501090b0607060209120f0c09 64
    0x494448406001c107005850048001042103401031600165000d12540c1b210f0844204ca981001903040005c1d0348128006842e0403180e00c01c255250050524a0301d044043e5031b403040340ca00528817507010418843c080c040303a000b0001150020011f0442a030784032024030041500716541840c42c0c42c006183d9002c85d80003005a01100c1048000394034111900c0d40f45040400450380c402078900810142056654600c009800c0701410140907014181158400110741211135001c5418011044d1202110700076020721002d00d010107400c64404031492100482c010f2642c0b0000701801d07490000b4006031b45004035035072003070a48240c8485203095190000a070b030301c064850400e00d1990000c5c0701400303074004034283c41d500b0110350320404042644550000b07041d01c0c1180c0144420b4951030b8001c205690541c0a003130300600c20390303004011a003400808203456100e0b0000180c00300384c0008010306070340c884c00c40c80c0d40100b031342c402034404500340d403983c00b0349680c440b0100c03600c1071a2000101e050052078178078a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 925056250 1250 925055000 925055011
    0x130606150e0a06050f1309020406120b100804031413031a090606090c07050f030f03091603080a03050601020309100815040219030522030903140a03120b0a08030c03041409 75
    0x2002c1c10020803100c1362400d54400c10381620120f0f004540002e110003140040c09c05840b40d621548810b4460f010080100d6600202c158414071002c60071210264015152070313000354043c54044902c0c020b03910b0b110250b00c1441a40c0b03000044190000003442140c010f20030000001238030210310f940758042620b035030f01d005492255101101c00041140040e00f0401403251610900580d01c801010086c1e050840e00010308a9800740400402c00c58101c00038080e020701d21003000600900070b8115152403110f0700030311045206055840001c1002c5178020002c0c1e0341113210082c002c6100326940c0000800e00d0342c0543c2c140104031020351b13280040749043d00944000b0480800fa0110000c01e4840440141001400c2d8203d8800c603005c54100080080142040300740c000d454004843d0310b186481000f041c003a0394800081d8014022034000a584071940c001c030b11003600800f10b0700c140342100040100e01281e20111844c40001500c6001500201c05402140d00c210808070700540322506024140208980 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 925057500 1250 925056250 925056257
    0x60516020d120603051605040e0601151808030a02070f0b160609080f030405070303080708061807050c030406020f0d0306081f0b060307032021130606150e0a06 70
    0x44a9801841110403010742c20901e8004a001c641c0d80d01e4050900e41d6010080d4000c0840070420707c40d03410280183d0b0202c2040708000c100540c034081c51284840c12280000c01040040722030070301d12200c038280d0303400036120f4070058990381c00000001030f5507181c2900c610302801c0070900700001c01e01641001d9a01c2c18142c00e20102c41e5034840e40c0d440b8000d200920044483c11814009030800c3c2d0b8814018622807031140c8001e0050b0381c05c60030003900740074000342200d04002e41041004104c0d198000b10310651045244880c2050f205d8280c1921540190a294942c0d44004940000c50a6000800c0b041201400040e580d0700c502e0440c00310181d42c8940240003066001c0324591240c0340e8485a114030400c8624000105144040c00041650303200b5290080001c1c0c8401000c901001c0c55080150720100000e0010b1a264100c158510030b40506030301c4040900f40d440006511424490074a00010750001007044844d03292601070740351070480c84540c0c1c0013880c0d0003208011400c2c03002080c000d552180c4c9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 925058750 1250 925057500 925057513
    0xa09090c2001110a0507030206130809090415020f0d0513030c0b07031812080703060807051c080a02011d031e030a0902041a040b18060d0f050a0f06051602 68
    0x711004626110348040c02940da10507500e05062412070207800043c01ca81e44079644d50b40746080c02440d044024003c1c400c5540c0000e4510b0008100300102d45a07010181d80180982d41d8906045048000350350301c005106000240141d10b01c5044002006a460303280803c2055032a025540c015000300b05000401040b51910044085540301112943c855024500400c1d2703103c0c28506031500c3c0c03140768030445505071060f65a50f0200d8019001d0382d070102551404124252401c5030243d030b588144c0c8100d034094081c400c00051b015020414914455400000c4070350784110382c450090007080703000344107240003403c8450390820b0724000c4103d5481c06e003044040041080b049011800c640e0010b0a01e04e03445664507a000c0058441d800342d10400403034405a004070160700707403d1105580b1440c000f41c1c403035164102c92002480300c55002541103081a20049004206c0c0c1c502035030204241e1001400500c45d1800b07800400102007100038040c0d01c16401070000307440d00c5001401c01844c044000015800c42c0c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 925060000 1250 925058750 925058777
    0x170a1e0e2503170d2f0a021213032a090c0e03010e1b03120301030803060d140a03020d0c0b06010c050717100e06010e18010906020f0a09090c 62
    0x15041501c8604201d108048940e603207588030694455542e00d01c500c0640c0c00f2850307020801607881600b020703444120100e2032180442030f400c2160840305886048100380810603803403080c03003004101c1c0801140f20040790340360080307800c0310030401061004584e6203010a101c21910768070002200c01007408803a0300c45205060111140180c80581c118000301311a14410421980c3d007400340c1c013100c400441c041c1c41c08280700b040e0300040c1c0068a50060103640001e180c0c0c0403901c0b0f0203003100d04480e00300401944a03143c05001030340091410401030501100300b018a288442d01150542a691107902101c803030f0107120509948804203014040d109005000c0081d03d03550081c07001c1d205a40c80f44055420598503806400c000b1041c50020802d82c0d402908140001030b0b1a102d07407840c0c140e80100070422581b4154800309070150080841004a101680da40082d07a82500540e81e0710758004400d540300e0912031603400300ca41110300d500d0002000c0c10b1000400447d03070308c00d03e001468a40d451100c086410f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 925061250 1250 925060000 925060033
    0x50d060902121635180a080f0409141f0b030c0d09080a020d1106010e010614280e090f0705090a080a0c0e0a02120115170a1e0e 56
    0x44449405001c134402d082c00d2070041c002003400942a14070700c01640b0400600791100c054000400b1900742900d8205105200c00e00000c4841201d5444a5259520000708034039500700c3c0180c2c0d103d048141e0800642c14084040e0303003582d51203000b012408100300d502142007041000d000707102d011240701041001c121684040002482c1d0720600c90800b08654003141d80c1d080322603210700c0310880140c00c4035000c015040c7c0d224003440b85020000b4001c1140d541060750303861400d0810700c200428044547e01c038400380c2104600340d4038a0100108030741c160404043c2c40f600c0005005400c03400040c4e03080075026162500781411401910802110101d6590f03200040ea180e078000340b0110740c040c070318007000140541e0802046040034400c10420b00d0395858460440c13410700e070181580021030300600a0711900564400c55504564020304824020311905900b510460841d07a8084200b2110104005c2080e846421121164080e0343c0080400003580540000b2a0501d40b49842d40e508165112005540c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 925062500 1250 925061250 925061281
    0x21020d030302031f0801020c0c030c03060f070c1a0118090309060806010513080c03060f01030f030e042405030d0509010c08030402031504050109110901030b06040f0b040606050d06090212 82
    0x1a6030488511340142e4000c4480011069401000969000900000d8401040c0a0b10f0b0260b00154010310400146000081c2c0310071340100501c0400020307a00180082c0d202e103400703100c9183c015000c7c0e112859a0b40503030315400024001c16400700780310003c01629840c01d20410b02240d4241e62405a02814950200c0d40c00c00007615041c1040f07400d010200f00048980d5035071009008010040080100c52400e060800c000108035041860300c520042000c1260080e41702100c1e540b52502901e08a80c01001a0041c41440c01940303580108603103100980071015040c0040c1c0b10201c9c100c0d40103c0044c441100c9034030402c41c000e800118040040301c009880c078400740d41c00510040645030b1404201c1c0c1c1c1ca0500c0e4008403000d550720ba4685c007040080c0310310204949403299040d184860998110340302c240e60380a005c0c1441740500d56488085250000c02d9005a942c840010018000d1760b41e6048020655003028482c29859450710a0006200000c0d20071924075410550801140303a5800750940c0c00c102e03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 925063750 1250 925062500 925062511
    0x30720030307140f032d070c060503040515040f05150c09010e0319030f11030a0c08090f0301060b09040e0712021e18010311040507080a0218150421020d03030203 71
    0x46180700d0b036400340d4000d2000e803c2203018426034446e0554042e00303d09040d0400c009521944170204600004255100240c9040d21082c1c1001c0e5540c1e200c42c601980760082030000c1e41c0307052043c00c0500040103d002d030510b40f0740e030080d01200c84080111542119900341a194210406820840b00d501e950148180303060010004003500c038180c0c4040c400c084034903c42c000442c00540c0c0000304001d042d820883d10079511080d070000303600b02080e0a0b0040c2013113031000005002172102041f25a269a41e0721000001d82d80702600a003e150b54591900250f50420812584203070308189481d40f81e607800080030f03011554422002c20804420f03400f408803d00d03414821920200e428404401c0e1038841e004507080c10079103a01081d135507600d1420440c4c01d003444407002c68403440c145024421070580c07207140d070b5400406174500180c0d688010343e89000d140030851881034020034090002c0605e010342a024004a8404204118569100c01c00e030203141c442001c3c000790b01403000c01c0c1120109120350f01965112 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 925065000 1250 925063750 925063753
    0x705150403062a05090108060d0f060e061b031501052110030606060f0804082a060a140c0418060b07200301090218061503040503072003030714 63
    0x281d2030ba110082a0b0b4038001a02a10941d5240c801401e80c2c5800009a2108054034101d0b050100090000b40940e0004d0320080c8a00410390300d41003448a2000009080c60340030004001842140c980592a81400c4400700107010100c411043c0c1040c0d8039045038407448407141010b00b1040490015269030b007080134440307003144541da00401c0d071080c4454441d0280d400c1c60b400c40e00041c658a0b01c03006461481e0000020002540241d0000380d030052007003a045948821a01e8482202150070071140058540604490000308015040f07984040780c2d5034080c50b07610340140315040290546501c0782c0000d4500540c4024100010040e20300161905e04d0442c110510208a590b684c5e400380c1000c0c0c00504007a14145a0b848000c0b001d03945445040000950540c002d01c0a4409500000c00c4040560040d2110b0913001d40020300c181c0e9080a21840f6000000c40e03070b504c03801d003402e0003507894100444c00c603030400036002000307103c5040b031000d042d05240080095240642c240ea807004a600031040c00b0f03145 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 925066250 1250 925065000 925065007
    0x604090318090b24161e031d040213030803060105073305100311040e0312010e060d0803060d03090e090102210114010f02070b1209010c03050702070515 67
    0x406901d80c0440010100c01001242c03500c0f01808110b03007094038940c0341c40c100650120301c0225840716019581083c8141050184080403030800a2400c201c0b1210b8004804402d80508101500003142c55000e503960550791480018443c28403041b13129000074040341ca06000320400015405a009562007001803400030b00713100d10355403a01542044004a848148120f0a4010400c0d0400d411402064800e4038140418242071921403142c148a01000d4034410101000d102c054030b0300e42010719600a010201e03071703442e20b81907440c5810f10001e0140d01810600007020070440d00e08081015000e070341060700716241d502d403a41002100d01003103400b1010b0080b600390000e4002a142c0149100d0708503007002680e650320b500100c280302c1c02a44419601c4081600042c022141012010000c0c1c49080c2080c80d94150f9501c4140c0ca000c082e41c0c010116982e0001c2d840e041040944903990240074040300034010b0106240c410303000d0303070000c0b0b41800c01a0b024a20801161400c1508800e0b281d10042c2c2540c42d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 925067500 1250 925066250 925066277
    0x3010515041505180a050108130c080f0a03110a020a05010c020d0512090406060c05031b030c0102030705090a120f1e0206030a0207020a1d0703050a0b030d122306040903 74
    0xc09040b00d20250b4046000030410490388010f6a26103180d2800440b410031002e0b0400001038040b0700c0207802c2c0c07080b02041c03156607820841000c5100000c1c05504c403c031141448c4444416580f02041d1400701d00280314038030008402840019116103240d4002c1c0320003501e50404d0011500030368140c2050b640000c4080a000c0850010f21418100b140c10050305582d80680e10b043c8016a406540554204003002c070000010490101c250b80711813621a40740d15018011800c854998002c6420f0b90f140795100100340080c50707800c0b80040c00c44903020b0b00d40748400342d6598002c5e8050340303810201400010301c1e0050702c00064425158030840e4080c500c1d072501d40d00110b4002c1030342600308980d11201154001101030540c40c1c00c00d8004010a0702c0800e01d07281e0403c031503040316085005011700b0180368490011030703584845504103403194140642100c2012400882c01003611310300d0440d0100c070703c1c03a20341502c072002c100d0f8098a80549051203001802d807111024080140010b903400e40810030800c07032004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 925068750 1250 925067500 925067519
    0x3011730071e15060506070b160903051204050112020306130c0203130f170f03180103061d07081506041a070c081c030b0d0b092508061b0301051504 65
    0x28881c0c002da03403d4000000c0405040200c43c0c1c0760308000c0c0304110030700c03124000690410140d5403040040300c0016044048500c1642c8a80e41a04001c060f40200400d43c03410301560005001101e40980e6040d0305104420a044120b100075140035400200e90155080b038051181c204131854001c1e4030490f8a404405040541c110304560019501c00c0d44d0f0300000c12050b5010f04600c030000c40d145024203644915540c405950740315140030184458440e800601c05a8040d5101c180280002010807000382044c0050030340d606d008640a00104501c4c40c00701c0d03410b0660304842c0304c4a0307602510443c681400d008451034101905001e00c00350810420000c0005221141504020248140104100100c2e2403100282e203101c00030b0319080501d010410b0126594000300c490100381c02c0b612564841d100c1c841c8903424000c250000ca070358226400e42c01d82c5044102041d00086800c5503054464a0b150360400c0003101c10f0203c540b0f207a01c00140300601c40c905d0b01541c5d282c000941591b103c1d18003a5140c0070003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 925070000 1250 925068750 925068803
    0x1b01120b1503070e04060f0b0c1c030204030203010b040c090e1008150406052412160602010c140702010e060c10090c082811010918021207110a0803130501020301173007 74
    0x2b9000a8021804100f1410240102511080b007102c0c140602ca840590003090411144541c510a0a100004c40c4a1004010302d481c00b8000103802c0c1d403021005015100c03080030301550100c0e03c451030040050884c0b4031400b130640e0011038a410f4090161210801c000b10101c04605000841c06203103a01d0001102c030301c2c1d103100205100c1e000410750500c1c03080b000c1c00140c60003001302c003406000c10140300140c1c2d001c800107a5246040301d400d80c82e1003610b210589030008219002c1681032502d5044424040054240c0c001c54003c04102c400712040000701c0b07040e214401d100e608213020b20001310307800513103802e90582c413080e01071410f4007a403680d40b03280c8003484051900005e02e195000907440004c44c401885a517001d41d20781450f0b1081176444a0583c1d48948001e40540618030110115001c9101c100d11401c84507000402503403256150340c1104102824089003c14601c11701004019204048007618002c1d00c240d03032003196981401404290580c00480103c81a845044100b004e810480300c10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 925071250 1250 925070000 925070053
    0x20d020108090309190618080a0f06020f1c0b15031302030115090c090b0702030a0204050403140d050609011e1208042d06021b01120b1503070e04060f0b0c 68
    0x4190169140040160070b03551f5181c1d510200c02c0180760306000300000025404802e590000b031103103c17a003590038588001e0042603000940320100103440104043e83c07524190807401f0002c0e080041785401001c0144015545004178100ca1081c8001850f8030003111603038401074000360000c0751024000e55003005513010b5410107480255039501c0e100c0c0d01c551002d18a8090601002207a29224045d00002ea964074940300003032107180c0354000103080510890018040149a000c43c40c0c036180b2884044001d00021034016006042a00001500c80e121b0702000030000e0840103038030700d000c1c11b0448148110300d6011003560807035401c00000884400011240c100000310404103465858803110301c0032a03c100307070702000856100025240c100001041c0f21b2000703041c242003644100d10b441004401500a07480c2960b4080a41034448407250154402507100d07480540c1d900d100c0c919030204200445da201d01034402c4404d05940107204448104004154800304001110407550441c1149130001100460 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 925072500 1250 925071250 925071289
    0x309150408040302030627151f05061b1002070807080724060503011b020d12060302030d0c0203070f0305030a11150a0c120e061f0306050a021201050409020d020108090309 75
    0x200c0000b2140700242c007607c0e018038001d0f2082a41084a8109015007e00400141290004d0081d241600c00f0b401c4002000b0142143e61200018085090414560402c1250358050a4266100080790f80300311a0855070010b80d00703040c090b458503003000c2501301c080121403012011801003a0402088080400b0800520021951034200410b06080d103011940200b0a002e074034006102541c0c010070490805100f9140c560080c0a0604a9401030300c4103a1000c3e4060042620046801d9803224120495900135070807660502e5075221007050310f050a2001600641081c00943c0d075051085010505403040b40c01200d0401101c0783e0700000d10b1805a81d4080304582e03400480d501d160300400065440482888208030300b405c1e04541c0748d02c51300018020342405292154040210b044022404041c54101004014918010301a0402036000c142c2801c503600700c50000242ca807606002e003040103580030b0140c01001d1580e500540e42e10710098203000c024041071000e42d82c1d9464160a003200c1c0c541c00c40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 925073750 1250 925072500 925072531
    0x6130c051204200f010e0f010c080d020337050402010c061802120c0f12120d05270a0201030c09080f0a120e090c09061c1a010503091504080403020306 66
    0x5200c2c84000036443c20081c083c2a10310001c000d160b800c08419182404c0640701d81c03c014602c01300403182107180100007807202c80041805050071519030301440c41603000c01280c4c441580e03682c601404107040e000300510340b800840401d4001c1841c13038002070b402610604061b220b604090392240c040d65400c02c010a1881c410345c80d01002d501c0d01001400c60004100040c0c00482c95860100346140c082042c09800340d4520484480e21480821501078031345200412940c0b60085e031590fa002400b415102e00841c0c0c0c04181d241c944410b48000700762100001303a03000303210121180d030055024180420310007061081e41140002e5022003445089114060303c0050984000c03d0324085080c114490022801c2110301d504c0703814192510707103500d5000b042c0143e0740c030b03260100c1000044551052880d62901d59900c82c41c0c07800105802c2c2c00921002c4841a480d610310080500111442d0200311001842688960560b5041782a01601c03640c0090040301800c2c17600e80c03a1780103e864007034140e40c80c3d00ca580307184 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 925075000 1250 925073750 925073783
    0x301060c0b06060a0e090603030903030c03070311150106030f060b0d090605011a0f070602070c0909030f030509031e07080f12010807030807140f0105010b2106130c051204 75
    0x8114190b01803011141d80f0700305482e01d80018040002c018204d8044c400150109000341c1d0200152103040c40010100d9541e0032004010784d032250000d20040740030801110301e001c2403100c04a2100b01c2d01c410342120000907840c0c41c01c02c4025103044409102010b035200030104a007201c0d5001000030340d18408010816105610300310084a030140d00c507111103180710420300103001da4801218000540440e50a40304c00e81424050b00030311030402c00034118100b003080010b0105140d00b00c2c02100340203854075440700901603001d405445040350100081d410070408070301003c1036004c8560b50404441100e81c00c008180c0d607a480282e01024440c9030850001c100498101804044203000d0315035031014007203052456640d12031038007a50000030504d51009042d104201001c00c0a134411421000080c003003541d554041e0403965000071803407950300b1260000900c481e0300c0c561089000d51009040182c44034440f17620007004000f00c42801b8200700e410070075030709510403000d085401240101c620b0381921142 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 925076250 1250 925075000 925075013
    0x5010e04060b120d03061e050a0b0c1504150e011503031b05030c100501060c030804060f0227040b10080c0309010e0f0c0f04113c070b0603061306200301060c 69
    0x1040c0c8111100c240d10300240300e23503203402410400701e03508010f920751107101640000b800c0180e25416000111103190800040c00f2010b104180c001c08002c0040002e299800f420314242d540d140400d00811607105000c200003449011100518030000d9940c001c0c1142d0741d80c9241c01d55128140b482200d9102419101858542e4443c1500604050404048801c091350f400380c4a4040100090402607941d10460b901d0300345901103400d44203071415102d003900003844c4404a01d199105000340561326000b0303034818504009800c2002000251182d8440d581c45041980041d4070003000b0a1003552141403d4901810030000c1580c403825003400f603d90300302c2e1401406400850f40003058810750600c407652782002e6a60b4103c44803c000c00d00c0004100c000342402a40114107186803446010541114071800d1003203101401c0f209200300f0382003481e5283d5030201980c841d41652a0340d800c035500010f44001421170307803007200c0c03a565113844040050301c030090504040e00244c2c800740200f42c6c400702240800c0013 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 925077500 1250 925076250 925076279
    0x9140606011b200d140c0604050a0b070f0503310303090905100f0b120610090e1f0303050406023d020c010203010f0f080105010e04060b120d0306 64
    0x3032902c100c8010b181d0301a074100c0c0020600241140100c0420b01e1410550490780240400015101500104041c9416000b440242c0b1030f1152501820000d0140c91400408440172203100602d014165400c2c82c4900b003141d40308241c203c60000241d44588005481031011304403482129a00700e40c1d041e00c030008500700c103c2550105610005445040c00000d0b0024140c1092740d0741c0500c0015141d440c1e0b443c58200070003a402c501d07800c1c58240d100041c402000401022049070b2a02421515240c3d1000c1c000d40b40c1074a441c18006c1180084240045804541900e42c07007402e60304600c41002c0450311241c0ca2655940044d000514009814000c45170100302c500301c0441075800c14000000500450300d000080c2d000b05c0311456050301c00030314003001141c05480d80b1040a0b402103649507918000070300b10005520454401040035003000628402c1840303440e0483e070190300e03244110713a9941d0300c2c48000c0c601c0009141c2d0100c15600ca0305401c000401800c086a40e103520000f032800d080c040398058204 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 925078750 1250 925077500 925077511
    0xb07020a02030303012105070b030901061d061c060216020906030c100819061e0b040f1206110307030b0a120c0512010b0904060f0c080606070b07030f091406 69
    0x5024030240c0d80140c400000700ca04644280c5440c03440902e007041c20843c803018500024015126071700c004180110070100560049428030020440160b403441c1151802d00004e0f5008a8241c0381c0e40010550305250b88042200c241150710504040e42503900e200c05c0340c0103261808a400e41c040b0b0078100314240b4100702500140114024031403214520006002900100c0f0060104102c440c041588182d03d010011282c600c011001c0c050140c48080c002c600c0a982d8405090f00a0054000554124072904650558940342070326074006091281c0c804210f00c0d41d900c22542607959101401140c00510003440c058445035402058062161041001d03500e502c0c1c00170500e0b14168584880000c40f40c1e00c0803801c4680c152031503c80582804d140c1d40c0100405407407250803034560003c002c01c001003a030040a0b110f003101000c001d0585181011909040300301d4000c0c1e00544100000300c0401c0c44451000d40c00055440c0c049801220f0380702c0c60050b04c02201040302e0700185500c0d440c100e10000c6c0071003503110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 925080000 1250 925078750 925078753
    0x504020a14030a11060c03040321030c1709070302041103240a1404090203010912090654050a05041131060c03020f070305031c09060609090b0702 64
    0x768003140007075240c6001e12001481c042d80000d130380d6607035184e0f036040d00d41151106003a02c0c1c5480d56410880794060000c929564440100d9500b988242d01034440c12006400f50707541c3c04200480d061840c0d0940307202500c2e10600c1c1c82a4100003006070f4030f901444003918040c813103807034603401d00280036198440200341d10b20401951015611a913100c0d203d0280890ba1407e880300b203c2000e10000c40c2c001c20070848041e4040d401c1c034803240240070b000b040301042c00f0002e0b960740030a103039128021540310f200c011852071402c03410309450b680400c2c0702091841200c1902d1021410b984c1000f480c288a002a182901c0b0752342000000308038901e41020010010f00f41601c0c18801000a4a1500d026100e804101410720750b103002000e0801c114070080100a5a01e016080030a6840340800fa005441c0c01c00210018401c6800240c0220030204030300048030344c004c0c0254140900c034243c5600349007441000a003055a224203900100da520301075a00104030800700041e042003581050000c0d0700c002890f81065 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 925081250 1250 925080000 925080029
    0x5011809050114040f3317071d07021c033e030606030a02031902040608060901080d020d0809030d090c05010f080c1204021f030b0901120b0c0a05040b0d0504020a 71
    0x15813401031001d041e4131143d6481480086d101c01c0202c00548480d4000019a0400c0c07424500c0010300003071031a055038940c0855102103139201c0102c545007407045aa000040c0c120048141c4160150303200040e10000d1742c14003082c0300d030075904108001e1042040c021000f03090240100c0b500c401c00d0305482c282c0b034a0700c1e032414039500d0040f0204515101c060081c2d45000d6001000403503c0e0f81c0e624038200140100c0300301755912559068028a01403064403028420020000001107050300091b0883d0042d10a03000f41c0b01e00c1c00500d9054861083c001c00074001800104042c50101c030051062580303980c45a41035814aa09020004203050240c1d00c084091044a000b40070503000388005465512000f100d690311141d40d0b40c4042040c81d40b0904401c01e81f0004188103038503145d00742e04211021001942c03c00043d82e03a41000d081c29001000001d08481d000318045008520381c00e0041a201d10316050003441c0654685c00e007000f0358001c592840d2180d44d51000c0c44114500180200c00601120031741259 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 925082500 1250 925081250 925081271
    0x1e030f03060815130203060906191e0e10060803041508010f1217070809090a050105060d0e071e090509010204050105120403440f0105011809050114040f 67
    0x140d070b9080f41c0d610ba02d000c01c0600000d00d282400e2490f0240b0700c1d0301030180c2c0c1907402d02907000741c1d0f122401c0d180301c07905401a0b100c09140d9003940c4030301c41c503441e04603004542c440b4030910210b00910101c103500c11325005180c1c95100f0200076009040061403500300440c0d440345000303801c100e0030610004050030003140f03200400010805520501c2610540c042e005242c0d0520f24007443da8400011200d100f0000124a00007802a20400781442a406403410b04055071110101811200240105584005e09008100d80c0300044c7d4001c0e104100300d40c0c02c030f07980c0c541c0f10301c0d03002510044603004c0b0304a40d036070103014025200c807801010742000078a4021b508290811002820300e028200e034100740c00c200751001405252250b604400c8030058110a1810b41144a00241c80900302d200646403810201000b130748690781e240140351040c1c507418914903660b401c1c0700045503450b4010000b0488407800b00740214600700a8402d55008069a2100f91100041c0600344003c2c4d4a2401056030700920f400c0007042c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 925083750 1250 925082500 925082503
    0xf02070201092c010e061e10140c15090d030c09050d110409060e07060203390f0a02010f020a0f0b1f0312090b130e131e030f030608 58
    0x40694101600c2c20580249030740030302c41d0440c0064420f034141020140000380c2204a0301540f03000f44400c1d241525501c21100514503a07a1503158480d4100b00e00403840c2030614070903030001440302c40b02c2c0a46071900507441003241c60181e0111071242c46840c00300c00e0003003100d410881a4894040750406108048103464080c2000000d80302c0d480c041c040301c050343c80400420005c00e401140005008100420b086d0801d4001404078400251040c0310754000440e50078000810380700050359980203200400c044201004c001d440c0310301100b0b40001100c1c2c41840486040c0032442660359907000509442e444d03800014500c400c44066201513402c2212030700d020a1001c2c407505d02d2072360007112400590301e401188550102104020401200100c9800f00030400c4a405031181d4103441c0d919900c00340d80724040d01900b171040000c00050020390310382c104074011081c4c130045c0c0e0107800c46d01280c40480c102e40318021a00c01d81c0c104410320351440312554007059080340c840d030500740c00780c902003000350b041c0744101d1f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 925085000 1250 925083750 925083767
    0x50a1116062a11040f380a1a09030d0e04050c0c0604031d0d030309060b040b0a032409051f1a010c151506030e0102090108130609080307120f02070201 66
    0x180140400c40403c40c91030b2507541100301403041400040042e1700c181541c0741c02d06502c0407015030110380404600140024010389002c2c501100406040c90186030060410b02e0513072130040c1d98140d4405100d0803034a42d806011003a100c4515450315094113602d40308001c100e800c0140400368042d4103010300d0400e010002210390b407140e494103091a6a000306005440400d01c0e113184a0340c406091140d0804155060700030050b068820300703083c4840c10801c0f08020585140000c0c0c2a00069000800c1020415103003005a852081c48840001912118020402c0e02c003802415a0240e1041d008090341c400c00c0d502e1580140d0703c4e81000c0000807110210b01111401c40c1c0c420504000c80c2070118000c0c00103907035081c0c8000102d42410131801000c00111490488030f8400c1601007407a0645046118006000b1100d00c4030059649220642d03a008403c0c1500c2490a410781e0416555103411000815050003903004140c10b4881280c1081d0300b0a001085e1460000210360b4030b401444403400603600b05440 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 925086250 1250 925085000 925085003
    0xe010311090915012606010303170406060504021611040903120c0e1323070503040b07020c120303011a041a0c0a080a090f05030607080106050a1116062a 67
    0x284099100d46405074908500c2c051103000400743c2c803000151038042c2e100b806040e240410b108020b9920961440c43d22004248009000700d1880700f00002c4444804d004640d009101e08400503c40352901d007c90300300d8101d6010042d1030314000011509019107043c2c2c1e9407005004407030500c042d10543d68005c024031481059a8161500c2d0256001d41600a6640071400080503121b610715a0034038940f40301904284c1c124011030003505038183d8407000c0050b821031248807203845140c03854445542e0300611031001420384045000301400342001c1e690f406041c41e50848110700458895040c080100800b0f020030510181440301000308008510f18810940480b1594417412a04c072051703202c1d02d50421040c440010a071320f03400100b425480b030708242c2c1601a90100b01a00a810b903c2d0f02c24103a9411050381c002c2c02180c0403000401403944100001c100351030031840c0184807445035509182c6003514502565814504000d800d100a552044001e0403402840030044a484100c200700e0907210b018800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 925087500 1250 925086250 925086259
    0x905100e0c2a0c040504060504060b0a030f020f0a03080a0c0c050a03020a050d050705150408070b03190b0f13051b040b0703080a0603080301090c0e0103050127060f0f0602070e010311 80
    0x9010b40c1c0703106010380c50180001030024001403805150420051008440840c3c4007482d00c010440a81001e19002050703079485000d8010540c2a6002c00c080740d03170a490800d41c00800648003000003585034026040514880d2640080005140b60540740b692441d00114002c1840704020000759403480e2401040714420f6400c100c03400c50b9070800c20300380708158001541007030200510385020039000b0002c004440c04001a10701c0345486011f103481620040d5201c2d1003060342c0704410000c1c1d03925a071002070310481c0248980c207044100401718501d03c6800b80700d400f54598500c01c0195102101c0e6034006900086d070720951804d03003003c07401e5171075018400b8086c0c10802a400011041012980f06d0030196401c511505d0700c0790380d1840400301404040e80c802e130018013620f0301c08840394000c0c05540d0588020b00c81400103e0070128420039a00751030300c500c0010039114440000d0220b040100800501240340d090030500e4100b00020785003080075881030310500042001000402c0e0101d6180010030000c84 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 925088750 1250 925087500 925087567
    0xb011202030a110a11060a0506010c020f12010c0e03010b030607050f13050315072c0103020c120408011d0a03140306120d030510080307080306090403090905100e0c 72
    0x400b450010300034401054540000026442c1856404c200d40c1240040403000712012a51800b010205450b000e841d0540411a604100030061420900000e800040540310030000c01d5411121030968080c41441d10214a02101c2604e00e404c0038010401c000205130f00424483c100803000812621401c80c001039405030200b400144e450350882da0100909004044450030a0407541c000240740c002d0f24108081070302c0c48510310308114800c1c02d00e8440c00148003203800380002c60005401a5001c038507410b08a004d0040d1101c4c03510741103800b1f40003400b1190000200024410007900030195061b02840155221500d80b01c0081e50004403031803580d5014401a40325242c1c44007040e822850f05948951a0150007e030540a07581503000911402c076021b04651615982e0560948034843c04030007504c500c80402c009512428040c412982152280c50501c0907640e58260706422104e042d00d411352954418042080301444c0907140c10f41042c007500300d17030b4500015204142048014401038180700800d49 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 925090000 1250 925088750 925088761
    0x101403060d0c0f0305100605090603150c070b0112020103052503090f020306040b0f060604050303190507050601270e1506222403050a1b0f060e040b040b01120203 71
    0x560500c2c000701107104904000e15200c1c5045501c0b4203515a13002d5100385008400583c502d04020414001d46018024020800361154182500c030300003803010100c00d48c20040200001c800441484c000c0c6011400348000907158030005003910030140c01801001061f034580040048201559102901c00c2d00b000181854149440721991400c40806541405103a0400003030148104032a40300b0b407068041e0300302c25a954400c020340c0b80598021641c050b03100344004402c0440c1406410f140c120541002030501d6880d60b10076280c00000d0b0040034200603601c580c000118202641c40c030101c02501414021440590b0700d00f50b907040c031401c00b0340185149202141040c0c0382c8054000b51429008220072a041507111008042c1141d240c40f20791281800c8503e40d8030a6001003e141901d50040c007410002c141e0f5129211034284500c840300750244114030000304004224141c000070b01c059120344604541c107030200f04c21900716071301c03113409a070910100c1412682c0c0418098148840404016201d8441 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 925091250 1250 925090000 925090013
    0x12010e0a03030f05060402042d051302070b0907060504061209020d14010b010314040b06040905100b010e040c170705041203170a1509020a09030b01060504230319031b0809101403060d 80
    0x279680110b4212010071055075000007140c00a2440501944070750709140c949100e00340d5a00c04a2050303100248080c0810b00c40756200d04108001c03448014008111058141c00103032406000960032101c41c8540f00e4084031202080c01001c06401e000d0804004048144002d00503a29004200400300390070040044c600c0da84650044002c550003800b100c01390103258408000501c0d1507000203000c00e4903100d000c80c2c58a0680a20301442c0d040d50340d81003880c000c0791f82803c030041d00039040c00300b40075040c8404200915841c045507581406591034030760b0984c607084512000c00d006080c40c0c4509003800101030f01040140200001c403509008014ad40340c80b4044126a001196000201608031182c000601280c0c030030098400d40300b5200b40b21180c1011590050b108214411035241c054000225200000030412004140507000c1c4c1030550b40c821548142c0102c01a0b50141140d1501010412001500340f02140440c6240c0b1400c1c1001c110081e41c0142c00d690000600d01c511402d036101510040081 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 925092500 1250 925091250 925091339
    0xf1c0f0c0c030818030105160804050a050f16081b13020c0106030605012103090b03040606090c0801170304030c090509150408070615050f12010e0a03030f0506040204 73
    0x100700e003003046050b49a1074004020f41c0070850115041d98601c2000c2070a103410b20940740030350420180c8580e0649040740544485000138801c0c0d4060050900b1840411801c1c403a0028034045c18010b002588221200b1401141c1590801521540b1030703604510600e500c0c8102240c20507040f030f6941d1240c0c0707040124902a100d40d42c1c11014a50070700d0f0000080000720740040341664000c1808140d404280031600040e94130101000d000268022800c1016490113002141c02500034000442c1c595103508803441030303a49c1e080389140050b440724010048408007a1000385000c00c600040c5180900d5615940d40304401c500510f0017859807980800d20b440d40c100404890484d040106035082e2400d410301c2020382c0c014410035181142824008192010f002c2c1c042801d8440c01401100c02010303c00c14800041d11900750b42c0303220740d43c40c40780e0745248404005401020744203590202e030a80f0103c0041c819103801800ca94015401407005100004c080291415503c03880c0160454020300114510711415 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 925093750 1250 925092500 925092503
    0xf01050f2d2511010c0516060b0d020907270f052b0f1104201614030403060f02131a12180c0315160c05030c010203090f1c0f0c 56
    0x21140540c503144542c004283c00365603507030000200000801000f065a25200706180422a480340842260001c2c0850744484d084280c01340c20440b080c83d582e130228101c0f40c019180c12012070740b02403188451415851451382c00c000e2200070742000d503162441c054007000080c000c0d18851a021814110b107081d0514511802ca01c0000014000e150f00b0705016103007011410b0306503428000010220078904060040c0a80082800d000c41158142e44440000e2034000c0d0440c900d2640203912070310007003000c0d0500300880d809020b010b59a11865450640100c1d0b000d880e210780e2030343c01407000440561007801080200c55504c2c4410010030b1000e99061258071485000d090020f00800038000e5514401c0410082440701034220382d20720141070209552138007610f14a0381084241d1002070f8101030040400300303080c6042e0070010b11402403560380f5400d5800c034455012540e90f0110402401307800420102c65001d9400001d00345d4510510a00307908801c800080105001540710004075240c41030f4000703801107 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 925095000 1250 925093750 925093801
    0x80304150b06091c12090608090d23070c030c1401090f0e042306010501030b010c021003021e0309010903020705010c030503040303110f0a02070311013e0f01050f2d 72
    0x13442d001501506d100b0050140b0340005800d4000130781110000206044880c403107071160040d0041d80342c5240d054080c070a8400781c018005000440c0020380100424028510910b40806100d0900502c0514602d07040b41e424108012035600308800d1060f406100103440700107054400c036555a0800390144001c0000d0f9408121008105946d19000031030f081c0d0594501341d07001e00c05248000300449059950b0007000e940700c03950075020001c0500a81c001c01003810500d00200008105150028058000311080026a512401800105079041c0310041c05409c090800ca688035010741c0b001403003800300030070080c00e02d940c3c2c0154110280f541d00549020021211115a64404042009440e40a01d10007100c2000d2881a120300660189950f481404004004085030007840d002600c41c40c4071800f04d141c0604514000710364520402d100d0030840100080c0003052605080e900c031100c4282c0200b0b80d044203454500f0000490103034841e400d220445e1a0f11034032440d15402c50182c611344403030842c40e045 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 925096250 1250 925095000 925095023
    0xc02030909150112020f0901030c1101020a0e0a0e10030b0604090210020d090b090f2209081e07080f0a1107081501081b0603040602070807080304150b06091c 69
    0x201420b0281c90741e444084e03075500107044802080900340c2c0507041e00180c551500f403101c4100ea501c0b071341c001c0310782550b14a015038142d002c00b2000b608903444580081c002440142010390705003840b28030040240780c00c0c21000c54616104a81506415450100500400020010490790358594106107001c3e1780041980007002424200039569000d0340101c800407030308025000030714080e05010343c0e42c20100179108441058414081250603800740042d00181e41d40d000e84c0202111701403081804403403103045101c3d40e0b0b00c03003482c0d030034003011a01d454644079903000c10864001508d07841c00e9400e4280c8001d402c03030311100d01c1c01080c0ea980b8030b440b280164901c10300000068a403400100040300b0f000070304e42003243e640c0315051141ca40d5403903040b8280d01840582c60050300d0400c0740003903501030701504c80141058245d60700d000380d07503000440940e1004008014881805014428410707e040f80f400708000c3c441030f07500414a40c1c05801201c3d4401c802e0140507030a207011000703500c043c0c2c50703200c0e078800f90 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 925097500 1250 925096250 925096261
    0x7060603080a031424010c0203070801020a02012301081005040f0b072f0d180f06090914070804060507030603061e0e030301230604030503130801050a02040b030a0c02030909 76
    0x6000d1207800c07030713280c030132903c042000900202058115144032204245a110441c0c00541e10029090001c907010300c100703600064500c07001e1014019400c01c5038004595407420540002804254400088614501c00e0040207030712030000c0d05c1200c44d0442140410196900e040841c2070890513034025000b01d40c01c80820800030380c081c4402c005000101f4007503014010248418001603444c99103007150b5400101c0c0c884442d40a0400b80307180006540c0110141500c2e842c80110100250b030051010890526042c0f0156100d40200f540071b080c401d004684c0c030710b0300c200000c207020800b0304040c20ba15911008261350710301c2030b0040800780d50012810300001003140c0c03101f51003800001d0b0341c0b5805458124240546c10020048a04032006401500701481d41e039603074547c4403d03680c100c4980c482010000000054070074800342400342044000c10480501c2c104d002801d59100a1080c1225841040309000d510002c2d805d483d04044400303400101c2d00c5894074181d2442c0716051032107038010300c2d031070030003c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 925098750 1250 925097500 925097507
    0x7120201050103020916050403021903020d050a0302240402011107050414040213050702100e01270302060a18080f070812010825050f0a0504060807141203030c07060603080a 76
    0x1e040f24070070366004605544400c4240320342403107044203d0008100b0042000580f50812498410794011240b0b0800c46549030300040c1401c1c90500300f1110758108601483c00e0603010300c140d007240c1e01c5200051781710300800040701d5800d002c004c000034103211300d05042c0c40ca0882d0410124006e400090000c224401c4024220751501d441214200d11400350300c8090f4028003210301800e806201c0304c1d0003c02c4031304104094100904144910520b00d9980da80121000c41d104804007892500b112040d00540b03040713410f0003418030500400001c020350600d040c0f0b602c2060344880c50b0b0022600900c140b03032a40c4084070a40c0e039510031510064150600490301d10812410500d0050488101d0001c964101c2490580700316010308040c51403511009007601000303141800420010718440081828a42d192103000013000c44040c0d0b00044115032103800c051100302e0704407281026841c000c81d15032002000da82e07070140c0e0303920005050000b00c0710003050580402c005604414081c5034400d00c80f989490310f414008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 925100000 1250 925098750 925098761
    0x1716120614010b040911120f040807150c030f0902030d030f06080f010222180e1c0f031a0618150406050a1209051209131811030f0c1507120201 63
    0x25a8044ca49074140424000c00030844044c030b040307540c07c401c4982d038006512801a07070040c400d8a81c5c035410089400094078480213459541c9501800040b9905108001000c64640800100d51249091400400359800040b05620f81c1c03442e14010910754514407c0ca400360a076940003485912500e50710961914040d0007503c08400881401da0b5090700110260700c2071245485001d000d4003c00b1a450b0340407960790480c02c05c9540c41303c12101ca094908034844030800d01c0400d0071001810f0307484c0746500d055160107140e03401900140d90351044690500003031011f200350301c068130000312600e803d280c0759241d0100000620110586584d1038568904c400b80980d44440701890020f9035107a0040303910403880c410f004403150088000d01840310b43e1454860254001c0440540c054400120038240d080360380106812402c80780d2003a0b85e815128582100b00302004601c4a110303801c02002004103080000b40807035980e400b15020064214884070911680c410300d0b0700901130b1007140e02d45014054054005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 925101250 1250 925100000 925100009
    0xc030503030402041419020a0e091509011205060c07030c080408060702010516021009031b060b100e10080411210f07050d26070b011716120614010b04 66
    0x1780a0300f040c0081d00300c4018000c4450300d00c0b000303160300110704400e0590b000e0141c0f0345460400e1804491400c00007140c600d01140c003070418608100740e07a412814a88156401003071100c00e001030091481e0380f40c680322400281032021026000c01c0d5101414440c0c403080c071350359400201a50340d460312500741a840d04004c95420015600300030108036140c1190701f42c40c0e00e0010740c2d800b9040c50130380540e80710041c0100180503000c00c0b43c0a000e17441c002e001144d208a4030f521030381c40028044441018015004000c0f41c0c07000502400c188c182d0003a03215003000d4500d840e8030380b400001c1560f880c03038080a280b182882aa030042610380c0c801c0041c0300b101030b81d14007081c1400c2c11244104800154a56220101d002d01a0000f01603040880081c1c21044c1840b4083c64a44428144040018021585801c1924290f0b41d004100004101c900d048402c0340041030050000380031490028545210218018464855007c50a81d24042800102e6210300103907901b01000d4225540d54a00786441034029004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 925102500 1250 925101250 925101259
    0xe220302030a090e01030210030c170a0e0f240a02040909151506140a271e0f0e1302040f0e0f01020715020a020f0706020303151008010b0a05070c030503030402 70
    0x70201c2c201114202c001e041b6a0300400c03000c010210031004030090200103860f942031046406110b00740002c3c0d00100b600c511411b200c0043d109107500300c4a454044c513414201d081e170f08603440b0001e0f00040071550356000c410350501e2041544982d02c4041c001c1c42281d1103580e28901d490b184204010300d40e070a20141c681e8511092042303484004210008400c18030552011500ca002850b0345000b40c1c4016000e42c4a0600f04280e0034981c031200d603000440d145840c824001180001070140010311700c072004a80840c6001d526407141012a03031158140130b0300a02d40041030300d000007000e411800361000c0040d40d014000348a00644000c038000a40503d940c20300107030060060703110384000d0500c02d581d41725410806010b907450200d55440000d600049192046000f44240d0514050003005030400401c20740e4015a682d28282980c4e40303410b4007681d002c51145090070010000c880c2d00500c407034199401e01441da903403030903040070503240c1c0d22a00707000410326004540b00000740100403018510850085d83d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 925103750 1250 925102500 925102517
    0x40305360405010e0f061e0901120605010602030711040b040621150b0904060b060c03180a0605040602060403031104080a150b0103052419150e060306010203040e220302030a 76
    0x1491000c1380e010445079102d4510320440000d0782c616080c481a86108442a1450100360012000c40d00c8a44260045000c201e0468285c504208039803142c140140715a2028601740343c4140e450f4420310746207900052140347c42da05050f0380c594440d40302a0007000030606003041401c41c00c0001a2001707010341c00380ca000300c00c240070101c0e8000c580201616100300500c3c1c7d0100c0c2c1c2d00c9a9644000340741440e0025000241400f001201540810007844e0307006000000031409062102048030b001300c650000810400240010081a034001a07070a8000380d06041c041038200d190b0082c0384080c0501d40c0040b44500c900c1e81c140c0d00340210380300b07040461030000701c0030320102c04c0040040d015920251189007020030040300c801600e180030035101045460040141c0c40301d00390081c082143c03001c1d9404c0140c0c0d85400c5802e42c08891f0b000b260a500c01e40090301d82d00e0642c60460000307503c0303004511a18000407904000100c6403109810002c40400340740c0030040251265040095403500904c0d201800706400c031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 925105000 1250 925103750 925103759
    0x2010b0f0406180e0118031107271a10030e151b0a02102c01150902250602030103021302030f010b07051c0806040c05090904030536040501 61
    0x180aa0b1090315500000e0001d01801401210020442070940c091555070302e410300c00111045082d0482d00038042da0f11f200e181e800141403d41010120380c402e0f401c24103040c3c940048541041a007140e403a030341e050005542d00c0102c0c562a41340c0404a1510b50165400d02810145038040d4480a21a19070f007049501103816400c8811445100350b41074400a110803100300185a101001407213506050310640e855414440c070500e058407011560000c0c00c40004040d04000d0401054118140808000034048062444203a8540703070007070301544551540014001e0a0b0080c841c81d803000e1914000002c014030780e0340d400c015009403c203002c00ca206d075080007030401e000600d50080d240500c0450380b400010343d103402c51225455020500840d4540120070306407030040d450124103803d0a10341d8540041c2841c01200b080101c43d41840404280103090054514903198407403500e0380f05605040083e602c40c1642d45150207408000f8a0741502e094400c0c030060718414400c00e0b045064010350302844079076202c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 925106250 1250 925105000 925105009
    0x30b10120b031b06090316080109020114070c060e01050906030901020408010506152205030307030306050f0409030903020d08070b10030314040302130f2318120d200a02010b0f 77
    0x65a0300c84840b03040c4000000f4603c4c1201c001d0005080040440d41d00c0c1100608118542e1103580c400d202c0307070350740725604400c2d0f580244c030b0880705000c109050b51400500381c1da14400d00c0a1402502c08010032142108040c1e4014009c03203002500c000c0c5003545910345440c0140c041d5202e806207201550a04007c29201d040c92858442240502d41c0c996080490340204001e25030a20760340355268100301800000d0549040c4000d01001c5c1c040d5030b0201b40241001d013444440340c1490314480c040c0b4034040354000800da01c0801201a00e50440b0103091642c03060034007203524020500702505c1000804140051f20051480030f10440380710703403111000c095090340004002d00603488040d40000c0c4850b031200c0000140ea01c4070040d06900b0000180262284040d0799000c050100340c0c44a02031081c1c14058501c404081048001d642c03c40144003030301c0142040308060060205400c45a51101e03511070b125a100000c40c0ca441c40c12a100f15220050301000070b002c1e00c004e40c0210b010380503015241120341403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 925107500 1250 925106250 925106263
    0x207081e0708301b010506010801062307020612160807050304110f03010608030c070303081b041a0d050408070209091c050711030703030809061e1303030b10120b03 72
    0x6041c541c06070341c0a01040036141c0f91400c2d80b01d000c4003503420406040d070700303c2c810341c41038200950100018031403911000141c403000041e08548144000158614804444c00d0312118a819003160095242c901038400b003121400f4541c028210b1003580350030040800c809400d1a003540c1c001d070b40c4403c06c50321800400d0f5002e100c285ca0190410003042c1c125015421306030301451603035402034000508180c1c0e600c21305080d0f801c055070144054100750410424543d00108451b0170000c0b0303000b165001c2200c1c4226010612580c17080145e8807001d429124110050041a610801e4100c0f030144014941407070804a0b60323005640c124403c052a4010510030030340040c040c80110541a13400600c4544820280d0b425001642e00b201e503900b0f040d200741c116480c14030403007005522036190b01c9620700702450040e0900d54010079030714403040d110940407044c1546107000c2d50040320f95129032802c08030900b011800f0706a40343c01c0d10b400c00d15400051207180d501110b00c2440c0c1d0350400c800c01030307641e8441c00c2544440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 925108750 1250 925107500 925107523
    0x2001020604060b01050c070b13091b080c0d0c091d06030714060c03042603160807021309031107050d05030702060a030605030717070b091c030207081e0708 68
    0x24031a600040001d0354541c4903c0ea280b405041c81401e1102c0c18082030b2811300e6a40000c400381c6e0021809040d40c2201c000c82002502c20801c050001d1069100f58072141710b0440c013981c040040d0080802d01e0100d141d001c0340c0940b50003020a0014802c410f00141045206110300080440f807a1919032094404011080c007815004020304041403800b6804107080c10138100d0075501c08400c000a002070241040100020900480c034120884054906907015807104180060b16400800c0030b00b80300241031411003400c41c1d01074205602c83d2554004a5502540a423540a000b0b00d040c1c184018140c11a116066180f4180c0403a80c19685520601c4915844e001000308981c1c414000c1400520300388003e091460142d1800003030455850b00064a490056030248210080c02d44107080100414044403001d055180b01031881d068029000c2081076045800700e141039558009150205442032140900800001003140d2840a42403a4180d0f030032700311588128144140c07130000529420105228030281e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 925110000 1250 925108750 925108753
    0x30906110307020d02040b13050f060a03081209010609020a020a230d0c02040f140906150916020c0415090b123f2a030904110f1204200102 61
    0xc4031a070309011044c81e01000490340151920841461500c034180070440341c071040c120220740c1d4281130b043c1c1b121101c0c01420190041c4100c0c182400401c01d00c1e4100c8d1240000b0075140e503129038038110501d005100507001000b4044c000070b070501d616035000a42d41c14450041101480f65000040b40d461544040f2034419065000304036022902801149903003441400504003203460850712181c401154400706440190160910034054200c008010b0070364800b1a18907500400d106407130002e41460401010440782d080c20081c100c6640b4801e100e00009443d01130000e0140a408070302c0340c01d10443d140108071a02e0716000b5072507101e2408088451038120303054090421403030b6032070700c048044040d0148003007075110300521008800c51040b039422205507940307005c0d0b4541890094640b200800388110381d83d0780004442e0369840600100403a4907008040b035000841039407400c41143d950242d00b01d08080d100d808110401215805440c0e50700c5184076541d0a05407041c2c51010403014091442c409005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 925111250 1250 925110000 925110007
    0xc06060306052202130f0b0312040317030106230d05090106150206060603180f070b070b0609072019060204081203040827030d031401080c0607080d09020d0f0309061103 74
    0x115800e40e01601c01b04d502c101000c100a07083c2c5020038548a046428000003000002d800c10500c581c842a84c000c4c0014020b140d89035500d040c60080c2008400240c0c0091400101e0450031694442412151401c0c0864014040d614100201c18001d140d03921030a00204644440a020b0b9840403441f1407003076400405940c00d41d01c1e0702003400c03001411005601c03134510504e0442031703101c0c804000080080c4074190760340e941d40c0c0c0c451400082c0f200d0301602e0640603204410a0050b280d03001600c6c01384034aa00d00b810540304000b10300d1246403800600c81c112000088407040780900007150001c0c4195981003084070340040700c1c501e07411128441100c1c0545108001e0080e4100e01c3c44881c8008501003038241c0c0946850700c607000080c208040714244c81d0200b5600c40c00400f0403000c00e0341845c0105040405407160044e02d070302082e09849106801481d10000143c0503008800310f511503002d2507005884014142e1040c07401e1030b03108020010030350119003054000100544241104100240d580340518207 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 925112500 1250 925111250 925111279
    0x1207030b0f0903070f06050712110d2406020f0f06061509031002030711010c051c02130e100906080105130f02010207031410110f0909070c06060306052202 68
    0x1410003016100d04440e000410480c408503100c01d10745d80c0014040ea20000d21420050400b42c68a1441ea2203415840e0404942d503007140039076400e8404404008002007400500721680c0ca680110303c5003181041071403400b0108105a000030a062075400e5202160342d0a10b1018007142e5408045412030340c49152010680410b50072440a40070350400074088071523072920108010103a81003242e801d00000ca4210301d0002400e02402000100032071405c12a18003074000d40c1c062f0111803040400300703205030000307170045200c800c10f00120014130030800304100e541040310b0382e841000c1c224400d11070b5031402c0c4440800e0201c1c04cc4a202d00074036007a403090b101410389a44410880356445030a0b030660094107000000700c1e1909140302404255040a0700c100307098500c00c071049664640315400c40b1103092014040c000c20b4102210181d80c0c007296440800d40d601402210304160031f6200426840c00d0181c00405c0281c02c0e041640a8050410221203c0d5465000c407401000e2124000c1e40c0301241100707845 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 925113750 1250 925112500 925112521
    0x702030606330403050607030b0f040e0303130203120a0c050d180306110904050c040504060608010e0a090f061503030305011d0a05220b0f060a0b0d0c0507020315061207030b 76
    0x240c0c18885a96080c2004e079a0384615041c000c00321010008252280329020b41c0b45041200f450501c2000c550812000c0422005c1c0307a5603000040c00400f64030340c03040011007596410090b4480b01e104a50100d0ba0b520b079082c400900c60400054121524850801041c4c1c20350300500d04040e03410b150301008842c0602d581c4405000c0c01448122114070310b02040000e84603191405110700c07921000890960f141e1900044c80b00302d41280d030000c81004042d0005020705080d031000c2d680c1204c01001c02085207104d07810103c1b4080c1d04180000c00981c07815810380000200018130404590180d101040700d603a03210360700307510090f0343c840a04006a01c000003810b04415540480c0d01310031304d180c10071004440510500a8040c7c81c641c241d40c0c0000d24000c10044482107407005030b1101c410303a50104d0350392401c902034005011b012007481d4600e44075031f03030100411310600c241d84042c1e03002070880314450200c41c0e11000c2100f050364668001c5080b8050300d26030000014207001129030015020009a4401c40c00c031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 925115000 1250 925113750 925113829
    0x140102121e13060e1603030207090b0102071a09031f050c04080a060f110f190c2303070204060e0906010509270c0d080309190c0e0a0e060109020702030606 68
    0x849986130b54800700032500d1070800000400700b140e0102c0c0c42006085040c0a4a000c1240e400505554149080016580d90104588040316401d200f0b8520402c170a100002d403d015134000650540305051070240d68801400392840000c004460810054a80082e201a584640c1c001c03001d565124a10000008005a00c000752940e2054400190b4401081003001c681e4041022809640d001086c0044041c40d8551016040b0801b8280080e040c80b50350340d400b0902c000c0404062064100041343e0003480f9090088031061507006100300040d90b111030070020107a9055074481e01c548120000404c0505100c0c40c0a0f0143c002c604000c140c1d441162915140306200038042074031801400107880da01d445000004151500c00c1801b13507187e14001140c02d15040315055001402e59000d40c0040100d01c200081c1e4055640110b08071403540c1e00c1103102d00280525000052030f0380311b28400006c100c41103502030f0501c14801c86c161102c54840c030003041030424030440c13544100c01260b10200082d01403c01c52 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 925116250 1250 925115000 925115003
    0x3042117090717030d1508070605180910061b150c050d0f021209061303030209030109021509040b0103140a020a020a050106080d080f040c0b16140102121e13 69
    0x880d003076035443e4100d03240218904560025a5840440c0c0e1900f204982d0094080340490700e400c00c0d036154500b00139142ea901052040006120000443c0401d0260329076001154400107080c2400c5810200a000f2903203c541c41a0720005000d006401901c440c10b8035480a4542c002020f0b001d10080d071981c070030040a1340f15041003401400c0010800b4000a4000ca0310405500c180c010307141d41d0300032104041740000405541c483e400031008c0059031000040d80c28072803905440c005880b02844c0e80843d00500a0700b001a50007050368003000c5500400c000108203601003658140001c96a400041d81681c3d0800020302802d036003c0005081320300d40383d0103800442e100307104a50b030403003080d1201401c641c0990080700d8160881c100c1c000030160008021a000020300181c229949071546608440c0710403401141032514001913540c4050303443c0100c0b02c0000381c000303c0d2036240313000140c4150b0003940501c0241c1106c11441c0c1c0003070201450f1181000c907900001003220840c0d5601510112505200c010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 925117500 1250 925116250 925116253
    0x18140c090102070e0c130b030106020322080f0601080d020d05070b04020406050d0b0603011d031801050c0f06102907020121021e0a090b28050304211709 67
    0x80009812600c440d086010306507420345031ba568076041d1200039036201d06e5088103c240c40d040004000c0e183e800405c803141c14051001c0400090b407420300801c4420410f030300c800b44900c1200d054940d00305011803880d0494140004883e88480304000690702d607501d484510b8007050302809481e012940703650107203034014801007000070704c2912100040ca083d0080082a20501003030360800006050900c24480740548080701100d20008520318142d4a00c2141b050f806030161620b602c83c0c01e640201c0607194002c0f0300d042a0f03140c400c1450001a03a078031044640c401c114004020000d130a00450714020303080c9500d002d1105915241c048008025800210100c1c1003044590b09104401103141c0390304a0081c156001503601d89141039800300e019100000c91194003410070140a401da045001d50f070032a80354280c15a01c450f90500b0032400c8070080c0f612442c0c40c800c0000341012541d4054000d511540c45800c0400707102543d144080c9209180e040398402007985541c0b8400c04600c01001c0e0f42c0c0c06500d080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 925118750 1250 925117500 925117513
    0x9020d1506052d04060f080108191b15020d09050901082121010608060f0916170a060512121606091505100902071101110f011518140c090102 62
    0x3e049110340c401c0e4084070009008110f41540558812801c500500d1a00d000f45001c2c01c040102c510b2100078114005c105d0b14603143c0c00200c20612408010083c4400314042a98810000b006922001c800b0742441c00104400781c040b41c24036000703c0c0f06041c0c803040b40040014034034058161002c8624501e2680c03104405003d5100080242001401034908894038100203514007a0080c0060f00081c2242e8480c0103c42001171998440710300c0c06138030010700c0c0320b0284110300da00001c0da4954000040700c420790720340c2c0b4108041d183e80342e000380701190002c1c1e5181c043c480c1f440705502c0d1141e0031044c01d080203100411803500303000e1030b1001c100b160b03e01500b00060700340c0c02a903c802140310001504194030b038542007000781c801c6400404600070034100d10b00354600700c442c4c0d48034640c42d20651700d002d061050244003107134521020452045c003030000c0002049030070240781001702118030318440c007914280d0350510074902000d00e01502c3c0c0c0241020001150a03210100040340c6a0400d0380000d04611400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 925120000 1250 925118750 925118827
    0xf0303010b09040213170106060e030307050d08060609040f05161b03140d0f050a060807080309150712030b03100603021e031f02040f0b0c0604110a03060609020d150605 74
    0x52000080c091b10300f60000518502d0864098041c41842544900c81d0b0002c2c0207210214a000c80c80709142501440e01403d2592a140050698003130381e9a0141c100d403501d418100c2c5448a54003540c0a226841119043c5e00c1104070304030342d0b1108244034000c03260007449062001038001c4001d09115050b41c5401401c0120a011507012500240c0000082c1c5071100e0912030071950074480c0700013400c00003000e0010070f800d192540d40c0d24440d0580304d0740a9207171200403441e80c1d540d04003070710b48240d841a5810203032002020010040d01c1c81d01407203031190103086e005502e01c0849118070412241c1c060824554201c2c10307003a07050b0081411840e0b0f605401030444454585030000310440e50341000c60f600585030340c00d0001400c00030b8200c0d00000401c0200b00700c9100c1c5203000142d060351140d80110b840d6400b100080104110600d182d100403d83e0307080c20000708044200350007400c07004420110801c1b80042680c5809110300301743c8510340114804024610025031042c8035844038150105c226000e0b2090b4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 925121250 1250 925120000 925120019
    0xf01230c1c09140c010e060301050a0303120e0f03040806060a050a060305130c080f0601080307030207120302010905030a030c11010b010f030905191202071d07050702030c18090f0303010b09040213 86
    0x4081260b55034201c4000700c0344d151381141001d1111101074404908540c144804100c4a4005000c054240034403070349440c07100030058005c0281508000c0a41b41c200307170450002c0340d9941140c01030381d0340c0340908000240c40f8240ba02441d000c40e6801888101810700d01402640109006041101d10b048032811000c0400c1c40c0079500b00082844c0c60041442d52010704116040c10b1043e041002e003500304004840120f640021f040068452001940c0040003040c541640144841ca9004115010201d034043d500d68060b4040342c00d4900030b4560840302440d605e1703614222004080c089000c240b03031030140c0f40c07030314071941c45181081e10800440c1c102028590414020303a040000403241e8560050000c4000c0b54140107a00040c181c280014600c01c505034100c10108100501240c100304003c2079a4041d55010040c1c030032405409081c0c00537039000c681c20196955421036010100e885100070310405e0380000003ca0b0704942c03055001d00c1c1003178000020400039600500c005984640110b07004a80c4514 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 925122500 1250 925121250 925121273
    0x206030403031d0303090706030b06030105012d0f1b0218060d0209040f060b0109080c010f03111201090c050403030c17120f06100306060c12050c0f01230c1c09 70
    0x10403000313540302d182c403420491402c40d482d0425010107081c00480c0082c0d4a900c01502e06490007400d00b586210300c00d0520000701e107a0080d0080d03240200300c030285541d50f0000d4001c000a0f50325912510aa4518800f2582a8000403c001c1d0880110903074011104c01007050160840c000604420540c1070f5a0005040c1a0003918181c0380945c0c1443ca15042250314030403040e8042080c20952481c03850041480e4549120800c40c42c18400c444040e030b0445413007075020b00c2e440d41c0900c08650705da020390081c020724601e00340078042d9514a41904030380c0c0c0902850944003100d03410390702d4080c81d4a01c0d541e0303602003004110442031320100900c946000f030802c41c03a155104446100311010140341620807c02050040c07d80c1a09151914000344541c96000301011620313500318142c500e202c503103801e046030203105510b4030302030074041d04101140910043d080b41414404031510201903200300c0b034a0152aa900b81d0b400e0782c1074401004856820140d0317000b0007590b5641c04c440040c036007c164075803002c01003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 925123750 1250 925122500 925122551
    0x1020703110610030b0705180a030b0423031b0c041b1706100e0a091b09090b092a03010902040819034103011d0c07020603040303 57
    0x1003503081d88004480d01086001c0c1e001003588058100d0a04c2c5032908410010007419803020400d0004410b00594110150000310910143c032481d43c0030351b60f013061080542c2c00c7c0d03421254011141c1120700d15014890031080312054110165203003004420382c106207402d481c14150181d000f00e840050441e52584a0000f22207600029807425840951004140f220301b05020440c8410702820b00401d80c44504414941c3d500a040c140441003801000400c10505a8800c940b1181030001c030940c152515903401150f02500c0d00c540d0405603c0e45148000d44009562842c1c120036810300041d00d840c9020f40502c0c01810000300080c5400c0f00c840903519980c400d0f041454400d40005041003840b004001c03001d91596814070704040141d02d07079401008001c00038070341100c080100354400c1d040b202d8002000d980000e4103000c101102203500c01c1c20b440e5002446144054401400e003145000c841413813652140d0084600c01d8a0700f00c02e40e080081d0303504041c1080c2d0800d41d4485218841241400f91b020f0060b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 925125000 1250 925123750 925123757
    0x80d45061515050a050909071205070203040602010f06080c0f010c0503191d010206180304050a030b0f1806010b03071101051005090603012a02010e060a05090601060c12081801020703 80
    0x140d09050b100c407042d001a1280100f0030600b00501c55046070700800341d44402404860400365612070b00c500b01c440403200340002e41c11501e04418008c0c9a9000001841200e045800234022020203600180486040e44103081c215040340424000d40c0c68050018441d0250506040c0f050040c0c0d0745690b807841d0004001c40b0380840e140118101c4060f048070140080c4811084001264148400000e45944015045400c00a10706460280c5440240203039806000301410360100310341e03171b0b007005c01580b0f0b0103880c00c00d1a05070200110b54a030304c01c030407070031250702c224002410140d20304140d0881c0d55000038185010400340c80c4540f00c4603c028042e07e03003e00c41d510000601035041000300030380400301520a43c401d1b89052180c50911022150401ea00e43c0054002ca14400000406034098203a001c4001d12900540040011080c51030780002c0c01290044200c4500343c1e21410f0984001c0e80d2040e0240c007800c0b002403074020b00b521940c0c249500860040e03001c0c0c40e003204242000d080e40c02ca01c1c0101e020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 925126250 1250 925125000 925125041
    0xd17031008060f0103081e160305041701060b12040201090e070237021507020a06120b010c1a07090515040303020c0303041a030403090e04080d4506 65
    0x60709002c201d03081d00890140340f41c0d520b6524640e100b00040c0b1440d8120746c90600000d11301c40081041e00192000001226444440c0b0001813400802c580c0c00b40c098910b00d00d000c1140040101030510030740040c2c41002410510700400300c05201d4100900420407410000c2c407000101b5803900c02c0510794000c1c0e0760381e0001c0c0179a400c603500403606030b8641d45403070401070b039030310340200719100528860302d1400c1d01600c912400041180240c600d82c03090f42c1020350450701541c0000b0f05c903a406841c403801c000041c0000c120001c01a001100d54a00030403004c0d201104c003202800a0008a01566400444508000803110345e51000701c6e10f40340c4040b003010340081021800f0424160140304004c0e001d2001c8000d18503250911404420031401c11404404021003c00040c04050146810700c0140c0706229a1a1103882c140c42c104841d0b500191074400c440b030522506003030030700360f05e212038110007024260080041d00a00c00f082e40010000050710b41036200491000200d422442003044c2c040302c90b402e241a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 925127500 1250 925126250 925126259
    0x403060606020c01021b01050703021516180b040b0d021c05070e0a0305060f0c0408070f1404020703120e10050f041b18050a061502060403090906050d020d170310 71
    0x10200581522415508800800f0381c082c6086e0340b0352080c201007420115100c860305e040c22441c1c22081c0c51110140c2000c00300b4071000310522030000d0040b0080d940c41e60202a00b0540c2d02000702c1c010301c075441c003114050000744080f0134040081d115410003400c0043c14030000004ca21241300d2402e047c460140e50300e1003881010341d401810021841c1c03003959818040752030741e85c9aa9890800401452090001402042c139241d0444100d03801031a03424200c64009440d41d250406007081c600c6281281c80d065007054020b030529000f0f0750702c096015101c5840a21000644034050003a9840721620340c082c1c04a20b1200c100740c0c1c80382d00c0c000c0c034010100700120300e828544600104400d0740b80b1190f81da41c550381009034140e005200302d58003506900208240c0c0f2010300703590160000d0b401c0f03012840001030311030b2409039000038807520841c000d681d640c408907620440b0804948181c054140c01c0071100003203e002d400c0c9124450f5100340b00e0a240d41c1c050500145131080ca0f000dc1ea100c00724903003054030810 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 925128750 1250 925127500 925127503
    0xc0a052d122401082803030e0706050307021e060a0b03010e0a06050604050703050103020303071e02100f1e050a03110909040c0801050606030c12060f04020a030b091f05010c060b06040306060602 85
    0x2800341010100824104485031756084441110100060001c0b0f01c2c001d080d001c0600c242c002d410403030449000c0350710f600e4407688e000e440350b002210868014401c419096000015440c5481150a4010b000d02410380311195100003404010768000e13015074a41100303001201c01040100744150013950001070600305281000251200a0007400030181450018409030b64080211180baaa01c03408105a24188110011114941c010041e51003190031401079241071304400075100021481c0c0e03400d0800490905a00840d0103482d1f0909e0000f0070a010203032115009074061440440d5925040341400507240010f6103a0008440c2180c80c0060800c04100520303003401540c0d040202240c0d41401c1d032404e103400100c54061100c2c640340c0002204003189132078445000b20000e640010b80f05643d1406e00c640d010300175000d20752400b4040c03107021000800161a01d00c1094801c0c11000d0b80105091800e001120303c01c3d68118292415695000c42803070f2591510000c00040d40b00d00800710b01c480c030303224001c1e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 925130000 1250 925128750 925128823
    0x5090411041e15171306050106080618040c060f020724111b060901120509061506040305120307050408030c071d0618180109050c0a052d12 61
    0x9449144891004a0100ba0844441907104c180507640920941e2024840c0242d0800c010b000f41101c1c1c03401001080e9a6400740300688901002c0e14170b00742105801199103410001103602902400c00c060003409418490301400001e01034a00c12200798644461500750140d65960750410122440c01c54001c00c690850000b0000000c0b14010300a24209500101e0390400a0510345100b50000606201568084c480c200d0245105030300030041494918451170b5a05420b4582e01550448040c0c13010071498400100c900b92a4000060303d82d44070500c40960f81a00081d0408c01800f40038000800c43c18420005040384c140c0900040500c0d5180c50b19103945041c000b100703000d0f0485040704001064030380165400800d5034500290441d07544a52000c545181e0b1001944040d500b0300000720300740300300069502010079003140c104248555541c108880007803a0409001c60700000d0035030104001d501750780c0903440e000c00b410031030001400c9500c1d1403e1100ca1580154990509080c5500d00040001c0380e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 925131250 1250 925130000 925130009
    0x3060a0905011206141b0904020c06070e0906030714040f18050a0c091a0d030219080301031202010905330403020102120a0b06090d020a05100203040303020613030e0105090411041e 79
    0x105202d05150b1b0951265003607960344103a0b0030500007501c20f41d9407115030480d64040000d07010b81d222401c040d10010110f130459001c0d14820034409000c56150b180100d034140444c1c1c0560100e12000d9144000d1101400b42622000341c540da0b1044442980106a09081d8174144680040c05900030303545454040140d050308250041e906d003a8035a5030690201c3c25040032440215a800b2002510345000c80c80d281ca40d07041c40b04400b107a0304088080124050285050b02d105006048881d680c503481203088950035480a0195481a003191905501c4a03182c4410104c40c00c0d02c031007403d190b04a190700d0940c1d05036021030051794001010040c0c00d5a40421035000340341c81c10b052050081181c0040e150b400b0b0404c9140c030440199220310119a1040c0400004200280030140002d4004a010b502c0360068801034016014a0703001500c0500c403a02c5c080c810300c0d81520b544a020024070b004540903008580c0c2d10360001e60710041d400d944a03601010304028000c6234940c0e0400c600c1c584943e50b040030940d11 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 925132500 1250 925131250 925131281
    0x1b08010602010b092a180906030c09011a0f030f0405011404020a15031803020313060c0b010b070809090405010b0a09060b042937120203060a0905011206 67
    0x38504000d03540c400f50143c2107081c1c1d003075030800c2c10a050610340c005241d02c806145a42c0e0300150092640943c51030fa686c6419003101c010400b9076920301403546a90049400540c08120100148030b60440d040c0f8800120320400002c504000c906410300000b6803080e5200e40c2150f0110b4100010003400340a800310101010a92520703d040903408500107805601640c200604902c1440d00b20b944261f100d1104080c80c00108021032080e0300b0065201e500040103400c1e84403a0200205800340a00c10b600c02d12035101013040b909038a8a0054800742e04810412269103204005119540e52142e10356070055000d1000018580a42c1c1c007008001a0107900000941d030a002007000180c94490035a000c03501160340e11030000011185e0300400c10b55440b0700302e01a800c04200308104842c0d0144040899002d002100c5082e0020282d824a081c02681160005030300150340102506882d0080d41d0001c2000e03003c125019107a2000d8820750700c007600310b14a201e01c0e152100b81400045d02a040f0882501038 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 925133750 1250 925132500 925132511
    0x405090309130203180a0c0806061f03091a100f1a04140118080105100f081c0e13050f0601030b031902011e120c0806010203041e03061b0801060201 65
    0x20100308140b03414031904400b0395000c400150903500e030500071030141c107820303059510340601880c3c012801140c0c3c0c019010a84540c100013040c600380012043d00805001d90104054250240c085000d13116001084130160002c241909031a60b4105ca01030180d2201c054466032181008030514405c885a40200f10b000c01c50714080440400c040104c4003991320711000c80c100044960010b80e8840e540514ac02e495150b05840041c0110b41980000c0c00f03500c80200580310a030361307220707660b03464541801046120b81224054032520100b0b0013036262440315506045150350180000101c40007804d44003418040c1e01c40040100c0d915400c07811640c4603209007410048500004080b9544500303041e0741202015501600d0025680039121480224029140b0a805030301e241030014a0311142180c2c1141980c108030070140380a0046841d54420070060b4000c1d410309280000c5440050756851004013007001d00c880100c00f142c041d01a4940d00c5035074100b4850604e000d242d0060911205a000c40d08592406 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 925135000 1250 925133750 925133767
    0x70e0105040e0603010b15070b0106050306220b0303040602010606080c1204080730020f01050114040c0e030f0102030403260601031a0a0314100e070501050c070306020409090204050903 81
    0xc015201a904038940822203a900c00340883d0061041c02d18003540301005040ca26446003030b4070000c051030303803003410004100d0340d88500584d05404180d500c1640085006059074818a0340c14400e2010003c1e42008501076103007030b01007415580607401060050751038003014409603802070b0146070401494040146441c0010b2085a00c8600c050801002c03064002090700500c01d010441e12440e580c1880f03c0e141100706000c05080b81031000c00b800025000300720340b403200b6650612030141200c41c2c5110820020380ba60301000010181121030350140b02045201d200e00da01c0800c0703808900342d021000140d8074101402d015003000140d80751281c4a4048100005a10000a600301c0d00b241080c20046000b540b00000b81e6420b416581d502d60f0000d900c0d000c00002d0008001e1070f0605800d40a06a8880c0c0e0444e1041c50161070001c210005030341e0240c1c0040215501c07440040c50400d00340e501795120284c40340d881c2c20980e4880e0b03100c0081790352102d00e0702017545407500c50560440100f1780150700d03200c0d10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 925136250 1250 925135000 925135007
    0x60c111c21020c0304050925030b010908011505150c0a12090b0a08010315060e040b0a02071703090705060c1b0307050d050f07050406050a0e0703021606090209070e01 73
    0x140d14040c20018059180400200050300c070649082509406540340c181c014259503581d0803500c100c1c0c1c8260100c2d00402c80030180c0601407180a00d400244800e40a4035010a40180816016803410042e1200700001c00320000c0c42049415201c40c0148840a8544000c002a400400e003030b03440c940d0310800c058402c4800010300780c0c550030342c00f61642c903803070725010f0040d14406503a6021508803100060115102c80e40580c0700b5040c3c0e48910369444c2c85941e8080180300b2600a8080c01900c0e00d031800c04200464036000389654040301808003d450a81f40b66070b014444030001d4510b010442c00842808600c400a0010038040c2c2019595a403c00f0302d44039110f60340e1504030091480500303200d405010035442c140006c401030700003c3c10109903480e491501c169500c244d120006c046000320100401e6038a000c0c050b0384200c600c01850005a9400c15890040360b010242900c4141a07081111200c644501c1c006060928010700300040c2809950050140b800303401040c05040041c482a40ca4150380c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 925137500 1250 925136250 925136293
    0x30f0b03070e01030605090307080d09030207140d060209030f0f06180d0909020c0a1b09061410050325080a0507230d0b130506031605150a03090b0103060c11 69
    0x304903170081215298840068254840c01c0340c00b4113046800204040400c55070380111128500c0f030341c21642c8140d03423411244545503580d00d02c15480540030914901254031600a02400349008003601c12410303d6218160ad40130300b556050850303820110801c59844007003105040c9006121000d0b181362001218018400a801d00407009503c1d40440c80100703c00d02000104052507008140d0200c45405c002142a42d004a20448a00c541061004901504180401100800c0250280014202c0300c4d0040c2c40503080108207050309240403252000f1041c922035240600002c644444086090402c10f02c81641c1004151105200100d1026004508001a03000055640d0724a0a031150748611000001c2d1990f0200c03190b000c040c41c4411000c564695010798081e440490403a03800004403941641e680303089101c1c0c01c1c0e00002c09407840503004400340082c43d28401604c0c0000341990250303103a005584003a003066890b40d82e10320101c0c0d130050704007604620f0190070f03000070701c01217241c1082840c1181 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 925138750 1250 925137500 925137503
    0xc0d020d02012c03120901060f090207021c0f0b0c1206030321092104050307061b030516060e01092f060a0207050307140307050618040e1903030f0b03070e0103 70
    0x500080f580d01d405030f010300544c2c4410700c1c200240c0c030050901c079480b07034040d045901845041542c03040c40000c2d500590320031120341c01e6018207002c0a00d50031022044603089101801d556030410003140000207000e10317025501c00d04003403421540360481c0d5040d510760b0b2000100654040d80c010040c0030360055090310131274404214410210411703942c281d12142044600d070100e02400080c0e401811004040a01074400c0d95000d0701141d0030141d45140841c0c600420480c034007024030b20307200e100c00444e1242008083d404101080c0d100c4000507507031118110b0705450f410155503551111030030304200810f41c035038011f40d003007d04008042c50a807100c1c04490102200c03852140758001920402075000740306200c0104001400d59030354641d509824013140d507100c100343c1c1c428060010080b440d450154203840c00200c038401da501480c2e84007401c1c04001e0407100c200c48541c6c81181110300355403689880080e2034611a0382c0200b00106030748103c1003a46c22404090340b0a0b0040c590920002c0c0300b031240f40741140d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 925140000 1250 925138750 925138811
    0x6021812190201030f060905061f0503190213120b010801050915060406030c1d0709140607030c0506010b07060e0d0503070c06090203060c030f0601031a040f02040b0c0d020d0201 78
    0x15400b4030050b002040c0398921542010306020340029609059880a441400e00ba1360221040035039440842c2d09070b0300c95103104080744051011580120913045851f8a4900145d8010300d419106a00c0c1c081d54440d5600042680328404449000c000c00305007503d004041d00e40091015013040001c90381c0394054000c64011081004001034419595070308084021030b0002d1302d400c42d0b20388421546481d001c40d07560340b00f040c4110001103001684140380d010200c414100100e444141e00a0411040f07901c105019410840a60f00c00c802141092201500030031440d205a950b03040b8500d00001a20f0038442c0a0025400c02c2c980c140201d40c002c0300710796006403203151150303c5031441d14010005010010011b505071045900304801d840031900114006c418076400159190f03140310045069901090503e0310740b02c0c8c4500108650304064000c01c00052a1080c0507040c070f41c403403810600c66040f0050045103a804a40d2407620181c042c40303030380085481031009105200c0030814864a802007282d0141da40c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 925141250 1250 925140000 925140043
    0x24091401150339030309150e0d11031e0105061e091b0f0a0f1706010c02091503031c0c0906090b1b0102120601091e0b03070c0f06021812 60
    0x426140700ca621403025268510081c1c003c4d03da00b0001c10300d424601031102002c001c1082c0d10b907114041c11520015401c0181416a640b02e19a60701c03880030001070840e90142b24000041a06a078003502e105210b40c3d0010001a4a181410420040d065280d03103110049c1002d10f00610b1075120160070f5130f403014080600640500c6060b41c04c4c04144508074007646034030400b00b40400c0c8640e010244a2904d001540c41780000c003072420740340904250944015020540800107a0010b083c1102220360107a200f603200600f501c1c188001c0b07801c42e8050f002c1412400b20f409020220000b45105054111040d0b01d09600e103241443c4020302444013602440840c0200030440710002e5070107542c40b200800c44203000795250845048c24111001007503d03018080f4418150101d0b216201940310803a00c081c900e89080c0c0c0e14504101c815141d0701c00b42861080000291118004c038006004241c3c100d4894400117a4400300001040744070045000e05a00c22448000c998100034000510b29040c2400054400e19 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 925142500 1250 925141250 925141313
    0x312040804080601090603020a050429120706111b1c0c0f0e16140714070b0708030405070e04020d06050702161413050f04240914011503 60
    0x40e405654400502442100000305400382180c00c904101e81c03083d540b10b00515240c80070401940c603104a0071999505480038003c80d08504400c031200b00002400640d128001c59042e6810005c0940140c40859610500900c00160800090090148038245911500842400540c803000400810a042d0017500c3d458000d2001c180c24000062100220105003244e5420300c81548110440310304440000544980d108035008060084200000200d41840c200c603076030754401c0c0d000c00340000300045c2c03044500100b031041c560002816490302a05519031246414903115103480b40c150814111340014509000041c0c450104008000340d000710080380c959103507103040346400c50403112060280d0b09640c0004001c0c90321000d0f0100203100395102000d82018880d00420381c1d02c01d03130b1030000c1881210f000a0119080014468030920303001e405205107010b0036191810b54080410949558050082c030004401c4240709820401205d404003070304081c43c0d900ca1141d04901c0322000043c0e00c802c40b58024 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 925143750 1250 925142500 925142513
    0x70c0801020a0e0111120f2511030f010c020705040e0c0307140112021e0f0c01021206100e0a170a0206041203180e07230a17010b0c031204 61
    0x1005408104001c640307442d4182c0008016085440308140418800108242c407840301041c10494200d81e02e00880c41d200c11410341d01c50590064010810807071070716000c038450074000c0a889002a010b600a11404401c040406003880311018041e5000c0c1e01d00b8803901102c1c5d07008610a011258121350000d83e107614080e1150400003100c048542c540114200880c01803250000d0090b591420380e601e820407501c4c120b0200c00ca1140d080031801029080c0c14400d9159407080c0108600001040003e0030f180301180220f00360b80102c4418803140603143d0820105040501101c030440c4038920307040002505c0040400c101c85d049005014289080e140d42c0c00c1074003410804818240d5000d040e2a558075903d02c1300e1a83c00c1c840020880000309034420032900120202e0b44902a01d2254200541076261158180c680f021b03982854036203a82c6c0380c2043c10364894540058541c0700400e48030b2003c0021024408860120f058001c003403500f2050014040350318000041d100c1840311807000359400e48442c200700 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 925145000 1250 925143750 925143773
    0xe0c03071101090510060906230a0305150105031c0e0f040b150c0d0908100221010306050405070e070507170403081c050105060a05160303060b041403060a0203090d0507 74
    0x40ca2039030804038010f0400c200040c2d8180046020380040100503282c820610a80e40030344181e6001d80c0380c0ea20082800e01c42d01d606119021130040c01c1c0c20032143c0d207030790301400d10596030042e8200101040040006040901040040b801454030500040301200c4000d0700154903035640900620a90040c018252216480100680c900501c2c5454a00700c0300d1102003d94481018807810740a0302103542e09881c01030902d035064501c105e019041d0b501a4610440003074000c0400101807490a404170003000a412016034065801003001040303d1401342441441c1540c0c90340700c940d00c010144100710104e176010044e502d07211761202c00e407141e55070b04605614041c000e0380c00180c00b1300c800043c407181c42d1b18010004010546601d501b8019070781e95004111041c00360074151000f00d9030811814119403185141c0c0700300c007072003403c000644c2502e849502c0400c0d0010b03000a01c4250922a081042d441e0801c0907950062801500354510315208001949078401a6001000d010b000728024003005980c4210 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 925146250 1250 925145000 925145027
    0x19031b080d090c170a05070e01150c06060b131403060f130314210c0702031b03011515030b041802060304080c010504050615030a030f1110050a020306190e0c0307 71
    0x410481070410700940fa150903421500b06c82c0c0e4464250005802500d143c480740c100c03040840b80541d08805030300141c85000b1030360001c66403107959100c0880c0c0034110001510110140301d4082c140b050520000c01000d01003481d1040c402d80c0900c04101c280d6200da9001a800305102c035441012360403d24090300c00f80c848006441c00d4401c00320740301071356465079400000c076a0303a00340c6a00301c00c0d100c44500f00082d12407520040e4140e00206901c50f0642207004500d800c0e09009000007440e40c04290744a80114115080291442c243c035502e000c440394140116060000110750030032844c10344030a501007003005003500a004100c0400040c0601034814150345849403698000e110920340b629042d505d07040b0440700d40c1548092410021102d041c0000c01606442d03050725011290b60340080c3c196805c0200b85264080c1e8070030301c490380041c00004d00034203016024a0402503120301300042000703141c034a9100c1c0c00c10110741c103031010046010350701c8030160018002c03603203c0d94a032100030044070742c110003400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 925147500 1250 925146250 925146269
    0x60e0708010f05090d090303051603091d09060702010c09090506210c030d172712090a05030111031306112107020601050d080c0f19031b080d090c 64
    0xc44011081c890f40040d03100722401d8080c1c525503c2c0c058002d030354040c0c0b80d000250000b07005116040c4081e180b80d4070250094041e050800203140d440080e17a01410460b8203840341c40800000340140c41c40108080c0350808a24002480011080b00006042c401035215440304507407224041243ca4a41100305690000030030308400d400040b81180c2c503598120305016600030700c03030090000e00c200e214106040d001940d50301140300680300c0c03540315003248056099185691907080c00003084800e0810800510b15642012113031954000c604200000e01c6030345c41107020b030f4100185005211814802c60340c0c040302d4407964042e8682d0074242000181501c3d42400981100055a854400410003c144501c45d80c0803004c1002d0355401c000302d84a040c01c2c42019000703c1c0b400c2d0703441e00042c010710203400900960f404817800302a820702e00c5403a200c0840d4801c1d540c944044040d03c1031507400820501c0e000c41b15400f410300c0c211030b5642d001c1140b2907202c3d09910f10b541d40c1c101c0000c00c07500071030b0030004020a56 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 925148750 1250 925147500 925147511
    0x1406032d0304170f070612020a030632030d0807270f050f191403031204031713030807202e05040506010905131707020405010b090d060e070801 63
    0xc5074a129405100a103d25070700c924038111443e00b0300026101c00703440307640c0c1c5d031011320204c903c56000294202c5072000c1c0c141522020302213005003951141021402d00604054240b031090101031036442c0000c1c442a001e038110b52000c02d18181c109440c1e5400c114140341040c920b06081e02d0001c00580c082070078020841c1c0c101800604681082c903980240d4008468004079075074248200010042a043d9a488450040b074081103c096650409540e02d00054150b070700c2c103034682e1000b103065401160101c010541d4400c070b5031003d21203a000e140e840f406090310103900100b0303524080c1041c24003d00c45c1c4100a501c405407610311006060540d0b000d6140e070304403007080900741400c2c0280d03d00420385002000d05442c40221011680c000d6a0099410a000d002e00b6401c014845e4003900300100302c2108141040c80a0300014440c0c100700c1c40c41d40810426035140c807020310401055035010780c4a42043c02061000f0038865650260003100d1a6210f5400074003460341e9100e20341451000d1f44001c22551801 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 925150000 1250 925148750 925148759
    0x60a0c17040f08011a1005041a04080f030c03090f060c0f07140415030b1503060f0f06010804031e021006090207061b090303081b0705010207061406032d0304 69
    0x48054825142c90030754011502c0e8641e40741030700720307007200342d07001e03d4184108003016242c240b100140d0140d40040c0341130713442c1c107840e1800741c5010751600c12482c2c01c01d0000101000409400c0c1301c11b8516440301409140703001e10b0000400c3c0d03079000b2614041e1088a001d2031a03042c9030b9818086509a40f01d480540b0102c1c180300342c41c9504d0344160310600b0f01500070701c001611586424401d21240104100002c100d05045850b84010080028002c1e0761903140c81c0810003040c1ea0030011075100744030403a202c20040c0340041103014818005840b042c14481c44034280400260000d41707140726404000c1c5249282c03001003000303d1814810040d5104502c1c81d00401044142c0190010720b200307400350100748035840091003501200780c000c10b1030600080c030040040c07000900c98500c0d640c002144000d03080200d50550740c18102c0740e126242c01c441c1070f03500040c04030400c000d5001e0380c17001c01c9400000030790724030b040300200c1d031520b005143c2c8480c40e444442d0300110303502e003205900071075000440c00c41c0d031102c1d00d9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 925151250 1250 925150000 925150043
    0xc0201050f070926070801020c0d18050d150b0406080a0c0b030c0910051201060c060e0115060507030207030c0f0f1a09010e0f040f0b040b040b0906060a0c 68
    0x90710860500030310040041c880c030340100300b48400c03100d000c040d048070031405110088a895050301114400e000d440e00c0050701080c00d0000d00041e44a65000c0d000d45101c0c003001804007441d004040d01d1050900f8820002580e808007655040380d0003480525444095244ac1001029220001c550242c03034a00041031200000a0350000148619000402c0725160508451140000c4072aa05003000030007000300181040030381c0e046c245810f0b0400d01e0408510910b0400070b000241c0251001800c06c80d14a0144a039500a00c0740b00400d08001304515050001078406000d458020401889000100201090310030441d040080d80c0280c400035107151590104442843c2c6845200904407117842c000c02c0c40e1402d0844401451000701c2031514002c0c3e42801503032080543c0c034484c1e44c0014502502c0c6650b440ea40141002418015000945000302c401040111004005030178043c0e0f15248200d0380341d0b115620440e402000448001c0d40714145468111400685500001e10070103120f0010540c0f25107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 925152500 1250 925151250 925151261
    0x220306021305010503150d021203070b0f1312140403050708030306040506180412171602010f0207020a0e1515250f0b07030609020c03180f0109170a02040c0201 70
    0x401c04039101e00259120011210b81c001900c1c46644d042c0031612114503841d00c0421070705c140f403015019595030841507a40c14210b4100c00400d40e5000350304410041e03100c050f000392507032144590030304902d11050354030340c1004801d007540c04038240030503401d068590b000c0741c0065400031a8084e04031407020752600310140d200d42080e1100d901032030400001c11814600407500c50203d4101032031010441ea0b468580c24055080e60855000303002505400103104040e04800603c0384045802110003184c100c04d0003800c5600c4180c0f040c011500c140700b00401a510720052070111441100c004c0619144c01c0c8101c0082d200c8a00344503400814131280d039410303035490b0015156440850141038140c0b031904020b00a00302070f0820040c8988501c0c0049000a80d40b80b100a4000d80203180002d003850700c94210108aa1010312210415030022511141120758100c8d0160046010360b404600381c0403010001c1c1950045000301c1c0ca4481300b01c240c80041c9001084150040c9800401c1881000c0144c1c038040d00074131 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 925153750 1250 925152500 925152517
    0xe011515030e0d0e0d02060a020d020d051812010e01051608280f0e0601086a050603010b010e031c020f0d0504080607081b22030602 58
    0x2084201003068040c042e106410544410782c0c00350240c82d00300d050460300c8140c00c81e030555020030004504400b41c0c40e0710300541130b007075825001009086c00d101030107450078840d2074004e02080010840c1c1d941c519451030031295008002e13605141002c3c05c014501340900001e8560316015807030402003040c3d42c0d007101d00c021203866107619040740507190060b9100200300c01000040c1d03824a8030b0612000001c0d04c1c0e0091126480607540000c3c107500d0300d031031103080ca042a802124980c1c06035100d440d81080101d4a15228208119120f03800d01d00b4140b01641072808a920648c0340031106000317044540e00d0b04001915000fa61151014a08005840001004165003680c000d6103000404e0b000c0d94040d041d94040d5400041c001c20269407034a08800303110214148400840c0603248aa00d0011010800c000089180f511880c2e22a402c00f40369902d001002070920081200060900004043e000b15541c912070795401c01603070717484011020112180885103594050b0383c84030800018400d03254050030182 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 925155000 1250 925153750 925153769
    0x5042a2001060503030319241a13060e01020a0501050f070f02061b13030b0114181003120512090a060c030c0e040513021c0b130302060f0a0e0115 64
    0x61401820031800c0311064082c00740c0681c0104042030040d4401200302440c42d6078018040340c987d0034011055072a040044078208000c1a100041c0160010443c0f00600c03038407007544213070920030000c010011507100d6104481c2844051580a0b0807644240100302103141c20400030f05c00c60801003846900c01008030b40e28070000e4409440b40105a01c04074002d800740c0c1c2511b68280c440303030001600300e289504c10107010580035501e003030000028000160660081c0307000c111340c003490a000000e002c000c500280b41074070002403400c20440c0700800441200f00b130b80d802902d5070124296400d01901c840c0308403466440107900341c400f040300030031001424841d01ca10a40c014091450358860030b900741c8420b0592440801c10702c0c5149480c40c28946d210382d50090b1900042e443d071103415004030381310a40c2d07490344010b440240c003140701c10f10a40110450300b0211b01142400046440d4500079200d034000380103226213600c4030004c039882c80040c1e088801c80e0342c0e4003c001c1290f10022101c007011281541314a0320030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 925156250 1250 925155000 925155047
    0xc15150310020a02030a08060621060f0f0109030807020112090b1009020a050d1104030f26190503100f18050a02180919060315051b0405042a 62
    0x301d041d18020f0b00c09101c40c58000354100020010240c0b6006802090350f60408800e000c250b2203405c542c01e14018040100080783d0355818a10180708811000702c1c80503004040403d00d030147c41e41e10607088070440343c1001000d511800d0324170041360a400503480880e0901c2c20b012140050010300f8002030700170064406500c04550b0303a00c610320243c1c0601440c9402055007031242c52500c0341503030400248001349400a40c90b01d91241c1d502021445c003040300343c9083d034403205081482c1501c2c00e0815102c1249120003400e041d6201c8001c0c0c0c0c044000403403c070822002001051541e04030328251009411255840c440c860f031507031440c12082123107044600300799040402044145410740700722200c1080d051080c0c030000004c1000d1200d41c5101400c0d01c1114621b01601d507a4052051103030101451081c00d0419011a80145140603148064031544100c2000340701d00d2500075141c0215001c49005490218114410011001c190b54865400c003803402d150151041c2c8155200e4881411450716201c44800c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 925157500 1250 925156250 925156273
    0x151b0c090e0f120702060403060501090c18050a0303031a09070203180f09131502031612050f18100e030405010206010803040f031e0807120807050c060c0c151503 71
    0x5031010030ba261508070390451020782c219400030500419849001a1404d4034080d40c95a0b400110740090703000b51a0581c0d940b105684003036010000000402208240103a22804c010008445503036620004052668030f544032103079103400c8000780501070802441000f65182c0850040c0d201c4e403210710409041d5100320314510191801d40c20415500501502c002c0f15035407051000381c0304160603403040e60908405100c410300385429000031440b45c98044034481c402620040d01402100801000462050608082000d01c081501d8426800301c500e01c1c0d140e044c9020f4201d0f060515928491072000141450398501c0781550003c0100112542a230071070b010350382d840c002251280503600442505e05c41d02201000841c9082d0700d4411100010b001d144540340d05e540c2d038241a580440f00c216038001c1041040107059030064017042d4405510b003481450314010b22183c544502000381388541d0382c2e401050505000c0001c01880384101382c4075210b01040e01700345003c0d40251401200d0940310b40b04601400382c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 925158750 1250 925157500 925157503
    0x60c08010510090e07020a0c0f031a2e05130902090c0c12070204060b0301090e0d02010c02030703080a090b19050610050304020f1827070f151b0c090e 66
    0x2c9041070b0341e8403481c2190a0810b0a0300192000e0944411442050319101c04a880d00024100404480241c490090714500d4150503400d05890018840e691410411000a1580220050107004032a901c142c412901c0500506090190429500000d41290320200b6078615032081d94254000c9540da40f055540842d114168400c0310ba2868083e0003840e01915000741d8100500411803004101007503040d10f40107982e1481d0426445440c4450b11400f03103020f41e00b801d111140c107035407c5100030f00c40c02000c200f01030341e2407107804c0c0000e00300f1520400040d401c01d040d604c0502c0e031a90001e1900002e0400082c480c1014a2044040768075902d4100800c400d0b14149030118201c85040c2c0300c1505654070780e0200310701d0f02c1c00580c10350f82040b04040104d1543c40c0701c00546201e104c8090104000360224501c1003007200b64039102e183c81e50302032141841007d004020b00390440b0b05903a40d02c00030a03038140007154144c0300701003500c1c02100b1649842c010840703e10010b00a5950b41d5a042040005904006 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 925160000 1250 925158750 925158769
    0x21b040209210c03031602040c03110f1e1303030206011e050d1e060204080c03030906031503070f03121419030b280303180e0705031909060c080105 65
    0x1035501c810b4429a0800c81d0032142e1160a5406854055074810a64803011904603840101c15128194802d241082180341c1803203450080303086480c3c10014400710110440c194403511a100050300340100702c0e0281c0301420342c4000c4103603400300e030b48607180d11494a8014420034940405c5015028050000c00e6009001c2214a84038805000480501b0b140c1000d00483d4820280180d4612458008144011850410003840b0900c11200166030b1482c1c01c08040c00c12140340c810341d100b900304101e022155030b5002c05a90700081d090388243c1405c015000000d181c00c5496005d40da118000036000020305c02c04407403500c0c00241685520030703501d4810301c0c2140c852103410200740c1204140020588013505c42c0e070158096240103032442c11800540a00300d070044080c0f62a0811114080c5424000c240d84020302c442507031040340002700518140703200c0306020340e0010800b408100c0302100243c88603d0021038078038101001c403001c000f40809070911101420100281d6008260b46c030740006071074145805503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 925161250 1250 925160000 925160017
    0x910120f230304050103090f08071b050303040513020306041e020a090e09030d0e030d14010312050322021c03020105091b0a09020f041a07120912030c0203070b0a021b0402 75
    0x6140f4103828400150b00070246002c0545410b03a007807054500242020008104142c080c1a00c900e00c50300b1000c800c2c0da0b0a1903508264001d8101b0f11040017140c48001d50824a031401420260302c030340d00c52011400a055107600c104081c104d04a0041c0e00c0081c941c001c055002940e0307900f0101507140c1100d81515101910400c010b5801008182c0d0807821550208411509110641f4901aa07000c0200d05581d0880d404402c0c0400079001001086004c1e04e840046107101d040c07150940c5404007801c0e00d600f00d00158949a00044d13002c00086507034002d140c841c5d018951810050400440c01d00074007c00302202e604039076118502074403035181e0640d0f0791150580c3c1c008009145c80360800c005040a5003096103da0f642d00d106210102780c1082c8042007441c10862000215100d0b0220309014040010344074208050141d600014004407100c3d5011091594050030044c1c1902814030119203868040d074401404207202190349032419502040020714500c0da40041da11001ca8442000101c0c4203a202 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 925162500 1250 925161250 925161253
    0x708071e0f08040614150a080a0206040e190f06080606150f09030a080708120f0408040312050d0507020c120105010803090f01140406080a0509010213050910120f23 72
    0x40084000e2040b42d0307882d40144201000300c0c180342d65149200301c6513001e55804a200001002c44120f608004509000800848008282000305600400c4041c4541c2c00b400e074003200c41000147c05000280c4400c0910a200c030303400c002d90b82c4001c020a0050003e4000d40c00c190141d072020803c1d03803802400602c41990203079010391410b0320034594065580e000c4000180c050180c40101d1021407a14009440300034000c0965654907000a030b2a2440c401008040c011140002c80920010800310420382e0240c90348038244040c116a0700000ba40c1e01e01542c0340c250344c0c40341040200b0001542c003003039091103003801741d4161982e507500c62541420780702e09002d4103640350700070b120b0a100c0f4942180710740c90060060420305000440ca06404000303910a03004200440d00e5001480700d40442481260b07030208441000314209502003880003034407003240c07141d2881012040c1c042a074810f01030000354001c0ca2540029501a8054030300b00e10b84003201c0000340d683c007a1000011007019a84001c03170090030410300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 925163750 1250 925162500 925162517
    0x4090b0102150f07110f060703110c0a1106162409031b0311151b180d0213020706061403010c0f0c1b0801092307030303051306050708071e 61
    0x1d18071071040300c0007002c550402c482c0111a800702401403106c84950014900039028030300c0d0112000d82a5501118181c2295400304503c0243d2100864011240340e0301906643d40840c0013000075902e0301032000078400040c00300342140708105004002040c400c00d0800942c0d402407048000e0b4040b245010f00c06004507002c00078100c6c3c40360383e4030340054069200b410001c8519003c02500c500d0400d900c4024442e201590080c80742c0115105402114066010b00e00c03403905840c0c0700e01c0200803404101860282c110346a0907011959914200d81c050410440215120440782c01d1840103080307203100303002070101041d031482a542418056170444c02d920342c44692410480c614200c492a00c141000e503240c19034403811044240c9000900c0c0000d00320100040352011303082c00d0411520b281003403018844604102143c51100c40070032248110394060400061030f030b5540b01c3e03465202182500c02000140307088204041d00380c000f0101c2e030040030a030f618030301582c11403c400260118142e02c0c803400b0a8510 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 925165000 1250 925163750 925163761
    0x3020f1b04021b0d020a0303110712111c020a06060506070209040b07020a060212250f0c0f020a060305040b01080a0201020a121205040309060320030601030e0304180204090b010215 79
    0x64000300f61520281000c0d03864464280c1c680d90a2505030708100740141c1000c07220200780346c1d050190035002c010301055a03250040710758400000c0c02030156546c0600502e681d40800d5540140001d0100350000f880461245081800003510780039451070441d6500c1ca040c5001c1030505202c0f00f914125540035084500c80c1e1215107801944d220020070680840c070842103607c000407080e002622040313500182498960a010f2080e0420080c101200c102501e40d0124001200b0341c4904404426161360500791052491820581e1002d00c046030040c1d0082d4040c400060710300e078540c0c440785c4941d014012000d56039886045140d1501c3c5043c40117070050b0700500180d804101c4455191800201c4d0741040c900e0642010540360546000b140c00b6404200d4400317003004401e416000314a6a08981e504420641d043c0800c118070500015042604040c1d07181d120700541441003040305d0103800c0c80001001c09c40c98003c00c01d0081d50050007001c1c0b10364148821440300e03500000b0242e103282c015070b4000000d42c1d9403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 925166250 1250 925165000 925165009
    0x30207020303041707030b0a0b091f0e0115030e210f0408100501140a2709080c0a1502094002030a061a030c0304051c050703020f1b 58
    0x118106a03454042080009030b40c141e5100a01007000030107024240682c503504003070003140d8005003d55000c90a01c0c0840040e076683c0140154450b03e4079001c0790726680413140700c00d0511001c4d0810650302908100200d0203030040c00c82c03000349450594003070100380d000500b400d4685181d4507003c85448032986200d405076800c4006081e000c162100f01604103540d8400c510700e005079501c084118156075000621503042c8011009804100030351381001140d14012078150000e6032200491103803150b104003400040201d8105203013007600b00d840707103480d004580d01854807201c0f044811a82801034005103007000c00715001f40d410504008040c44480c294481c0880002d0011143d10030f0785064511029040030041c0710004503070400e41400607101e10b01035036100c041f01c5441e0001c0e20541200c0314421200641d4200311303507002c80d48141e01c0b5183e84541c035005191007003c444030700741c6d448804071f85031030305600002a00d915800b99007203a0b91545905201601d80602c4074a0980114240c140d0381c0385400c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 925167500 1250 925166250 925166257
    0x507090b07060509161e0f0503120d09050703030816020a12050702040f02040f062309010c0501020d091a0f07020c10020a05010c050418060e0f04063e190302 69
    0x43c01d004da440745c171011020a660101240c0203601548203102e020045140b8aa40c03890142c021112004110390070600000d58402c1c408100e400d4402000032000840091900a00740d82c640c8101190034442d10781c900541a02411103000c800700c090030003101c1030356100107003034000c15800c02c444c26000301070400c040300c075680b1220083c1d8019441d820b10310f40e0500c0350b03c002d000904000d10301c036002a0620200a05a020307070310050240904880315640703070300140c0b011691750701400d0800d11038155a51074600d002e4002c80c0d5412560700c0c500344820080c403600e202c0f41c864140645090b10780725034600e000d4200d0007809580c44030043e401545000320a0400090300d2200040d540120b9005648685d111400d580c141d02034003001400c003040400c201c5856928061031110400c00511030582411a06c04585e070300142000080c5409002103000d10510380c6c04079202e000e5803040110b440040008907501c10701046410003860700e8a2081e014664500c900342c584000c41007421200100310803008402035003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 925168750 1250 925167500 925167511
    0x30b0603061c0f1401180803010509060a090204180e030a0f18090513060b030a0b130c0518070905030109030c060e0717010c02010b0108070c12051606020304060507090b070605 77
    0x1001802d86802290f600640400514407601c4590300000c03007100c403e030942d00c0c000b071101c2c80ca00e0505d005000249480083d82e0558501707440d501215900d00d00043e8504405500c20142c4503c00640841c05001450003d10550b5440c0002e00580440440d4103a0303901c00e40c0140d800041c8410a1b40da2117501c5010410000c5c0b04643d2003d03000351320350b5040022620203480c0c000700c41d2000301c004400c012490103030f0101403404401600c03841c44161544032001d07100412501c041000c6a000c0006c11003d2031b40c000c042c1030090b000e14958a206002c45001f8241961480c02241e8613203000201c510b014010094920f41c103569540000f42e1a949000191800008000b2280103144020070251110140c2000c075180305800840c10744182d110190855030744614442c1089100c0c000c03c164560044034802031180e101040d01002c0c0d50004046035103001d03106019800010221104003805900d4000d07501881c003070741e0200566161100f06489003102d610811403410802e10804000c1165980000c2e40034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 925170000 1250 925168750 925168789
    0x30105061e01080c22080f01020f0f13120f1a190e0705042a031a21030d02072904150905060a09150515060c010603081b0d030b060306 59
    0x103041860211143e082c02c902c44215080e007104108106c40040051060700b8507681700031480e002030701c0c0c0e41d803600e0700c41c9030283e0703180c001c00080e205c4004131039005900c010106214101c070703203c421b4608100c0c031040101c8143c4105e0b00e41aa0038400b00b41000c00507008a1100c0041807915a448140700301500c500a8010311340e0140c07c0c80020961503601031000710036140105990f19003c9801d840d000500300854402c01c052400c0214461000b651010a6000d14116041504066080b00c83c03489240c00580d089910302002c44c401c00500c49540251001901c9503003140120f6142c4604001110f15110030400394440a20200700400d454202e058414180c2901c04601c0d0525a03c8680c5000002d4585070140c5648044420611842c04034400c2c411706542070610240c142002d240304066603224266108440000704217514050940c4070700c000b0342d8030540203921192a84080c10300f50b240c0c1c80c090309460140c492100c410320700c03034865003d607048010306550642d100d0805010190002198625030f1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 925171250 1250 925170000 925170007
    0xe150a0503010507020a02150313080903033a0212070315030b070e0405070e01170a020c16090b104a040605030f0703080904020702150405030105061e01080c 69
    0x12500e00f8090103101c0c1c15241c004084038443d92044c4000110a4810707014100f5003441803100401c004802510820341041116444480c003400003407c5110b01020420100d480f106204030280303249590402051802c0303090704c3c03c007070030a00c030000b07030f00c545614844044202e00006640c54002d62010320107200c07105004402c1c40d201e594490071410b05886540219120043d400c181d45001d0091a90100e032624114908400d00d01c0041d00e500c0c0c044840750040d5107100f00040f08402c05905465840b070201c8220b880800308899900d0390b02086001d45808241003100408180c2810443c0040100e55075966462502004040076010345103c00e01c19407001c06607000503141c1603404d2000d050001049040c0f0140b0989804010890740d152707000b070f0b0003a04050000004101c001c11044100c0341c000e5600350b41d035041100014000c2c418880000e51004d2009080914084008041d01c00d89406400030480b80c0c80305030801c034070721501c4401c001814010a15128140d4490200f80d50800c4a845200e0704 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 925172500 1250 925171250 925171259
    0x5040302060f09090a1b12180b0405010c03020f0415090f0303030e1005091009060b0a170d02061302010f17090102070c091512030c0215031602070e150a 67
    0x1c15502041140140c070300d003c101800d07113240c01102c0b00d41010001500704410000001041044014501c01000384207100880302040d02064000d8120403d12011000b9800a50b1400d00d208040964040e24190700e881c2110300414000d10071609101d82c003e00103410146400103242c0b07481c1105000341e0400000c0203001800250100c601006907200386c4011940b40c0d890301100d46450409161401258244414070a0300c041c040f070048102c000c0d0a50103d80380c041818110003800c1240101e82d04050911800603100306030114a43d2840388000603140300d40d410341000c903034030b103010703101c19000481c0c40d00700e07c00560240700461700301d103030314201006504c400c070403119400e42044881485694000510b00c0c02c00540d40f00342d01c0a49801c078410400740030341c40400340f400181402140c482020740c101c50300a0500079251000240d40c0104100c0301c40b031081d681042180c006988444041190404221410340007164003000c3c3d45842c404104241d8410680490003041d24008c16006030b5070000104 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 925173750 1250 925172500 925172509
    0xb0c0f030703270809131515080a0c0e01030903110d020d030b151803030d02070302100c050c0607080a06090f0219170a022a0a0506010609030507090c05040302 70
    0x51081616880c00140e10306002071007103243c86a00c40b6842c804010008a02c0010013000683c0d10012003580c0059082d515049540001e00a840e03580684218002c00011a80000c3c1800f540d1203980341d03074078440c80d101c607108402036070380b100400004222024450441c80d442544000d5200f4000e20342440d1012507000c00e41c5c248040704e01070070010b8002c03400300840150540660203002c00c081e00c481107180e160000360b03440384c0181c0d4444048241030f100c2c0504035980800664070442c804030011550b801c61441d010b90340703c601002841703001c0d0401c200d50381c1450040d001d84500c0040c141c007400003aa14120f003110798003c01400702ea00c003640c441d400316106140780314800700040c0b00d50380140d031410010b0f501807440d649081c540d01042800b05100740c980807203c1700c0c16000088400056250b15a00c5548204076140b5044d000750b551010000700c1d0b0815000030b401004070300450a03151166201c00c4115510402404050f00d036600446040007040a690b1041a800400c2e03c0c146041945a03400034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 925175000 1250 925173750 925173757
    0x2a0e0f0414070206010609230d0c081e16051e01031803021f02040f03201c060b03030f070f020d0209010608150d031409040f0c0c0605160c0b0c0f 64
    0x42005070b0151006100c207c0d0443c11140192a40305400c0300914090070010340820f0950b55424000c030a128490340030480c4408950002d04002016240340000401e0a000015140b404503003c61085442d284090501042c1000a0b42d101070701c23000050091038040100d4419800c0c840d410165158a106818000d00c8045c58406200f03501070a036901c2040a050441e5085d03800d0148810302c100001c2011080351004c48045030343c002855400c8031410601044407914540d10103400c100302c2c2e03003044000ea64070311030507000301c0c440c1108001401814041c10361b40e01480c03c80f02c5005c7c0c810814070021919524031804101d100400e001c3e049210b076804116603900030707031000c4d0114040d0000e002e015400c4e404913603490103064070109543ca01d180c400500385001444010455034001030a4000c5031919086035404c00b400400c2130001751007520000348620f803c6030040c1c0c0c58910340350100c0c2e240c582c0c00313100403141d1416a030394403044c0300c031a201d14044050140070a00c5050040028031034001080014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 925176250 1250 925175000 925175011
    0x8010f03112b11040c0912080c0604030e0301051003030e0d0606080f030702010908060405100f02190801051c050c151204050c010f0c0b070809070504050a2a0e0f0414 73
    0x29202e03801958030300440521115000648a2400c007003501c004507a001c4400402c0301d0710001c4d506a22096814604964441d089040c441401044100001c0c140c00c009542d01c0040c065000b0081543c80e40240c10f80790480d804001c001031022000350501e481c0c600030180036580034020005000790b403450650720b00080000c0c2c00b10f40d500b0100d4071700103560300310880784010710071034024100314981655110386a5040c40c1c284c00070255500c4c60b21400041c140d040c2c0320710b088401f00500d0b0840ba0341c000500903102c02d00c00c0620801308141c0403160000307051010350207144c5c00001066282031010030000040c0f8120300c0c07644101014400700c201000e00148160045002e28041c1403d410400f00041003003032140e800c941441490740c140d6001a41402500c0d80c418000c0c81c0054603600c0b81c0707001a080181551010f540305040105010b409086540100c46844042624079500020042400202d2800d850700308003240442407601b5141c240801a40950318009000081c44182d004288a0b014803d898 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 925177500 1250 925176250 925176319
    0x903010207290106080c071a0403080f33030a0c030b10050603070519020c0d080301050910050904060906020409060305030306031e0c220204061e08010f0311 69
    0x48010350203038260b0a000c407592000e412214550b050030b40c05010000301410644075000d00064500c28405140180311100c103180140b10030710700705410020500341003036980000e076401400220300880e0300307184500720140009410201055044020500e00c01280e5041c1d505800b94980b044001820480480061803003090b0060301e030f007401590346480c2c080700d80101d806248108180071b540c036045401d9480c9009044041e11452041c01c40c02c07401e0500720003503160000650020782003000a408007844c140c1d6016206032041e0b54542841003909000c2d40309150300441c802c804200855150f4000c2590180a107102500d0655580f0202e811126203500944042d0004420301c0030130b1409120458001e00c2e0000c8456020162500b0a519055041e0b02e4900c1600d070449881120600c0500200c50607580c6035023107441d10b075980009099680510000000720604001e0514040d002d040a941a0741d030820050320140e081d0b60320810300c1500e4a050756440342003d84108180c0411482c0015108080d92 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 925178750 1250 925177500 925177523
    0xb0c03070c0909020f0f031005090d0e150a0f020a1b06020c0d021003020c0c0a090b030d02070b160609200117251107060c1505060a1403030903010207 66
    0x140241c0051a40d0000340c550350414150001690341c410b610603070703440b0850342a00240b03046000245003603e2074500c520704605000410165401c045594003900c0d00c5620b5a2b0810480b00c4200b20200c282c2840304550300341c05001e12100700d8410030100454171106d004480303c40810f41c99181007454100e00420400d452100d050011541c18824040c20a01c1502d41e6013410390540c1c0001d00c117584d101d09031410107038003094029580f00c04003d2103800c02d0010b8481c60000c0d40303554848000d4003590281c0c074020f01c2044c101c550302d9440001d0540403100800d410713078200350321100b951030708100305170041d201c25849171103140120f4107802c0c607030b500114070308108504075945000141c4031112200040031280055010040005164041200c2d40c88031071094056100442e4000e80340c084044004913190b02c00c00402081480d00300d09101301060003a01000030301e00b20701101005891701121920b4000580c0a01045103c2c60702c1080807102200409072424440a040800d00f20381001e01c1c250355148090 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 925179856 1106 925178750 925178753
    0x110303010e191a24040e010302030105180d0e060c160807060924090b0301080a15090203190c15020a0c050105250809040603140705040c020a14070b0c0307 68
    0x40c0c0c40ea81c17540d031242846103042000f40000c074001d610704400b185031081120813241d0102c00d00e900810b252151803004490f003c0749000c0007904503000340010b0051740c06c00e000742907003c100d240030002032a20389495145401e0b050f600c42d400740004075005120740c00c113800c0d03000c21070500d581c00f000900d0050b80049070b140c41654803416149002000114107404080b81001d07a40f40140380498591414000c820b0403550f40e000c0013941580155180070b6007071001c4071072800807406100c0f9400042d0782d54208921510441041c00300580241001d902080209a00c51010340000c1c60010300b420b102c1d002c4112541241d25240c0368024000e072110b07082050000480381c40303400103403080c0412503580c03511101d0982c80b540748007603c1c00751050210f020300349032049942280e0a03900412000c01c085d120a1140b200900400d545800751440c0487c80400040c010a6000265002183d0380d0586 = true := by decide +kernel

theorem cover : BRFrame.Cov 925000000 925179856 := by
  have h0 := BRFrame.cov_init 925000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 925000000 ≤ n) (h2 : n < 925179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
