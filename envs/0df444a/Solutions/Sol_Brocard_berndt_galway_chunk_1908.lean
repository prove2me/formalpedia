-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1908
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:07:04.569763+00:00
-- url     : https://prove2.me/submissions/1a168c7f-9914-4267-9537-3f4aff887494

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 342985611 ≤ n < 343165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 342986861 1250 342985611 342985627
    0x21306090803030403020d051305150703270506090f090f0f0702070f061409040e030913020414010804020109090903021615090303200712020319110d03030905100501060311 76
    0xd21888002c1d0f6807010b210021270482e90807000e0460441c058580904080d0b000c44044070490840e4000e0f540c100c0019415034a044207902c2110004100700d06500206600542084100000340d0012801180c1040c000001c41c2480c0d40c8d031071002c07030044481200803130403400c01c00c55264103440014124001d640c0a03035410001e41c001c50220104881e004e00c1c0c900110340c6041c0401d210703407288100c000d600500304143c071b000f402404030041201c86030403a81c0c0311a84403c001c500c81a0700403071250204911840400c003e065001304000b0b41d0042c81490032003030151300c6064285c100c48045130140c0041c0d002204991584504070000301c003a00880035032055040e5006002011800da42c04002c08001c04c00038a810103c1c11312980d209849990001e54030100c0c0c8841c0100005404550264420f1154070080c40300c0e00320280c07002003550740046c420201c4900080511888005144084040650350b11206020903802d214000006426a80201c0c0315403400c01c00500b6a5040b83d0700110380740041266103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 342988111 1250 342986861 342986863
    0x22020d140c18011407230a051507090b0405040504020604120308010801140906150111151b030f0708040c03020901120201080105040c050d051504020a020a1e1713080102130609080303040302 83
    0x3410341383c0d010b00200000c0c445446c40c101160b054412044192055000306010018081560707681480d1540b80140b00796039210003140c1c440da4620a200c02440308110a01907428a50803143e841030000e0010b901e403691381d14400c500c80210f500182c000400210050010b0002805400c01020000a0140c02801c042d410300341c541d07101422501100c2e43e207801c070403040e0340220b9170000c40308400016100c40072842010b480c42a50205c55000c40003000040c00407140c1c1800c01682cac001e140d040020080c41e40d41440a41d030049024006880c1a0004c010010050791240c2c4014040d040d4182c070314807040b44510000d0301d0080180c004601c12814a41c820004070f40c894195001c00051407008910b68945015540225070b0180045030010300000311300e8491500000c9000311580710b802a0131101e801025030070000044040c008000d407452078804010981203401406c1804070b841201101c43d07a0382c003850f908982c0180300301003100300c008a04226140c0c105d00ca1000501b5524007440c07a40c41c01e03503402 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 342989361 1250 342988111 342988117
    0x8040809060711040f1e1116060204050402040303030b0f0901030519060e01110c1209010507031409031b0f01020a0b0708130c06170622020d140c180114 67
    0x15070240d2008203000d010301c51601440600144041c10400c0100e40100c40325019103c828000b00d0740052015290390303111807600ca01c0400d4402c14641c035080c0b152503107048032a100311900c00d4440079004c0c040441c1d01d80e00ca10007400194403d443c00220020700c00148100080b5003ca62485802c0040042011480105003500354004000120034034900d40d241400081940c00190000f541c40d10800e0070f44c580050000300b89150900044502c1d000b014a542e080743d00c60f0321295030008009004c5000041e0191203008454101510b01c0f0f81400c0e160804a071500340364060903100e0340c80e2401042120700340142c03002000340b02807001d40523080f61501e0300301c0c0e221000341180301044008000910210440caa01c2240a507100041c45002e40d82c07410700030409400e6110715001c07244010045103d40c50022211803084854581a0382d041720409602c000035040a0001422710b42c0f66080100315000c5144103912401051110a85410707a4040d08152107408a081c541886001004d0a043d10a88800c0d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 342990611 1250 342989361 342989377
    0x3150602030702180a11040b0405010e06041a0706020408061501090f030b040f11090109020a080f041a090705030a150f050105090411060f0d0903032d020f13030c0306050601080408 79
    0x1013a400d0b9103407096200002e02e40c00702c00c58200d9001107808101d005a43d03008004035502640c40c00703450041b4800b040b12900c25803041d90491424032001c2c80079021004003400d0424050b140050509640354902814107401b1202d12040110b10015443d156800541481c040c0c10000c240d20794150640d81c0b00552884003074405401401540703180b000f080a80000148030020240c031103c01942c0d9a070f5610040c0d0072200d400400301d117110b000209110280c1c0d48540c400c41c0c1141d1500743c183c80350481c04106040c0a881d04001e0300842001040ca92801c204189505202da01080c00314804031407000101ca410540b2032001d00d0620004021075559040121b401c1908103a0620707a0b43c8085000851900c03440ca030b49401c1a00204c2c2071124600c1940c403014942c0d0103510180008030001103e47c030803940f420f4035000da880752080712160302d0016a0180050341071141780c0c2ca00d40800115050110201030b8403c0310341003444917040c81044207500403150010700a09101209061070781d640e031568050600 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 342991861 1250 342990611 342990649
    0xb040608100b0c0703031e08060906040f1b0809010509070501140903070e04050d0e13020a02190506240105090f031f020d0c02031206090612070603150602030702 71
    0x811441884001070030001c00e440c01c8000e0740c4100c0241100e440300d00c031348030a40c0855640240d000b10200c03408600380c8002055075951010b40e0b544010012110009001160860340e10440640c1040161242c00580801401c020b42207aa00b4500142410320003082030503a41d0612003030181c0103400082140580d98242041d075500200c0054400190281102051b8540b02c0c3c3c0c04001140384400e88024021800780c3d05a0f030610041d95001d03100003001c07107000c035040361249940d800c000002e036003d04a4441244141e505c4019a440d0340704803202c3d06002550140c01050a10640445003050390640184c034804072101c0740025400a800c42c01942c0045014894840420001740d80178814503502e09880c41d211505140e007801048025040103c560000c1d5140c1030400c2c4940e800041521000001052614000e9071100d0034800d08107405007020380c111040000040c9006007d10030b040c083d1055980000d6a01100944025100243c0c1d1002c01590002c000c1400562108a2080e090b031a480d2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 342993111 1250 342991861 342991877
    0x1106130302031201091a120601031401060902070819080403020718020d0905010606030c1815020f0f0a110904030c0308060a0f06030e0705010503010803040e0603100504050c1305010b0406 82
    0x41001d90551062100b5000c81092682c0041219040b42e440307034502402078180c4500014003a4140902030203120300c1d10741d0641c4000010400280b07131010711079a06481038008100d199446010307030217a0b004194215080c00d0045170781c0e991154407404030b08101002e071422410f18105510080d44800e400d024411044030000c8000c4903404403901241c85061800030108032900050a06038000c01c2a400340a000030304024002158900c1444e030b21000010525006807d2843c08118440c101200b2004800358052103560918001050141140500c0e440c0c02800c000b800b1b506c0c152180802c0144001d100c1e072920000d01c00401c0c0e12101c2054030603894107050301e02d500e410313000460840c00c55200f100e098146c000003160042e03240d0403041c80000b081013100c070100d880c1c00041d01c00b4002401914251352081c0001c000411168600940004c0082e09440c0710340003840c4100190f4208680507522988031040c11441d03410300e042211110a001c00c000c00ca25414030001802502c103620400040003140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 342994361 1250 342993111 342993113
    0x40606090b0f040e0106080a0c1d1c0215070b0f070c020603090a050303090106061805060a1d0a12030e0d05060a2007030e090c040302130c0e0301050901020d0b01110613 74
    0x41c045a0142c0929a41c3c4c0000390f0b5510030040c10044121081d0301281e0401410340b07900f034022030010301a407001c0c80740b23000080321480c14010560100c1c400b0303590010401c800100942c0f200c01d0300402c1000042c01e0b440c1d031445c5d0741c2041d11154101a204040603a121010884d910f907205040007c001e41c100c984582c0da88450036240d1521400344c1d0003500d40d002c0001400b21443c415800030302100e4240e01c0c1c800380881e00021850005e002442210341005003002140c65591013550b0003080c4032810f580c0c44070740c4c0381c1e02d04c0400d41c180c220750400706051078011859400d054000499480590341282e4521000216940e01078492078050555555140c035103d40f20b00003000b030064200100d80c80d544a0b41c03640500d0600800750800c5248050061031800081100384d81c5d0074086605aa030050141c92101c0800341c03811008001000e020340400c842140980800d903400c0c007403d40500850000980ca038481c0c4c1c03403941c00b110381d112141414030000d0700e404a450440400c0d06030f800104d40724814502c0243d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 342995611 1250 342994361 342994387
    0xa032a021c021806120f060705130e0408070215090d08030702070b180f0913080a09080d020a050606060c061306020903060403030e07062a03210b0f040606090b 70
    0x70420000394022440c1600c1c444203c581810107104500440c1e0181d6030708a011203450300c3d50426128a0600c2d000034000444d0340d401031005201c1c50b102e0840617540d00360f940c00c400d40394100035101180c40010004a01c419490078480c1c503e8003000d498070081c07038403144900107161420300503402003844102000158180f4000e10800000300400c4000035640c02c0b00e4003038058080c4200d0307222417282c12246076030714450070304089c200c2c0b052030f1261710001000d02544465002c2d41101018404011090b0400f0a5503181800841003445c0d26070024582122a440c10790308050005000a00945050011540c10b08000a085800141d0405410003a0065042c6100684544c50000340c06d4030840003840300305980365000392400c24518090b40c10498640c00103c2d0080d010854800f40da4446001305540700305a00c1c90210442d1107810300500d00303034400c4400f400682804029014880d0750301450541c0b420005d2201040040c2141c1c1080b40382d0030003c020300b15845500a581500c41c01046403810070ba4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 342996861 1250 342995611 342995659
    0x8061902091003060e180307140a081606050a051612240617070c02040c090f0602010c03060b0c190f05011d150124051b0a032a02 57
    0x5002e416110340b002c0a034406000361080e84601e500149046000588030b42d0706c50300d985540391942c0d02561904c001a203807070400c0944221007003003a01030322003e80300203040b04000388007601c00c03506981440c00c0e007410300702d0803502c2c01881c0d894514103040030005e590a04000081042d00030341803a140344058400320030010450b901001d03050350a1055140d13845403913001c00341d00702c1d07480b079076000f50002a00c08040c170300150645130384007c21000200100186001c0e0007001400c8568906901910307175030003440c40d4040c9994816800342c3d43d00c44e1207900240d0700d0301a4034080d00500040724a000c1944085541d600c01c49076640401801000d461420071404107101c00c4d82d150480b00038840f010401d00c0b0103039100000c8900d640240310303606019022042c1182e11504903603040c04003044e5016911a0307400c00541c1028031004002c4100700e0b00741040c13100303201e480f2491603250080640c003003980340c0a4002d07245500d285600c2c00c44400e100d020382000c2c000c0704854681c19501301e80620815608007004003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 342998111 1250 342996861 342996877
    0x7290718051c03030e0f150a020702010905040911030a060b0109060e031005190603030509010914090f0705091206010303080c0f03070f0e0907030c080112050c041a10020a0210030608061902 83
    0xc0a580b02e2006c140f00d000030700d03224140c1103e044845907260007152000724443c0800007808980040340402c4146840c3d03000e050f234035004105070901890102c0019060019502c01104c0b8956520402d10a03940d002100f0700241c6421b080004820401d2000a5034410200507440b00d86515200010b6204c0404842030f0500b0031188401e01c0b075280c4a160145c2590046c84003032b03000620030303a80010300f01101e040c070500000020b4180103060b1a00b8003500e000800003400b1340d0500100300900c00a42d240d2012521a4041d1440a80059411890000d10000c0c02400709822410103000540c00c2c28161000c1340c0d00604941404201d404410009030307074160740050460b500200e40004c04c0f000c960503070070880180f01c1c0b070340da042042c6c6c1e2140461141c80032100c50141c01503010860200050a060340000e0030303101c00c00d034100002c4420340d00044c1041c45002c104001600a0790a200460a01c5060400400120306051222508143c800c40ea80c0c4c00061445000078032441c903031628040180c0c1124904 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 342999361 1250 342998111 342998113
    0x120c07050a1b2405070f0c12050c030f06040c060c051002041502100c0203041802041502030a1205070f051c0f06180c0509010507290718051c03030e 65
    0x12045841480c2c0c0259002e21a119905550180e1a85101c0050f50742c110601d0007601d8403030401c0901d440303c110503100c075002290246801c00002ca0f8000d40b001148141c0e42c8228004c01e8425075081c2410b041a101480c0002c09a00c20018440005d0702c1400c4078054034403a25241c2101d00ea5402c0c203601c0c21004c15071100501d0f20000b0042030301d680ca0312122440c1000398084030081950210780380708a400c070860340310041c0c109100500071181d24043e0220b100781120000f5040985500b03100042c1e619a840e00c40259000042101c4a103400800e203030f03000340d00d914040001d8a00712201411804044c040c0000300000000c4400326000300d00924903a02d003499108011003103580042100a0420b4003d0500c81c02c03030300c00b2078921076100d0f015440c03181c1c10680e00d16007000000001503400c0c4e04081d1040316501074018013030501d00c0111489447c0c091070019010005d00740014054240040c041c091404010018001d04c03454a800c5184014420f600c20144030385012420308800401603140d0310200c0e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 343000611 1250 342999361 342999383
    0x903030603050609060615161502070302070e06030d0f0302070b10360b120d0302030709090905070b0a030212040516080d020c0609060d020a1d030102120c07050a 71
    0x141981940900107482c031034000c803030305901c510a0403561344004a40c0103900c00b110307410481c000d2130b610000d403040d289035200d51003161405030780f40441c0040000d200a912a40400c443c01856410029680200120401d45845042c071101203074680100c158008284046600040e1003240310707038120751071240c101d0a000200d04140121401641803407207085070110085041038921407175000354500c425a001d000c5402c1c0c082d10211200070b840c2d061044c13507004030010002c0c000450288100d181400c042c1d540141c0e43e14000c4c00142207a40c00b034100003451840c10000c0000113000181c08000c0d6101050860303100c02075040200c0103441503031a809214101903040c8410001d000a0301d6101030b0010100481054032080600d0340c98000e0512131005034080070b4264030a00304000240b140c030b00040c0c40145002c44000144003aa80040c15103070000d030600800e5080b003102c2010380c40300d20000310000d51406010088213041d201b4050400b0755104000112034081280070402c0d56007407548500c1e0040c5d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 343001861 1250 343000611 343000613
    0xe0601060503090d0c020a09050a151409040210110604030201051f0509132d02100305100605030415020414040605040c0e0103050c0d050c030403110a03080123032e050705071202070909 81
    0xd80bd86259494081500c03d40115007811000c1d001e4001d910050440f43c0991380301c3c0c0030802d85425051820b01030201c500001c1c51294028440c0d5407189000b6000441c0600f00a12441e8074645089404080360220690074041d80d51800f0f80690005103980703134130100c11040e080000e0711140001e0401018102c0f07016624042610140c030590350340c001c4070130654504400030260b050380c000302e46202c4d04410030f1009001450080c2c018642160158081000043c540000c00c4100d0340107801075046000c2d11210b804d464a0103006180213000c1c1510280203200060f01c02500c414803d82202e414151100700003450305a0050980d8004040700c0c2061003207040c110080c5006620a56090300001c882c903400c00302c000c400085c1a09400e40c5640c8101c0c45038601600c0403070800e481070103190780c2c48900d103406c11150790400c00340300803030b8a81d91140740c10240e010030a00322620400489508a0811040220041d08038003035072055074100803949424941d05008a00301009504002c80d201d01e0040118 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 343003111 1250 343001861 343001881
    0x70e0127020c0a05070b030c0712020f070f0806090d0207060309110a030c060809070b040504050a23010f09063005060c070b13170c010e030d0e0601060503090d0c020a0905 75
    0x79100718068021703140c00c5034603802c01c0005440102c68038480080104001c1000492078031448101650b0340c81504d00007044480c81c5402c026459214035400d0800c06014001004d0906c40d494000f10810001e0000c01d580d000040d44417162441800f080c10b60f51210141031181c010035030070300c2410080c1f01d41c8500d0703202c2c9085034480031580540340015034100c001648550300061080701355405100342d107040c01d240034200805440001c0a1009598481092800c6218020001d001d0030301031010010b8076604113480040c2400a82e80406005400c0030000c104054a20310240c60018011403258081002000e030781e25108151303003004056100d4542000100204900a085a10b00c03821003030841d901e81202c14000e40e214103c01072b0426480c8025901c48015000080040444150000c00c04940c44880c903429500312003907014543d5124590403e075000c2c01d200050240c505801c005055080c090820380d034507000e2411107000d110280c20744009565450155000910f291201130046103020b4842c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 343004361 1250 343003111 343003123
    0x50903150a050112050a020f0604030209070c140c090105060304030903080d090c0b0903060a320603060a0507050706050403091203030b010305070201061202190510050a090602070e0127020c 83
    0x1c007641034a810b0011601c020240181c90b0026042001010400790b070350200910002c1c01d80d100c59000d1000c200000068903030000b07403441480f040d182c64401c14200d060110b80c0601f0461100c0c00f903000403c00207055038030b00d851079041d200180d4410740c03a03559514058440405941002e4030520000c03803080010801a04583e1589100700d903182061a599035400085005425000b9031540042000400c41030f034540c1f050301c02c201d00d1002c0403540c078881036031103485074041e96009000008400800203075090800416401101033740c820091443c103020002c1c032901450100620554407080424145845a40040040c0c188592091014070035450040e005111140744240070130700740710000346500e00611410044030115001da0088440715801c010920000e140c0c510814240c0f120007140c01e86840f24024840710007515070680d5840d000802425841540d4480011540502c80522151000001d0310b41120404188003074503035400000c00c0d521440034840b01801510100b448202c00c04000f0741 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 343005611 1250 343004361 343004371
    0x3130305250303050f0a02070f0602030d0e0a0503040312090801061205060a0c14070201120203070903150204030305090d0614040b010f050402070f033507030c0201020910030c05090315 81
    0x18030240e070100522503020032031082c4805000f2800030322101c0d101d40600002040c9220746481921151138460b45501030501c3c00d13800c02d400507400803400d80d48401c841c1c4189180e96001100600c10004282d4801c1e40d00d201c0c6000c000c0101d0f540980141c0340c1030280040ca0b000d03000680081c0442a00d5201240b4181145001a5140c0c400c540105801414038401d00300c2c21800c036504c280a003840307922200a2a442890224100000c001c5800d440c028144050741c00740c941503403405059480d50911030000c50701d407181161134510410081001035084030403a880d0190698900c00400c502c0d00385200205140454028080c00340400c000070003008060746411fa600801e100c6060310b4640c810700040780200b01c00203094140c007082c03060220303000b01004009072414a4056100c20071400c0068440209030850b000780c140b02005014003940c050242c004481c0c5140b008508140390f4070000303400b407071003005d0920615a482928550640c403030740445001c080041e0494182d0801c0d06280d034620142252 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 343006861 1250 343005611 343005643
    0x1050a110901020a290f01030302070b2119020d090309061107090207050304120609030e0607030e0d020f06070b04020307060f020312060d0f0305090117010f140303130305 75
    0x31012414020000545001c0081030b03000700284140b9a85aa4000950140c1017034241410350104003070070104d0744074a22518400650072601d5255280c081d00d0010290014404140d00340a50007103401403c0c2030202100f042201c042d555211800c03102070710207204890404003400094605d04081068004040481c840c1d52580400c0366a183c00302c40141683c891000341d80c0046004200540e2140c028144883c0a541664940ba41d03070303420303501d8206410074101c5205860740c41d2034044c180c11001038803442c40240e44080c0303028000e0790700420844001c5001803144502002d07030801d64070740c5903541181c5400034049550f91080c40c200b20a11080403182280309200e40000481c0191107a80e241101101d2034006509144856040584014005000030b80190307050310724402040e09881c540e507172180251551951880c40400060a016180d40880070300f10005004220500c0190062404c0701c0345010542001c0c1c490100190852182030505a007640c103130000442030000224800e650744401031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 343008111 1250 343006861 343006871
    0x10209011202040f0506130e0907031a13060c020a0b07170903070803040b09121b0f1c03091b171b030a031b05071e0503010204050303071b150201050a 66
    0x990701d0607485103000b82400b041c440c043c10025802c2040c05030003e00183c00d190240d20752600c01c02c000420003280e440c0801d50082d8410024840c0c000a074a581130240d4900004502c1c10038480c60f40c01346181c0004040b00d030f0720510b000c0224404c2c800340000d2580139444001d58248038000500002090710781b0250100c031400400c09810001040345d01480e80186142e003103540c0d580351640d11142c0140807031076034010000482c003100c6403940148402d9600d007900c411007a1004049a00d000302d003106810301a031007940300a56003c20704484100c420310614000c684403903685889214032003090000c0001e10344041001c20341c070040461906144400604448980b078030800f2100f4100d6500440c00e401d41c00030020b05000c2440f641c5040c0000504c0b0000150aa0041e52418a0021503130f10008007001446120340300910a628207100502e0110005c1d404c150401d400240c132489071000c000d002c4a42c26a0817160032443c409080000e020025070841d40c0000003c0c043e0103403400300c8480c1c4200d4502 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 343009361 1250 343008111 343008137
    0x41e140c0109060c020d0b06031f05040b060d0f062f040918111003110304060f060b090a0b030604061e0812180411090409140c0a03030503130f1401020901 68
    0x240313201c00485600100030100039650380c1c980441142000c4d25541d018000c2d126881a09913a41018920044030030900040038941401c00266062000d004203216605881119010a802c50070390f1002c15040840000c0c03083d110500d0100003c0b12401103201d0906402e00942c4418041c8080c0080700c145100038030800d461303101902019090319800400d8956003e800010600742605103503007500160400003842042d070720b1419516002203c04039070b096107800801205541502844009103c404030a6080042040015000c2901030103021010b9030040300142e00da588a4003c0c0c0000e0009240d42e078004042c0450f10f5000720018001c80303407240306480c000848010140c080354020103101c103402003066503500800000d0a107031240708440d070f48248600c00701a542c611450703441c10b00c1083c1150f281c0e030414150138206480c00349807034450300100000b0000300e0740000869074841d040740f40f001104442844d0214003c0c0400b480544051805e420010b81151b05600a1440c041d091720740034060200c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 343010611 1250 343009361 343009367
    0x20901080f0a06020a0e040f02090f030705030c04050a0b100216050a1202130906020c031e030405210c010501030614060d0c05010c08090d050307032006041e140c010906 74
    0x48480103078140d5100000c0315003ca00c0079405003841c40c2ca07a01e050200c4060640000341601c4e11032a084c11a0781c0c0c00a480d08603807800c0003c2c803203290700a50240010504c3c0500083e1a080820320440c000c54a410004079a2a41c0303a10105000c00014030000814020300ca00175a103560306100d41d840c3e0102213001040c5c074a00701025104954941c0174402800600780d090000071080841300e0002035890300645000544280042d01c4d0702540800156207514186003040c01040c114030216081d42e10400c02d02000c82c07000f00f51035074030f00c45c00005d9140d00c81590449807468810800d800c00a9481d010020040229030b401144180e4810b104000050711a00c3c1003008000c0801001405240c002400f0005540200702c2c1c0e080c0306004903036107410034030300e000803a24604a40300d080f51f06400008441e0109500140b4042100265180e95054420190000c1c0d039204e0001e00013510700703e0311044200c141c60070695a98403455104040754501d0004d0500c803541c400c25480c8643c080b904500e004100248 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 343011861 1250 343010611 343010623
    0xa0f0305120a0522080c1219030203040b011505040305030c1c020309031c0908120a03060b04030c06080c0705010c090e0109020f0d0218030a030810140108042d0803010302090108 78
    0x400152010004404c51403181c10707507510001166501c006005000d4641d01c14070203100c0310b03040044116a0f400340844140110020100079a0038140305005100100711031144103070644441800c1148400250901a1401d01a80d4002803451100141e00c81003d0000300c0c05500150000c1e50b20740c86607000c10000e0b80c907806640c2d1403581550165207070340b040b1110b24450784000d1b149410306801c41d40d11040a9030415554002152041400060004038294144920310042c11001501e50909080d0341e185c0d40307981da0503c0b0701800c0000990204d450440803100319001c0c660f0180c0204074000850344094440c0146108000768410000c000044210a0307008480c1c036517900507002850030400d000348000941041c54984034187d140004c800c52910100400c614a500a8440d10300c07601e0304098043c00040c00303402050a000d0307070001e50f14169030040207040d0880c0e4080900840342e1191048030220750700701e540f0030218060341010481403003900d40042d4141c900960380215640c1e200d02000d589d0380 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 343013111 1250 343011861 343011871
    0xf090a0b030c0d051525020303040b01051005071709130b090c0c15180703150f0606090b090d0203031c1a01091203090b03010f05030c03060c0412050a0f0305120a05 72
    0x500f005a00e0a0050070038400745500c01c1c03200c0e01c18204070382c000b414880300c002da01006c0d0016900000510041c0105140028010300d07003250915028850300b10024410f0151200040216a4088111440c030f2400000d481e01c444028040841a14014060101030001d00d0280da001340c030030101281c070704030240046400e0405000c0061036035810001c40c82c248032200400d61030908050041414011405024200040d8020700d0a0100e00000c6000003048504c01d080900495280c031604201c025000f219520403070309a49903050b103408100001c14011090060000d5040c000021030035400401d15140382c0d640782c00d42c24104103204401020300401540101c2440c00b1441e810303400c002c4201c1c19100303600305038443d01d08022010395800c102d01083d042030308030300d041114001c024425400c08001b118800042103005013800c2c1030030480d4401c144628012402d40303664426460003400003c10140b100d140c2c1c880d0b41d44c0016075150400401e1a0001854520140c0c4590045403441c3c581c1d0150501034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 343014361 1250 343013111 343013113
    0x503040624060e03150c0c0c0d0809011403130b0627150109050f0d150c1d030102210703150308030601090b040b031f03020d0311100e1b0f090a0b030c0d05 68
    0x340e103851b15502e9280d0044400c03010030f032140c448400905c0e1603407401c0c203101a210f150280e0b118558240003400c0f03945a1030b40100080030a004004d520412a0741c0c050800340c00540b030103140c2e152940445c04035041030b4139200301000103c00307540c8008551001c951140946903d24080300080c4401110b0308034440c8211644250403480354400e074501070b40503500c0386114a03008400c4980001d05e2a0907640c0401442c0007050382002e25800099281c4071590070002d00300d008502e03020302e520901312444140c440032508216188002030700341e4000d5114a21405001c14071046080e528903120981d6441101e0490001d11401e800045150320305080d1070907155010802421030750f17141800c040040304801e0160541c0d500347d1001001d81c46410005011602130354030001d21160310034200f13280030b649142c4c0c00b6034036240003a4440c0c140408140e6000046690b443c3e8840351000c0301c00180303035814840c04240d10280c03042c00c0c80700d0491603501c40c005a900136801d44044d100c49000300015554139990180c10703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 343015611 1250 343014361 343014403
    0x2010c0215101a0301080106062d0207080709020417030c07030f030c0b0115020609030a1b081e07060f020f0406080415051302010201050a0606020d0503040624060e03 73
    0x40403944610700c075408105049442041d40d51801c1007401d240d05103182001c031a200200601402001b0b00402d400740845091425406120341c440030542c0840c0d484451203812040140c905403032080c0900310003480d040c42110096615005002c0096005200c4c649554800c4002070b44500d2010003550042800030f8040c0c651280755440d4061821030742503084003001791030424500050302c805891030180040d000360300310303603c95908080d180c80c07000b4102071860742c8240308284a96a0100107406590007001c155000d128540c40c0410890050714038513070070400c40e01c0d41108160041005810910b00440d41800240d1066498800700d10a2502d4140091b00c05c00061103805d00400c2e0b8240c00900c11001c005282ca40341d80c2a40490340300b42c9060002d1440392415009541e0309000d41ca412800c0900c1c100000343c50710ba400b0755241075444070081071150201c001014000755500c0407229111140030444410700c0703880c0d54000c0e01c83c28040c100200c3c0041103800d019081c00590320712501c3c8000d2403140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 343016861 1250 343015611 343015633
    0x810030503030424020d0501080d1110020904111209060f0108030904090f0c0303091e0b030609100801050c0d0e060f01180b0d060207050d1d060d0912110c0102010c02 73
    0x50012031074440700b60413125501105042429100a1050844200c0c00040720b5040c0115542099440149442040842c0400c3e04c4040300108510f580380101c0500113a686c0d0709000401d025100c0c10b034410b103840e0004110354054580340f150040c0300d001044140c1d0b80555541501c455042003c0c090318030150310a00c10010380d81480d6000c41a85805102032a107040b41c9075441c00284040e6420480008104440412101d60600c022074032030f0052980e030b0b40f25282403000c081494080104041c3c4a408440041380c28610604103210282c0009802444507180030100c00055500485601c00d965240914241d665140441c02d54095034100c1088400d9903c0d044640848810f100451034802d652140d00b0000307075075400d4550502c80c0c803e900150701c64110b800e00da400d00d00502150400d0240094061400ca02c0c8941c10400c2d03c4012201c0035203942040e0746400c001d104101c2c004018078588241c01e0480c80d00b08500000c2e00f8101000c40303480401c0300c0012800d030750400105901503481056804 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 343018111 1250 343016861 343016873
    0x10602151303050c06040c0e0108010c02030d09060603051e06062e031104090902040e06091e0a0f050303040203010605190b0d0209061303060c0906050708030402130e0d08100305030304 81
    0x4007036180203280190a004603e9012802c040d01603a0840310000d00c00710401210102ca9512801050010700821442242c540065100c1c402d41e8400803215a50b595101d0400503503600010182d40c000e4102c4141c046880d000040c416025a900c4000b0710401c0000b500c0351030328690ba20000c507110300c581c2c0d0b02c1c1c2d0490602e160107200007420071001c2c59201e00d504201c4403400c901900040148110106041c1e14038018441100c2010758408415045142000400000029142c8406ca02060003580c0f884040100c28100750105800a00604207400e819050144c0000a14081c13802100208007441d921420050110200c61041f096038884080401400c1c002c00c0250810f00c2d0940b1000d4a050340c3c00000560a61040d01d14020340f1041c850140309011040c8500034085007281071138606070b424580c015082d80603500d001044070400000040071500d5260041e03400900882003880340038500004140c0750342501c5541400100448000b60443d02c4181200040301d0304140590b20b940c0381c6490f15 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 343019361 1250 343018111 343018141
    0x30807020111010f090c05040e030f0705100203010f0929060903070801091b060e010804020f12060f01170c100e03120304060f052401030c03090b1602010501060215 72
    0x281e0512400b0032041071004030a00882a45a240c0d8070001407070140c518180703040c1c40054100341d02440c5004a0354101c414008126000c040040076103a444180c0340c0303482c034030703101014452555060000c800061640c001403ca10292550f403502840f201001415418402030300c000d80c1c1410111503d1642e445040050080c140548083c042d074086a854003481c40c20b4a11016049401d81e1200c0200022803446250000c0034226a14001911001d200c000030404c0c100680041c2c4600b041401c170000c00c0ea0f4032045ca4410b610400c042c4ea0652400d00d591400207442441007811a40380446c10400501d404601401010030040400b01034082e901d0040300c215259090030b5030144100c01d503180d14510680d0155200b00d00c5031401140c45041a003002080c0d480142001d00030b0400c84480c03480380049040e0f40004207100780790015046809140440140500d98009004591a6000e214043d5408400308040300351940080c0000c1e6600e01c0100c0c2d45802c00581c00792910054404210303100440104 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 343020611 1250 343019361 343019363
    0x5030d2d180b010312080f070f210e0d020c01020c0d0602090d080d020306030705010806010804031110020d061a04030b0412140a0e090c0408070b13030c0e07080c040f030807 76
    0xc0307940c6107407680d40510044080e007080e2194028100443c403801d030b00c1003005500c81a16a2905010b08080d0400350500c4c03280d81e000d90910950101c032854141c810780e403080c0e40c004004014440320003000748803500c6002c0d240c0454010300504840221650002072841030700071b40a0b050300404100c5403100402900005006a4849540904d65000c240c0d4500070344494040c0200c0180d81c0d0901208040c80e1400e1030b0700c5035041c8503000c0f0400c84c0903a0085146688070780c15040048141d141041d0707190a10001d040030740e03040340c030204169440280070f5221405503440001d4040d6004240240440035000300d00c80180340042140025000a1102801440300302d0942407014600d420049100031f160421000c4600180211b40607250602d003030346a541c0c1120041c5015890306090460032600d0319168001c84c44985400150360703c4801585140800468210a2181303007640c4079601070795540d00960f00c0000140c0b01710045211010480b085500701c039150080100103a00d10740d104142c0ba000b03400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 343021861 1250 343020611 343020641
    0x806180f161e050c1603050d12050105100e0130140f06120a0203060c071b03050309040b0312030c0307020d02060105010f030c0507140f0f0303040c060e060d060305030d2d 75
    0x500b41c0c0c1094171660000c0143d03204a0150940c84440b01005113060340d00c0701440c140608000c010019031300c0d0765800c0c14070a80b584ca40116003c1180d40140d903c800501400204001400000c0c203900e4043c50418419038440300301400186d602642d04070358a2400d540e24070398181400c01082d16464020124003509101030103450b4a14000d0300000d040440890341c50600d8031001803d00708101607422201990f40303a10820450003411511010390364001c500009008075a1103980c1a51a0380c1088580c07019003407801c2c10340c0c0c0c1786868a4515a603410a4540c0d038054800c41c058800400d001080c0c15041e2981a92115140e4000030360481c0680011007140d010700108212100210b04400341c00c1001603c210000c1110401114420b07140502109441a880d003040c01400b00040815103103004882c2070749070285c030311000c2c400048c1c5680b10f152400050603142c039000000300440440a40054030300003400f0005540f06061418140744203946070342d44040c00141e1a9003030ba10a80c41500c8440c0e001d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 343023111 1250 343021861 343021873
    0x705070305120a14120613060506280f050316050c01090c0608010b09060304060f0b060c07060e31060906090e0706170103030806180f161e050c 63
    0x146485003000c480181000c244200003640308145508518104403160081309600d203012209503e02c4041c8002800d800c0c03140e150b03d29140c2000c00c840c5c102e6070162900030085035a4201000c0040035603c02f852110f10303000c0c00d0346901c40705a03000d103420604042607030b22031030b1070f60750b4403d504c040b84880c2c05140010700070280300c0312030340380b07000d21031148220b20501c01e00080c1800c09402070184401640b0a103030320f0030304001980d025101c2c2c0043c0d94105a02c405c0104040a40c503100c2806404c600d8110307500030001040d0155103130800101d5004458590b160781410b200400d09000841c81c1180c50050104441801c090f020000d0328403201d808200d081000500a0b220070400084d140c0701d0f4001c004880c0c48a04020000e1800c0c440c0000400003800e000c4101c1d00c038900410b417000c0c2c0503c005000d105034440001d13515114150040340c08a22002441c22610382044c05e100304402c1a9243d0525205070405e00d50014058518140b40c0c49540101d043d50a04a200c100e030325a1000361100840c2c0207807 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 343024361 1250 343023111 343023113
    0x501140d1e03050d09030f020f0601080c04090c1a18030303060f0603060301090206220f03030f050d020d050c0304051b0102061305100c2a020d0f0227060103140105030d0507050703 79
    0x3407081700141d52003561041d10641c01500020718201e645880000710350465001005040000030341700d10422015240800c4521060030990840d4450b41c0c88541c100400d04901d80055607800010034580300403098804049040d5400c2c0342e500d01003140c0c04ca4010000100030301541ca4010083d56201c0c000400110b0000b07501e038003040403034000d42c140340890400c043e41c8102080030b071941a40030344400101070602514644008010070007a0102d4014004000f480e4024045180c0486054502c8444148940c0c24074840c483e0140d441120241c581c1d000388032031154040c001c07041c2c16032114016802001e07542c0300d01d00c442400c0c8500090864003480b41c0100d802c1056120702030681e03138201d5501c1d01c0c0d1003e48c0144500501820026440d4010381c0c284e00d11a0043c1e944101800b80550004030380b003c044891704c0403030300300c69403910700000c1c01070306020951f2030404400c002071181e0800c1c1e03014444481b1a0b41001603144080c01007c0d81904026180c283c91403144024190301d134000e1089490729956 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 343025611 1250 343024361 343024387
    0x12070203100f020c101a0102010e0705010c140303130201091409041104061d01030b060108040510020f04051906030b151222030306030203120a020d210c030501140d1e0305 75
    0x1d000c000120f2629006e41d0340f0306491404880c00702410030300007070042c003008400c1d0760b0301c41c40340d402031906008007082e0020600c40c6085c0105090280542161f6a030b05180d0030b4000303a59891b4400b280041c1c0c1052011404800f816102450300b007000e00380d5000c5454590341e4050150020500e5900155102c0740050440e004403a018078161020342c000c8083d504605202048900007032065060044200601000840010f07042d94610101d8000584490320b8584801c02881154415540b20b03243c503c00700101c1c0c10100d54402216155102040040d002109100c030802a0612170215010700b070180c56103080580e00682d038803803194100c00107111100f9030700c200c0c55a16a072043e0b00090f580c42060007141001c0044070b82400101380100e00b0103048020007596606110096001c0241d4070b20b1420756071286540700d600e0b074103071544144009420004018002c003000d1041d147c940641040c0c4c01c2c41c03418080f102d514441e41103500032404c40081d9501d10183c1090750340450400c0010001080b0340070b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 343026861 1250 343025611 343025623
    0x91401090320010e0a0f030c02090702030a020f01061d0c0409050906011703070213153809060f0714030301030f0b090c1e13020a03090512070203100f020c 68
    0x482501c40c000d4080d5240c0c88808003180900681d0481d1307142c01c61000c0b484500180c0141c3c00355000b80c090800780c3c114a0110358201035114000e41005803281440b0485030040054051040d4690841e400428502c0300c480c00e0744c4103841480d02e40007075601000f45051035540026407101c80120241d14183d540d10300f010840e0b500b02c0d14111250460300041c04040c0e1180c0351a820180500d00035420616176400082c903668a103c1d50b410300d40c0d504d401072542000070007400002011000143c40242c0315800304102c4240100803940b00c00c0117071016071900c642d040c01c20b845000c8800703041a4100040d440281c1001d40c40b00b0810b8507440c440000141c0300e01c408200071400b8502c1004298042d030680c0c54100718000010300302440d41d40000b90710400d45e444014241d505500c0070307015180e0030b410f0031010400e070700408081a007040d40000b0b01a03140c1c68068100b544400c3c4110701b2078241c1a41e01d01d140c0a80d01031828000d6040d000741c10710322518070054211110403030310980d00514000391004024035041d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 343028111 1250 343026861 343026863
    0x909010b07020118050109090506010c020409030e0f01210b0d0507080a060c0e030c06090d08180f03030712080a0f14100812030a02070515070903060614060d09140109 73
    0x500d00241640865038841c0560802c00380f412074840c0c0041c140400645281c4a40c0103001030242d4500c0019410381c803562214100d550094002c125411090800400d4440391840340c074000e40c01103100c0c03c5194440c080000c603a18082c04040c107000c007900e81210280030f2042c5030a5011507031611402c0894000c1c4010030081102400800c0207094900e4414242c60006684409005c010b94000185450108000456160445000340d5a0350403000141d090118482c0103000d50202080041e8480c6d08440b44650341d00c4221054500c0320f41d03a8080591b0382c440c501000f071001e1881d901c036070f8840d401000819001710756110b0101d0141c460340301d0a800c980e0052184070a10103401c0900c0340c818081401880500801c00203010030070f083c0c0700e40700720610002e004d40f8551a4006510411710205000c250790005002c08070300001e00340b01000800c00006030100b540e01e107140480000360b0200305c542e4070000c041c0280c442410081c1007680c440040868110a607040c07039900661107041d40080c45282581 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 343029361 1250 343028111 343028129
    0xb030705180904081e0d0e010204090f231003020d11010305011523160309080d0f0929040f080c03010522060b030111071208161202090901 61
    0x4042540c841c08145841520a502424001090201064a890071600240140d8501c4100c3c05458036004034030340b01c2e418022003064070740031130b00400c8581034004200f20b0300202d0050000034013200302d61003217405418040380c400c000c800ca5a0080341000070415842800d00c880c030180c05581e03030086441000007800440b8444410409001c0543e05441080c2c05850484543d1503804a501405003042d0f40010300000d0b4a4001031802d552688840d0403524080a00c2101e0074542d201840c01824081c424054450030380580c260760310140c1d20034219013411061540d900e4200034901b80b00003c0d02c41624020b1051854a15035400520341503000800050030030040340c086c154078000e08207062549a0368020f1081c1d0410040c422120f0b9894040d98144c4c68401d03102401c04941e29240c0001c00005400541550030305006205170f8105201500d00c103401410303444403260440004071800c440844114440204c400414110360b0300c1103508003c500c25036800140303800c0c00e20b00000c03c802c000b40e02074035030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 343030611 1250 343029361 343029367
    0x30f15150301030209150109061d1206330906010309020a081c0c0809040b1207060206010303140a020d030f060f08101419091e060b040506060403021f02070b030705 72
    0x1141021102146e0011401d5062500ca880e044e00003080180c0310302c03841040090541158100d1170001040030359110008007807100602c0d6040c3c2c0c01d0340710f010898410001004548110704030b510401e420380c107441e9070708070080e211013140800c002015a010307041c0303410982d6502981d00180c90301410103000d81b4602c40281400d40d5104000341c0c004220070b041d50200030031005598005940034007600c40c1e02030121808218581048003052018031b80c0306c00b001952040d8800041c3c40c83d008188907050703901990b98846140c26a285540091040f8448000164030443d03940031100c2c4031b58413402c0c9402c207800012603032943d0b80010401c0e00101ea0040ba0803030b007000311501c000d1180d03840b410580d1200000e402d8007519081b0044020304801501c502091900c1d104000208020102d0202e082103490442d00140107081c00e003e8002e146080b4007a00807460800402e0740c41c5083d00c150307001c03a0360003040740c038000150840040400b071402001c0d006502c238040d000f10300c1440401c0910700c20842550b450351 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 343031861 1250 343030611 343030613
    0xb22120b04020306150d0b070512190b1c060f0e03040801020c06070f020a12090f09020d0b01030204050307030609050a08030118180b0622050705040501020c15030f1515030103 77
    0x305051024004a070341040c0522805d042e503d034080e021350800d070005a0844e03d82e4801100fa101d9104042c00d0007209201ea07010051501e01c0d210354040d0039001141d081249078411420301c1000f040c030b00920981d5800d1038008100140c0d0070382051041c000c2c4400702041c6e0f500e482400e686190041d0700402100c0c0d4000c030f0b4807805807004000143d03010341b591801d401c20451440000e501d84014090240c41811700e0301d01190413038020600c683c0240701d00740f403080740e5540d40c0051300029080a941c0040c01400c0c001c0b120740304c0d0310030700030b9500307803100280a0120b83c0e1440d91020700604120a0440b0140561280704000c01d03840b10103103000300f020b03c04603042c06420840c1c0200302c1d031a07d2008000d819600c946000494280341d40140d00c02029660311030702580c401c10006a090b40c000049030100c4c2405d00700943c540d8810064402c5410a808407526826043c0811000c001d020345151203070b110074000604980030708006660042c201001a00313981c0c51503030100e4401d498841c49041c0c80040000104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 343033111 1250 343031861 343031863
    0x9090204050a060b07080c010b100c031701080601060f0320030103021219080c15090c180c03070507020d0503070b0412020a0201020607030e2d15010b22120b040203 72
    0x60b4400c5210600700442d03410401080d8043c00b07494800b5140c010041205200030303200750f00a0040c440000c20303072814151030140041202d01d04c0701049000550700d0101503030308010520914140da06007400b034140c980c2004021501c09e84ca4540181c10151101100078420344071110848003140c1500c0d40541d00d60541c0180b00c500c0007041d14000300e40c0d00c004101c0018908080d4842512640202442ea0b039041450b0700070b24208001803200081c00400041c404601c0001071150498002035440b519030345010003c03021110400c440c5000307040d40420000e10701c10703c2030004110841c4002d00c0f034101440141c6a10b407841c2c215800c11104480c100c000c1c03000303100c410f0308004203a5010b44018141000750341c1c0000c0d116400a041c12051684492125132110414080d86d922402c0800c6405101034202e0032040409000c090400d01c680260007420400540d81d00000b81680d00c0d441d02c507403510040c1e0194070304003000d607094020110321091000c1000d64409443e43d65590040542e6034503800e11380101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 343034361 1250 343033111 343033121
    0x50705040f03081207170106050703051b0604110d0308180304031209050310110a1805030d030b090106020604021807050906030406150f0609090e0c06030c042c0a0c030b060409090204 80
    0x501705108525030000001c58500003840d0540c0c81c1890041d440f04a42e1030709407401c1c05404400c07140a18040c40490711140c0004126100b42e01500c200146c41407202c041c0030703061203040f5028001038444000104220128000d01c0030540f821001c40e4582076072616a0100220b140c025580001c142c1c0d0810003041c90b00700710500d4540d00348481088202c1c44540003d070a4418012102d0500602d401448140c08001c440680144005800d8a01c0e2030044000240106541d24405c3c0c807034a910700020800c2c91001403450b206a90290203503044112003100e10740000c5004044404001c8200150702058540102440c080e6126210219006001c8041040c200740680c002c12044440804100951903200300c03ca4100c0c0d02d143e600007210651041c0190030603c00003180da81054000043c0041150107000a2084801c1d0b107004d019804400021100c05404003201c007a616044500840d2591102d544206081d400398140000c12004e01004184540c002d54000300c800c42c0d9a11800c0103504043c05030b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 343035611 1250 343034361 343034371
    0x6011b0f0807060615080a06060e0f031e03040f1403060f090f120a0305092b0903050102040e040213060e15120d020717160326070c0609060219020103050705040f030812 74
    0x1f00b0b110349414440010541c0304081010761184401102c0b004540d202400f8a6039954002c4821034a405102200503940354400e200da1450075941220002c1c42d5048032076507081100006024041c1515070b4024080b140c440139095042078000c080c50008244410020311502c2e0007504202c40e00c4121420b000340855000402400507a008144041d090190101003a60940102d810502e8254060601224244003542009140e03600c00580480d003002d0340040c05201d503100715000782c3d002c20803203110400d9171030f00d10440508a052102055841d00040c1c504c0c00189406401034410740c21001c41d03a803030000c01134107450240c0c01204041c8007031074495840c1550411075070020000301048084245a4071030511000e0140724962141e62807580210120000c421401200d65840303803124205268200c04511802d00415182c0314000fa40c0b80c00803030342c03004210010144002500882e001540a40401001001002410080451014960104003000e540580d030303500c2c0c540080c41c1a0f840720000283c9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 343036861 1250 343035611 343035631
    0x7150c0206070807050a0c021203070602030a05330f06070b070f080703090b0a0e0c03060403180e010e190b0402070c090b0609060a0f02120c060f06011b0f080706061508 74
    0x442d51070000d40003842002c0a0394127440070002c104054410074110701840a00800150000003403242c5180c1940200740104000c038401c610141401d1001a06a0142d10708078032003030b000c00c2801c00b992401c2e00e684510040042c080524011076580d405800c48030490f40c8401140c01c1e000c41103c9140c0c4419020b510503440d050802044927203484d110300200006040b0581c841d01c1da40561121074091040304c1c10100c010701143c8031803c0c28a4081c20704103010904101144070310000040e403140e070103205030481d40c544034050815110843d03180914280b0303600d5130115503203400d0800c900361120b10080500d103000d2440050b0807414441040300303407005025014419a414001480f840c1d6500341200c0134035043c0d040c440d9203034145d0181030b41031511030030404c000e2000210f1106c040d007001043c881c1c07089000c1d000350a8143e661320300640c0e418080b40d4801c054518043d0180001520280c4070000c0c09000d0302c9540e040c61a42d07a649000c0c0c66503038101494403072882075005050b45c0c200f006941c00400f000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 343038111 1250 343036861 343036867
    0x8060a060b090f090c16050a1a1501030e1c03090203070e162a06051602070b0f160c1202010807030e0a11010c0c0b04081905030f07150c020607080705 66
    0x4000078000f41810a0801d1240c0c01100200742218018400c0726044090140d045001400c1d40c1040ba48513a00c414059800c0d150301c0502d00443d442000c66288140c2400072041c07444e0541e00c00440c02000100c2e0429803d125040008400d07040361000d00c0c801c2c040c2da80d0040b50400e00c600c181420f010560b0b01c901840c0c003001e824003202c0030410500814070505450810150546a450708035103106d034443c942c00700100c90702c588041c170406e80c202501c17030f2040300030b01c2ca420449980b00700e946615522643c00c00083c203010803e0040c4086006214000ea20401606000b84544802d14240303240d81c800880e00e03288a48a000310350704004050ba20081f941001c000f2506a8046070340c0303501201e20300034030240843c0784012540c7c0c06a454200070b035400c182c80700c601d40c1e1a500c004030954080e02814800344140b000c2e162503e1401072200c643c655107c0041d60415080a11054190704900c5048440d401d000210b04004580e9100300d00980c04c155009101c00e00f03020002400001019041c1e50411500b0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 343039361 1250 343038111 343038127
    0x12010111e070503070c030813050102060405071512060b0702010905030318132c06092a06040b0d061e1401082701240f0b0d0b040608060a060b 63
    0xd0106501e5040c4030306003540d90021454602e085208004c0010043c50320400040103003c3c0c014041c0c500e40001000d17001c14581c03940016643c480d001c4038024101d030f11485040c8481c15a00c0b03180c440c001ca50341030043c5048002940c082c240d50454210210301c11380030400c2419513a20002c1c500003002c0a07000765240c1001c00d00260000c05031505034074082d004554135110350610756030114001d460407217621100390724104441001002c6843d070b40c00c01d503c19000801c08104000c201c05101c040d030780400c0940e03180c020400580952407c2c4409500c20000d010001d5030746510b10081c010415140c0000034070604041c804619060f1600c9120003107441000c051003400340c030b43c00a6410000c00d0824001642c1c41402c60101803905030000700c1e40b00c41c04008461a100150440c01c82c0c1036550400150b01c12020300d1500da5030b9407620400d51802c803c0e0700100300740d40c0ba1600400c000140c844000c9082101c68000c81e09031541c90340701c043c196202104100c504501c52040c00c020f0300104106d20b147c0a02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 343040611 1250 343039361 343039387
    0x50c070e061f05070b011404110a0f030515090103050a2f0103150b04080307030e040c171905390d0b010c050f030c0f0706080c0901201011 61
    0xa030070140c00140c07545000c50751020b0190f0140c6030f009a100c07900040c2581c45000c5402c9507503280c00224000d50030b040d0354a45240441c82034500e548001ea848103400d000c5500100e000d80005403c4003219080a81c2c1c490140d00ca805108c3d01840c040c4c4020401d9003000c1c0b0f490208100d00154403e00b612003e252194482000701e50440422000d2802141c074414409510003880b074540c1c800b903009030340054001802c540c0072024180307441c00f9489010182030718000344000d0f1078100300741100040614018840356400040c3c00c68010380d02010140301a001c0d0303044101128001d554103851070600d050699180044116260045510580b1400412112102d882090301a44d00e059101685998041000364070420041554a8102c400c41d00000040703e60380d600ca80c0007000590300d0740504481900e100400150792800c1791100c0e40c901c1c4160344c4180d161069600201c2401341041014580c1d000c01c8445800d00c0c0c075040d031070a0081e0841c0140003808000b00c4950401e0f0b0028010b00780458095412 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 343041861 1250 343040611 343040629
    0x110c010c080706020921010c05120f0c0d0c020a110117071112070803040606050a030c09021602130507021c200106051503071205130f06150303050c070e06 68
    0x7a00011041c0c8684852502c40080c0c05454041600500841e1001c80030f4000040c40355130040c1218002c00401c080c00700c0481d11481070004406421840d00085171030b500246040c280c1c0102070700306a44c1031140c10707101d40701690070016802e00141e010b20740110038046450b00c0c50f20043c0b824200b81c1010130b1426030320341503240002c00c0d03002485281805041c6040052051111003030322030015035600c004500d0b1921141d002603a00751655440d1520128443c24640030b00c030700b9690041044400d0500d0030703900380c003e5401900c1c041d00c030404010300100140c43c0c442039000180e4056002140030310b0080402840e0045584170000c46801c036184e02864182c010f00d00a04110340c4d4a00c810052a01440341030241005030701c103d400c04007c3c83c040904590400c0554020b00565171595030180742c00c0c3c1d540050390780036a02c61124008120451002030020750140c190707a441120049184c0c40c06a5609070160002d40c01900400e500080300f05a81c003080c0308000c06040d0121044500782440e00c080389440d1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 343043111 1250 343041861 343041863
    0xc06180604121103070b040c0b27150d0903030509010510120c1a0309010e0a031202030604110f120603070e01051216090902030d0c03050a050f121501110c010c 70
    0x1001d0510102d6503280b0410f0144090312111088a641300150300d04031940d82401c54040d21030800c802c201280d515052000c84507061038003119010b503519810720b100740c424910000c3c140d0041a92100c010781004001c0a003000c0e40c2c01e844001004031180c140982510801040b2040c20392600b420403001c4c050821100c0140c44803401080c0d0054814604000100e1064018520b0180f62020b40004134066000452060729428001e00004400c8041c55a640464000080c0420601da07030a840d50621980590382c44607005001094103820021840043d52080295003c454000113010500f00b1322103481903000382081e00104140c2e46070120b095050300060041c240300340140181401c0c030420401407141c561010340003c2d0f06551340c1c0e81640000781080d601c124042d00403a980440c519000d11000f045040d00350701c49900c4c004424204503031a038007060802da400c0105002c1e003205201082c8100c0e100711402a40e41015201c0300c0000b61011130b6000d062110b55110320f02150845c1d0307004058400b81 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 343044361 1250 343043111 343043123
    0xc040b011e05070218180703020307060819090c151b0803070c0503031006080f1614040306060810050115050d0f0e010c08010513021333050c06180604 66
    0x301c005010219614400c1801c065800680880358403140010f20030b030315000781508100d03440b10407000c104d81b47d110180d500c40a90700d40c10105040000d2030085980300d80c810342e031403d0004001005022102290329501c81503038030940d1030a00703001d0120390000c810349900e10303810080071102c00450045001000004009e202c6040070000c6116035000302c0032040c4095118069075200d24141c0940361451800f440364500040202c00480c0710030130310f01c011a0082c1c840c1303107a5001c007103043c080517140034031030500940481008000001c040f030154420000a003081f00050150301011503111020f5a030181c10032000c0e0701103923180f00c030380541003030071104c07038490a50020032a1707008103030110000c08115040c40615400c143d240010554000f6941d4160384003120389503651481c072072510080b400780100305031013070702030b90428070182081954444078041600c114540180040240000030703c00304408502003200403a1600100d4810b02400350b0140c5191049819079804075086669424094006011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 343045611 1250 343044361 343044407
    0x3041202010228020907110613050c1017010f0f090f060f090516020601150c08070606060206090c060f0708070501060905150a0f0f271a030c040b01 65
    0x110790091009140c54480301c0c042001d00c80c2c0040040d400900104002c9115640b204006201d4a002c0c9907540f1280e5645070040c000c50f918400c40d45000c42d868401564103209411660310a5590324000c100310f04030543d600340514001c0714a4481da81c0040c0c105006460078102e0901082104113141c104540300303040301041040181c5005030042a0941002c810201c2c038007004074100300903420035401401803c82911105c41d4905080b61141828041c2000c09402840c2c5900b159104071400050507008030b902c2ea00e030901c40c0d42e520040b1207886d40a607026030010020000021000d0050301e64121007030b51841d00c5d1404d41c0001940711702c501040100520340c08510b140038004254481800b400d03e51074100502e04011380b090b440d221540302d00c42c0c4100f03000f2a01042070359081d07a403102180c10100c000744416042c1f0308412008045104402c03e96a066079009007122198003950303e00003072004085011902d40401e25007030000a03e42e00340101c1c14200c074040d25134ce12048003449082c402d10740c640c1c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 343046861 1250 343045611 343045613
    0x31206080a03030c080a050c04090b151801020607080408040911090409110f0a05150903100603080717030609010302061c0911090123010302031005060703180801020705030412 77
    0x40186000c0d00a10a80e1140a26070010503070981c1c0710081100d500d8441100300d949020245098850450340b42038010780a01040100d8949034105466445000303180320101440455540a26040f580907050130130f02c0d00105900958041c009640c00200301e161051051500751030b062028815407040f51202980c1d08812a4000d0040056502c5c05400800034002200790b810100640c1800f1a0340a200d00310700c003001c008c2850007200c3c00b011610080e1609079100031003000c58030f2a4211090641c2c060054400c04124019284100c0c009548541001900e0310707001c1c1050800a50040b01d00c608000d020030911841e1394480e0030b014116681220344d55903078801d91030385e11076081d50018850001420701d01e01c03070100070b100030342d01000a00c1951220502d0380c4e18a520300e007120082000d5940303500c3e035280c20740345544650000d40d80b1810a0703a000040d25981c20228510381e20645c0160b000482c1140c1c1c0e11744070340010000c440240f03040b00095007815095290030342c5034072483c800e103004440300301e00c1c0d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 343048111 1250 343046861 343046897
    0x131203051204021201020309060601030605030d1b03030e0d0507051b0f090702121305030d090e0a02090402130801020d060807082d1f1503030804140717030912150403 73
    0x40000084d50029520380c00c054180300c0d0b8500c01500c016003c00e0030000081a0350a000607035403106203c03641c849541c0325900008140d0480e51030425420161540c5c0301001506040003908000301d001e507125a5a80c190341801030900c0a03041c030250740080c40712481107150b40d410070401c8800800701e132024115103e00c40140d280c40c0864000c240d0095002c1803241100c400083c40200701d9a007501520b15804144004660201081c01501c1d0b07154030b01004914440380035030241c09090f202620061500301100b9039501c1c0c82c54690312990720350b9000116000b00741d201d40103000081003800300400031541040d0701d0035212207072250300c0d559003c07074950b03030241d040401d070501112383c6200740580352000c50f06c515011881280380c1c1d82c0003201e810f18250103415480d5890000c00c0742e4159899140c0707511541d80e090020035a42e4110761091140030400b1400400c40e040708416901a14011940c4111160600c600000d4000b00c3e0305031a0042190411600c1e0503001d1b041c1d01981c98540211091503141001c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 343049361 1250 343048111 343048129
    0x5130b031e18070906080f0105041a0c071a0414060105061c06032012031801110102130b04050a060207051e010c0503030f22020f0910120813120305120402 68
    0x42e06070340b02e140b100050140340c03a4000c40030754841030262001400b03140768080c2a2340040c1e4008002d0050726101e907002d10f283c00c41107a0000c43c0350f951203280482503204d00268550520407503000c40890000d1004110b00c409514108a40c400094030703440d0f00d80000900d0354094840705c1103c9121340c8100103814201548408051548004441e04250100340307100524468140614080d103941c071180300d100c0800001b136880250304034024004040c007000c01140c3c204103621b000040380d074003484400c0c80b185140d40580f0141c9501c2155a4a4a10b08000c100b80300044c4c1d07000c6401d640254006014a85030b500010004800204c1d1a0700c44000ca2801210301d83c0d03010b070020b800c5004c04014000c941914000c01d40c007920106070410054503083e092a41d02d081003802c020343c0328015025098483c01c041300c0340d40e0701c445041000c0d040203941e5405000788251040045902c032000050a0b40e10f009102d2042010700340c50b41903403001220654000d05030348035002c0050303c410b4560780010119510709c082 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 343050611 1250 343049361 343049401
    0x140705030309010902041d0d140d051302031e06011716060206040309091b0c082203021509060f0d0209060711030607021f0b031c05130b031e 62
    0x21a562890040512030080001203070803482a41451104d5211502c7d03180c0c13001c2001d075034001a0228a880906c196581404500080b0740d80c58148803080a01a01f84241442030400c004082e070211864810581001c10003804000d400042e08044038584400040183c1075541000c0280c0d20030a19801807481d0001e01d5a80c5020b45080c0071010420641c0409d441c0d01551198a4080e0001d8460303008c0c0b03058444801000303050030b50940c141140d4a1140c45240b41d0180a0f4503998075024114455260700540d04a22540703113a58a0010400c508100203160f00b240ea1380840541000c40485c00254144114141148031007404a000c4219001c10342c11104c510000400b62076841c1d08a00d055142c49a4035403500d403180c011840010403041c00490010341484100342810a04050410740c070000304014002d03650035128203e814803114040c030070503003141005511940d803101128541c43e000d0224603089080049414800d21561520b034010070940c2c1441308a0035003081e90342c0c40080c0800d40303500d01c0d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 343051861 1250 343050611 343050613
    0x30405010e120f03040e010e01030b0f1f14030f01110915090301020406030608010b040903020616110d05040806010803070f0308130204060f090612081b0f060709140315040201140705 80
    0x90300f035081d80c0000c01001161642e211441040c0e0380c5a032413201907002444060300c01e941070b800084240e616107826950012901c00c2d01c6041845128001c5c410f18117a40208100440e54080680300e850104500d04000100b58028130222034104c00d00d2056009400341d0038080c8860070b861145c0070840350282c07500498090300031500e0300c1e5110310007006060315104100c00c0d03510301804109141441d0140820458145d0014611501c4008004400a18800013002049035000e8174809281c01481082c185030700c141d40307040e16141010410f50510f0010b0740710250541c02009442d000410204070f0b20b0740c90750141002d031081d5030380791105001740010f0000290f00501d804400b242c1d4410341a00001070314031420341000440d88800845482c1440b00e1005044211b087c4842072188400c0740c0038559280c1d5203c16141c40c645807881c1545405001d440800101e040018140000011b003549120f0500742200101170f101d98165145152800192000c2d04000340c1000403808284c4070b00c21034086540c480 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 343053111 1250 343051861 343051873
    0x50f01020307020601050103060e04030c150b040e010507090e0f040803071215080d0f050f0d0b06120702011104032001091e03110f060406030506040b1309051509030405010e12 77
    0xd0b100a44903039003401b540d03021a00d000700c0403403078200ca11071183c030407076149e29584c56900880e1103003801d0180c651441042251500100030854641d0300844000511072000401c507400d04507400f030030301d880f640c0000c51a01c119a04000d1030380190040b040c0c2003030304001103d503262940c00701102c0645410101d4410039007000c07480842d0030144a45072044407031360000d9401410b13248504491415444402500081d4203000c030881e02c0c3c0d400001000746c662007900005003607500202060302a041244c0b11002404400104000c1caa0280181c00c50b4800a40e51f1314909800c5556150016901c900c0e09065184001070481d0964003c1c010320010300721b1921143c24182c0c2000b00d401c102d08641c0800c503000020325a950849003040d540c0175000550007801281020300301f0804400800000382600d5200d51a00021002ca440e2888074103c3c5003003240004c80d8854080c00c020b0304d460301d0000e00b072511030882c6040020314400803050701c00740c0d9070901e000240d40c6121800a10080c03a20b4601440a0180c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 343054361 1250 343053111 343053121
    0x10020715051603150825030b041a072c01090e01080a031101150618050a031101032313031403011d13050a08030a021c0606110c1507050f010203 63
    0x10840b40700200707095400340000800002e010407206a10720420400b603100050126440801d0f2600da01210281c0080e0700030680c1d2a2a21078180000344c40644054101c6945803802220303080559900411034145100c0d040c0e000b010304282d1910745c10100340307680c0314281d1300900360b0b04c60100e07940201a081013440007541c56003503d60700c519400404401094007252120762030b010600500100028416802c1c03c1c1c24134113003042e25013036080118034a180811b1500412a03a90381da88104c05940078014004000310700b000054129807440f02c04207400c1c05050a441152a24180d0803640180101808924401640750035101c07040c0c94241801081c40203c000309040313604a40a5102070312142d482202c1c0d441b140109281c1b090300040203002c5402810030b5102160480d0011604812400401460641d10741c014000710320b0b035200410f0000d519000108815a40308a80080080182c00501400040c00c0b0014941c0c41514011480700e0380c0110384042804800e200720a120390001000b95680e1400b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 343055611 1250 343054361 343054381
    0x302030a200c15060d080c030c030409020d060605090f100228060b060a05071112030a080403030b220e1905060f07030903020c0411040807180e0109051002071505 71
    0x8105414220702c20140c00f01e800b0700e808211070b8040e1501030800034040e05161258402ea6000c501c0805c8248010492030500c008104020001440089801601d0303030701c28418036040d140302d64010800c01005200e5903000d42d0f1003241e500320546089a001c01c03c0b1440180517400c11503191214425280485503034414454802611014184074240c1044007c1302c07502045601c0c021540141d0010b4010301c80400001c010401e000f800c0c800040542295480303840406103107a02c2800702400180c070a006200401d50180a00040000e0803541201840b010040d1030019016034140b0301c51007500c0302094006180280000a032000f40e101c0841c0a03a0b40900300990785010581d103a203011074014002503c00341c402c0c03091100351a0700d40d0250114100c014100006130000250490046a04000020311000101309120007000f068130f0070790000d032802c83c7e5001107c4071036081220030f90501d034098000541c0401d00c0d1010490003980103844000c02d0400ba04144009003501041d80d14050034056003000e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 343056861 1250 343055611 343055617
    0xc05061209070501020a030804030c0317090307140102030114090615160506060303070f020907170a0e01150522060504020d1a0102160b090d0b160f0f050702010302030a20 75
    0x84048100c2e01003e5981c0012607807040314080c050b0020361000c000c034002130302c102d0b6443d143d035000e4a4080170840c485500015021001e0341c0b4144103500000380e05040004c2038440c1c0e13600070b050100860035985030000d060401941c5016081c862041075000131155a41c02c82c1c04018a00c0c42d03040e40340c84485603940052184040d07142600d6501c640000114249000404c80b4030003640802d0b031050703119541c0e00740007403d00c010300001c0600203c40050400078051085840c81508289004241044816002401c4031384050003a070556490250030702298076814403041102c030b140d1265508000c8601004001404181c1046510600004000340165040e42011403100440030300c01c40002d414100581e555690042080820845440204074045d07401000e0841050003030085680c10b100d0b40d480400449088414210a9220f10030481c0031561042d620341ca841c90a081034031600c070394640060440d005c4e0b407800904068001000a6681d00c00346c000d118943c1d4202e4030700d83c83c1080000104a650 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 343058111 1250 343056861 343056871
    0x15080102090a35150a052e1a0705010e01140a02030402030a06050c0c07031a01150203120a02040e13020405060d0807110103020c1905100b1003090c050612 68
    0x1042c402000c10100520200c81c008410803001e9040c0c01ca981c03002c02903883d1840f0721580654062401111094074140d0a0b07603124041100001600307280c515411a0140042c0144da41101c940a40d4480707800c01421455059601032403100001c1c0340c004048060905c20a2402007580d42005c0350382d01c0d40d81c1c05402080c0c0483c55100c0c1c00300789540380700c4448120300045802a50503800142e0700d1000c03854a51001e50403090111460345442840000c0f207103030002c3c81c1c0c012940c0300c820117001b241c141c0a83c0308007409401400c05607010203042d00002540d80c05004c1c030300680d0300f91050128212640e9503044900512080c2408801450500c0100000c220f021034186d00a03030500d40040c02c20f29000300f5980416a00051b000d042c080f0740d440b03001d40000c1884816046c56070030008030302100c9003080100b4405001105441554510b8540302e070810003d45081d140c0d45040101d410075641e1040110300c5951490300d00000c10000c613003403a030307003511040c0d0105811680000d0740c0103070150702a810034802c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 343059361 1250 343058111 343058119
    0x16030803070e011b060c23040801050601050a0f080c07061a0102070f0b0715060f12033519020a02030a11060405070b0f07061409010b0a0510030905011508010209 71
    0x1e15241d6006503000d481004803800282005030301c4d580004c01540c000b0000c1070140c40c081070902418140c9030013a0000d00c00307504030460040f03420481101c0034000c5540c403001c2840e0203414503801000160082d040c9407403881c02e010501c00081c004160314030566046580041c07007401b1348841044145491124600300e180180200380c03020640c0e00b026044107044030b0409590915003445501d0b0407035086480000240c001da1036220004900307560202060140c40401844258841c3c82d14003d03007051540c0c486091455103921a04040c8150488440752101c000580b9205a995030300400c8681920000c43c292107a01c04240425482c0d80000503100403029500d80c8404469800b850a0303440360300311401026075004040a1100b00c2e01d50020b044500c0801c0001e50508145590b44015500e14512041124224804100382c030301c0709000d078100380703a420703100110118280300c08030b01107800003a003140a154440580d0300030040250b02c001041d20110714003035a440e03140d0305024040d500c0a40f0035403007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 343060611 1250 343059361 343059377
    0x9030b06010207031203020c07080a030201062606160c0b070f020f030315010507020d120309150c14160b0f16050f09010c021513030c0602010c050d0e1603080307 71
    0x3507035000054182c141c9400c000071044885444030114082d5002c040001864000c000c000101e210b010410451200d1080e0008511341d410040f182000400b0700c2c4440e8070070418503014040c680b8000ca000d60304003000081c40040b0410303010b41550403100020b00105a6100c80c0c0420540540c40240c14419100c90344c00d88458201c0007280301d55900080d50070242d0782c140641e00d66039960150004299a51004d81005080c01c01502c80c054800404800785011940710b81c101002c201c03040c1e40300203110f8041481000300180b00f803401045c0c403040d100039034094007001404000d9503048499464080303030300c20358100a0b403800e600c40301e00514041d1610b48203069071003080c8800900034415140380c585401140c50401690000466298825150990b00540c0680380b03421548a160001e0503800c084515150280346145070000c04408680d0002d400c5900d4015024201070b8031808a0b0780032047d440c2d0105030960001402d030709190009680c4101511031010010400c0181c0c009940700700c03213648078028 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 343061861 1250 343060611 343060621
    0x206220602010207051e070302060304060219031b0e06091504091103041e03031b02030c0f16031b08011b020c032d011d01141308030115020f060709030b 67
    0x200f80d00407802c00800c150030410351400302d21036011080840c1c0103d0411220f40a50701d401041043e8010341c1c05403100350700000c00e544000a0b8000c001e060b124940f0342001001030340040300004280e0042d05100f0428160a5032019a840304142c400354500100041c01c22446240c000c500703641301d03106807001076040c02c181c00d81c001d40c410182c901c41d035001800e00b20f03010400800c1e500360342030015040b02030581e1002c0e500d03820307140050310405103a500d80043d41e45400c0506031503d020303058400720150360702c00c8104480c4007224407640403c5075070001003400b22403102c000004d111001600503000a600e408005070410418006803071110466400740d07110340c50742100b0300d81c45160794807100d80c046141c28888070a00d9a81d0380341380903005041c0000215805440344002240100d0324103414560744a00e00401d4801070f01d110340ea007000305000c1901c00f07044c480c2d8603403415001c140304a0700001092500482114002c6c060181040d0362030042c0d0b40303140b8116070050135181160009640315880b540000f0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 343063111 1250 343061861 343061863
    0x110406030605151207140d0e0c040903020d0f050d020c0a02180405060c0a0c0b010816080705091315020d05180f060a021812060702010b0303070804060c0c030206220602 74
    0x5101d1030b61007210b05280500d1341e40720404c0e020010b071444080000030b201e01a01102d000c0301070000140000c1010600d030780a805954642181a80781e60b01c00c929111894001940006031040c0043e864103050381500d06051080c1e42c00e01800707074030100841c000500740d549440040382d000f01240c801c483e4034400c0390041001e08032000e012900140b40741e000303201042c2c20b90451409020401620b243c60b003500611580d840c02c00358400c1e80900119030105c04040e6000346483d1030100501581c800034081c162401d0b0000314600700c06070107160014442090041402004103010b19140000101550782d42240039100008160441e011510481e09410100b03440c080032840d0040c40c40c541008219544401308040025480342c0704a4035a0340543d201084144c072340c201036070b41031316000d00a0091854030704000b0303080d21144102e4620a401c10008600095a00c01c2503406a401c2450910303424036492400d1159050a0340020f54403040210b008c840340340244a41d002c1d000e210000098481d41e0381c050503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 343064361 1250 343063111 343063129
    0x30e0a05190806180309190302060a03050a111e03060103140907030203010b1c02040506040b1203071104060302210118051b01091208090f1011010509030901080a0f0b04110406030605 80
    0x50744c0764100300402c144601d0510807480303140c1c1d80c41e9258842c140e43e03a400645103520048138400401d450b80101f0070082071612407039410240c4840d0316403074050410300d030450014180329a60b65034003022000c61500d9101e603000c0700754920ba01448070701c10300f049402039641e8001c42c0b0080b0310960800f2029001070926013002d001d852280102151600c085130b0030800a80703001400140c200c0e9882c01c541940e50b07079041c00122804400c5010750343d580d40d9818580c2652092240e4140558100b0b0340420040c0c8034515000c10071058210101c60000b00c0050030b9000d07102510810302c40d148190580e1060020100da44100400078954885074aa45a00152580b000320b100c0c1840302f40745881700e400858580e0000b482000c40003064114814810b100281851001950000000d03024070300c8520b040c1350902c078440e0860b1040c0002c600305010307500000d1980f100200341685154a981c00c8901000060f0400210030030024018000c0040c41600d940d4141c002d4403ca10000b13040600016040c1012808 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 343065611 1250 343064361 343064401
    0x2031315060f0e150a0b070204050a020a0804021005071703010e0f01080c0409020a050405010603140906041509052d1908040509100f0f150813030e0a05190806 70
    0x74540403034600340000081000013010800315200104580c20160784030321305c0c04042d06902100c1515281140180011510010700f4240341e01d2040001010864201c100103a01641c121240078418208800480d200d01500c01c1c01800d4187c0800a1030940600002540c103843c4028620700c855621807000c90007060082c46500840c3c2c11a41c00001070b07040607040654901e00103841d41718450742c1c9501007001c50300240e0100002070744c0d4507800e0400708444001e4980204081008040d40d090607140c64034500302e003441d15a246550f9000c46401c000c0c007802011002005441c03284a44003a2854415501c00503800105050065811078080702e00c3c00d00b0601081ca4004d203195040605080c2032181810001c6e11032280c160011000042104410f1031100c00b9101202c0010aa14600b01400b840c00120309420000c0c42401010042d8100442a910340190380601d4400c40702400440440e545001a40016030080c418000702160340b10707070140c80d40031580d42d0811070b10743e03035181c045903400c0d1045406 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 343066861 1250 343065611 343065629
    0x5060f1609031401020f0c0616020a08043302011b0201060303051e0c0304030c080606060a05090f012001270308070f02010b0d050c030d09051c080d0203131506 70
    0x7000d0000c01d000442149010151800061030007049901441d07664004070001c1c05941e0080e410040c2042d142a08032007038103010300003408505c0655031540c07524001c0c0c2c00740150080601060000c0d80000d440c240d90000c0403901c020f5a87d401c000301c001d001e03001e00102c41014800c41034500b610325105224840c220ba415544943c01d0000ca10100c00d031600c00ea090014100384140610f1400020600c0200004c4ac0300d024454032040ca4000441e040c120000d1005102d64002c1c80b1190800303400900300c4490000458802c5031240c002401039442083d01043c8240000141c0a50100070701c05500100c100340403605001f642d59881030103034040011008005002605c0e850104403154001c1201c200a040c0a0001144119045003c1003690301c481c03509403400d034003900c0d01d4802410f0901500e00e401c1880d00e0044d444a06010121700800c0c4055004c0700320041c40180a001c1c0040e60301030740c40301a229001950749042480710007008c01c200d100191f0b0028040040c1e022010182d224034411918610 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 343068111 1250 343066861 343066877
    0xb060d020721050418060302030718061d04060e151504050a18023312060a0609053001050f01080610090b0111070b041401090f0b03101205060f16 64
    0x140c000b00b0070003400d814030405d15240c0d030300840181d606015903805061a03100101b44058411610001e40d0301c1d43c0c0c00142a10304848240c00d41407191044c56520035045200807130840349000401c2c0c40c003400c0700c0c1408443c40c1b41d0720511103911010019150003d0080381c1c1880291580c440c0c18003164010350608280c02c4120a0301001030901841d6034007541240d00c005043d240d00c01c640328041d50040407a10207079140020f515004804658203050300220180c1d944010704d0300380800a40b480045001d40e0348107682c500c00c28081072561034000c492610b5141c01d82c00c00c035245401d0440c081d100507100245d01624110010811010009000f07204161b40ba510005c1c0900e09120b0000500182c614141007020007560380036241d2007008074000612280801c04ea9032840d0840b40c9400e090401191410010110030412142d42c60034094800c0e03d511f44d161640e04e4880082244290b070785648023541040041001009001c00880c01134810040c07070300000c3d000d80d280072103074a010700b80d444400f021a5200c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 343069361 1250 343068111 343068119
    0xf190203010f1a070c06080a06080105040b010b0319060b090a0806040f02060906310b0406020618010b1309051902031b0112021315140a08040302010b060d0207210504 73
    0x606090000e90300b01c031443c140751140350b0302c07021343e41200d54101d0004031345043d0500024214a1107458002c10583d07008010500301a500c00e14900018030800e4010390b0b001c030100e40c800e140440e520450504620003041050b55681c60030017580c0000d0b10b120b200c1c89400d400029222008a00b0600c11a440f4861030072801c80c030380c2003000d82e0300105152500002c0074400c0031030018604a076155014801071041142c1241c02d03414a01c04040c0e03030400040890240010810315030000780702600080004040112081c841159a005010710704e920360340700141010080003c1d8141c1c2c012481a80140180d41c4544002e043d0441680c0010400035016072000c0725104030f000d050b0341c00082ca03141c1458001c010341603002c2c0c1c0700f0990304802c6d40c00000c065115002c20013105e959400c039180c40302c0b9003054801c5c0c040d0340c0c444001500a0b100030740e02b8000804001400c252003076011b0551100000e048513150600e40d00080000d4001000031101e08648200c5403c0c0100401f40b10461a40c070b964500c4d10305810 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 343070611 1250 343069361 343069379
    0x1080f1207080426060a020a0c0f1e0b04050c030309130c020109150b0f1005090d0f0215040e0709030209150409060207061b080403091413050f190203010f 68
    0x1e54402c2ea21081d0a0001044806003d00d100544000c0481c03041040080302a1050520070b000d00303111401841080942001a00910024a4590000310015210441c0d05200050074401e014040314640f60403414404c11020b5074015005074024411196002200300c18141c0d01d20a103c085580150300d42100204e01c809a041440e24a06178400410289601d03564126041120b140002d40c003074554013100b00c10b04041c24601280700c402c50381407214a00e90324000d0603e100382c40b050b0340103d0a5940e214140280e0156140751203901074908242c200398110181d4a6412034000c0d40300658003580070481d0030b840740303201c101600d400a19410700c540740d0082d418210b042140d800b0341c10907100c00b16a804150b03e48081c1250f03c0c01804081a24035001c1c030003900c8000302400060a000307405051201107903100c2401801c0c1c0d140f100350440c040050600241c407503c005024000758034141402c0052811000c4809401403401c603071000c1400c4140b030030f04d100b42c2c00240107a50301114840300c00c0003542d00c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 343071861 1250 343070611 343070617
    0x301110703021e030403120e0904030207060e0f150307171f0602030c100e0a1b050315010f030605071101022230080f0f0307081501050703120213060c050601080f12 72
    0x30908107019234005c0400451081d007000c03201940507030062001005465000301a540c1c032a442180c2504c840c0d642c00e00080c0300d6210780e81c8007503000340b004400110344070f01504a001060b201218480090b244c401c5001c0c4405160f803d0960842e0300900d40003038018000819904071010000c0500301400c0c1410045004041d19280c0d0301007403068548000100e2501a07070a070120a0b002484001c40d410308043c0752400da8400718011501c2c0c00c1c00300401c5005c03c0c09080000341c0f6480a0041510340762800202d44d0086001442680ea5100080c0c0c103030385095022444241c55840004201d265503501600d03c400044452100151400c1d0b0380222102d80342102c2c2001140c0c41003c0e81c60801101c04054030f2240c1050380b840c0c01000000040c0f00308036030004402d0780e001b800020088144154030000822038011954000c0600c04002801013120b5107640503140024610070b840c80841d690350100408503e2040300540d408c2c09007000100d405070001c100c00c1207020f003082c02054890301004e000444c943c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 343073111 1250 343071861 343071893
    0xb060328031223040606050f060d020304060b060d020304020103110a2304080604030522030206090927012a0c021c06050f1806010806070c060603020301110703021e030403 75
    0xb0b503840c60300000c0300940714000329000290654040c03040c6001c0c82c00804903541504940d05c40c0c0c0303003280741815507560101250318032001c1710009601c0b0303141c91030640050b001d14450140d1218010441c1000801d5560185200328001d90302403000c00511401d5240f280b003030803a004005020401040c074a5852034900c43e040e146004200c82c1340960325441a800e250f0251022000944000340c3c0f610018854014414107d486400d0325400c54659800641c540c0700381003070703940564180da00061091082100010210340c4800c01020200480484d00c4d00810148c00e014204404003a420b0580284403d41001d000d0803070b44440c00c0c1c209494007003206000644e0740701c41d00b503107502d0003030703800508280605030082586501000d10307810001c140903030300c0c09142411845a440240100b004603070005c0c025410920314203146400b00301b1350400c10080c180b036800c065055802c5c4540460011180002022100d00035420742d420f0011a0030718204040d045442e1920f543c0c403d10052020400c1d19890815039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 343074361 1250 343073111 343073147
    0x2030114010f120809040e0109030207060f05120c0705012a1404060e06070618030e0303070b0c1b010216020a0510020604060f180b01050423180304120b06032803 71
    0x40c00400080545803007e0020704240d4450071030508064040050300003a1902e402c0903521f400510703038014440d00070314180003410150f00011403140600e120880e141c40390003400a01100d07002d9001c1000c035400300321040b05010403040300d109003188581c0e20408000071507800d0500e803500e049001ca4150012100080d40303e0b5003000500d0000d0700c14407485c0900c40703003200440c0001005040107003100c005107140034000d40040060b1000101c1005c100781d801401090b2280d11041c000003035280b10311415140c4c140640c8009420142608004150381004d0f1003105c4004400307441e1400e11140507000541400560f012034041400224541c101c02482c84c1e44c058005040956900208a64021240d0548807050104018001410540541040d103600040840400d6800946607034100344010a5068619120701300070310744410900445005120035414000d00a00170b040c091803104041c0c0701c142c828030805203619007110100d860126812481e4440320407494040c0c43c180c1d485601c0d090080f41c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 343075611 1250 343074361 343074367
    0x1d031f02160b01030303050a090206071704150215010f0509010909020105071a07030f0203160e060d020f040f0e04020607151d01090c0e10060f18090902030114010f1208 74
    0xd001e808100088289004921260b05540b650801404660000d0210a602400c0c00c00c2080580c41e008215081c60b640150074400108001103001c0396030050750820101b0351003901111500540c001044520380b501d518070f03650f259984002e4482d550703615101d015080301c2e02400410900c001079001141d07890060604500d00781c00c0b0f40c1c884110740d00b11038480c9030131445a01480240c0c2d6041c440e19020713510441085156040620483e402c0c904101d000c001000f56012158849403110415501003180c1e040055440e42c1420128400541040c05007214680f800e4000080903000103105501454000d454103140003000d850700204040480a10710701191a0401c0c444a81000708030103520040d4100000b581062520f880d08020312180e121200303084c0002c1c148640101c6016080088480c0d42c00d0000c4d000780d04c2c40b421303154218200c02c0662007001549001550000940050454034401c800800c01c00f400e0080101c5010402e000d1000601c001c054184040300307161100398410790082110b141 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 343076861 1250 343075611 343075627
    0x1302220213060530010506070311030409050f10060509041a031507110703050706030e1608060f010806190c020a0204061410020609121b0f0d1d031f02 66
    0x31115080d9808140003a00001c0c44c0006030f203004551070501888000402c0080c20004034410500c0f07010b0080a2088000282c4001010b00415008410304e40d0501a0380d140c80d501c0700264004c28081f01d03012080080b900001309680742001c20b00c800d81e050f58543c10308003082c0b50180001072015000640640e9040c0c024201d042da410805407031351441c003086508180c80e0607030000f801000e17840c0301820030f60721a44052000540204029058491502e070015203070010301106480c040100c0000103642c40070f0440410501c4000c54007604c544001c82008400780d980d45003c40d5500003c88a1040540070790303060107020f800680100c0c0c43c0746498811134a229889400042c1110300c1c6a00c811080b20400c00f03240107078204040001e84050160014010500e04101c110703407526003e20780f0404551000038018504d40c6022105003c040181c022039500c80446103055645010340000c1c0340c040340c15000e60030000300110348a401a48400f40107000704c0740740028040300c100098a203044880b602400180 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 343078111 1250 343076861 343076887
    0x1207021c0c02010e0405040b06190506190302070210091a030106020a030e12010f0605100305190b130614090a0e03070b0901110a02070303120605060403080703030608010e0c040513022202 82
    0x6c0d010314003650079503089003003200400c40c030342039030703000305001c00c0c0580100f007145907245015104145022101c80700072900000d4110028403030072030001d520102d0b584094181d0b40d807110850050362080c9848010190f46510009900c0c0001d124160069018900040000344101d03544ca00c42003024009000780300141000c542901c0180482803001a40c6074001c0180b45000c000e050302ca805203040400040c24082c03202044070342280d559044143d207030b010084454548500360048403440c0ba80411005458401d00708480c44801c030440d10400050000c691440b145100d455580b99401004500d018501e686038003524a00800b4849103540e6000940c0d400f0740603400415804050b81c3c0500700460440c500076100660101c1011091440e20700140030703036140d12003110305a90708120400e4a45405184c102c0280c005030300882829401c3c07a540c030100070300c0040c10340c0c440325045070280f00c5a038562040042120748001e02a521502d070342000661210300801d062160258100701500d0203d00d02411 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 343079361 1250 343078111 343078121
    0x18010c0606091e060f06230d0f051807060f0905121e01141801021903050a06050301020c100c26010e13020f060c10050901021207021c0c02010e04 64
    0x22881c1c8544500d45040ca12560080e01e41d40702504800400c0000d00301145060360340c043e40502d02c1480a8180440c1f122000e80901c14402401c2180f0b07a0f5032019170b002c0f960080d0100d183c03101072007401c0c80042403058003800001c40e26000302d1f0b030081202d00d01c4c20744c088521044141d03422040c4a1131000115264030780740d000c8018070b40a04010500398420320000b00342c1d416500d0301d615081e407422800d01d807c1000390404e26001419100c080c100500304d0f0350054024824042800d1403166990800d92040790180c01c250b1240c940032200b00085541d030700c2030500740d105005112040317420002410b020460540d105042c13090036031904000201c060303080e1050014044141c00c100c00380c801c0c010402b50007444c10b81c03a0321151404680600c0a010741c08038044070b00c0030f544544519404245019003a204200710620442d0b02c080a02c40380c281481424000c2d400848403058894800c400102010700016200f2503080c80c41c4040d07440c2d00848501141c000c19444c00c100d040000446029520381d4850240c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 343080611 1250 343079361 343079369
    0x30e1f0e0603060a09090b010e060126180105180f0106051813020a030b220f0f031b03030e01201210050d12031d0a15020c1906050604060b18010c0606 66
    0x7c44032550505d9910240303084010070070380c100280401c0c8480150b00002140f00b90116800040c02d56448400c280403071a081c521700762109618150400c4a69400c18101c40804400c0f0420703601c002c511588024241e600500071150060b440300059910030030603c0c0416401441c01c840c40e040e0014990002e010841664410396540c001003007030040e2112078a0a1900701481002008881e054595855941c64960000645000304004d41402898014841c0007004040305903015a4003a8034a00030300100ba007146586071643c0303005860202c501c41c81b400b08584000480d080c0b4102419088911010341008240340c1d00980c522000207569240c54129030301e5944a07415103d6101034040c170080031030308400001d065595004510002e000e00200b003a01400f604400d46e45941700780480804003902ca008142001489003080c8440c02424800b1060a040d02c55482032046488050400c03041e07e11500a12072400410448003800400b00d50504120310410b060186040301c2a84401c1c0403503002d544 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 343081861 1250 343080611 343080623
    0x90d0309030c050303040f120213060b0c01050a020a0903121b030806091b030c070302070e0a020316030203040c05010507020d1a0702010c110a020405061507030e1f0e0603060a0909 79
    0x2018001c1100b005600300140000b40e0080d81014a8501060541c0070300e0b10070101858075900480c419512018103003125210703031120038040190303514441401507201030701d8002079502e86000300311140c41078021100d108285075540e4440504640712440010f851524082c12710540780c00d003000c400030044480840c10301a40b1200b545283c00c40074080f0003100240b035105503401c000881040d21540c0420b498001007188086034980900e403406a240180030b17003018084440d02801c02140031141c0c1c004600c11000e00300c0c0d40303440080c0c200050b0180d0000356001012110840780501c100d51150010b89039007400100010880c0700b054030ba03c107848504981202480c4842d0f0104000d081e0240140440d0700b201e803801102c1e0700721a000c0d813919192022002881162580003040342d07503840815041c14114065001c0303551b0749a9180c080d00c1442010750060160007407025403202111440c0b15080c1801d210344030f455110886408100a940c0018007155001d042840040b808508c18494a01c1e1284100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 343083111 1250 343081861 343081877
    0x3061802041d060a15080609030d140f01052b0f0201081b090d0204110a020304090507080f04110102030c030c010b030709150e060f090703050609010501030c050a0509030102090d03 79
    0xc010300c01650000705102e40307101000301100045040004550381d1251401c880003038806104000648110b0325a4000c01c0c0a01c64101481110400070000b0b00c0c00124020b010401c00f000428121a484011a00c00758101030000040205080c500c4500101e40d58803c1074100340c0c40c1038000520410798150090700d083d40c100383c1c0301c011540c200b00b01540003141d40c0307518451031040110318402403051140e030b18000e880c0c0800410840d1103075008140e28403291266140c4800a02d0b1000355a50840e11404204508280c0482d01403406445203c0c0600032440000006a4840d2102c250f4bc805048145045100c00c02503004036a40500250000c848240c0000c070700c02441100f00341c40c002c02900030310401460004910000401c010211049521440501109550724000a985440501c90035500a2088010061004e40c564011417160008540e8809e00e1390303c0d1030045040710710078618a00400d000b0003106501902071409852031030342c0107001524106044001c51001c01040304114007042c498 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 343084361 1250 343083111 343083113
    0x1204050606100801051c020609090f040c0506030c030a0e15072c010215090a240f0903021b0a080706050903190b06130b03010603050607020d03061202060c07030618 72
    0x107000100b0030624900e070411055060900103490300d080d0052804802c0290751a1500b151a0b071410390320b00c0180102070209510304840050f0244204890848540c080c41c04086218a0950f043c0ca01400b02000605d0035665418401c0d00206084a80d041e400e2040d4002c60703d440100c0c403d0103103c0e0032541d8856078030701b40304128244891074045820075070052440c03006030341d42d90026592400d0a80000c811460b17442d941d5101d4103103103442e1400b4201e041c910f00c91050351441e102c800f44281d60311034802c00c910001503141008440ca0128014016000b0803034a116044000441c680302250080200701c84d05c1d034900400b46041c0d0198400d0020641c081000882803400344040034480000d200483c210072090390700d2441080000700520f108440c10040000400020b5000556800001d8020002d1039240e0400a556400841c0d07903400510400c000c00500c2440390184070200e4003032603080300a425080c1e00704203941d004200d10b255648140d400000c0030035203d0003454100c0d055204071000e80707030312 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 343085611 1250 343084361 343084369
    0x50903010b0a050d03210207050102180d1106030a0e06090706091d0703110f120114041103060607021f1110020a0203090d0203010b060705010501090b100c060c051204050606 76
    0x5022111449900c1c000400c21003134961142d240d500b01d905240c41c183c1c54142d0000080c000141c502688071007480030416100300700055009101100d0070b54900c1e0807648641040084800d000c1c50b0080904600d40c1e550622400c010001d1600064000d80c08200e0041c8031000514101c000c0311044542c0d07001d4035040004541118401c000791010b02641c041c2d546d0074000345058003901070031100425903102441980304c9550015250400811410384d551540e2010419041c1c0b03034213010701c0c940d0145a4800069a18151140b5203d448107040500c3c103544d154802c001441c2c202c04016a0843c480b1020301c0202c62880d51001d40c60803042d154180360f5014000600d14151b0701894074a884d5204200216501e5000001d84510b068129000e0415000a1000c240503100c1c42084a07000344008c56014100700e4103402c11030590321006410003441008408009003404c40d8a04200402d0b0840c01a031301180007600104185852418020714001218036610402541240e064629030806000d002c0c0b2468 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 343086861 1250 343085611 343085621
    0x31b104e020c0d110111030f07080123010315091107030908030a0912170309010e1209100807031b0e01081509070c030c1e030f05071115070b010605090301 68
    0x158040d811410411090601d65541c101141a40288401d048410341e20f51001d4116403201d0780d40840040d01c1e4102840c0c141c035040c00560311000403c400e00c00110782d1083d091001c2d034508841c614104600c480003c019001001001c01009038007258950209a031080750044c03083c0e8000310b8007c0395840089040c020300002c02608001410340007000084142d50f40a107000054960080b800781281d0454545240c2c00c20011401c65400b01010007000030f501c1041d03101c0110703500d04038141d400440401d580d809042c0700d407841d450750100400b4003081e512841440b403e90302ca052030600003030301034482c2501481440025411000143c00341107503403055a10417141904811906841d1086500940024a810031300034002d83c100800392903c84180341c441c1c0340d000403003a084800c11200c0c078000361041705281d490b69019804075410100d000e00c180e220350101c610072a0040420399000201d0000c0207886011114000700140041c0164130200c3c1d010b104280c02000b1681300e081d0b40780b80e003000f81425a1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 343088111 1250 343086861 343087007
    0x40b131104060b071712010302041e0c03020a0905010e1503070210092108100b0f0f03100e090a03140702010c14060601080109020403020a0504092906031b10 69
    0x2c5c1c280301e0502080d42c18200141900e40c111008100c120602c0c0655018403091840480007600700350340310301e12a03050360061188010301c0d03039824800c9880d500107550000403119001e0300311700c2c620258101013400034003441e00200a0f1040c0c0e000181103200181c182c81d041c1ea410748450b0f00d5138101100d0100202d00180c000281d50402c6103983c40e1078000d1681d0f454561003000a5a0b4001900400040001c0101c900d00004c07414a562070342804400041242c0c0503008141d41848186c0106114100001d0344c607050302c2d07040c0e4409030504080c007403a14642e0002403040f0f05000e100c00510380003411402c10b00d0701801c3d50300003d08084c9400302c00108011410f81c0401c0039184100002d01c0942c81d00035001060b40c0f0240c2d000b00304841c040c600b1407048000c2071210f062185050840d2414404103648080c010725003182240c00d0800000e500f01c10f104103004e0b00640c800c900f50354016110b40a40400e8a00c040c13416011300e000e11481900030f91101810b81001c1290075450b1000d9126045070f11407850031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 343089361 1250 343088111 343088153
    0x110d02030303090d0f0e2101020913050109050a020309031e12010602010209100f020c01140918091203011d0702010905010e030904060b030106141b10050603010b09040b131104060b07 80
    0x240c0e001b8001c281c1001049662640c034064401921010740b0094048850315400500300c50900410741c0e0440d0010003080c0620050241003402046003030005000362401240d00502039494541482550a0f0150010410b0950400c0501c244d544030414261a14000c000603000135980d001103004028102c824100d11606104a80742e050080ea54009a40d40441e6803e08128145250320f05058203a401503510081d800a07035281c0d010717840352108983d10700503032940d01290b0b051100540c0303c000c2400240102d42c2d6402c1e00050206418000c541025001760050000188023412510340ba8207507503041c1034490a951001030304207510300f00361140100512040341c80c60704550401360000d0014641c0a21031441101c0490035002140da0343e10034008020348081103410341ca801746aa900902001c07a9401d209520702a60010207003081c65626204c2ea6020090960303540c1d501c1c00a4082405540e1306a50a842c0c25000499030740b40d6106240280c5200080203032135640d18a80b00002052280c580d0000e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 343090611 1250 343089361 343089377
    0x90b031801140c0a120b0d08040303140301150c0204020912070f060504030b071116151d090103150603021816020316020609042711040e0a110d02030303090d0f 70
    0x110107043c00944600326150310b4000c2c0200386191002014001c004003030f40c2d00082a41d940030801c0205402001240e22a40343e005000141d100e010815010910407102c0b04d4006881d030508241c458200e800f2081c0c0700a000609000e4201e02092031200d076600c0c0e05070315a014020a100e014110807008000b40860f2030007900d01030543c3d0303a0804041c0d014006c034013030140c0f90700d0300c2c800290180595418408001541c0444554450000b044880341040708000300c2e407050b210420301e01300c04100711040180030301304540591071a40d8100036030111122000d480c941d01c85000c401030341c5500b072010400f0740102c101d0205040803a24a000ca039800c450b07000030b55000301301100d4402103070480c06a040d60112002502e4a0711400424060418004441d0070040c10b021555800303404030f80c01200c1c01e0300500301c0034260138074881440100d881103006010164008914030b000112444034141c0303086030241c00c2c52609249640400c0c915041950002070a800c075110740c0d40f00c2da0780520003480c41e40c614a07110030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 343091861 1250 343090611 343090621
    0x1003020f060f0d05091905070501090605040e0f06010306080a050321060312030a020708040e091510030206070609050a080a08090a020a2606180601050d02060316090b03180114 77
    0x10b40d0f20903000c4000380c450b110400951150070601003040d002c400a040207900030964500144c540300d03d4060140424603510022620b1407081c411754081c0c40384c204c6040300c6512005a01840750100510160415032101004a0b049906200e8024454442d20055440742cbe919150040601c1103045030580c2e00d400c0c1400c00240b5500040c2a250900070810100d40c3c0ba22985c014101034032420b075014200f0000000d0000d031071151a9400340c451507038202034030b09180c3c00c41c4809000580c1580e1020342c40c48540000d101626040000784800da10070381c0700051050050341d400313003040c0010701e0588040501292003850745403c0441d46a1004191020b40082502c690000f01c2002c001e01803a641408200007010706a070081e440c00c0000743c030b0003045070010b1030403042c2030300d40004850a808141c001c84000050900b41548900222035005000d5421980c40e40a40018100c8142c0d410b01007101c25400064401d400b540114001e5540c80c1e14440d80c00306000700b09080d101e01c0b0030349440b10080203007000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 343093111 1250 343091861 343091887
    0x20030a0e010252060e0f010309030503071b06050c030601080f0103080403030f030e12040f0807050d080a210504060b0612150a0b0c07030303290405130b1003020f06 72
    0x1001441c602640081c1118824001c0510003e100349400007801c0010b00100d6242d400c82140e45000f40c046a0269003110084011001d03a101c2640040100c2d000340080b4a10600428918a0020f1004d030041c6000c0310302d44405003590000c1d18040d0403c0c200209120083d6400303070b4242c0c0e016058900c0c0328105c0d4550b0f03490f8000b81c0705030b100250401013405d2400c1442e0348a0380040319551140d41c229540c5840060320000c8540c41485404020100d088002800389030105d84081100e80080c00c1e0307482c01119032520542a406104101e04101d55601c483c032404000c80341840443d10007000000d5249000d140001c01c03034298040da60f00c129024000d048005c010700100710351240c4c4661400d1f032005a0304000c00e0a469040d0080b0400380f1011902c0030300707400d000455134101c2c0d00940c4d0a01c043d101d214545031209008510b410480300801129011078103054005681005c4102e40210f401c6038181c54818456600b07880301d88d007080312894200700b9490820f2540d20184030441d62149811000020340d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 343094361 1250 343093111 343093183
    0x1c110924040203070908150105040b12063405181c140309130504020a0f050a060c0809040e010c09050301020f0d05090c061309060e011520030a0e0102 66
    0x34610581d0004002031040c1c2c420540d44000f420108101c0b00c00c0085100580c0f0b03803010034003685003d0ba103001c850720b5443c0350000000c0e080b0005100500015120a80421102242d0003080c055080303404100e0081c0c000c0c442c1c441c040ea06115650503461300806141e88400d000c001c40c603644074180100305501d0f0480004142c00030341340d0044c000d0004140217410281035004095885a0112741a0031002ea003824035081244654400c5815034191a240c1e100703003984543ca80507694000001203c00d001c4e40740070b01460f281c42401021101e060001e4178000034180d6140703207042c0b01c081c0d450f4003400c145107400c0f01101d805880224025424210041e41983c5680903030803004081644520201d95802020701201318860800b420142c0c0e2503040c091555558120b0344a50764038546040d4000461405000340720781a82e600c0020001655610681240d810b49041003000f402c0802d0700d0f1000e4500d000b04001c0a042c00680c0700c80d03070150308000002e030403d00003450b482c51501415640e040c280d0962000307 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 343095611 1250 343094361 343094431
    0xe040506030a060c090e0c040b1209010b0a0f0501031506082701020403030503100603050f0408091f0305091207080412170d061518141c1109 62
    0x825a5440380080d00e048401d0101810082c0350407030901e44641d010441805880300c19405060a403641c03280c2548912940c82860101c4d40140110300c1008074500c40603401c2004040007050030101c020004660000542c00120709000c5004100815601401107221451400050710800ca1400c41c0143c030030740380100504080888a1055000d5400c40400d40070303a0071080008548070780c1c03a45405000e5a00075284082007407401c203000100c02c0e2007400f6244c4129014255950551150740c0c038240b40d84c0201c141580c0c01090340080098040044141401d5981da42c1e80214650402082e907d080414407211031140300400c120120100310020110341c11241e200f10f100303100d8141424001184541480462910507001405102940d416081038090b200c940400c2c494003c4200010380c0c0d038410514036002e2004400c00c0800040c0d0810003d10000c2101130641c518140b6401d240403d01100141c0c201da40126142c44007030141000c4d009980d02100c0c4045c2c00f007407200008009050b110301c03214 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 343096861 1250 343095611 343095619
    0x309102309030102040b030901020405150f1e090d03030b1309050c1306081603030e0108041a0c0d020714010501080d082e030809130605100c020d0515040b0a09030e 72
    0x3051601d60302c007541200c00401c1050300d00d030740b00d0400c4d400d030030b0203544940715080c41050f84950043c00318151000322004030031300c4413055141c00303088250303008030310310045e881d489180c028010142c40d512184400c100c06c80c420b680001c0e0b00c03a0802c4c06c0054030009203201f4202a841c01c0049000520005020030718070300c08403004030f16882c3d40c100540207403404c0d401070140340c0100940058040030b44001502980c0c800d40354543e05091080044440c1d28003160042c0008900440b103d540b0303980c0500840e0000ca4116a5520b40b0708040100020303030b80221822680e41e00d04003901820700d0000c0c0f042e103014080100c090480e02150007001400820050481c2640724103041d58000411002c0314100108039101503400b0582d90380c0d05000078140c1086001e940950709900030380f03d10000740c1c4640001e6900080c40051300d1151000b0440e1101046002280c20070109201c40300880c00070081c10700400e980a1852905181929203080710420244c62a1078003800c1100c0304001070f420114101c14024241c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 343098111 1250 343096861 343096867
    0x506120c18090c0a0308071a07050f0a0c0b010f0f090b18090a1718030c060d0c1202030c040f1403030a0c1a0106051305060c0a0201030506120f03091023 67
    0x20100381c10702d0050000194410050800041000500c40141c00102d00031a244001001143d00d4a0380c1e03041c08480a2000540800000402030bc0c0b4501801115202d4074080742a5410f90b03480303440012081e000394040714001901000003500140d44040a030039204014880514024003140032b41c82c2c00680c0039183d894840028104070820044151110303003151070420b03070301c042624200d095403005411400064007452000764906000a83c00c0e6205005410245400e0202c1801c00c01071100360151020005840420740400111b40041e50044a001c440e6641c1c2c2e600c2d0030212000c8104d0b82e070110b83d603031540c0f02d8640351994001c0140c405180c840c0c2070010036981e441c54040000c00441801401038100b800011413400c0d88140546144081e580c06801c9164a41041101c5402954546082540100080001944203802071900320001418a0066403404800c0d01c0c02d0600f0742d95003428540c0040344070400c514040925600f082c1c00c600b041c0e40038603110102c0341090550070040103101d070800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 343099361 1250 343098111 343098121
    0x30f07081b0d12060509070909020c0304050307090f0c0f05040b03060604090507030606080907050a03062007060207051009020f040c0509030a0b0603100c0f0c060b130506120c18 78
    0x1070040110104403510580e402d070950060003602c202c40f081110081da502d4082c000c0750300d04014118a010b034420f500c6041000d45403020040207944102c04c81c0030366007c21300c000255600c041001c01d0141550401c00b017180540e03c401c4e441110241c00c2904204840040702d441c3c01504a4125416500e2002e081552580d94801291a900c135560109400d54600401c1280140e03041d4080d01c21341c0c02c0d0f5900d561041c1c40700d11000d5a41e0065000d250307808003074010308200242c80c5501001c051102518661041a0040441e0140f50050381054541036000280c4408000040c001e0134414818100204203049584d00429000030805481c10302840c0c0d100780304400d1a000300181e640c5610014200c8000a00300c0c0750260007400301f07890341da01920400800ca603040c003607401901e40c141455a07504020458141040f98800310011081d682c0555644102640c0c5d01d610b03c01d407050102071040807425080807014010001c1e806000312810760004000101c00b0380e2265030f80100c19030345440d01c407c0d030340761 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 343100611 1250 343099361 343099387
    0x307050319020702130f0b01050c0d0e04090203031306140a05070b04110a080703030e0f0108070c11030a0b01260309010e0a091d120306090f1306060e0117030f0708 72
    0x16030101a6001805c01c0400da41580701d504020000030f0301040500c4485034801c010740f8a0b0081402c0100c40d0b401a9284020052240c11016100c1100810100d1031b041c8503000300c0e043da800480080c8c0455441a4180081900202d6036541c1300321241d9051b14002041d18003c0150241c4400203210302c5061020900b031000101c4840003e0f00014046950244d440d2900303aa01e8489200072004102c00004520325840c0159a2102030401a103c81909540f4114121084a2114000c440c0c00c2c0440c42140301e1510100a848600ca12401104040c0d50420100840d12a08001c1c200b03000e0079901e100010f440400300548884d60020b0070700c03030040140710740011602e5141d0b400001f01d003454031041c501103c2e6001c03541003000c0600015203600c49038400040d40e8a201c2156000d80007001480820200441d07014070740c2e40001400f5101007005003941e04c1c1d4041c3c0c3e000354012080c4080140040c480d4a201c00241c610304441c00008500d00400351100f980c0600540e24054441080468a481c0c1d03405 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 343101861 1250 343100611 343100617
    0x171b0f031c2a0b07030c20010e15041e2d1406101514070605010501090608090601121103030a090509060d0b0f0405120c030301092304060c0e040e070e0c030705031902 73
    0x4462000105c071880807141f113000b40100401c0114610030060039101d11a542558030740901d0f00642da4908081c0010722035414410184000c40380b003d6040520803c901c40302c10a00180744d0172072090304920302241070a03101b5020002c00b848090708081c04bc005101c1e0850030307040440d00850403101d122010b004064860000101c102802c070400041c02d50100708480c2d000905271642600e8030420240c45003030488ac400c10803150029154400c90062043e80411251036210a20990b603a10f81c0100110100e0305540140d0f5240010654603d01440140f90000c101035000c202528615203604503521401d880000107454410800091408a42400002d00150f440104002c128907507944280c480580d0301d50091140f03851061404c290718001003142020544c101140c164a5145a00c49454001c01025502550f106201d04122488190b4a941c00f8445104001a0140021529140d03254815140060958617100e07000c208129a50340c00000b0740f0b401c41c1400c1d450405441c01000d20200901c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 343103111 1250 343101861 343101887
    0x60a0f1806020c0709051e04081b06040209011505180303041d0115020307030c1b1a04030204150f030b13060203010f171b0f031c2a0b07030c 62
    0x560090103401841015001401e0700d03940b8004407082c0581e640780d2181150b01c1901d002c191810003101c04001041e010f100650081d02a4821905d400102d40c4280720035a40403241b102c040c0c104030100b000b0752500f82032490041c4007003001c10080b4040c0c0714000b0041d202d83c01142e40d40d03501e80c1c0051002914100180d50240800801c4003004000d40051000d884400b480703020440d22480c500004414408401d8441e01a4140c4441d9003903803090303503509094640d5640c805078410701c0a0380003c0d00f81d0401c40207050dc6001031101541c950450041c403040e11031030b010200346090309500410074198016040401c480c2c100c0309820b040c0d1510612000080140100034008174004800492884140a040340480b2000c61f049104140c05600b09510b4261241001003804000c80364000b040c240140008140f450080648002c00748007207568502c0380c007680281d0001420440c100c2504078218803004246c41034a000c001c4802d040c1d43d28803160b031f0f4000b8140e804040c2c495201440ca9400780c84564194 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 343104361 1250 343103111 343103141
    0x3130b0907050123091c1b0501050301090525051e030405030d0207080f07060b0111160b09011119020103270602070f05190302070f080a110102030408030703080609060105090102060a0f 81
    0x1100c000c5d8049101541002d4081d07c01c44480f0b0305031400344107120b1045c1e0488006844150650703203003010140040100901c003100a00d020400384a03584002550040c1050054642c1520b07001d0300003291101680d18441850302d10b0b002c0083c44080f07407000003900c071a00d18869001d699600340d8a4888924041c5030340800c600c040104400701001200d4000c2010780d6002c3c0c0c0d410200380b007a40882661140902080b01c41003031784a400b41710280500c1c00804040206050120315003102c01c0140d882c00110f41c8004c040310018060403011513030315000380c00390034450391003044100b5448805c5240381da6540034020122a8009805020400300180e1000c805030418103541d1100d00003e261305a020f00b00504130018040e452011911180f07019001e004e0384e21010040000c0c8181da07542441a0000c010307414103600c002d003c0081c2030201040101401c512995840c0303580c0c10644c0c144060a1001742c0050f041c00424080821145d03800140340b035110302900303804242e40892002070340080440c1c409459807 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 343105611 1250 343104361 343104379
    0x180b15060c150f04020d03030c140f0306040f020910231605060a0501270204030b0108030703030b0102070302090c180402030903090a0503060106050f03180303130b090705012309 78
    0x703112000c520b10040c0362400408807042d6890904100d584641110002d500c10724211307600700464442e500004943c501400d10604d070a00c0c0091502c0785800c013451021700380ca0001300700501c1d81401d00a0301074030143d0400540c10003500d075001601c0500f4640740007040060480364807080007403035842100103080c0034003041e60702c05505400c070701c90790a049030568442c8035550202e50866914070031303141200c2c03013049026050b0307544e0b03401c0310b603101c0c036000c070817200d03190244001f00c081001c0b406203034001c14500006540c0d904031490060155043c40c1c0c001810f540002104001507100c82010a0f80f022542885690704c489004070701c0020f00150000c2c2e40c00600c00302c2000105900003009103000e00d000c448000500390368808069582d1303030900940780050400d00c000781c01e0001010195405c0032000c0707402106030300900c1d4054910b030011602c40c1d0440d8004504c040c240500129001d4010607010041d0510320b003000c001a081d03180e220800503041c5005902c001642403841e09480c1c2505c0e00400c8804 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 343106861 1250 343105611 343105627
    0xe040204030804030203011a1323010603091a0f07050d090507090f0e0303010b070602031911040302040c02210c0313030602030a0c050a0e10090b03040302010519180b1506 75
    0x2c0079081030208034000c0d0700e050048420709281d200000c8031141c00504c1c0c0a00e401929800d0005048882603281c03007100018003000d000305403602464040d00107130b030300050880b4403424905107600b0020400030078862040184220458416001c552002403070600a41e01c11418101c14002e045400c07010308580200d0f50081011040c0d600301c0c6031554031a03070040c40241300d21b280c02c5481c0d20080c4a4607100080400030300000910701e40145030300c90045500c61041644489c04803090703070b82038000101da420380000c0501c11031605210758507100c0c08500c018182c0c0401d108814004002100d9a44a070050110304914011001c00c00c07034100c0c44120180c010441e5a81c03600c003029400c2a0b9140c007029061054408035284a001555444c1c0035940c1d030101d41c507107501c02748001510040b40107400c00510340c001141c150100b04c010b40c041c0e80300c3e80c0006102d1401c9007030b106c442a0040200e40d10a42058552000f08602100440344540c00801003046500c809662050080340300c0b2000740c01502c0070030221 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 343108111 1250 343106861 343106873
    0x7020d060c030509030c1c0e060a0f021203010501170a241d0c0301060e0301090804031217011214010e070f0906081504060510031506030606140a03120e04020403 71
    0x2941c00d0076a0744080c40103480c1c400d8603684a0160b0300344610760340d020510705418440b211042840040b0725042c0044900f2214010881c140e00404001d408a03c0c10341840b10a103a041104044106200190504550401d40000c20308090381120860030480200420b404032202c0e840b0800080030f804c1c1107014603071a0001819140424410801885100c0c07074000304034911561554400c8001e08400c500e10381c04c0940c02e407445001807010710740641d80c4604813000100c8120040c8043c600030b03000c158101c001200010440103c40211500c0e220b41131004100d241802604840081d81c800c007864005580e01842a00624440740d4440203031103083d0340018502550711100701925a980028040103403034008140e500d000c0c2e884074040c8000c10700001400b05004d036110a4001c201208420b0030f00382d580e00da0b690401d100e0780c00781c92420369a03003080040003071f03e2160700001c01c0803211040100840c50300150313445295110190520b01c100ba543c0d1413161080802a181c600b000f80115140c0e92641451 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 343109361 1250 343108111 343108121
    0x1d06150a0e1f0e0a0905010b0a051b0a0803011806030c050103020a030207050d0e01020708060601050711190603050603011508120919060504141e010311160f03031107050303061507020d06 82
    0x8134043c2c3e1030350300041140310711800340764142c4105119252414540304412a12640283e00303080c203800d8440111590b0f06400c0c040030500303a0180c0303901500d0394145500d0002c01900902d4080c1c85515100082002aaa40116400300d03042400c0060300c0d40c82d150015406841014001081c500411003880c200f55044040148161401c0e8220341200d80c846130300c00d548000c103445e0b10340071803828041c1c1c5002505a0003624840d00c0040c200c2c2500301e0390003003100c40002458200c8000f180c0c65204001c0315007824400e01c02000048248004118078052070f403601c0341050101d101260200140003400f0b03844280700c0f02041c01c1880b41c558000c030754548005091781c00c680140c000b5099202010b00151402c920100f101d1070035240252441d4030000c0065000b44140e03c00703040300c0e00d0180701c1d0100e0022400e4403c40c406014150f8101c2020061400030201e0b0301c404180d400d001414030020b40030500c0081aa1b034032920988184c0808080001c94030326034061450025800b84419400c401040b0140e000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 343110611 1250 343109361 343109387
    0x22060504110a1b0309030206070305040902030a0605030d05090d021e060403060203150d110427110301050a060f1e180b03060603030a02030a180f1d06150a0e1f 70
    0x1071030a43d030390703a400e100c1c90309500d03c1e00540003d40b550f0050002d850100000c08001380f207418440c0c50a503440506006980040703c4000700150b84a80c100250f00381840b16030000641c1d4603009180580140000e00540d24030a00640202070781c0317403040303564201200c1111030b00000810503921550390b881c0c1705001c0d41c0221031509102d00284007251040c2013242d4003921303e9a020400d0900c034890b12003844010008280c50095003c2c6202c003054111440b0f111030f1150500900d550402200c061081c1800d5450103004109040d2901200300250000101d584d01510010001c1c842402d0000524035410b1a20350002c2c03985440d00c00c4004c6101600d50702c6000f10400c1a000e51f600ca80e2000d04040c0c80b4002c1540e10000f68000b048410b1016105025104c0c6131903c0301418607810f40c0780c3c450154000c0040d04904001000010940c4404100410240d41300004607503402c0309003d40d1154604500030907003070406000881010102c2a40c40c3d003103400d03000d45404a5444184041000204140c1040340 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 343111861 1250 343110611 343110617
    0x2030304260304060503073f27140304030501110403060e0a0b0a0903031107030305011a0405030c0d020303072f060f1909120501140a090222060504110a 67
    0x5049038000700d011060b01d04495a0740c95a03811651403460a82d00f0480980368180c16080c03a901c040c3c408440c444082108075070080205c80c0d412a941c04020450303040300b00c00000c03500324801075041800000e455464080d80504ca101d03180301c5800c030a40c030f1800b0fa504000c08950030400d1424a041d40a0042c10840740241e0007480310344062880c07551030303980a0001130f0164200c40001502407185401000380d692013841c0c0010402150308a0840f2900000012800252508e0040280d20044024844101c1188940310310341494a0006070340c8443c02d401007070003030305551031701c105641e070500c1505c060b55007214180b48150761041800200d03600ea00b00340389210744101c40900003410240d040d9514a442d0001c52440c247c0c3c02208008205507210502040200410000c11001011000305220794072950000c40c800d8914032503000c0c108001000803c42915242034900540d13610744100c0002541c1824254042032041400ca0141105400c402d409c54180300c11b48078003414400003000406000c1d5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 343113111 1250 343111861 343111919
    0x6020606041a030c01030e0a0803130b0106020f0607080403140703030e0607050a0504030b06030304030210030608010516021b0301110a1215030203030d020d0906240501051903020d0902030304 84
    0x9028042e45800c45070160564001c000802076540280d1062000c0c40d41e00c0111000c0c440c0035614170304264800c90b40000c1450f0300001200c108002200441d0240100340080e003418070054a20560ba87c0005110384104000100401c2c14140120034051641009034110b139031318060f50501a025143c03050f28000c0390b114003000540c4142c4038070143c45c080700c907540c0c402e03140a14507114104080006000341c2c0e8503000c10407000005a8480c0d1403000da00780241c40c04500189000401030031550003d1040440e0425490200c140b1135000c0f03408034005217000e46c619000c0202e40c1c00f084c010711180300c842c03410700c60002c4d8003d9011740044400c940e82001100500c04405980d070000500b01c22448005d4040c1c2c028005812000140d4024005080340c1010006203411f5a40320307030382520198024881441c01e03881d090740354041c00103a200058030080c209146850321126002c040c40212171701003001c00d07a0108020f55102c2098100482190b001403c17282c44030780781d90340124500300c103501c060072580c1c40c0c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 343114361 1250 343113111 343113131
    0xf0507060e03030a0513120b090c03010c120c1808010f11090d12140403080903060604090206180307050307090e0d1701030f02010e0406080319030b03071a0f040602060604 75
    0x141c520300701c54160280c051030400342c2a203801c0e501d541042a030034003815402c20011034070640f1080d5401c1c855000706d905140c01d09001c05400d00701100c0790022030099047c90003403500c0c1900702c48045d1100042e0b500c0042c0441e4610400c44060492030811160621000b40004000a05402014802c800f43c00e0401003019080039103c424801c020000e6000801c01d1014008110101903000350000c240c2002894210040f1040c071065001d500112580701c00030408403102c0c107080020550010042d101080540441e8000032983d015409161804554140a40780d2940342882580e00804000d000c507110305407955991070240c4505d58030003003a48a04021604400e12600580001c464a45210085a400c58585600c080c83ca100181d050010034044500c071511640b10704130080c440320001d03586600d400078400d508603200340d000f10100b41c100b100061003079501146240c2114606ca10410110311000302400f0304d80138030580006625400700340021420b80206845128041c1103d0400c124194 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 343115611 1250 343114361 343114367
    0x9010203060f090f01120305190914090601170c04050315070e101d010e1801030c173309060720100b010504091e05010e07050a050703030204120f050706 67
    0xf080310082202e880e0100100802d01c010541075141034000d00e4190714025200120964502c1440c50040009400d07460402110341d0503061300c40c02030b00481d400b01e003900302140002c3c4011704a01800801c4200c0f84007041c2c8082030042103030014940901503884608003503b160031070407021036004000c030741d9071046200103181c0008001c0707003038215445a540f42d14007000c98548000368000303060b0620100c0d540b41c8245540702e20802d0342c0f9084415030f04041d503040d40f404400d1f401d06a4440044c14030400c42c00c900f4481c000c09c0300c8140348281d40119034260020b00c00017184849580440b441d00544c0e1060000038240411010720441068881910f81c01032940b0703410005050a02c6140e181d003042442c503406c40003035044100c5040c41494054241134541a11008807801c080600145032501c511140c00c1c440d19000302401000300c00b020142d94504090040c01d1882421600800c00c000055160209802941136902802051450b0503503100b86181003c3c803811a24410b9031684240c040009203688 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 343116861 1250 343115611 343115629
    0x503101e05070f030f110d05040c061d06090a0929100519020c03101a0f0609061c02071406090606010e10020708100c1101020301080a0807060e0609010203060f 70
    0x116943e4040e5400b03168008400416152a880c0c0741340307441d101a070f924a0160406040a55800303900040ca0b800c0a20f010b00d00913440fa40400d00f8401600140c01d42110303481600c403d260703020b4410540e03c03145100001ca0501c242e4103d00c0c0d407686030401c01b0b000803440b900201d600061355250702c0e451201c51000c008000d406000da82e000150104042c0c90262195200d458220001e40100c07143c0d40300010009007030401800310b41c0b0849542c5d0344100c3d4003400100000b5a0703010151034800000e0840360106425104800185005000001e80d0342c8000703110006c40c403050005480110340f01c5289203000c00d800440d25051043e10b22030f410205c1d8600d000406c0441c0a54030503142c0e0708110700345009110106810002c00000c2d4001d100001954140c1805008400c100d030900019041c502840081c040303448100302112668414001404003103000900072240031f4001415540754603051402d0005019410084250b134040e640612203910015009103009200032070380303000b0300a5081d0a000c0146 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 343118111 1250 343116861 343116871
    0xf07090b030601380c061602070b070b040305093c010503090a02010305090f1b01140301150c020f0607050d09050f01090e070201180c0801060902040b09190503101e05 73
    0x2403621410ba1010990111207040740462001c8150800322881a62820251b049540030f60003c40703050115445541880024058202c526440d41003090603203401118500051000782031140004122205540300e00c2020a21005550308401914094003402d000c0c00f041c1400c00603030340c004c400050031076008609030307441080110001c01d002c140301c4e00110003801000d424940c0034000c144884818450500c200d5102d5078900385c0c0101c01c502408001410300074501400c1403494814001400083c0c0611042760304c4101071319140c03041c00c400e0300000710302c1c03040b8129281c6c0c4940000344030410001d02045484684c04ad9441d0309500e0fa0b5113406100c414a100c140c2030f40004c0107514188190005100400d81244641c40005003c0b2a02d541c6c2c0d56480380c0107034003034442c43d9aa950030003400c1c0c400d0084401030700205409504040c64004905541d00991002c41d1203106454003c2000910806000004010007021250f20f44552561b0740700a04040c55110b0b00c60013012600740d0100c2080c080c0d28014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 343119361 1250 343118111 343118159
    0x70309061416020406050a0906050a0605090a0909031716020c030c010f0815030601080a14010c080c0703110601120c0902030903030112170a03270804060507050f07090b030601 77
    0x20854140403101c80202c000480c1e002c4c0e40c9283c0483c60391140489240500200704001640c0d604010401c113002a1580c071003001c001741000700d02ca01c0e40300ca81c00d00d011136a03840c902040305400d42c60190f4000b42400c1c0c5050041c0b03000810001880e00d02c1c21400c0d543c0700c2d50340036504c02002d040d00341768131981500c0403207001c01d181c10108050544124100c9a202d9110b56002d08050003031400a030418000b83d0140019a01400b0380c41e0500c801005034604007001400208101c00d4800c1c000313402d00d0001003510309803610129141082c14011140d40720f1b41d0130b0030010380da140e6851f040c8880c0140607820342920090b00c55100490600c481d0300c00c49024025910041d400c607881d00041c3e20700808410411103213104408121a01d01411001a281c05511900c020550210808844030070001c2c031404001c106401c1143c040c0410455000c031002ea078500c1c90f01c0c0f0362707403180d9091140c64214003940401d0148103c0d440003d60310400d034008501c1c04012410307110941d81c0d48010b044c1c41481841003002e1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 343120611 1250 343119361 343119367
    0x6030c08010303091a0403022e0302090a0b03090a1a01080f070806060f01020a1a040b22030f111504020312040e130204062310050a0e060304060e03040b0703090614 72
    0x740440c0c5c41c460005900c004061480c26441380d001c00d988a541c4451201c2c6142620004600ea00058101701034520fa185030860400341e450000509680d101c1c030496070b4061000000c2603900c034080c0104d9070041c0d0016141300380c81d9103d81c8012100c40c800d102e880c246004002c43d81070b86810124400b41100c0c0701000500e40e03901c40c802041000400380c0310701c9041d441a498007a00080305502121035440501545695510307090070076040546c8010100c441250f8801d8040b5200400750f9030000509400d841d00614001c900c560580340c110410b0b030701000511035206014890f10516000070711542c400d0301a14000703100301c031406820740214000c0c03201c01030a900002e4403994111145a03034450006001040c41945c50761140c0703c806082d0b8620001844180130b450050030030241c058403540c0c40e440d117a445c1400c40d49c4c000300506040c805203031145900002160501c02c2541042d1043c50070031082e031703030b41d03503641c06010b0b071281c1c000c1c1d01c114007244211000151890181c0c0c4072403261a00143c510389 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 343121861 1250 343120611 343120619
    0x318080d05090f060403170703110d050a020903030c011b0816110a0b0c0910020609031606060509072c09063d031b14030405071a0406030c0801030309 66
    0x203841d0050240c507480c41000381895a0840400219000c0c84c001d45a40050b0a40038038490803281d4001c1c002006c1c541003070300c2d0140e0a85101e08070b0f00130480e4980005015280c101e581002780c03049441041d498400412103076504901035000d040300d403a40080f00f041450300002c040d20311000803140e00d5042a10859100030a500500c1b1325015001d04105541d41007a4a2703036045a010010b03241c512164a0119001c201424800749000c4215000d000800403403070805c486c2070b9a4407070700c09601840444c0c103148030208811604854094600213105a02525059070001e00c142a282000c4440501d035800541980300d030301500103520880036204542c143e81c0d0000340038920940b042d80070101e0f80700000b80390b051450340100c200b6584210388a041c034a0701526008054500c28210744503040b00135020f04a42a4000420708000d402030f22182e0748036030b142e04085041903020740c00401c512080492006e00001c0f0080200709540c2c1e20740702080000451082250541402d0000a01144e5403220500c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 343123111 1250 343121861 343121887
    0x612050a06080a021210050f0613050906130c09020a020102091f1407050c030106060e0109090212150d08030c04030b0f0f0c0d1d030c060610020705090709051e01031808 74
    0x2c251140000c40c1c6c40e117a001054101251000c8600d291103040b8071052001d245462000302c1c0b111040e0341014401406d00803856900d6040150405004006c2c0004950030071140d92140302c020440030382c046440784204800a8040e604c0100ba451080303200706229001545031910b030007154403003655000107100c1d28000e070fa4215484100d055545103d0141d168800340c0c1d0900803c4041c21444d0f036645003140c0c942001401004a0386c00080c6201e0051000b00c4d5484403494116901c184007124041c014617507000800e030403100818024104490000822414400c0c00c00104100e0344501013620300d80c0d884002440869109490711406040d404020a04030020311014100c160040680040c4403181000260140b03426003440d940d071340c0c002144075401820305014003607000320103850105013611200d1001303440703201a0080501c203081d0600459203a52180e20003201516000d0401c0701c000101d071002a040d0400c030207515000034209408901020182c030000e281d0281d05c600e00d513040816840e402e03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 343124361 1250 343123111 343123129
    0xf1a0a141612020c0102060a0216080a050c062d0f04140102040f030b06030f01060602060f0702120703031a04060f090b0d0812090d05030705030c0309070b040612050a06080a02 77
    0x400780581552040d40082203412030340405040040d001401030f81d035003100180c1020002002c1d040c801d4418040ca00c00000403100e113000c071540c000c1644d0380d94404c0c08803d44e440d0003030030303003039489407181004103c0603619600c06203200010348089040a40798201d49050030910884c0c1040c0a07090b10f101040000d03156804041d00818031000141c20701e0f80b51402500e003a0400d40c0107685c0b90250a040c040c00d0305080c03028140303407003074600203101d0b03141402d00117941c4240103010000c099412500003070b84148280010082e40e919100b01c1941d0300c40c0ca0800030040d00c121241800107802c424a02c2c02240b03040c5c8211011901e80081074045207103052500302c01040c140110036000601100c41600050045c001081c04580045554460303007408010145041d014004580074023400300300340441d40e504a01034039400004910103590300d03501c0034031041c14104145d000c031012040104000ca07003982c0014241641019010042100d50b5412004c0410388110344141e49817500100c03004809410181e9413 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 343125611 1250 343124361 343124377
    0x406030e0c040c09050f0901120b07030213060c021f141602100801030c08030702030622051615080103120c08120f04020906030f2d070f1a0a14 63
    0x240c0e029075040902040503522141d102d00002004030030140414640590802408103080c0c60080d40c81d0b0500420403491900807034060f103110344820000d0026803083d0100ca040030822140964084d540d254090138207500c10004030f116200700401402d03000b5000303490528460a0f0354448460b006000740c2001c1980c411003009001140701084000036807203486100c12080e40e643d848550541c550b0400c0081008690003035100c0760000c000590160f580002c21540145002d441210400d8841c241c0d49110380c50150010154065100800340c6c0c805000c1e5208102c64004800281107200344d00111075014003404010043c0c80342a034417000283c45803203a05146445507034800d10b00343c0d00010702140c0a8040700d40e0341c000c0030745c43c04020450a1012241d504103030b0a80c001d01c1007a9840058585540004d0f00011440c00d03000c40d42e045202a0022003000000800140d81c000c03529613240d02a0503070140540c11003900ca002010a403129140100c1c0c54410683d42c81500c1c451507802104040d0f400404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 343126861 1250 343125611 343125613
    0x606090307030314070501111e04060905131404030807080601260a0b0a080a0c060c030806121e1507050423060715020a091a090409080d060e0106020609070b0406030e 73
    0x14004c00284242300f0b101511000ca0312840d103c083da00d80c8803003605c0400c490031b0410f030307020b0200300045138200310741c0410b03a8001c0300c00041c49101c0250000003800c460301140c200f80030240a01050680000240340280001da0711040103a540c170006503145071602e090070103500c401c03d0241542c0d642c10440580c1110900001284001c0e8203000a800704030a600701c03a00c5078001e40514010025610340c420003c000d1400c20182c400c8094801400720702000301020b0145240410b40d1088100c103210300c00c48c3c0090500b41c0e401c0840c904000d507907103205441c0c2c034850313440015000c01c6156025606540c00c40b07020010b00f65203200c1d103022211007084400314480d00b0500a0224070009010956083c8040c4c08581006854600d0fa18005190340c5240c0d20440d55814105142610a031091046540342c42096801150300c20703141c80c15015502c2102c0f04c8052803444d0103000302e00b00c16102640340c12145240c0c04c40d680b94649a401c1606c2d10f80d280303d00d003020a4100001c2103c0e6009070440343c0001c1e2100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 343128111 1250 343126861 343126867
    0x703150b030a2306010b041403070b13030510050903030c0703020703240b0901150c170c0703021014090411070507030c060f030902100e060c03130e0606090307030314 73
    0xc01092901241c80e408a80440c1c20040d0300500e0300c85594400005074856004024a500d010a803404a03c02c03030080301901810038002034280e840400111004101ea0b0030a42d503900300d0003010114000150008645a008200c2a0802011240030303550049640102861941c0c440300404501644410300450640c000c1b0040000810482c0c0c210a030001e0344007454804880250a107201210408a5141c1c407070110b074001441101c5442825a159030004e080040041c0c45a04140324418404120101c00b00400038181500768000300341601124800d0381c0c40401c80103d02c03410356003070803020010182c4007401c2c032644507145459045000d0300b15070782007a540340a080d5282c0900386400764100755030220341d105003082200d90007400300c2080c00141c5010031419695500140038001a5002001000b010701101d8ae160707518032040711031420000c81101e54500780c80c02880240da03214410110100d0000d0b002a5003402e103041100c00e0314a0040141841d1030a580e01500d1040c0382d920841c04500e001c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 343129361 1250 343128111 343128131
    0x13050a080406050a0806010c051005100506030c0409140f0a02211f150215071e030f0c1b0b1f031b05060a09090525030902090c0309070315 61
    0x4400901c040d1035250748450f516640e01102418550019110a0401c044103050b100072850204144104550010000c122078607195811380045059800c03030381d40818004248503917810010000c2049601030b0f00c0501402d02503040121030810211010303590400500000760481c241c41d401001d01011910886151484081c51030410110807240b000700c024042c0b240c8050707803803141d0300c4000a0451130300e03c0d0492020181c00030b4558802c50511602c1040c0d0784080b800d0240074039a0000f9207003c2e1a5800300702413205800030064095081003050062074034103a0b40300c00b4803801c0d28100f480405c00469221400300e0382e41064000b0005e00c2d020300b10f41c402c080e1080203500780e06084011070088100c2001900100708580e038040309a40094441c001c100880390007a9040480b0340222103c21000080c2681c4800c03070a41c2c0d2520881294103644802288035500a80540c40500890b0095548034140e917601041d2030f080b440240c40b0250142d100d00070070400103112070540c480700c02582c0c4010641000e4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 343130611 1250 343129361 343129373
    0x8060103080903100204093903091a2a032503060b030c0c060a090201081f05040c0302190309080910140c0a150603031b02031f060501030c03020702060313050a 70
    0x1a8001841241c3c8607082c8105804004004481c2d1078003a23032074149099183c04992078170303003401e00810302456262220b400c240705169103800013000c080c045400c15450001c80d20f80928511007032810111320300c40c003a52441c150100c02d03a0301c5420b25104400500360050125036007035070181211801c05d41ca40c0d101040305c5101d24082c40c050001007000d141c46000c0751100508040c2c00828100000381391034041c10240c1e81c4401d41030f0f0011000a8104060200030b001062041c1054010311f4002d400c06040940d2240d040d401012042041d480c010324104602c01c0c120159480b00c500036000d20414031460b4458502403a5008209071075081030300c10361403c4503009403c4e41220a00c0402d940040321000d0920029814804008080da80b0401c161811603a016003481d168841207035441c3d00030104041103403420030029950b804426041024440c1d02c407601d4025106600900740020f04282a412540f4004c0c001e903012164001c240324219a00d020000e402c0c8542d02c80152014403906207403d0100e45 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 343131861 1250 343130611 343130617
    0x90a03060e0d020610090902131b14120414012703080c04030f0b070c050a0b01260709020705150406150f082d010e060402030f07080601030809031002 66
    0xc440c00d80800d2014510304003078184070000d46401c05640040041101c840d200c810100300303803503512000140e450740790300108000f440000e46040c941880e040340000c020300c880700b401c101c0c200240c0e540c09020401d92640c160b507000b103240d0364102040f0000460b00148120b185504040500340000840006c81c090750154074034103010005800c0350105802050540c0480600c2e4000036a40100b85854619520101c14601c0400d024041c0061000070030404e51044540a81c01600801110705000003070a110542c2c1c1028814103078a41c5011181103c0011561201c1000d445200c0142c5400e910305081103010350b2005400700c070b89000708018000c0c2d00d1144007036940294041e0038001041021200201c046031601d4010000d4909200420006400b00007400403510003100c914900b02d0610460107a0b210303c042007950515400d248400c10301d0f082c00122507103c3c6000f01c00b15000d28010b85201034030341005004182c616000b0b03c0041c0b010900313190042440c0d04020341114101d004060445003260 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 343133111 1250 343131861 343131863
    0x918020d12022401091107020a0b090a0302090f0712181b09020703051801090b04050f12030301080a110a050d0305030709150c03030e0d08010909140706050c0f0a020d06020f090a03 79
    0xd40801e005028802440c41b951843c6c40204071000d01e0302c81c5c1138000507603456980c454400c00c0d0700001610036542c0c480e40004802164003900c26000c90400081600203440200ea1403000a0301c48024032001080c0303401007090103030881d410031001c3c1c1243e07143c1c0789000542c0c0001090a62008000246204451009080303283c02551081d0b2940c2555096401c0390b043c0c02d26150401106060512244481000f154200c3e84116500551424000b0108a50080034801c0102500000c000040c0c40c1c2000310b980c0e5842480383d4000d01019002004111424200c0e01070680c000707003070345100000a80101d0046402c614582085040507070345503000d904d2540c3da040751400056626802004054042c02041e00922801002d0440b1a125407001881e0a0301441200d491640314400b80003409040d80500c0c040b84018019201d0880d15000050005d501c43c0c440340183e8484e1348500075400c03401046500070351b40e004200c218050701c56262440a500700720050341036017104019201650355042c0800d0011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 343134361 1250 343133111 343133173
    0x1401150c0b090708070602120d05070309020310020d0f0912141201090b1c11010e0406030f1109060a0e06040203040606050409110307090c0203030112080c0303010b03010918020d1202 80
    0x5804d24401e00c1c00c0850320341c000307010355007c55510b80041400c0410785007241c0030100c001030355544220b0300302d020300002000607400d1b015284802c00041c40f10740080100c3c03041180140071000030f44040c2e20032156211005044540021002c501340c500c00c0710503040c00d242e004901c0e03041c11124006940d61801c20780c4030340d204542e00d00104110741488a2a00c00e000700d1103142c458000126181e54148181c03940d0301320304004102c0c0a1b00080c4d40c1d664003c5000c0c540000d2035075070b01c4006107000350306c009c00385a20340c0c1f16111101c000742139460201c07120b1781030710901e50040744a9103c440501c4065000a00201e4195803a10008034a0307072900c1c41040c10460140340c809000001560505052031150b40040e840141404d141201c605d8001046a0440e81e0091a030020320181e0306240704507014410b00c0300b2060200000028526040602450598032040010400d110021301642010114500001d4001c1d40c0f4031940c001080c03403111043c86403c0d841c0140c51207040342c0010011304800300d0b203807001e10b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 343135611 1250 343134361 343134373
    0x40501060e16080f0c2b090503251a0403030906020c010b04050603031813090c180f0c0f18030b19050a0e071a0d06120b0a1401150c0b09 60
    0x2c00d6808640b07160080d40000e092070a0f4103040c0015051441107254a08040000403c3c1c0c80c170041810010480090b10302408024462152030044e8403940000e0344079607480d0b0031104004148110040d2010b00f06d6000c003152080780401c0400100d0303000010420703018075541c2c10704040429128001800900d00700000001c0e00341d5031078104400c445010340f03070b0390203540140420b410182c031284a100c840383d000c41c0e071541160400c4082c50702800c04914020009440303040000b5810403000f04044540d4100c0b201400142c0201000408580e0102d00348070010320406060080d480c02101000700585014034004151500d07038580c012281d0003981e4043c007020107410f01c41800381d598810f060b040300076040b06001c500344400f43d190380d07802a4003a007020f0341c00c5180b070481070b80300050484481e80c40ca038100b8000b10340e80e191400a00d000264041c1c2e961610f45000030003240c20751086030007501450850075526428050048040d102e1112004e00b40442720110401143c415900c05214415540c01845 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 343136861 1250 343135611 343135651
    0x20a09081603021c1b290c030313080714030301090b09010312080c042c0a02130605130801020f0c010c0503090d080a060521010e030f090405040501060e 67
    0x2280071000401c0c9844003440d85014001a6144650440344183c03848507443d003e050b5060502041c0c1c50045902002c100032070340000c20030a80181180704a110503000c2c481840d890303c07214103900c280c8518418035041000054407803000d20b9081c061250082c9d00c2e4900b4502c05903204039419141181d800480d6201000400122401e80582d9495003015250b07107103d03500d19954a00c040540c828648240485c200000e0300100c010300c15900103041c65107101c030000b1701841b00d0300210071110315200080030b0818001070001c001c42c004c4a803550070b203401501702c0c10b241c40030840d1b480e00981076007180861074400000d040c0c83c0c24005040d82550700b8035119a20000b10b220b00342180e84c0c1000310405c0c000c042c410002d62850115803086500e03032034100081d00b90303582d1003074900810003a00459403126192803600f441101e9240d030243c031845868000c105002c81d180c0d00076074900031011000510b5600308420541c6061a4019503001340c4204000315a00c1e031600c040c1d1404c00c0040300e005080c0c1d620014800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 343138111 1250 343136861 343136863
    0x1b0601050a08030405091611120307021006050108060111070b0a030213050906030703080c01020708041410140702013c0e010e1305070c0503030901060812041d070201060306020a0908 80
    0xc0c000b4040200154603262070003020580b0108020580340900400e00030500503a405180043c0000c141d410075110000009040c119080c2c106452000c01403040c1c88885480c031003181705410588005031202a0a51b03502c00044400d00c81d08107940000f400380e080002040d080c404060070240950703440150302d0312205038401d5102d50040d406a8411000300040c01a1601d000c01c491080e41d81103403103255a11074442d040d6001e80b2030303210002c2c0211700025000503254900020780e400410100c13003103070b500079503e2011220440b20791100c0040082c100580c000543c005c030300305200184060305061080a41d160b241a880360070110918021910f0110b2100703480e8070040ba900c8800302401c111030310a42402c08100d0404010761603203141c0e5030f076030f01180c801400341c0800e00605511034101c0b40e4918000d00da0502030b00140c03144214510403a01c9509401c0c0c0b140003501c00b60323004420304030358044040849014200d80903001d082555a18840440452418002410302e850a40c07101301000b0314040c445 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 343139361 1250 343138111 343138129
    0x516060e0909010c0503060d030905100905010305090a050c01030e1908040303080709080601090e0a051006090e060112060209010912030201140f1317120a0b01140c03030402090c1b060105 82
    0x4490b4076407410340c02040c0d40390010140c98004c1802e40768041709207540d14040e65807a5468000b964010250381c15903a0240d0f00c10b030300b802078076030a9034280155161414455a1901142001099038200480450142d4840d41c003c4080590410848030428911940074075086080312040da10044001014020701d90400c2103250091814a08030140900d4448000d840f141d041c050594015210644484005003c019403280e4940080c15105452903070700d01c9000800309480740310289820070302d40030200400811704c0c1d4104c0d110803103902ca40c2b003805d6980500a40c441e0040c94144550004042140002801d0340a4028441d4000040700222000002e0304440c000380700300c03946070480041001c1c421803441c0902403d1740c0300600382c0301101c881c140c060090046408464900050a00b0880800b9032a000019549020b0300c40203100700a1a008000d00c0c030403514100304903841000410010f041000c041a0301030403c3c06403e0030f080d1429404411050260700000140d0300c41c80050180d40f900c003000e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 343140611 1250 343139361 343139371
    0x90d080d020a140408070e07050c0f060a060b04060c0602160f05011a0409050a06090302031e18030601030f140109020603040501020a03060509010f0612111303030e040203010513090516060e09 84
    0x340e044c5484c010310160340b64400d00803040c1030100040810640d9001c1e100f03803180031b683c1505036075415801d01075850b80c0300f00c01c03108052614185040040e80f0780d08a400c030b0701940c45999442c0c07400315050b16100040d40c81000c020100000c40340099012030020702c207440820b8455030010440301414500300044080f1440ca1520603031818483c8000910000380d14042c503540a540820400c000b4242030741140503504004100d8020003114000ca211582e000b0181d04541d51100080b5034507a0040c160749603c240001000c20b100c03020728201083c48000e2281403001d9080c000710b00844958081003040d00162811160380c0e40118500e580d2581502444019203001c0e241584998504961844480c556209010902040712600102544590888810100315810244e61401c00c2031415a40c03100521066001420f49000d03280c861820f402207078100c40e8004c118070302c42420001e11400402e07801c4c00445441c8a10720500c02d07042e14000b0808000d20540d265451440001c0061159414004103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 343141861 1250 343140611 343140647
    0x60a15080a0f06060c2901060c0c1502030403021513301e05120c2404030f08090309130f06062c010909050901020a09060c0b040206090d080d020a 64
    0x1d050104c2c503807026480b620190020f01d401d0301481c0c180f52019803084080a949042581100042000750f00701050151051140c04460000c560f12a00104056000480e800058008100410143c90410520072140c1c05038015507180101100d200d0703001d07940c55807203610104008113000b200800404459a5810090120fa0050024913915070034442e100381222017603420042c1c00c05050003800c001d8403442d000f1030703e102c640d51200c1c05c8000380d0700c00d251300048c0c1c0404000b04159007a9003c0e01c1d0954099171b45921072241030516050251600d001c0200700c8107462001380f20004041ea1814400001001280705c0011035041110424066803501e40048050040c640c9d081d0311051200e2a010b018042c00300030010403500007078012614841d1543c070940100342404103020000c8030640c02840e109819841c0c0d41d000540d907400640d2404c2c02d443e00030b0300300c4106000040150414000924801c2001400ea084ea40300a640f262000d40202103541c081544c040340344551641c00c6142082c1008440c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 343143111 1250 343141861 343141871
    0x30b12030a0801061103090603270f0d0302070809060a110f0318040207061b050405090105090402091501140403050609010f1514012f060610050f03060a15080a0f 71
    0x107400902000b41c10300c560420460300c084605009941442036680100380140710503960300700090400c0300c0040840c001444200c98000c601c1800741d000540104d40c990000147c00305a10440c1c06500a40040e5001c3e0752140d010060442d8542e980341c020b000c2d041207030721203401c4040070060981c5012090307c08551507510411002c899001c0c0e00366070701403070081150056070720101e500d440710260136061543c0d00054410007400640a030041c02401c01d035031090303400c4a00c50382c2e144100208400c0c1564069000042c40000c1510805021011502c08106040c20801110403906014182e44194806c0d50150484024881140401e01420000032612007090020140700540c0c44240b558502c14010340061a44605880340d0080c0140078110740e1f61f9a501101e01204c0001e81800c0c0340003040d000d0340b4040c40001030b01030f183c4004240300c505642cad5140c605181d00e54032a101d079984080d2030150b2150207154000342c040d0340b007614807013461081c0c3d440d0001c80c240502c0f0002a203052090851269041c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 343144361 1250 343143111 343143127
    0xf0506090706120b0d060501060801031202010b06030705031302061b010608070b0909041e0803040201030f0c020c0118090c020708120405030606040c2007050f0613030f02130606030b1203 82
    0x40b0540b00b140320000d40004c4d130740d21042d0010320303120700301e1340010211410200000b40858121078924105c9016002c00c6070101c071194801c900300c44c51003a10030b81c17101b001c1c03000c40c00c1e0070700c1030b0302450f8000b0442c1c1603214551000c1d000070b0295004111281400d4800703c2100007044028021580145042c000800c03155080680d030704034500421103424000c0441400240502c0744c3d80054000c8034907010a074000c50000c0f420410b00b642c1c0100c0c1c042e07003ca801c0c008000c88000c0d892007070005260895002c1c1c0300900111004403019041844243c00a1110719004900300d100d038030031424484229001081c94a02d081401d60410040d04085207100c041440200220780303001ca10280d0000741201c0001c0d1142e12039038144c03503030b201c11400e8180c0d401088284003009140043d03041b0036103c2c2252083d00001806040000703900c151040c40110480d07901d42000001d5001c0f07800f40c001840184403015480301c05440d0021260b16038000c100080d00c6003618441c0e8100780c4480082d44003d540554507002170 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 343145611 1250 343144361 343144367
    0x1e0602070e06011809050103050d030c0c02090103021201110f03040b1003210504120b1504110706050a020702030d1706010305270717160e070f0c02030114040f0506090706 75
    0xc02070009041c888025201c0b800c102d00303010407402170312000c1c10401003941c590510b41da542c5030800380840864a40b085003503080f03011322a00c0071025801021351aa5a09581c240700c0482c0f02c00c800005c00b903403224001520201c1a0001e030000e04009205140c8a107802e081500300307107001038002c1c07000300112001800490401038200f01103014000c41c00c4025041820201e17080d00c981d03448110420002c43e031120800400014950180090050014001c0560380401c021210401286051454100703ca4000901c854200c254851004900142800490703008a806c001404440070000b80c0100c070010100f220101049030091001e10341040980b90180d06212001ca03400400403100f544001220001072041041801915036025640b4070301261a0005585a440310a06500c0011250000c6901c04064507860310402c15651803200014000c01c0c2a2054808500c2c1030b40c040d500c074207101c0f5107143c45100729401188105000c1404d8100d60400b9801c00760054003075407554110080030004158 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 343146861 1250 343145611 343145639
    0x111090d0807020109050a060c140304081f021201030b09060a0c0e0120011b020118020d0b0714030c0403020906100807050c0a05061524070b060f04061e060207 70
    0x1d84a071071180e4074107481c0010f07507011040382d1101e0760200c0c0303c01c0042001980f10241307003c224818031002e4100345c480f01d1155100e004d90300909050354840c10103030b55503115450405c1c1c1d4040a0810040c90401c25a180b1303062108245c2081d1078008020061000803001008040d50000703c1c40020030001444030700c020305558681828904100520343c0c401d01c100004a50350305505903400080003040741e698140609000124244000341d413801c44010a0804800350036001150700810b1446003552680e6140c00741000a082e003010400d2858148001079200001180100314480303507251a2413561040040c0f210004028a0040740c09088100e0003e800a404503001003940c101b0503111079140c2c01032071403d40d1440010f042886003000344080f0390001050034001901c01d440360001346042410568022032414003804407a10b04000e224007048014510307942100d80180800d5162448000042c16104aa041b5400600e107040b140482048a000c08000070035207030014120030340c46c141349180321030703 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 343148111 1250 343146861 343146863
    0x5030d02070321120926090306011e03051f060b09030c09070311030f06010e060f120a090b0907061d0306060d03030207021002030a121b030b01050c01020a08090111090d 74
    0x1190100d50f04451038003d6441c001400c540d144104884041d6040001040701b402600f1102074406580c0c0181d950b20301000c8034003c20018004141c10791911120310140350481d4400d5822050103400803000a501384100c921002c1c400218681c481101040302044510725805408141410080c0203010744003c00c0032000100700301d603628015651400103801801494803003000185c400010090005015608a80501402e90340c0300d001100007020b028681c030550240c5080700d00c0500c12960b60055816440c1d500c055146800b1900406c5503540081c940d8065903046070740c0d040040d0500180780c0c015400c542d4501c1c11304c1c0710b0100441090119884038406000e07540a4180c3e0000f6505050182d0116504164080c00300c00d80341c408048001d40300d4004084a500056a10402014007102070054103000100c62800e041241c10500055008142c00701c1510b041c0b0405001c4251a81000e10141031410300703e8039005424501004060300b180c3d059820b80c10070310814800b40f4066100c07503c0b5040c3c0a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 343149361 1250 343148111 343148153
    0x11030d0215150120030d060305060f06030a03170c1c0f111e03150a12060507031a01050901030f0f0e0c030123040602250218060102100c0908010f0605030d020703 71
    0x612209a0307440c05d603c248086900c080f810502c0000400400152940c400d86031610307030704030036264002095244c54031407a000d00068242c6090b40c820f0301d07540310a680c2000202c60744078640303002c641070700e20000c548104001c034203030303039a600484d211880b4010302d0048e2000412242c0780200c80803940c0f94800c900304003150019800700000b5806a82c0c12520700c00d000c00201002c40035940c0307030040b0341c55220b084400c480b040d007402c02098840d4041c2c0206030200c00715486510015030381c0401150b10f501300c1a1054109921034007c1d032000c00e694800c901d550154100042071a20340301040919003042c1005a07030103030385400c00d41c1e6007084940c0315007100e41c107454000c2181078803a418803d002c0d01500d1040040040c00c03d00c0c15414003031106080da9200e00c00c2d510303149201c5061910f003e1100088500c14050f03080462238851803117442d4050080d0094508081030401d48411130076003124501200145070b1680c440c0148414501041080344001591004200040c150707510f10801c03861803c4003a4103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 343150611 1250 343149361 343149407
    0xc11010e0c030d0e0f030a0605061008041e08070f110a0b030f0106030c02070803030f01181b03020a020316080304020306100b0a1d0301020a09030b0108072111030d02151501 76
    0x3440d074608411703000d030107001800c44804040e1810018002c041c00e582040c4030302010860000314078040c0c040c42c0d100ba600442040a001c0b00740c2801c46d00d442c0045403c0710108800c1100e03070002415903004040007800351740e401c4942d248141c1400200c02098001090104050003007040c401c4980440c0381c10369030b20703203008a54920b003040d090345420000c3c0c010618501000c01000065500718840314102d42d10402c441141e00b2034010b10400700e8519084603000014032800c10341da280d000f60010300050550348101d0b071600c200c0702e081d8500c03282000812900b45d00d0010074081545401c1101c0b03070300000c4964414901c50304d05001100180300700c100350018050010b405c030301003c80b008006010309070080c00945d582d00320004028084451070108861040108001150398040055400c09844201240300f940f14070584202015040d03d803000c441064407510011100d40302880003480910b401d800910351440b45086818461900a00130300c0e018500001c05e034004c2e80d114050010300c0c904241e000c11 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 343151861 1250 343150611 343150637
    0xf0f060c1507021209030607200d02060406050718030f030302041a0c0d020d090509040606030c15020106050108040308040b1005190303030b0904030504270c11010e0c030d 75
    0x80103026484a411036401405486580640e09400c241d1040305183e0958020360481c42c1844254017a0101c0079415030700c1000050289400f80e045031520301e520385c1f0000c0d400101512071900d4040940c036800010f800c05410300c410000240941504016141400d180e000c49610741e1000d902c3c100c1c44094a000c2e902c80104007410700030390444000e0081e0020f1071031111500d0100d5a10b40d80721600c120105e00c5440d03204166144007140c00e90100000760f64032860355281034204010901c02800585070240e0380e642c000002000c0815001c020552086450404002c403900682117403503c0d030101d410b00c90100d0400000942c44201a0f6000d80d0280e034a22403501d41c00c004c81c2241c1c1c0903422150300324440480f10040740d10b000200c0c6040b603100703503801e100c0c401d0440c0034808080320a440060100d501848280020074407110900d09207104031b00e216500c0c0d046004000b0550b1110704590020498640143e184038000f80034290300d4649920090061070030240c04656034181916500f0200034000310000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 343153111 1250 343151861 343151869
    0x6060603070e0d290103080a030c0e031902011b030c140a0c080606040c050c0a1e08030f0103120203070f080d06080601030b01080f0610050118030816060501140f0f 72
    0x80610001c0c04203e02c5403010718180c9151500c3e9404500100ca503014032544402010102a050301c0e4402d01150500b100107a0540240c03640590500920201c0034440c013560301c0800488400f17408103c4805c0e41c407004e0307000241420380447c2c0010f00402400b140f00c0003007600080c1c2080c2c900c2d0b208607101081c040c0e0500090400455280003403180140e81400101542c0000e00c039030150100311010049401ea140c0c09940510a0b941003081581024200d10049810f45a6289903c01842c0301c024618002c0d035500c0340382d07500031104901c0080d00c140c01842440010b80d9010030070401d500042d4549506174032460008000d12030024051a40040c031a026002c203600402e00401c10b0808442c0556180e00d40021a10024040c45c44070b44280c540140c0344c10000104a4003d9021440400e10b2034141001168003150204030318000300003d080000000703001d0302c02404c0742c040700c01c035012145c2d04501d402d4007601c030123038001c00c0080c00c0600070070074690f140d002c181c0c003c82c41114004440c3c82008049 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 343154361 1250 343153111 343153127
    0x70501030b1f0c0213020d0f0f020a0c0f03050c030309010f060b04080c040e0c03010903020a02090a05060d080a0201060e04030e0a050102060c041211040203040f050d020d0f030507120c0507030e0a03050606060307 93
    0x30300081e400440d129491f01c04640100c1015070f0500c0060003043c8514010b442207004105540c000140d0307107030003c80410000340014204c2c40c06403800758074003a100f20381503145a105482141c1560b54840721401c3c0340ca071611801014004505120f0700e85441c051040382d50f2450b0b505141e10641c0d40d04410484003000f013113804441500a0f000f84107681207402c000c1c1d1150080d9406038041c1d600070001034450600c0d4403c41e0f00c20344000341280c1d4503600300d86a1000c590002d0450720155980c407200445e24400c125802803296100c0e40d00c01c83c01038521010700001300c02c2039001505650100c03040c0807442d0780b118140c1b0241c4e60410592044004103080916850900c80c2c18a44c1140c8000140700c1072001300710140707106500503000c861f01c0f00070300e0000300d94a0103026101c03800180e40f02c4c9400a100c0c4250015074011081e0702d046c898a9121801d5842101c0301c0e212060301041c00080c3c10010140c0161240c0f0303403404102c0316010414030795222240c40e900300504e500e01c140e81c00070000c0c455034095030311 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 343155611 1250 343154361 343154389
    0x9231005031006050910531005240a03080a03020c07080303070c021e100906021618180c0e250e0103200309070501030b1f0c02 56
    0x4403603006505540b0000206014098903000351006000280140c50507005042200c010303a20301810014075180708000034008002080c2d0310815a040c0c138036211411003842e202d036000d1440c0c00c00548440d0184070301d8020070140080110707007014100071045440c0303494429401141018201072810020000d4042912504020002040840c3e002070007541907000d4440280044c0880b035034651964800c0345d59000031141140000c0d0080c0c51600141020045000958400d454181806c0702880015018010340390b054000600300d07403020043c0715410064861503400c480c000002d081e04140d040f000642048810045151304c904101448403268640941625040070203014074680782c2c0e02052440030b0a0741d0307422000360312031641500e0780c581d0f55030420755008c0d54442c115481c01c808010340c003a08810080da02c0d60645c0145501940350a2401544a4136070350000c1c00c0c2032828040054101c46003189410300840e8002c1c05000352044d085a103500c400703000d04207654241d051b4400604030004100e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 343156861 1250 343155611 343155613
    0x3020d0b0d11130609060e48070204020d090302060a0603030c0209042409150c050d1a180a0e03031308090301020d0c03151406040603020f0d020408160923100503 71
    0x20005094000c590b002340118034aa04030510b4449a180001300c7c002c006102c08422501c410011982000343c03004012960304030550b15040000c0c60300024200e0304402d90f00d0407026150b01c0001c00f09541485980c1d800300810300e007008041e003151030017040700a02400003802401203101160510014910b84030014040e882e032408600c40002486000e400d0702e0504849050019012085080d0030740294000740720300e6a5024108034180c04064042d100591095100e0815040c001ca03c90303c407220344100c8180c490409030000c1c10840400c50880d086054152840d40041c8180662600c0000c1a100340c550804042500c51900d94001b80c0240314200b5200d101900e00745100d03000703981603040790820700266031000d4901650350074881c5045881035405a8011410041440400c0c042d50280140042c48100e4074145140c0a0303213142240d005800c04a02e07684103403880400e1031143c0e207680c0041c206000d0240155281030014041c107540ca0440b00c0341c8000c80c880000e111900801015004043c010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 343158111 1250 343156861 343156871
    0x203160503070c0b0a0906030b2b0b070302120a0501061b0c08030d09050d0201050415020d02090d050102090306220b131212061d04020d0c0308070303020d0b0d11130609 74
    0x15602c1303000c0707a0008500d070300450602c8a0004003d0300a1280c040c41880c09403c020540c00162a100c0c800203030000445d0301c60385550f0510020607002030811740b05041c4c50b100141c2c0ca401c07809110903c8540201036032145410b15005100715980441c0000c41151058044540c0d0301c3d5904c3d0190108020360040c2000348008510710719058215006408428000c40941c2d2a11900c0d031070407400d940080720041e0210820105200030400260300030010190088001414a0324410003c4c9003280c0c007a0064071541c0d0041606205413405001b4250440d88100c030842c4008051584828900290000502010323904800071302041f00610a8450455004000340c8030003045910140c03039203c044825542c2ea500d404d03408942c0e00c010001c881d40c640f0201c0601c448542d0345600300210125a008111002d0401c100c6c0080080c1007003002c0c00001d032180d1005600c0301c0c005488001299035004080c4d1041e401d440030480400c5001900041171103041c3d0b600c29806944040e80000ba02301c90b4000c24820b441c2c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 343159361 1250 343158111 343158119
    0x2106020f03060108060409020306041b05130b030601150e04050c0408030325020a02030601170a0510050a0b0406051e01140a0c1211100f060e010608040614070203160503070c 76
    0x2490007144110000d03200d040d210744800c801d0108946202078000d415a100c8000700b4041003107500b141c1c5e40f0301c1c1500c07400301340c1d55110004102001407000c1d0840c2142d4403000510420f1900b42b154070f0161100c0c0848828960709400024003803000281e845000d255500f0118103685000740131940500080f030103c0380d4a0030010001d0a021040051050034407180212503c47d007880440d40f221440e400034001c0c0f800e0303420311060b030300f01101d90590841d13584110507001002420902c003640300526028400101450005000411345640980081c0304610704034040c000d6980c0c00c40a203004070342d5001c44549a1021400607158004403d038485039205002c10044440c640c0b01800e50281032091303800308000480c0400c1035940344500b2100100f9074120101001492907a0307400b440c900e4401203008162075030340c1c01c4d18400c190020b8212800052a050805c400c5c0000c0d4007070905481129031124215190400c4002c0d10b80c06000540c50142815943e140700f400307002c00030381c0c0c2c22541040c900341c912691 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 343160611 1250 343159361 343159387
    0x10303050702040b2409040e06070206090f160b09010e06180f0303071a0403090506040e07030507090b090d020f0a090203040314030603060c0c010f140703180507210602 74
    0x4000c000300d11aa0130858100080e0412040004000000c007400e80c54003000c5418801e0940c004001840e0003d648400101e00100104078590280043d900a4890703800c0000c0792500f03050601c001803803030780d11840103190300c0e40182c140c1e00221410070a5094a40d00480012512a02c10702e5240b640300c2c00204445121004280103020810b8085400802c406c0f4180141920b0340649600030744041d1282c80e044240c40164114164001e1003454a80592515031000481982094100900c3c4042d10340800555607018400c2d590000c4150402c0b006c2d8510384490710841e40704039240c9034000c41d1004207200454076072200c0d2103404100185154266511280036500035001200c060300003442c442a200f4164200d2021070b409600090040c2002c1d0381c40c3c00b51030350aa030142c010140950b43e07170100d0900000c01031042c11100c0240e10782c0c0880d00c3c00d01000c01410b8400018007021220020044940010000a032000440d45220002c3d0030030000c45982c030310094044c960242c50030340009500c1c0b06070703a8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 343161861 1250 343160611 343160617
    0x190209121b040b0d06151a04060809030309120d0209041d121606050612030a0201090209091501090c11120901030f05190e0102220e0114060a030209011701030305 71
    0x801c92844054a01000702004103540b08080041d07003104141c080c8002154040d04056150031030040c13400591a0b94103545140300b200300140086400340410700384501c951081c02d20b81c0008805004600350301b081140a41c4030b400b410881402c1100020b16911500c4090301a9015080c00900400c00825001254480030140d03860520b05c1c2c0c0208030402050070024000d403100008100706035010710340c080e41d42c07100420f005485241d1042190802500c01c11042006000d5018182c0c00801d01c0d0315070788144000303c140501950314640000c1c1380b48030b04604405034203044504048001c10f40314010340341030780d08050981100d901c2d4024803024071801c80c089002040000800c0c0da0410041e4200c040300000c0f50741c1581c0c0d82c1c00c0346450341020074513a000b03a08010508801c0310b0005180c012990009070310040c2900062200c5074420300104441d4114240040c01440002002d40c2d08502101c0042c10f54405d15a002d028554081140c0469074483c941038482908000fa8207413455031281009002c86d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 343163111 1250 343161861 343161883
    0xa11011503230102040b0f120105010e0303121f030b010e0c120103030c0606090219080903190f031e0203091c0e0f15073819020912 58
    0x240c2808031000040c00050021011650400007086450080031084040c00502c0390a581e5559000d210104d000c0c486640100480703c3c2815000e84d85d8035007a4450081101d05922035410b21055008806890300e0200841d02c00710305030501940d05545034441c511019031400340b440c3318030115403c04000c00c038407020b10905070364420721005401c1c2c1d41c0712940003a40c4940420000030b807034440010800240a0790100c40039038803804009c80c1c41c94a030315100081303800452031800702c0c08213003500d0500550030000c00c42d003040410000d1450031802c00328402e62030500400d400c0c10024244e00003c4614802e500507103581002030356000b6480c00c0e4683c110065081528815072a001c0c1e58294102250040030900d280800c07038858039000000b2000700300104042410b100e4110540210300646807000800800c9118400d40300e481a150328158a00882120266280301420900c104480c441c146003980590003c501149030141c9013440c0000c1c006400b60f42c441e0758102404071100c1d4490707540401e86100304 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 343164361 1250 343163111 343163113
    0x22226010207080d0510290928050f0409120c02120a030206010609050d0c06030b0303070f060903110d1e03090f0c03030f1b0212030c061e070905010e0f030c060a11 72
    0x60307521103100c00940380c000c04c40c040481c1328003111187d00d1502d84000c0c0100b11f80060001030300340340380d000c1d004400e02d4510f607119144410400c24041da00d020580014180c2c801ea501300300005455454481008050035a60148410003405004542d903505c507111101010b0300c02d840c4200460314000c0d541d012f0030700500003c5007040d0030204413400c01d100d111001a4100140c0c00685190410903001800e003807603c59054002041000007140c101c10b400004e040c031070303800050081403d040c010880b02180b80c0004094000c2d0303c03034045150740066441c40401e40610080340300b043e0448194024049a20010300c1200484080390920024080c600204c80c02a00e807100041a030780c2d001c0742d070303c8071083c603809c0101c0b100c00d07254016080c112040103800302c03178a080301d150041410445180c0842100c1c1040c0030030784ea0400710a1820428010768202400d404c00f101c03500e0800300040c00005600042e2406040f60220090040c0c2d02048103517684c10001e8803032503031207140140041042e4151449034100d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 343165467 1106 343164361 343164391
    0x11060a02030c0607021f0b130603080306090709050a0b070528050705060f0301050f0328020a080c06070305030405010209040c03022226010207080d05 66
    0x26604a4006584408503215501c3c0741c114020102401c40d00052103110f900e80b130020000042c0440264045846200321002c50308071003504031010070700e508143c0000b042c04a01001540116025240c0d50820381d60250240c0e0802c0303107031145035004044110704000441d0240080c111b103030321a10540b403008450b880e16958402c41c40c440c041d100082c400c8600108202004060000c02c07040d030f04c881c1019401045a641400148500c501580c0d980020030f80c02c4d5000e0180349965900301055006941200070b80392244100c0d02c4049001c0d0358102c0c0c0201d40d5200000d03203e9000c6400618961411445070342c22155a0005071040f41c056409001c80540c503520360103504c0c00100a6171303006845581081200080c403010050002d00781610910511081c500c041c41c4917450308010a100200005425603540240f04840002e041c030300000c03030008600089504058017590492001c010 = true := by decide +kernel

theorem cover : BRFrame.Cov 342985611 343165467 := by
  have h0 := BRFrame.cov_init 342985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 342985611 ≤ n) (h2 : n < 343165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
