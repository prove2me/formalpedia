-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4826
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:51:55.370516+00:00
-- url     : https://prove2.me/submissions/523c62ba-84ce-45bb-b5f4-c07d357d252a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 867805755 ≤ n < 867985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 867807005 1250 867805755 867805769
    0x1b040c090f03080901080a0b06030f0a33090b09010911040803030403030b0a14010c060e0a050307210f0504030219230108010801290d08030c0d05060d110409030504 72
    0xd11a5103078a009450781c0d0111004501094a000001f245411640143d0b01c1d829000341c01c41c2e044d80c80d040c0010a1b5280003421040d0030544500c000f0501c034440c142d130041c103422072040b01c8545640ca041c9002c00b00016410040000c3e041c5290f440c0c003a00c03442905411260090750001c1d108525885850040c091900102201e0000009000a16905030040d01184800300e802400e0655200000c0c40d4402d20880811702003081e1910100c003003241580540b00106001c02038034801c030110348d50f46003117030311071401103500e450f40c080c4907050b070070000c4000600302a4601340580d11840783c06000c0c050303010350f100080c0300b00141076204046000c00710490b0010045c05039089000e441c06081401d9031500034510500144009000140c2800140940100c030030614000084c0800ca030280c42c490108990070007600030642c11440300c00207800390700452007055581c420a49403001041102e040d01c1010340300b10722500225101c000030501c51403403411000c004603000035054071103203030980f0030740901e500c221 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 867808255 1250 867807005 867807029
    0x171f12030528031401060c260d0f0605030c150f0f0a050c0610050d0807080408060906071d010f03051306020c010b010201150b0f1804090f0209091b040c09 68
    0x11a0000041c2d1440c0514560768070144901c480c2d0100100c1a04824451000040c0c0340f1829000403c032007021031021001e40038185201800402c0c00c02c5802e40c0540059110190b844c501d0740e819500078803481018041c110068003002d044400001d03001c060b05c0c585111000000640c511041c045403084550039920060540d0701d5990480014045810810840041d1b001d100d000a600e044080300100a9400080c8010300c05007982d140c4c002180c001c0f2008541c650400c01002c21101e4040081038404c0c80307003900a2030146001a002010010090100c1107800300b542e40c049402c1c2e800c540701600c000406d2500049507a14081c0844404459040281410b1310000d0703078021603401900103c1060704282c0007407020312034191410340240c3c4248120003c0d0345051100b8040c001c08140249142c0800d88025001e40070701d040041d0442c0d10782c0004560498000a200f004c604003410340983c0141c0340000760541d42c90080742c51b8014242162910301c038540c0d40c6006270869020f00140300c0900014941d503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 867809505 1250 867808255 867808297
    0x91e05130b0123090c19030b03030418060b070605220305031303020109170d0c0e130209060715061d2e03080d2c1902060f0a171f120305 60
    0x3038003060b4001c140440d046c41c00385240e401d129020780641000500d0160003185081d00e05403c107021980320301051b1042ca901c4440020f003030040c2d080035200c8613008c0d110000315400e00c007140655500b405281c004031145100054400310f5040019242e010242c0a003900c94a1510715089005160000c001000070250001e00d038040c80a00c00640038002c0340c550104501c0c40782c00016a42400c020704440c1d403107042c103d1440ca00c0d901c1c0390050800c042c000f07030003a420302078295a45a41c07100601c5240c0381d0b0960703c1070100081001c0e02c141981400d081800b4103000d0800780c0b248000b0300452140301444540f40b00c44610010445003091005581085565132181c010b4540600940b46501002c490440495221500d80b04049655181c0d61920801460000c02c08100e000190288010a9a1125041c03041c00c400e441c0d090000c10749091700e81d844002158000403555101c140c080c1801060803022004841480001900300080e038509400b919101c85042c17a046810703124004a40c101d104540383e81c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 867810755 1250 867809505 867809521
    0xe0f0c132103080a151a13170616390812010803090108041401060b0f070203070e09070918052a041e0c0207091e05130b012309 56
    0x6008211440ba41e210000d80c3c80d01c9000c402510521900c3e80b4454200e01070422013800c0031442d0000c60b103000500705040504e00120200846100d078030400c0c4207145000140c12000d030602c8080c0d0f202c60700d410303518080000800c00402c44200c0c084480e2403009402000d110b21411607107010038442c0000d140c99503030441480c040707103182c10400340010015845d40021480d085c1c080250307600500181c0d51102c0681d616114143c14030390f81949031249540e03910010942483c244000d040c141d81244000b550354445205140ca400c100350b008036900b00440b02070041e094004107107c0b08a0b0010040850001c070421400b000054421000070120b201c6d0348035001180da030002485a041d1500313420714058030902d41c1444103075000c1044100c1c0d001000400030310343c2c01c55a404442c2c0021948121000c450311280503208a030392107003143c1908a90b0350680e981030805401003a44c42113404000341c140345083d5844019080c8180940420311000d84058802c0c24004541864202801401140b04c2d050401d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 867812005 1250 867810755 867810809
    0x708060c071103030309030a260103030c03020f070803040b0708040b1204120206060303161113050108100204051302070321020405010807020c010e060903010e0f160e0f0c13 76
    0x407040707540c142c11a454000900e00030080e43d02c203040da04040d51800800c0e06048810860078000b04c00811742e882007104102010101141c043c40c4207842d0300401c41c02d43e00300070745021074400b010051640400d01c02d002d243d07004030541e01143e2001c14496113960340341ca0502c0644c012900000000840400e212140650511841780603034002c003c10510165401c5080381c079101c00b00d6030130341c26600030000b01e00070086400160300060300a1962031410102040002e00044d01c80305d207810307540d40354001408526000d01c850342940320900d5045180601e0f20340401d1410324610700030b0408650100340350302407500402d100c030780101c0e5900b2802c005008880940009402c00e00030f80b400074082c500000d407040d000140a0b0a0020305071030f617050f0800c3d85800c02a407035128800c80394240d502c5800449140000b00400700000708018040c2c2a00b50030113190a03140e00d07090b404030300200d4040081c00684055400d0b81500003a41b0340c61990703243d4070461103e224102c29440703041c041c10114004034110340d402e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 867813255 1250 867812005 867812017
    0x10020c1e040c090308191b030804030305090706090e0a232d0a1e230c040315020906071a070305150303180a0906180c080f040f050708060c 61
    0x11020480b80b0701c014011158002c15000003016058100948041990340c2c403075a40541c2d4280c544a4403410303400c0d2948814107004801100420014000c4c002010740500500d82c0c00064200104195868100d004003075003201d1081c22900106840401c01039075040d000b01d10201c00404036410080d880d1580c90030720718402c0301d1000362120025001403800e80d000c0c2d90a8008000541c04203602d48903035030444014516040810340300440c045100d446501c190050441c80b1480c11203407465445207150031040110001d1140c6070115003004184000340d030f841480c0a0041483c40016203a44013100451890701c10090082c2c904568414901141081001c10a101c0c4a06650902c4a074694151006248061640c0258160424081d002c005603a071800154100c400410080d1015602d050580c00c0f41c0107904a00c0c1c510589608110000e5a24042c0880e04078071480c0005107031600301b0200303079030801c0944010400701f458958801480810070002e0090005542961540e0401c44000d407084e038008 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 867814505 1250 867813255 867813259
    0x309070905060904331505040e1203010e070c0f0804050f1f0e04090606091b09060f0e06071a07020c0103050103050303060d171804050105040b030a0210020c1e 70
    0x408000360b103900741100c2203030103168010f0b0000c00c22810300b2281c5010414588001c6051070400782c8a10b800703c1940120141107092107043c400c0141003030284019140041d0400540303074054401c02e44c9080c52002104d0441e0584800803182d9116140d0440d0b0f401003500d4050306d04800320001c2000d000280005104581048525201c02042003091104040452070801c8100110000c1c030101c5e070707028080c1e401d0b4050008000090091745951044102d0b02141c005880c030a0b5212038204030f00b412507404c010740100c1e40c100764519500e0070000514582c8030301541c0c0c003000241d01c4041032300d03113070641070340d5609038801d00a4a10100000e000800b030031088131007100511070314007d1450b5501038407400303060b41d42001c007452035603036810140302d101c03505030404841004620900240020005000d880c040000880c0740031400f200380c00b0001602c4060f08082d125500d80b05800f04190350002d100d0301030380d9041c0e542c514040d0042000388d041020507080c9903004407114518685180007011405c09080c0c0c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 867815755 1250 867814505 867814511
    0x103230f0f15091617010e031c060501080c0a200109030c030906090605161704030b012402060f06060c010c0c05070806190e0705040c0305151c0201030e0c030303090709 74
    0x2d01000c00c3d500c005004042251800a000502c00c5801020170580341112201c0089000241046401c0c61540600600d00d0b240c0c5840e08441025a5540201c01c0201b10074604100e007130900b000305484500c1800f06410901624046001000d4081c03400c401d160100c000c003c00c0114058140540701031803000e030481c00215404c001103411400b5000c1102501e1243c1e50350b034109522407007240e20300404940c0945601c841c900d0441e0380003070041d0061014510801d004902c65161503c040180c0c1c41c070002d0002150745480e03081861640c005410741e03200440c44107240054580a003c44c4203403140304441e4a4039401c01c40b800200300d8002c9942d400c8644940c00f201e032606da840d4480c6071100c005444240e01018407054080781203070150800b04200400c001514840d0340d035030000074104c440d14010240425250b0081203001410403001c0159481c081d590300b000203608146480c86170641b988024141a42c81c09041c12889040000302c81c00c00018049039507a0420785003055031840325204088a080c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 867817005 1250 867815755 867815761
    0x70902040b030f24091506030916090204060c02091503030c0d0e0406145505130e01021e1b0106030506060103050415090c050a0605030103230f0f15 65
    0x40c40702001c00200c4015103546004c04600c0d0804c008000d014181214610079030121620b0399441900540c0560328050080440d03040690400020000b1035005040141c0305200411002c1d1700220aa25650b43c1142c80c0042c80d500c5c01c00c100b5440d4842c0003c0d94045c8004240c09d45492000980782d42c100c2e04c2a00c0d001c0744840e0302e100b0442a80d1150043e00840e030110b03d4040d0444c20600604a9210001d0520864018504084091020740a8038141c000015454911896058481d1031800c0c0d40316158802d00240c28000403441d40e424210714030f000147c1c0c84102c080340e160203506561884001c0b90b101d0b8003603400d5032504a082d401805640e800b1200d2004200300243d0144260012640e010001d0a4980d550380015401018002e20540e80001d02e45a4115818201c0c402c1002d01c500c54241075904500b880248500016603822079020b1280070801400400c0000d91161445845080e07441c40140d00c42808034200104031207100150300c68101c034206078090120340900e200e8040f64000d5221b51b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 867818255 1250 867817005 867817021
    0xe0a03020c18130f23060f06091e0702070812040e31020127060f0912020f0d08030a0e0c04020415350f090f100e070902040b030f 57
    0x240054031039848543c001103640c000242c1c5034800783c05180c0100ca0700031010b004903502c41d00910603d09020500e411100070800c1c481c6405c1c02880c1c110038156500501c2d454850384e100740500a4142030341d54401c180300050880340c802c21a44010f4000d5409441110784011000b861710381007030040c4580c00c3d02145c0001c0d00840529a081070a903414041c09c0c8440c900051101d8010148040680c100302a4009400007807466403040c542c48000a02c59880182c64004020152014901d4110800426800c20040c40521407400e80c4019011103400e800b41d46150000383d403070300a08100800e680004803c00000c1881070740000030350070390841035401a8102508004c100d110324041e6454401052440c0f20728244555060a000910040c0b4410040d2a849200361400f0100d0820041c944041c801c020700342c000282c8064001d08500001c062200c0354403901906c0e10440259200389681d524881c8202340c0c8200840401411400021980d89803540100851a03204840340504c260824011078448 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 867819505 1250 867818255 867818299
    0x1106090613050a061b03050a1404080f0d111509010905061303092c130506010b0c1014010e091513021c020114070c150302091009030309090509010e0a03020c 69
    0x500510707800c00f409207815a0b05687c0c03a001201007800f00403003110540e01600f51040100080d0910300014188584149441450710b440f1911907001c00015204412a004000400e02d601c2c0c80d09004c101c05540c1c8800b10f2900400c40b4081c00340c840d10960303040c4036160f8110320412060600994135800c40300d40b00c41140b42c0c04141d407414680714515000c8000e5800c460745803519008030403400103582801e19621000e01c1e283e0700f038000d444841b20001310220520782c03c0100c0701011800c18000e11900c1d03458600c28040c0312052041003008154900003c10001062040941900c955502d40f44070f170401300f101c0c04000c01017410032030103031810081c10030b02103403240490303110564144d407012021804c0b5020454980c1000c01f0441e11203068901c003041c0c0c448003241d01c0000d0709250b41c0c01601c81d21070008024031000c44c0301158040c0182c9145c01e00120b036100100d9000e48541c08000f203140d8036030070f42050051055022581c40350041519500030103a0220b920091002d0880c0c4115000014500081c88 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 867820755 1250 867819505 867819527
    0x20a030903170c0d0c03090501051f050a0e0103120519090f082a040b0301110909100810020307140310080d020708150903071b0906140d1106090613050a06 68
    0xc40c05044c098a00c3e201c2c06038000011030390b0185408168048166540b500703495055449030300800040025900c010740014040c070085c1f400f118100301036442c0000d0900362034018000540140c40951a94840d00d005a0846c0c15a00600080840c03d5a207920000c0110046010f840d2002d0743e0001d0000b15400000b442e20101e4441c5510407521a0003440b100300104500314945400c00d0f1940454095031741c0c03c1c8030700c2451461500c20165500c46200400084140003009800801f18040e024003004200142045034140c043c10010390760f48072010141d4582d1401d0020b42460400001000301c0514828040c10407a06940100c0f0303086240b00c3d030b081c5d85a1900d4003918406500c000401d9000c1c100365481a50070103001d1007078a1800036907807504400589009a024003610524008110000b4039114250003040000c1001d8070b400080c1001032148201e01001400400456552000c1030745c0c0c5108840381f10070000c001d65511120f582c0c2280c98a20302c0e108561142c0b180a2000802900071b103640c0b10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 867822005 1250 867820755 867820771
    0x2030c06091c030201110414181608062b0b0108061e0a02040503031b07080a11040c17090a06051308120c090a060c05010b1927020a03090317 62
    0x38001d4025034a18503686a0320b0301501150f403141051b5020a90302c40090029000c0c0d0840b1200b9401408240700408441d014403844102c030010400c040c001044170700307032180c203030a00d003c601648408001488070580300141c1c81401001c0c04c8050060780400c0d0800404a1103040c4d14016a0380c1d809200752140d4040790103040702800070f500c3d001c07070220910000e940f100c480c4100506064569000c68a90380180241105602031011100c520007c108040340003841c5080040c2040325096903400c0c10402e03504c46140c092615031300c1c220f209038001c090720b4141c41c00c484030101081c0340c08422540c0e0340116420a40b0b50034a084080380c00c2400360b0480e00d42c0941c205110034541a00d01c4502c1440250041194607680d0703060103a5105940d944120100814040e9251042840e4904001c0c0c21a000000e03201e1084103200f01c0d80c80c0c18000ea03500c0800b03c403004004038501001d0071110803c9800c0c090043c8000e64400a260040c00e82c26510030500d6600a58a10318080300c40304020070f0000b402d82d03150b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 867823255 1250 867822005 867822019
    0x60b0a120c1407030314010b030403090807060e041805011e0c080103020f0d260301060807030207050c060f04090f060e011a07201008060405150d0605130503030106050702030c0609 79
    0x8a019820400a00c2004c0c880c2c60001202c1c0449503484d941c43d03100b0f03001000001c100000307000500d9070040084001c0d28002003c0c0c00e48924290000e0543d0071140401c03402140c541c495800340c405043c2d02c09001c1a040002400030790345038651341c0d0905005c040c2c82c20001c1d18041000203510f110300c0a0074183c075406840480e041410308100030402c5141001150918041f81d4140b40140d01c2e1954405c504403030000c4652654100040900001d4005044008152041c86044045100050040301c5075205541c1642d40d442800940c031424800c0c0d810000d03c0c1400c10400c2c202c00440c56001100300d543c2d9840115240e40c9810307551107944482242e24007004c1c0c0900852011904800c08880c080705c0041c8403084800300d00002c241842c1d6007a003080d01141c014010001c43d810f00d4010b559000040d9113210115944060000d071132107008500240019a270341c00050001354150f01d1010380944c01104490700d035070303540000400740c1d442264200e00034012450905101c0c200b40d400d071149800014008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 867824505 1250 867823255 867823277
    0x130f0b1011060a0b0402040f060203090f010806060d0504080904090305040e060406030c0b0c0307231605100e0d050f0303070e06130302040f14070c03091a03060d0c0306060b0a120c 79
    0x286010300b113040c0c05594096820000001d5a941c0420f0080041955401a6480d8141e03c0b080040000241d9445410300c20880c040040b580d0341c040c122845801c1ca400d0000e420344850400444900440741d505400610f08540b640905030468090300849210b10594000d6680b44824407065691520004100480c003542c24405200d0300e8000e85a47c00004041700c1c01c03c0499160f403074015608500207a15406510394020544205100a144105503030141031070252034140443c03c016913162800040102d00202d035980c55030b58006d01c403952a001411100801c5c45911816140c0d0300a071034550108407124040c80d80c034100600ae40b0480c1045110701d040c02032841c0c0034403010b4001d442c2e5103007126030f417450400440150030074050701070071555480803c9541d0600c0c3c043d0800109402000181c14000780104001c010ba008803580b000090300d41e21100740092170881d000c0302c1c1d95000200010304080700484e00c1044080940342c0303035002d55141c00207030001e80c00c00402c84c0d17a00c114240005003d2890 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 867825755 1250 867824505 867824521
    0xf050f06090a20010c080d02120f09010f05090c270901020c0d0801050a06080705070204050a20030f07030e0a0c030803160c03080403081e090607030e0624130f0b101106 74
    0x43c00e81107c0000015280031114102400205021141000c5400c8858103000c04c88909109850042d80c1d4070b81e080003141085c0700620354440d040560588101030040d50f080c4500740076290030100702140c9a25a06034284003c0090203900090241140761203201c2207040c0741c510400c00c880c1240e01c05017004002d2406c2c034500f21f034514402015003040c040708118120040c0c8492080703510481841c000000c6084001005000c4050310300880300c4080002d1092160658403207000c280c00481a05000414542c444505414a407031030030050800c0c01030703000001c24004030400035072242c1203c54144083c1c0700f5400054a1070502d00d80050001510000010b000034080d08400380c101c0040d0f41e280c04000d0000641c1002c4100440c0ca40c81c907078011000340008503070580142c0c441990550301801840c9030440b0414030340a0140d501e00c41c42400c1c544403230020741f179440c1c03840c10420035464180a083c2140603114094070400070080d00964045007100080d03403140d80403242030010a401b03800d035500d42c1070b1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 867827005 1250 867825755 867825757
    0x41407060905060a031d0c0a0b040b09092e0303140f03070e030f0f160f180504030302310503120f070813081e03040f030f050f06090a20010c08 63
    0x401505043e960307540c2c1c100d6003241c46280851104c2800051549131060741c1404008c030241d6100340c01c0c404051006119200281e4141d440401d010703182450140e0f02c0d289070b01d544988840704003400c6440016083c94419000c804901541d01a0711500400103040d030000390188124040780b20f940700c061001c1442c0314032900c80300045d003038000c04a50981000c88030140c00d11040f0807407603285900c0760b0300007131002c0c0c00c03602090002c181c09407903041c405103441c107900e1203401882511445580e4840004081500076815111105105034880c54060320984800c0040c00c0d010210742486510020006000c4c07800203070a0044514400805090208074482800310390001c800071184a8410f010010080c0365444240e030040550000800614100c04149040d40020701c052100b1a081081305004045e01a0385002c11240d000600c00802c804034244039080000810014095000300d105218854000080d000d422034000c0d803c0390602660f5809c42e9a200b8030300c0c0701c6280480c003d1000c00d40480e224070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 867828255 1250 867827005 867827017
    0x209060909071505040f05030304030f0213090c0308070b090604021309030905150310150e21070b0405012604080a09081f06141e120f0604140706090506 67
    0x41150382d00d6480c2d0351a140e0104002403031100190000c207081014401d80b140c4200148805d034061841c0c64150380790b00c3e0b0004401d05c0040c0c02240550a00000c0a20692200101d40e1f040709484030182d40700e00c0c00103101e600000007510f012440300c000c140100c2d80031510f00c1c0a40d034002c1005490b2035045c0d0810016140d181c0c8160107110707200a0020703940c3ca032802500f20109049129554914100b401c03403a003c1c200c0c4d04070a21036a01c2c5040c60310429001130040e5400c030000c0304c00444500300610b03010700c1e01ea00020020410701a1000005031040e54001400540340240c8480000e9030085510700d407402c403c5079840d6000d140c1d550104001c602560001c0100e04003918103001001d403156100c900d0304044e0882e0312050072000307081d142d00b2507031313032003140c01a200420340c80000704901d200245d40c200d4080101080c20b50304e4043c3c22103540d1104c52902d180103800040c3e0701203103800030f1f145844000807902511103581140c1d0b4103400000108c2c00100b0b0740c1090b01e42c040c82c981400c0522049070000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 867829505 1250 867828255 867828271
    0x60824010207120c030507080316030302090f060d090201120e15091e0a030207050a061d121906060503060105090408030a060302040e030910030513030e0d120504080c03060402090609 80
    0x408012840f0101e0303c0350b0491040c0900406500e09140d1310701a86442d00652000c00c0c5038209000d82403a00d81c01c0e48501000903010714026849810202c0000c2d2211030b08c003421584008000341e800380d04131103608620381c1c081c001d03224011002000c0119000751010400c05450642040703100079071040780c01c041190400d8188049660101c526040d2060403840c50f45856800d600c984842d208140c2c0c10803071400078040a45060350150f01d081000360074041c004002100c0b14944003220360b0b130b41e03c1d41d00610505006500840384109402c000d048100d411410007550f4880c00c03e4070100b224240011a94100d51740541004c80903a91a102c26025810140824620a86541001015070b4035401500c0e80308004102450350b9000f00402c1040900500302400181070070300c802c0040c2070003100320f808a1203806081c14168800340100040340030300102001019040030b80b420490301a03005002e070007664544e800b03c440e010f00c84420541d8070581100d0095100002400203120b41c200101a203070880c0741 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 867830755 1250 867829505 867829513
    0x14040506070b0c070b13110409020108060d1a150406090c020309011b080f0a0815010e060c011e050405070816030326090c0f04180201270f0603060608240102 69
    0x1655940741c906141a60180c0c1782c90701c114030407414894030704480641e410040710200f1500352700d0b50010b042c800000348407070701c40c003001c14203142071040b030500e0f01d030f2840c05451030380b1170510381160462942111800c10700c7c06140b0b4440b022034900303034911410301010003d400450500e4034850046861107007411680d42d454174024811000260058003a00000c00500d805a0325900a0034000b000300100034903c62840230b00d09280340342a608081c01405d809825030b011551902c07410111405018209440012420a00d010051000c440c1d4800d900841c070500c2074840480e80c894004c1d07079403600440f181c841301c50311040c20800a406450100741003901250040c01110301c5421a032501c4500701c07080007240d0060510740000385401820f180940b007040b6010054044260311405140500c418000d051000c07c40041c180c401060040c2081c86c03103514900107685448082010003188584a503d000c00d0800704042007050080d4032007442044901e843d011040103002c0306007100010040c3d020b065000b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 867832005 1250 867830755 867830767
    0x180a02031306110a030b0607020a030605090a0f140f12041418090a1122050703060e0711060714071101090f0e06090124050306010e0a030302060714040506070b0c 71
    0x2041c3c1c001c552500340d0400c0342c0c6450300907040010b02541d880c5100756116000400840c0b005a80308000ea00c113880d00160002000d650385964079140c4070b03007001d01600d01c00301d00c0082000c0041a26680e0b0340504030704166a8404040ca95140d03403100c0c19400c50841e5601807000f031040004080c50002c0b19a00103000c0401085001012403c51105890f26031444e04050001420302c104050b61940c080d0b025680311000a42001c258044420031031090030b1003d444001241c2e0356403007038111901078120100c00d4030761800d108201500164080103e0000c2c1d000c2c000004105d2030184120904416620081c107280051994800310103545010405042c050420310104026082e5210f41d8081c0010366170841c45070402d40700b0051508816401103001e03844010302012140c1642050030b00080e07503410155200e0300ca800c016580d5108001c007042e0000078621000042c1580081c3c100e014610940715a1410030a4241e0b01149100300d01465401c0003080009000180e03549446642c400405030700c0d1800c0c00c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 867833255 1250 867832005 867832013
    0x50601050702120c040c02030a05071b0e271504080c10110706141501110c0904030c110d031b06110a0512010902090901030b040303020705010c0914180a020313 70
    0x1c10795600314985644000d010008034140b91085007614921b5000a506064500302c009029104401004040c0095081082e00480a040c44000906200c0301c000d800c0745040c212507030680b0306003007003400f880e442c9000502d0040808141c000000d01c0e20814000140d946440e048050707032194001e14214410f04241420b104224490032485e95900e085840e5070b010300c4d0401e041507078a4000c1c1004004001820b0112400100c40c0441d81c2c20002c2c2003035492000f40040250a114048410f00e420079810030400040562028801d06024032582c0c18240501c21031082c003840e401511002408100c4820000141641521039800c0442c451100072655810100304030005410040c1048082000820034a501e5181c4042da0760142079001c40850400601c2c0c0c0014207008818480940006407003404203082c540300c1d8044071400e40c2c004e8000d2041000d03c903070081c400081d0f403050f0920869095114170031498841241d0b0714906424051140719100c2c82801c0300294400341500114050b2500454001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 867834505 1250 867833255 867833269
    0x61008161b2001090608010b03061c050d030225020f060c010e0a0813061110110c1f1b050d020a0e0a060c11012c011b05010e010c0203090a09050601050702 68
    0x1030450381c21000a1141680001341c840403c03900440300740701d206030060200e030468006807540103a003250000c888403072a14802e051139900d0103015080d400744881040c401501034000702729590744030503040c04892108032030203155100154003c1d8080700d420420a40d9181c084058040c2080c143c0c0001001c2c030008a840d45400141c6004564007a004a4038003140101400450014440b90810b5000510301c100e4040d21a00e00703407107903040169140607484808070500f081d605d059110000b00c403070310300c0c0880d11442c0784a0380c00c103824002420000c10b0b55455502c607080484403100c6844081c14102c101c2c002801940007441510104045108080384558400031740400410342c40d2514100c1880a0401500302c2c4c481e42c4480c0e062040300603903650000c9034024030800303101021440301007002c100001290750303003034951454003510000f4120740103000040d8451003503040003c0c020045509915016612801044655548441c000c4810044840150411507000b8014903000e0710302009680000c0f80303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 867835755 1250 867834505 867834533
    0xf110414060906030303040b0106140d06091a0609030304030f02040b040222060e0a03060c031113050102071d0105151c020d150e0106050a030615020105061008161b 72
    0x10000e10340c080c0403480c00c00c02110390300004254041e5285103040d80354280001010300c00c030750070005c00c0c2c140303060001ca00000b03590300c1800000c0184032031696403416202610708801103d40d00d031034440031072101e0b1508000711808144050041c41c28a4607503195094220340111060b41c0060321070042d010180e440344020460700c0ca5800d00015004c1444403106981510b940144042c02003440502c05183d40703110070750741140d50140001c12040c440310f004902600c80002e003421116000b05108603500074080c50319007a124282c1c01c0340c0d40c01c0e0f56188540b007400c02d0000d50030307200d86007000180098108040d012081801101c903113454000314100c607503c410f400301c10319040c0d20390109038500c0400a501071400c6464500c00c1100090b42041003010203108184140814030100040800c0c2c1180290440e400529071b2032501401c807546c101010740681001c441e42c500c200003103400410101d01820913540a10003141c0c0191149903840421758a180004640c0c0b400c1c251001080f0300052400b04040003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 867837005 1250 867835755 867835781
    0x80d0c020319050607091703031506190906120506090c211311040b130216171b06040507051306171006050f131107050a0309060801150503040f1104 65
    0xb00f4079000100900060791600b011f412240914103801c03001400000f5aa00b18106104840d0049211400a140e9100c2e411914032070070301c42c45800500b80c1e000040042118640d4850268020b600c0243c1002c84404030341e120f6008104102060000c40d0703400150500c940c4049600001d1104251400304003c801c48800c01400001034044007000210589207013050000c1c3c1e402d11607003100100243c00d200e0742d403c0d801e01d0310740d0106407004501d55524142d07000541022043c80c3d000e6506d003414607a03600494900c9508490007107802030001e80040c143d0720803034101000e4840f003030403c0c04000a4650340d15602903078607180c8a010402811034041d10a66184e4400240600641c4070184820b4603180e92000b0b10842000407003000c4d5444290070000307450341003040010240c1085605d10f9131809000e0028000348110514039081603040032000b81511000c1e12050110ba80e58201c1e1405000100c5007103000a001340081000104104501d0342030038460348155041d40402400300b4103c0d440701c03241203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 867838255 1250 867837005 867837013
    0x9080310050a060c0305030f0a0b13020304060b09040c0b030c0904060909020109050a051c0c03140f060903041d07030e0f0a0b0604052a0c0d0309140106080d0c02031905 74
    0x10341c80c1ca8000344005080f2400d0880c4000c0c002e031000741041c00000d0099200040540001d9014400380d40400000310000742032070301000720310380300100a40013128100e408a01d80100405586020304103548a04d50295840741103d050422418154101801303008940c0010f0220700116500ca010342c02c09814080000038400d441e600004240c460039a0205014113400c6c0f00a00854543d85c410310011180c3d030107440c8416600d40390089104000b507101802d1420321074800050a40082004c00c0311039040001c41d401d548441008913102c0c0300383e00c1485015015480d5855040805640807a03100110b400c00080e25441c2481c0c3c0c60a100c800e04180c0840c0d0402900c21041007415036249070405425141003125241101d52800c640401c51040d41032060a504417800034030800b4101d030f8070018044160303410a0158034018014000401e0b044405006101007103842c00e0051144104950705103000303290b180c914180c1071b0b402c074543c090141e806010742011001c6400312104400e6415101d04020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 867839505 1250 867838255 867838259
    0x7050120150f1f060507080d0204090905060108010e030711030a021801090c020714150d06090207030e031605120f060f010e011203020c0402090a0509101404022a0109080310 76
    0x31844500042002400f845004031500e440620515079505880d4541803560f40c910080c24000407900070101e81510060000501041c0000c442d000007409074814021203580b80d0700e8910381c44c242c0f4400c1e25140070950040c0079900c04180501c40c500c5801501400303a5880c220281c0201d80c0c1902000b4544001034502c100420070409a403041440c5154644003619000d8145610742006401e0113219502c83c3c07502040c0f0900010041d800c681c211030001c0760420104c0c0d5141254000380d000440150081004a03800c502035080101d513194108400c070060306a09800e040c100b00703038174810800303d40340c034402c400341e0b0201c041c02001700500035409171501c40280d601d0418811020702058000c051070f41c46100174940000d40000380400d0b8504100c901603116064000070524128155202e154020350320070a210b01040788404d190292448014100444c00c842d02c24001a4410a51054141854104030190103001840d041c2082190440042501034045e1107161240d0800c0e9040e0301150044030301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 867840755 1250 867839505 867839521
    0x61d130e1c030621110603090f0105060108190c02010f0c0e15130905280c03050f100311040e060f070806010906090b07170f0403060509060105030705012015 69
    0x3a90460009031030140021030801d40f44248200b55000342d44d0945400c00524010840d00d018513219044000d49010b40701d1500c0c01126980b14141e0391603001c1d0754600300125600b075200702805482a600e1000309003801c8007200c001c2c00205425682042195610020105805414090200003c1c070715074501c4902d4801404010340c0411610075140202000c220002c1da801c40920800c044460100000415a840c54200d421f00b0006000da140542e114420341e110301c04442c0d0140507040340381c0e501045180c5d82c450640072602d078252501c000d0843c0410b01000050400c50450a10010103007020500d45000084607140c01010788070500c4200c1c00c00100960b01e80e0102d4041da100209103400e8000c14517001e0007401d89000c1d0b018800c580c0c0c00004410042c4050064920101c2100000c159035800500c0340c44407080c2c01c40c2c001181c42508240100704410000100e03e416142c0050117081304a00c1c00f00150f50400c1c80401c000d0620410819900156509001c1d4000b03000101720407024034030b0f207401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 867842005 1250 867840755 867840793
    0x8030a0f1805060414010603020a09020a0305090a050309060d0f050405030a0f021203061017100f0603061a2505150c0a0e090a0204030506010807060905060301061d130e 74
    0x1c1c0344502520485200045900010078030b40041d0400340d84084454920707507042c050f200d039030130294105080c00d50000e50008542d004240c050399554080205031204010103451340c2d0038000c00340c80c60740140008280c2e49000002031403a0300d464440000c186088014030800c1e108101d80c196066000801c500003003640012640e51082c80500c05082c0401000c00e0940c0355010180032140104813102905000078080c7c0083d040318088100482103c2c6014051100511000d000d2138085103c04c42002446c680203018400540710344480c29581120050b081d0f4007135030032150040900d2140c03100c44003809907a440b040d079003146c015400703458402d922640000020368007a0003564206010050718000c541c1c00042141104c0c81203400400944450350400043d004542024020b4020540005007108000510700201d4055450380910740c0d503248100b24142c0000d01c5810007051601040103100b2030f00702c0911442d10380060098404042c6540c5003411918120460700b0164031040c5003171900d080840c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 867843255 1250 867842005 867842021
    0x1020a02060c250f08071407080d05040e0601020a150912080c18030f010e1b040c020d0302090607060c0c0b1b09041e110a0f03060b0304140a08030a0f 66
    0x80c8051030302c0e0220b031240752071208460003c14284520200d41c02001504c5041600072500207140701d49a452605002c041c180080181c01e29902c10880009103100e804078250302228020b440d000d04040c034244e5516000400100454114054640000c0004000590700e24030300c018039000140ca0b201d070346006004800c240041d1014015100c04002101c00c184d4200c403104111180e558412001e540c010a24002c03124010491550804132030241070f02c4005101d01c45c0c0024081007501205640c800e00003190035480c09480140c108020f841c110500980040020718006040381d80791040c592228411161a215200c1c00250364500400600c85032040150b00007186080c0295100102141c4482e07030710031031304098015901c1704100d0222291001c2400d0000c128128148282001105c8103903e40e4428908a400300b0100d11f40c00e80070610a119441c00c0c1c1d16101d01441c51612142c8421101e41c194240740360741d07840342002c140e000442c00c1c4055402143e5400f030214100520221a0301500c40d26 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 867844505 1250 867843255 867843271
    0x21903080414061f21031803170a080f0408030105091003081801020d0e031011040302060d090b07030606080705160c06020f070905060306060d050708121305010c121202091201020a0206 81
    0x7011071920324684441401c4046c3d01d4201401019940c0c0d280c801d90640580c40a81660b021803400f03902085000300038a850446a9a0003030303a0f5452203000300d81204140c5000d802514144014070940c00d02c02c032a650407030018078400840644ea03940d0141d050b8000b034200b40d180100c42200c8c104035601040710810182c0907080543d0141c490001095482c00e1075040d0840c40380c1c581001c4030010b520441294051a00a0304583d560308031242003801600010100b203e0202c060400074421034800d214801c2550400e9841060580761024100c2d01da0b00000015800240540a014000307400840d45500400c4d04da000381c07c0e54000c6c05055800e09160342e020785c95460400303040100507036001c0354080e0f0000d01280c002072107680d070381480c51070310040c0d070041e0081d44a25400b0703030607070f98100b40070702030329070204403489080c64850340115001305c00728000510000e4402a03050341c850007609804000c00302200d005040109110020780000d0f512071a000c1e60303944c005100c036a0558184495a440500c1c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 867845755 1250 867844505 867844529
    0x312140d0c08060f18070c0c03062301080703030f05090402030a140a02040303050f1b0d020a11060901020316140a0c032603011211150c010b01021903080414061f 71
    0x8141c0100e45c1074500314400c18410b4443c100010300e0240030f540c0d1240c409800114504c8003d44074039040d40100000c0fa01d441e101d030744404014500603132085616060f13901903406006458610b0303805840c07150315003030b6440c02d22009100343c040340c0e203982c8044c520890744104c000ca10b52164135105a21140040c00c1501a180108420300119420404507207000352200c2c02c181c7d80d008240c5210111800c01c81e1039440c18004c5000c1d258031240d00044154420340104000d04001c03945a0400011b44120354645000d600240403040440c900069444003a60041141c50460310003401c0302e82c1003181c000c2d001c0b0b07020004c108092082c0b0004400d4810500e54000508600d281c01d447d104800303010501c01c0304005c44034541c00f0320412558a051010204014100400c00d00f980b1001600c6a0000d102c107613400d61900c4820172442d803000502c000300141c03190300400000c68544080361543c4004106444c079500c6071030712011061040041c2803044010211880302c0720b0401c11100c910700083d610042500c49 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 867847005 1250 867845755 867845779
    0x61a041a0909070905071101060609061d040b040507031a0603010e04020d0f15060312021b0111031c0209011211030a0504060b0a080304050a060201060b03010312140d0c0806 76
    0xc00e00426201844045525072031541da00384449141404580110403040e00700418803030541e41041d051032004103550f00912981d03031543c0c81164000464841e440000e6441880d0300c030130003401e0005450501d0050000300b50003445902160079600151512400256105001405d00c400301d0405100000308550452440d454612040e1302d088010380080d2042012070b00741020480c2c070440002c00141d03c0b0300031032440280b0080c601c008148a2100741d8440c002c059514800c0792000c551910265075803100110400c80342c90046958010307102002c031961204000818210010325180c11034101100400350f5500107003800100401d82c0c1d102c60010440c00c00e0700c0210790342040000d0b40c1c0e00840c8520001001d17911424400c001d00407455a281c0c0200000e40c0106400034040024820780d001641d0510555030340d48000ca0032529580700d92004070b20140300510001e0600c07100e026080800c0d00e425401c42c0e2415842a855600080d40d94203641d580c0d62450315000d07000107886c0e42c80b030300c1150002e60700c003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 867848255 1250 867847005 867847031
    0x60603080c0d030e1203130f061b08040302100b0406321005041a070b0f010302090123060a05270f0906032508070303020619090201050f070f06020304061a04 69
    0x10314032170340c0304904020200c000381c0e2080e10040486101e070741002804954850300e040100c0203245940c414800140700e960320441003401880114003844d8144d000702244180007400d18010600000180e5106403034581c00905d403501c0c0d0100d60318130584c021101840520714001a2504c04000318a41e0003020201d024081c06030300031068a04889040c1121100000910492081c1d441402402000070001400b80700f203102003008143d0503244240d40400386640c0781c0b0201a80760361109007200c5811951010300780e2504048010f049222280c0c1400760600da17031243c54400411016003c026806021100741c0c410317140106840c42c0c5003100756824030241c103141000c130741c03200c0021680e5420360115464110401c03955207400d00c000c1100da070546072102d46a10700292070f103070140c46246040c0030030f600640d0f6021203445001c0540f54140c5500b80760001140400d8625003003071b00705072550100300413842c01040d4240001d41c400c82c410000040c8444540c050040000300120b0001d000703501d000340d510150 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 867849505 1250 867848255 867848263
    0x60504060813060e0a050d2f0138040b01090909111f031401050f10090b0a1e09060516020a0801090b04030f2316060603080c0d030e 58
    0x1480151a0403500355031241c008444045001d00b00503e100e113000c10100c141c450210745210241c4c0301d90b01791034502d01c1c81c010480e8440e500d00101007445070703100c0814803030640480058590301d0f0550004148075000030034144200c219a0803452003c81056005d0000c03491420041d256040111010030080c259600020b19840e0b650043c1c191041d80c82411030184610f26441d10005600207107403010912180c1d1076150811000e003003460200c3d041c0300303030980d14010112160741642c5005c0c0081054143e61000c010141690081c0c210512201c001c0c0401c5030107000f030040c007031400147c4810282c1c410341d82c4040f0100240750440820010342910034012143e02c4030845a4110100021680c11422030000038102c4003e0b5004003921340ca031148100c1080b00b1b400c0211320540c040c0c0c95980c01703440a0082514203240e03102842c1d0304098000d00c60444114554090406072041c0c00c1030145042d015510f64044500d560803c0d22030803404500508507507000c1180659410551900740020420300a0a65032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 867850755 1250 867849505 867849509
    0x6151424030a110702100f09080303061c0206130602030a09080318040c0e19050406081c120e100504140a050a080306010c02090f01080114090a060510050a0f050906030106060504 78
    0x1410741c40d01518450f02d012a410b46012980003008170b54000e02680001d80701c00d6050f010000852510000014006008000d0768031400e00a0082003503107801c440c40508188049004981c056018091400ca24140542c000c02804082d0029565400141e6024200144990144455600802444c206460b044610441011042c0c4020404804002060302c12001159210f40c2151200e200c54940c00b42006e1701008446c0203540c200b201c241c44854850f2030700718820f01100e00103110a01c3d40c82072031141070500030240082c8000101080c008002605040e0940201280951940d05110038400510200c051000f007040c004c0c926580203980781070f158400c004011305800c17404800500a03902550411070000c1e1300500b00110352416030903518400c0b500b0300546a0715071038194250548240103684c203005000040040072809070690303441002e00802800e0b11840450341d90700080c07030385400d82c08902401e4a1084c1480b090308200038070151410084c034651203a0f0411108014050300001140c1c2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 867852005 1250 867850755 867850771
    0x71704030f0807050c01110702100201060e0f06030a0f06020304060e0c030c1201020c030a021605010203030c041e050405180f031617071e060b0a08030301120615142403 74
    0x2d2a0354560a00303992600030740c00c03980a903500700612000e48404050050100b140b00b103401c3c010341014000304908940da2406544109000000415071040d03c2c0751140e0b502c14001400c65801d10035554a0842c19950200700300c1d10307181c01200707110800c600d60041c1c1e204090f2000040070400d1418000035664a90210011f001703141d107121140403c1000e4040307402038032101088036a2490350b003d0095481c80f00c0300701c01c3c2501250034000f0410707610120459002d01144603409050a080c0085540403070340080c4041c48020b03200744001416191802900d02c2450088010b031900381d041e40b8010700f400120740d0360103041d0f042003000180400f42508030030011904070120707480c80180103221582e5403040c0c001c050300550108038200149042c6170141221680300311028452400c11500b44036401d103460003190901c1d0001e1006001d0302002e2031100c504103000b80004101808101c6807889600c40369080000d280a003c10104410308000c040f215010800b610944103881c1c902000c19030354000506045 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 867853255 1250 867852005 867852017
    0x180c0904111308060103150c050f16060501030c0f0e09100e1920012105150d0804061403040804030b1e090c03010507090b0d02070c1508071704030f 65
    0x10500300c01540948802030000040c002c091600c0d08641643c82400744422a82000743c0c1c2e6003144da00d04140560003003d0120b0320740d04c1c00c0079440f001d20b82458216048461002140d10002e0340401c3c0503000c0d85000b58000e558084190b410003400070390b200c0d215000007072140851028800d08100005110a03440468140080c00f1144041a14200320a40351402450f0050781100000d0284403085143c51800c0074040f1010301100d180199841f20752502488010003403001c600301d85118a030042c0b0351088643c620300381c2d041c0710840001d02417070340d0303d00641c1c640d03c02040034001c05401a04810091031500303212402d5242958801015201e5400700500e00360180c4049180c02d002241d6070381000d41c1030111a602403414004003542c88042c0d20740c1910940c208404241e605004041c0340090b101034011040ca0070010074034000107503220450072103100c0c010400024400c80c00b8841d2000301c0c00d556032800364506041c1001414004107540180815072060244000a034001d207039450b058a01e41010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 867854505 1250 867853255 867853271
    0x1020726030703022b08130615031b050102070315270312060b04081b03100606050406120b0609010f020c06180a0909030801062a0c0302180c0904 64
    0x100c8a10020068009080d00c0041401e00400d500850142c3d030300d082c05680104404030307034a0303000d103442e25807004140800c1114022900140403100f4103017806024601c049030322244401548135010a0703070b0040d03800480c4845040d41416191201e9002440248001d044150550321482000b2140f206002003041c1d484070b4968040780024807035200c07020100c40c00e00c0711540c141005007010780707113002c0344000c00e140501c0800e02110300c20598090b951680300904013070407070051002002c0c219029a6a0521414184801c08801c50060700080d081c03681d1070700e443c1c51030f10901411015020700c03000301c44ad050900f83e07542501c400041c0c504180003443c22a00d11448050280c0c240685000c54507000180014820318018444240702c15a480a032040102c00c2e5483c0c5131601100c24080d40240060003031310040000500c240402c0219038191003201d040303155540b0040b1001c12030008122804518071030104103500c3c01803041e18204070a01e05010b280c4c076245c0c02110b20b9100d843c1c01144155651508 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 867855755 1250 867854505 867854549
    0x1a040b07032c031006080309191523160201030c0e131b170103030c14031c0f0b0a051003020403060f240e15040207150b030d030b010207 60
    0x100400a8952211000e01c012442100b054009000d01c0090092061940500d0103040c9807090404451590f809107041044c510104040e80e81c03c94003003440b0410780980424407100d4020962414800e076210300c04203400c021200e42201c1901c40b003031200880140010021044440b48100f0200e60910380090343d00c05c2510181d40510195a1194006160a40701c0c41d80c41c020340c0c040d642c0f8001c1040c030580502039010084074680141680086120806401000040e004402841030540b2400424080154268103103145422100c0c0310000300c1c0c03404da08510082194400e01441c44070514003808004140f001040c0c80940d10300c14940180c0c3c901c20000b018030320990640d400380d40c1c03100c2d0602005042c0401303500600301140b07a2014055100c0702816040117410841c0003102d61110074400c503507980e03001c02211000149181a0051340030402e000c00500304240c0320788209480c3c80002100a0940207151404240d80c1031103040c1403400c00035604a80c0c000030740000312460410b03c42500049150 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 867857005 1250 867855755 867855767
    0x60b030d0f0810080a030f110307152a0302070221030a111f023406050903071a1f060e060d0905150121030912031707050903071a040b0703 61
    0x300400560217000742890402d9844210340c0000c00d6290f071502003607154500c0c00c44d00c921817040028070005d855015248034100070380184070300d94140200011290075001c4140592984007504500003070b80007541300c08501d810010041e029140c2c3c100c04c440e00030305400c1c65a0701e01c41c8201c03010910100d0705090080300c200b0014601810f6122aa4058540d0456003034000703500100703440c075800848c10601041500b15100c80c04040c60102420000d15032198640300d0040c1809025a21140400c00c11900031500c281c00030310207003065100200040c03030190458401042c12104200c0085c080c940100301075030740964145008007007121a55038642d40d0000c0e00e002041800e000904d280110303036010305201130f0301c1c102a0480307580b550700f012143d151303250540074044050802030106480c44c0084c4540c0c0801200050124424148100940550000d0709a80ea80c00c441002c00600c0020b90411203081c113006000c01401c00686801207a094020001040c0c0524050105c1680d400700d03220040c144106 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 867858255 1250 867857005 867857009
    0x1060518090a0e030c0102070c0b03070f050d06052d120601050f0d0c0609150c080f030618100911070c051002100203070201020304021518010809031b0a060b030d0f0810 74
    0x10444e0b03a00c004e28102d05003c2c3d00505400d46500000032070000310103104400b01d034490455a07940c1c0c400040c400708203071002d800030f04601c8551940c90303d010405449070f241080380400c0041424010b41d00d9080c2c0d540c144c030310308000e8902030b03042c42403841c00c540030005441c0c0c1503c00c11200040489101070206004c505c00720000b0340700044252000403d9a04012007405680d10342901d8031500a000e02c0c240c818010b10040142142d40070405481c2022506010307540142c002411080c0c0460403850311f00c041502590191089940b5500400c003c0c1018810881e4444000040d04d003416210346070440142e025109560188200f50482e01c0c529200f4008100890b507031100031034817030800e0403000b4002d400840e01240600b11004a43c4040704580003034401c0d00710038007540c1c440030a00728011614420040e01c144c43c2d0f48003e128005c0140c0c0750080c00d00035240240b0080c0742611450605030240c82c940350320a4001d8100d5210305400e20340c0b0107074130f5500c2c003450305008040e0307114140c0c1004408260713 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 867859505 1250 867858255 867858281
    0x201140a0e0d1505011a070605070c0609061b1d060a020109050a05060f0105010302040e0712060503010e0a0b0c04050604061b021011071e060c1103012301060518090a 73
    0x2d1000d003010040007219250031a111040200804d81e220412011481001d5103060048041408010002125a0001070784144c462400700446101581c3d040c003511541c440c100c0351039440e0801c1c01000070031230800207641082c624212111040c0c58010a140610301c003115405420300140424200b030003500005581c5501030b040310040c0c1003030700300240c880e081510400101c5504030000180d039882802500c05039a8400280b003481d8403480020750710241d6552141c4000c1d9124a07000405540c02e10540410381d02580151101030040d1030641d0340154000c03e912401c00013448284000e441d81c20a44050315450706022180c9500d0400321000f01e900280c00030360211045c000540700a600c000002a840790071422204460344403a078910000500300d5444911102010040040340c1c4034014003660030b400342c5440740000c1c0340e4102090a660300103036034030200703221440c075020b1000580407141d00504003440e0160030040503491100781c0000020a41e4455061038010030140c2941d40e00c058090208 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 867860755 1250 867859505 867859519
    0x30a180b0108010e0d050414010e03010c05090301050a112d030c0901030e0c220905011d071205060109050c0d0501030b1e090601091e050901021309090201140a0e 71
    0x34648910000c0090040c2d01c029403c0020030403c92070000b881000c0204d1503240d00303061608240c800048844280055030401c07001e110075044648082c81103103074101440c1da4155407603189130185800e442001d080030b4401c0e031401c00c2140a8007040700136582050101c2e803001c040710f003540040344801440e0f405055000c45001050021741c2016800908000c1001e89040c880889002d40031034440c0c541101032078120089110149250304c1e00101400e05806410300060301004945540707003120901c03009004d01c140c015003060024402040040010040313040c02c0c180e41102c079596961a0303031040c8900708079103844d000850320b160080d030241c80400034688410415503940c1e00700110345c0d020648030682c0600030038a135007188180d8044800e11510b00c401c002c014a034604800c1d4801010b03c0d601c100100700c540c2104240034100e6002d214020a0007000142c1c0340c407094054540d0342c0849500442c1c007146042e854500503604a54400080301d6608001382e2214205076050710880e03013084e84241e104603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 867862005 1250 867860755 867860801
    0x80304350901030605040209220f0219021c3212040c2c09070302030a0804080607030b010c1b09091a07020307031e020a0b04050105040302010e06010614030a 69
    0x300e50000390044880981c0c05000003950744092100f20301c21103400e540c111003558251428582042c0e5042d40ca20400c00c3d000400c482041d422030101c1e089515003010440c82d0811440c12254104550141d0078012605211340d14170b98840035050381480c041e095007039600b15184544807803e03880072003450000d044c0f0003a5544020300030111180011502150780c440700031008280401c1043d007814580d4464030f04980d04005901111403d020000d10303050003803040c4a800300050310148511300a061044500c207454909000030503091040040029041500d08400079900380e80c00031740c0300456500700c401454854031440c0c83c050711840e507800c485101401c01c4030880800c816a02c04e440c0001000c1c40c45405916a40e4049807a40700b10302c006400100c0c003d42c80301071811082010103820344280101d940070500c96552900358503003207170283c410307955030400c000c08c0c0754080c0145070116241c003025000d0303034bc1400700182000d200b400b1020b95941c0701000217202d41d00d1950005144856456200c070000c0c0d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 867863255 1250 867862005 867862103
    0x3c060f0c021f020601150207031b03060615030b01030c2127051b060406051602030703081c0c0f110114131401061202040b01021c020d0e01020307080304 67
    0x142e00c61000051080d403000017070b40b6801b0b03a0035469494407640a070050314070b90b45441e0a40000011000d0a20f090020000009244c40c400d800c000e014119000440400144019044840c0003503100d05050410318445111648040d08a441840118140401c000c00c024500c0041c0541c940c044040c82291802e012450704078466176800a1041c01120303002c2501c0001000e0380c81070040142d40020040c0018000180514040d100d040c0d440114030718080c0740740d00024034120740c580c01a200c10f1400507400c401420404410036a54031090f0051080010500d0020413100e00001140d0070440803840c107100100c1c00390030100030a07a1041c1450042c0c00d18210701090355090390000c82e52164a10b2200c074109006006020031141040c0544400a040e030302844007038182030900e01d04501071002d018115540c0000e03540c81021240d0f0080180399640280035219482c480c1c0300c541035520038040c11000034640350807a40e006034403204990f05013110070f40c045020746508111180c0300c0f1000151000e09 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 867864505 1250 867863255 867863299
    0x120605210d2a05010e0f062a03010605070203120a050a091d0f070c0f0b090d0206070c02010c060f051302100507020d12210212060405090d0c0512043c060f0c02 70
    0x1680350b051a0300d2448001c2d803840f2318042d01314801c403560b100c814001046528050070103040f4160020b41030741c40c0000913540240c540e5000607580c401099011554142d096032100b0181d0140603582610002824000c0918a213036100800c190b010b002c104000415441c03150488403c1a0303481800405414034620300611902401c031a0501d2134403c2455030740c5010300c0054850301030521601c4041242c0e0f96a00110340c00b09036074030291005a00d03001144e0400c0c0040c0301c2c3c82c4c0b25126510082009005070702c100030a0040114503d010400240000c50243e5142810140407a070711400a42d007440e501002580c401400801ca82c000c0041903c4001c9418050f40084c040034514444254407940d0b0581000221001520803180170f0f4840c44002002c1401006074101450054086811110310b100c0c00500b10741c03040c2c0058901d5410802c1c66562401251181c5c0107002220200100c101030605889080c4081c500c208410171141c200f1441045000301007401980b600603050006a00b03490007c1903032 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 867865755 1250 867864505 867864511
    0x6020c010c0206180a030f1211030c0d061a0438130501091203051b030408010b011209030e0d0c0e0c0403140d0906120605210d2a05010e0f06 62
    0x40031551102c41144c0702e004100c1810499254035002c442c03402d00b0300e041703421428144103280c2c0556035418500c0341d04106070203140701351009201c0079a00d110785079007071080e41c14940c400522641070404070301c040103205003500c1c1612907040c448850340f640990050380708a4801001c42076400e010300c1441030311800038000c1030042c090701c01140c15035641d13000444010440344a8880042c4d1b0b0f40c0084c0000900c100018180c0c81943c50030010394a0f000d07820b1a055030f0140c0c1c0404d5490795100c1007840d540d604180e0007076401844030002c01542c40982c402406103d241a00c49100300c200c0f1102d441008141400c40024004800c9207210a1078240090696a8070070b020584505081500c1d6111202c400240c6030401c0f00c40f6a580d08010f450070a055584110b41803d07103013a1521a60007142d00e07100c8100304503501d80d00404504880d500d030a0058101128801c0640411011401020081341080000c0308a20710305680c0f0704008846003052030040c21455a52026805104078042031044e00007071440c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 867867005 1250 867865755 867865771
    0x30615030c150905091314030306040c0905060f07020112240e040314030604090209100f08030708160807020409050c0405010b071a0405030f0c06151503060d06020c010c0206 76
    0x108003900c500301d609101e1044844180043c006100902c0182000280385800000c0c48020844100d265910010b1048401168600a90001c020840300b8036140c080c01903052400e0529450181c00c01c00498180d1213248480ea003680360001d940000c40e4450300840c0443c02500703000b0013410b05d403406408103c8242e00c1000030101d03810100491100c40d8280085d001c0e560585800c40007084d003c4080703c0340d4100605140e40603545a000001580f580d107900d512400340890038003100c0e81007003100d00e00070b10590400a010381c000d100c4940006e0750380c8103c170f0603114409a07d040c001a58036140d205032007a80030080d08982882c1b200401c100d4002800050240201c03010f10085c0e8965100010030300482c2c2001d4050012820501126008441201d41040c05002680e24122020388800220740c040031060150354846c000300019400308005481c009082261203000c2d20010b0340d5180801c0c003002d882d040c850165100d00c0010095942d048403a10f8000744000c6c4103682c0e841d000692a0f40303080714a50 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 867868255 1250 867867005 867867023
    0x170307120b10021506032d0106121a0901060b04060c03022503060911030d020a0303050603030a2c131e020702061911031201080d02062203050403061503 67
    0x181e128039280401c2d00300c1808036401410342400f00410302500c000041d00c2c031500341c081c041c071214240342d949038140d00355114000742006015854801d6407c50300c40b9170140010304400700500000520580000d4103801030251004459100d014401d0b00414940e405940c850f8800140080c4e081d030801007010b2202e0181e0240d44240420111070640d0010b0b90081d2500c0f2026900240700042150b817144a83c14001c060342c0d140600702d500428075003102d8121010141e48040c0341030b410507030f241c01540d6110100303030095800c101c0304c01d9001c0d1058003800200c0b400c107200083e0082e00209421900714041c0c90040c02803084654240c8004005d09010b24a440ca42880000e00404c2c42c1c90340c021221000d0b4003800b254900031080d070070820340e540c610400c442040b51941c070100d0700c09802c2001c1c0050204980d45810765500d410103240c608514140000c0540d0007040c200100b024105000e95015100d003100c0406a059900d02100d65102d10342006100a10b401d5407ea80d81c440818954140e0f44141000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 867869505 1250 867868255 867868271
    0x501060509010f1d07200309060301061806020c1809150a0509010b040501121712010305151f030b060109030b0f4f02310216020d17030712 61
    0x22100321882105c4100101e980c500c1d240c40108000c400c032103030b10f41808003541c2c203244814000540300c1e4003c0e80a00c002030012a443c07540d05e022b240341c600042215000030010404003c010410b042050718002e0b03081e844001c0018200501031003011a440c0311914440598603120f028800240000c4d00c080481e503107807000042240c102441018161007181350b01c44041c1c002c6985501102e0310544070042014014400c030080366007000c100c1d6010f144244040c1080d024116010314021100500c030006030750384040d2083e0611400400b40c0c00344c0b40c100c0c0c810050395456500607142101e80f075000400940d4a0000c0140e04103e031030711240141c2100c55000100080218150303504082c694981d128881004e04a0fa41080f018002c02c50b54400d035004125000c8454000030104070354010300d4550f1074800f12110320802d010b402c1305c65041d5005d100842c103040e00e0340402d20f484e401c1100000d00528210031840c0c14400e111407054007440204004907981d1510140080102c184081014806403c0501c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 867870755 1250 867869505 867869549
    0x30f030807080618010b07050c1201061806030b04020f040b060a11070605030603070608090a200906011103040b070f080c070f2913030506070e0a0e01060203160501060509010f 77
    0x482e14403d850490041301c40c0c1d0801c02e00c21790590045100b141d207840b91421255198554296036500495003400001d02c0c0e9240607240201c0d00c1c05c01000444040c5055004e0000071043d000f41e542181d01030320220302c00d2041d000454010038030302101c00d920000c00b00e6004c0040c1e5004100c110444004010340d071507107964280070b0b55170b4001600d5055041d0480c000c20b000080c4940c0c1ca483d0b00c04403140454a03558190b49488040c400d003e007503002804c5e07003440a4052424a034029a401000030b00e00a10342c4c2c0040e212040d10703030089007d811801c001c001000360a02503120510b401b81038100800a55a1a403003128030b0391141c10780f20320440714108000005144e51500484000301e0042c40301c0410030b00d800304030504d80758072200120554030480d44000c00802e0f000c0160b01d1099000d62160b01009100b00200719801c41550b1080c00b48005900040c0101d580c04070a49450504540c0801d140e04024548070f40034003a590059034200181100025091a4402c503000445801034101c400302c180440c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 867872005 1250 867870755 867870769
    0x30c0914241309020702150c010b0d061b02070302031902150414031002090f041e0e030c010e0307050d030519050702011d0109022404030b0a1505061c15030f0308070806 74
    0x50702a41c1f0803441869084005c00d5440207016610410000050b425405400071b5101350002d9002e4610581e142c07580c0c410342406003400014100d6030300050484a1039580020342d130702c45410b20b58043da101000564110b4951481c5c844a80d03500b052601c0e103554550301d00c0035415038141451486807084c03500d41030040c02c4510072201c000d1009044185112000320500002d484081080600d401c4505014486007400344503013181b40f5440c801541c2d07140e608460843c01d46004c2c821451250b01304102c104000391001843d1001910a81400309140d9550030007100c0c0240c040002c9101e950900d001c0040169065010b5440e00c0309110840354490b210300609806c0743e0302c20b14022740154560307a03110116801c910000710b00f820441c1101d03141a807640d44516041500380e41c4139001580729a03035800c40c0c401c0c181c40c1c00050101544c00504002c083c031030022581d0144810030004e80d503941442d04464114107444400707545c02403035007174002095180c02003004000b00c1d00c00c400659250041425031821007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 867873255 1250 867872005 867872017
    0x4020f090a050108040f02150d02070b041101170415020405150d110403021309021c03320f030411090405100605040b0102120f04080a0b07030c030c091424130902 71
    0xc006c6004600c2c41d03401c2c0a0140802d00040c00000380900c136808070203107580014184544100f100030102c0c10315107440369050024000e210b040c4080c02c1d1403505060003081480d980030f41c01104444041100241440c001d208a0f00040c1d04204074001468040000400030003441d141c280e81080f03e081000c03807002203070046000003903000d4030003041c00880b942c0a401c680d0005000401c070900398410706205200001c1251412004070f0203069003200700b59101442d604124000c0c020b00b0b514054603040c1c00c000c0c1d104125441c1100c40d000310118003404202d0000c0c03c0c60020180c091310440c209401c0c0590f4801030f1013510141d00d070034000e000c10701e07041030f0040025003001070f00109038010b5014241502034121507420b0104000c117200015003100708012411419005000000361414103840003400e9680444050b0103040c20011600c0070b69070b01510040c12901c405101c0c01c20120440000fa82841c083e07d079010344041c110002c107041172000700040c0840800b04101c059069540c4254905a005013 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 867874505 1250 867873255 867873263
    0x80a02070906120b0916140a0509060306070815060a0306050907110d0309080c0303100611030405100c03120c11010c030608060604020708040306020708071101022d070504020f090a05010804 83
    0xe0184140081c2c0a4014245c0098034041583e013440282c2c0e06840d407966140e0f000d070b5048004074401c05604d0802d144100301501c02903412001910381f10000c41c0e540c4a010b8003100400074401e00058803c1026500000c82080080003e581d0f41c1918030010060049406010b01c64241c201c0070502c0103015405807410812000040c0c2036020f81d01c14181d00074440302d14242d805000c100400d43c280301081c03004510078401600c802c04072506000c802007400f541c0c1d03107044906520801c0248045c0d941c049403403030b0581c501c0c0351800302da0390130f80350440b80100c546010f4081c803414400c1c500c00d0a0380201c1a520100b02d100c0081240c101c0c5070000300d055865500c00c8888981010022646a04154000f00b4100d4000c0301e0039450306603660351300740880c0e06c600804d40303013640040750190801c03405650f10500d4039001d200520040c140d00300f0500345552400300340c50081c02c840384039061900b0180200001403e000340115242c010f0001c082c2e080754800c2d000b8922555548101064941c022802d42d4025900 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 867875755 1250 867874505 867874529
    0x402100f020a120c080f0309011808070611090910050f180606030402120f010203040c0e07052704110301241202090a1511010f02040617060418080a02070906 69
    0x90703511414506240d0341d11450800641da06241c021520910080420f1410301c1b205c1507a130310f0002040c900b10340a50020b94109491109410089855501941d00031904410005503c2d201102c40c20121311a00041540040010042003d00000311900714120382096801000d0440f50104006c0c800f1105051078031100740d100081aaa81400300c0a580d0241c80581100c4e000d81e4001011498154003901c03064003030790000704000c1042031000565004000030412925181001c00c8040c2a900820b0480100c24000761041c9154000f0080f5440c2c01d158040d0003040034012001c0d00d12416030090041860b00000c3c1c13a00c03c00101c034524001e0048400540d515600d81426004035030195001e140c100d43c0c090360074540031400f180410680c0440148a407542c5448014900c031040c2900c07001554800081e00c18442002a150440c140300d0b0181000300c48080d59075107400015006000f000c1c031460f000e4110314003c0342000202002817086288076000c0301e48660307407000841e0660b442da002d000080e040f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 867877005 1250 867875755 867875773
    0x41803122304050f03030c0c0f0706120c0c06020d0903031a09070c05100507030c180e01060e13020712110c031207060b101d03061b0702180703050402100f02 69
    0x50200c84040e003051148080d0380b48a140ca410141c5590007d40382c0100321900091950b40c512000c00c545004145144003501301c0c1e070703e03110014014201d600c0308082d050791100314480d40070744902d100ca0300c401e41c084402c42d00e40100e0b0b04640001e010b8040101d0120b07180180701c80384486041e554030440a002408103400b550758800465030310304002e000321000e10031041942d0b450450f42c01151711602072a540025000913508008080b1008200161104000001c06020741c12141d460035042d036100f824410244818030011902202e01c40d403483c00c0652001c0783c60030400c84800c800311a03130b450964502c400d05900c1c58000d6140d0407015001c40d0705600c0a688400c0a810f80c03405030003000c0c082c003000a00c0b0642c10010031204540d074081400090581c0c60b241c10b808020030000141c2c0e00056004000900c1e02c0c400500c41c042c249a4480c1c0c46120200d43c1e1011582c0301003400c03a4001c049801c40105040140014020300000e6034120720070003c601c00c0070710803441107000280752105a030040c200c8003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 867878255 1250 867877005 867877061
    0x3060f14061c0f0f050d0807031b03020f070c1e08150105010804020406050433060206060f0f0a031a010b0f120601140406120e0c030312070e04180312 66
    0x92080e46044031041c41c41c900d2040444e496200c0f000905000e003000d4088680d0004000305010030003403000f8245458003c04072150a00310154800244160500503529000c8100e030314941d014544008041c0152944003060401c40089504003c400d14002d29446a07240c049142d2508034124820b9140b0000702c0040000f98403c48281e6000346c00030700300180c0e15442d14049419950301ca400340f015042d0000132481c2c00040700c0c2040d0644070010100c811160b0074000001d4171401c000c0c1c0800d01c20000d507a601d0f540d980da00e884080c00c404000300302d104c1e466500d02d0b111051032096005040c48070400070000540c13803a414111002d0b403030401220303407a000112055040072a405481d050420141d01e4030810102841d8004102034110364035000500312287c9080c4080d14032615039902030703070403044c40010725450010613151054514102004142c1e00c41404445d078110451800307a019060445121036602840030080380d9501030340e0fa044001700300e00d0384030302600c094091850345626401001c010407 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 867879505 1250 867878255 867878299
    0x605031605060f0a0e30030a021f0f051f060f0e09040c050a14040e0c1c03020f0a03030209030c030109080306040f0b0d050303010618030c03140c0a03060f1406 70
    0x40c89182060780d00980c00d0000f141241000c0922062030020088207403504040e00304d006c0c41040001d400035864084d030028001c1d2160641003081c01c01e040910307001c01d280c000c3e41c0c0185601900c428000c2009140c845c84003050320005000c4100c031001c00a1010406078032403420441446166100c401c60070001c9014070035507460040003074810705c028801c007149036925060281c00038500310f0700350910325204504010403101142c001040c0d640c4624800c50031500c0b2002c42400d1140c5203816001e0440007802c041c0d0602c5840c55803d4100d000d010f4241d030070582c0641c040c008135a0140c0032034a4080001062500301d492000c8090440c0409000040c054035054201741c820291007100402c10031400300101d00f070002da00d20211403640000c40144880c1350b01c00581221040340340401d180c0c040c42c40c2c440341800d148034007010b44100c0d0b05200398101c540c4100012166044003400c6038000503030342d0415500500d81442004841e41c200b100700601d0220070b100301e6004410007001541200c0d40310025082d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 867880755 1250 867879505 867879517
    0x1606080103052a100207050120190f05010905060a0615020a150f0510030209060109141e031e0706020304050307090b01020a0b1906090e1009020609060d0605031605060f 74
    0x18462070038408080b1a104c00080e180900e40680003400d101e4200000500300390032881c4a62400714040c48515498140060010042c0032911820041c1d003441d0305008050400741c800280096003440082010002c001582d0351168642200411482e0b40380c1d004401c400388182d6032400140e204000c9940407526051400c100c0901100000a0000d0032031103200581e242250000c00b4288918810400d500b416940e1650004091810005090800d001c180e09440c44002a601070100400c0285005183c48881448054000c0465904401802c6480e4452040312800091802405c40c00030303205000000703075020b843c0010003603c0c0081c00c00b004200140740007c9050304509c501101c040100d00c200d0110b80c0a0110685810408508000350200340c50305603110680320342c0342400501c0b00000126400d1018207030720310086070740311840c000115103008507059594800c80001d05100001c6055200304221740b41039055a4100300030082001d00445d4a100b003070b8002c401040f2180c62f2449400007090 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 867882005 1250 867880755 867880813
    0x30c060b0d050a0b1f0608162a051f020a091a0706020c1207080c0f150f04062c011107080406050f0d02040e0703150f1811030405160608010305 63
    0x1c0c5c1030349003a040405075616400a80421a08818032031002800503089004482a0070404400f031140398078140c408424640170412015801c055204000007031008039082c035090703180c1000000e01140024001d600c8a50a103003c03501601c40021201003811a20304000111149030f4100b8525407500c0010390700101d107071001402400216090000301001800352a8042c14202d40c50303203c4101118500a504d055180146e030011508a00310104240016840001c2c095941025200ca05d84030b8058840b01c403c0500401c0b20000d10404255183d0580e00083c5181000f400800b400d812034038903074030404102038501c0408100901c4034078001d01c002c0034a00203c990880c43c081c080382c1d040c0100d81154204403180c51080041c02201703a45405010491640450505210761420355803007402c007502d00c5588035600c17050800318075501499105a810b00320f14101c084d9645001d103030441e1158007109405c2d03c00032941d82d000c10010f1083c1f00050590381c0c00801410031407080c070224000c002d20101104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 867883255 1250 867882005 867882031
    0xd020408010612050706030b030a12110604141002070b16020f06010b0d0c030506100f0201021e090a060f0215040212101e18120e0607030c060b0d050a0b 67
    0x4a41000b4480c0100a1090340780300203108101380703030281c200600c55200ca010141000e07428805540d0128001c0307036590b030000010000c94407400082e144074605002214450049008001c02d2004140c80b503101d02d407840094404528450800d47d00324018440c019001c2d008600000e81030961001903070104403290700480700003003d0300c1c03041441c00344242c000700b003081c1d00400e181c801074035240601891400d0508041c0a2440c000300480d15502d040c80c54081080000c0040c24640c9000790304485140c0550030804440c0f1058020003816980503a40c000d014010035a4009501c0c0d20903070801000541d1580986100c59040205418603000640b081e43c2c0445e00646040002001300844101d0001d112004610700344401d0811100c0408131010016190a00a90010b02e000c9042d100c544181e0080340d0512035019490101c0701c5e001c070b600d40c0d50f810000000c1d036182415000002078950030f00c00d60051080040314405d11501040b1000000d11982c000c00e000000a6050381c035483e842000002e1074 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 867884505 1250 867883255 867883259
    0x9090106050603070203070b0601031109190906030c030203070801020f0d0e0309040c0210060803030105030d390b010519090b0f0a061709010204080d11030f0d0b0f0904080f0d0204 79
    0x25042d5000703940030300c0542c1c4006000da0408c60360302140f540c0130307900f400d040040500b540d4502075035118110710540b0075803c00b1102004c69200c40c0b03c04001d4404d00d1820012151640b806070440e03051404181d101e84a90440051040d02c14021201005925541c00c0d00781540c8080380400341140300e0a4806500040c4810710f0161031b130b0b21070100c85031060b50003081c43c520810702c3d24044660f1034000b10b0040c0c200700011f2210b82c8001448040c00c1d0180d152001c034109400800d034440180c1c244100000d541c0d4018000d007500f082c07030300e012841d034010064580e95999503010080b8949400f0b8040c0d908982445041044040527448051b050314060303d40000300c03c041c00080e440c07900e260090808503030f1409a1140d0840800040c1e580014001c00031407400c5d09000344160b40703204941d0403004001045010141c1001c1c02d0060700d224036030039402d2a881e100300300182c9000e48141c80030180668450b040440c0070389030100500c1c0c015604001d01e14600811030355032232001d501080342586156020000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 867885755 1250 867884505 867884509
    0x1902010204090c0804060b0108071407020a03120323070c14100f06151b0b090a050106270b0d06050a0b1201020c19030207150903050312060424050909010605 69
    0xf69040000c207590302c3c90114540340c42c00004031b50007030070300c68104240c0804105685420210407440011210030b05500d48686100007101d05c0100c2d00002c144a244c402d29900b0150540c02409001001c0ca21001c10a010b8031b49444a000046410700c00250302030001d14007180300c0440803644011074405480c9004101860641a40e072141c0d023500030315546010030042c44078210690f2541202038a0200703038410040c4000c290051548002602030b40600003c41e0303551404001802085a210001b170000d2a5290010020700c1c103200d40008180d0101115000321015900c508a0b20180c01804180416483c0d11010000c01004000a1056a40300100d040551303c04006003401402c0200160b80c0300d8080c0300e07407403c10701c444100c5158508141718001c0004e0300860304205136142003a00941c980e80010381100c1c4240700d40c0c0060010b00000401005a40c03d100200b8401e1405840920000900c8013240e0b0151100d50004540051480018031240c5800d4801c039410584034000410195141c41c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 867887005 1250 867885755 867885761
    0x27150e091b010207050906060c0106030b0901020c01060f0501080a0b1c0f170f120a020708030106030b1008090d140906040b07060e070f05101701060c020103110906190201020409 78
    0x196800c15580300080040c201c08050340803900500080c406008924545000300b900010050034652003401d002c100d4540d490002d42c0401300443c0c208000440c181010710300f441c001d40c4410b8080034554280500031525140c148412f90845074103070b40380c804503904c01003504020301154071003a0303001c850344c8402c2c07070403024081070510414080c1b8250300804040b80381c00a85da08102c055601c40c048180140c0c819801030701c045d6600c4498405100c20b060352100e4000d0b000748114003000700b4a00b00440007140f43c0d90706030310007044d6030303816940c000c003d0340035000036288500e04648115055119494030b0700558821420075002d07048280c81c00d400c1c941240e0003d0032582040d00181d980742404281e120a0040c24050751400209081c0980403103400c00c50781c00c2040c1000d01415011b2100404d0200c0554407a10700000c01400d82d6000c14400c0d43c4900b801002d0203407003c401d0340040e0a1203002070300c100075602125400345001b0016442c2c180e907c1a0940b001c016035031210195582888006800c02b01d0380 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 867888255 1250 867887005 867887011
    0x5030a0e120406090e01030f150f110d0507031a041a060d0e120a0219081204200603220507090f05011701090506010501050d0204170d0927150e 63
    0x3100700b034885081c0301006141c45125841421410b800310010000300b03010121944895030800790541d1b07802c1003921810301031700c50503c0d103141c0e8914001c0041d40d20303103048000c0d294010300e11a003800b05407140700085098135070020306124841211540071000b41340580c0b0050b075a2a0030900700711a2140b0360009141c0b50071188641015617124440f400070400c00340036103180310f2280c0c084942000d0103541c0081d5200e000040c1c2c0c01d841c0c0d800385007486c103002e140f105a602c0054a01001c0c4958601480c10b003000d50307014081c1d10340b0b0020021002c00c0c1450004240d901ca40c00c20110b086441148110a050303000d44610181d0300f5000b001e40100e105071050081c1c030200075491001051551500c03d0305210b041c4041e000e010300342d1510aa400c0060000f0480342e04503402460502e85460722176203264001e20071a4070408040710716008004683d0408107401070300c040c01e40c4440005c2c9507166020200580001c4580f403400052705021408000c50b5807110340b544000f018010507080d15880c203450544419 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 867889505 1250 867888255 867888283
    0x20a02090c04030506061c03180915154d07030201020c10080f0a0213030605011a09010807050c010f090503070219050f1c06020a05070510060608040305030a0e 70
    0x42c14414000100f000a4026800351140d180c001000c41c0311664000c61904002d0401910042d1002031101151241000d000003100c10000300504c2c40c298401500346c2d10448114001160100c12214010070a08440311080b10101c440034030742c45030300144901440c009881c502c0310400c00c10f9070700b556100d160300305141c820010716aa90660001900c0d06501c1d0000506c200a469800000319500503a10340d0411030403601c11426448207902807010703014207402210494904900081840001e4200c141250303001e486500100790500441d941910901ca012030200301d000d8040b0b510144200010700c003240d1610000660100358000741710a58038085030942c0c880d4000b081078025440c2132504034000d10316104c0c6045002e480c00000c6801c84a200c50401d20501c24031207003010b40b20400514404282d8842c4085580d200348000181c090b420102d02560948180307912001130003004e10481040d03800c00e80f03c240c080e035141c0d40d0488666100500d00710f40151070710f1303441c5000701080009082c0c82c640 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 867890755 1250 867889505 867889507
    0x708070b091e0307031b0c08030a032408030a1209060603060204090b090702061306020712080414210c0309030601170c0d020a09020c030c030406030606170f0a050601020a02090c 78
    0x108100600414140102d40307040e0b0820400039002070703040418642c070039511100c03030180c0340c03000e080410501000b940464101d010005604070155815404641c80d074250b5113080d100020710512141100362540143c1e11542d0013080000c4149015007681e041c201c091810106101000d40d45030400da808940c0100e404540202d004d11001085000ea4002e00e4000d403041c0c0b120340741c683c000954038031018044000c80311038400c2000500440b501264100c6400c099101c002520fa402c004001c00ca0855081d1a0307203942e444801c00c25440402c034000d000a045140c214800001d244c1c0c844260b002d044559481e01c01040720000316107051040d41c2c021302c01042c0d40e2020a02c4607010a04000110413183c1c400e1040624010059170b41c0c6400300c1c00d60708405c3d40140c503000a40891482c40c441d8180012003844041000501070f076054006400340e41490b99610150b84c610340b003c4078209001d5500c1c1d00d28484404c0010b0001311660300240c0d215605204031090f940c4250003003102d000040d9860740181c18 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 867892005 1250 867890755 867890773
    0x1430030a03290a060807032301050907050c03040b09120607030c03060503030405010203030c0a03060f0e0103052a0d0303150b092b1b0e0f070e0109050f01050708070b09 74
    0x1112520030030403030101900601c1c0b03121a000024009025030081c402030100d480003146815110f46d01c82010303440c480c040400d002d145460f004d9a0309900b40b00b00c501c150002d1000400c0d8038411020b452416102170010b40c04c0ca410000c405410388c10041035660450f920114100c101003040140a00421140d1000104061000001810f44006030041402544100410040c44c1da000003240c0d0b10410a281d01d5485e005207510480141c0115845545500d1807030340042182d0744c107020b40790b040713034403038021a6080c07005c00d400746295225412000b48007803054003070910703981441d001200640381f1a00e000194015610800d0261504640081040d07030000f09034102e141c20502d0740d04402d45001883d40d84418543c0c203008a0400020400030840b40e006101c00f01d05034510b100b448041c20502602e0169494100c0b010f8443c0c00003201c200e00000c10800842d01c095000b481000195000a011408a2078464005403401c0c1d2141c6d034215044201004924042201c0c8000310f0302071040c28010b001010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 867893255 1250 867892005 867892031
    0x1202030a1a0319111302270d020f131b0323041718040603060b180702070524030405010204030c0f0b030f07020a050a0c0f1430030a03 59
    0x21200c045032a000303603c14058956007000481480b020303180d20070b10a2400203c1500460040c10041842c2c04240d0300105030803200640041e801902030702540c0001509442d00c8080204159071210042cad040742445030b100003e420800324a56801e00041400b26036903412141c0182d8101c000480940002e56910303041508455000ba03d5a06003904602e01d4058181501c42222000d60090052000c420018442d006198810390b68403e006005004001266803814540d001d00ba03a0282c051040e000400c205482501d41d20001e4014906940203082260601c801c0c040c007400d846202a40c4100718020508480c43c1c074200951246208200260300c0c0c1d0302d1850304001c00f0f03129070420500800780b264182b24013148607055aa2001d8805034010f8285c0f80d800e01130b4100899070300090308038010310f102c4005000c180c005250440f031900242d0601142d48500b00310700341000070a416031020001e03205000680d203050503d0300d0000c0b0703513034001c80f10390703d1041c19403959101501c0c040c003180d20307003a44203004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 867894505 1250 867893255 867893291
    0x1505061503040c050402090a090501090c0824150d090c031703090a1b4103060a020a0e09090a05060105010807021005150a12020a08030f07030e011202030a 68
    0x2081400205419410b0aa54421003400207014440c0201e5011881400c180d5610804100618a44d001008075584030a821009407510002100118540401207000494803030410b0004500c40040d82210800c40c10801440380390300c0c50300b840c07007040038402d80e08070803414410b81d091a880f0f10001c8140740c0ca1460300a10200d41040300030426101402001603000c030106105038203a511010202c02c0d8101c8100202c42e40405420000643c15010104070401162068021305200610010070300a00e0f081d010051168009030b5058058000d100400c00c20040c03a00501000040ba042c11b1801442d42408100f881c0d004980d054100c0e40604000e00501c002070104602501003860000c05512342008003135076425070884031a10340c0e65100005510380c54038603199607848000a02401721169901d0300340c00d0715644030806a01c1002c030750500003400340c40002103a40c1a616600524200b58040c5c40c00e071840e511014455045c8990356100b1418480c10f0300c002c52080541c85c10002e1b007003040003044868 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 867895755 1250 867894505 867894529
    0x70e0a0b16140616050319050708041112100e01062403360314160b01120209060618090a05040318030305031602010f0903170a060b0a050c0109150506 66
    0x24540044041c08281220207136003103901c0304182000e9580303494002c244107410341070721190140146010b00380011141d02c41c8005020714042c1d08a070b440c1c10106410047c040e1190b0b804031400e82c0c40780d6a490034000042d000710317640f500590000100703d179403006400395003966050044001450b2500301c1031010307018428519001140344904002d0300b803101d006007801d0072040082200800500500c401c241c0328200d0140c0f150008400907480e8007000544980e103401c44542101e202040340e00104020801d800900345c5030741c0007405a8115100e0805000140d840b02e0b903140d51300105103002150540350210303001e002d10132840000600c0d280505000344500400e02c0710000100f10180d080001c02d500200780d94000b800e090f48030744440c500c5c450990040510150400c0040d0405100364189501300d505500d88003001e441541541d9207411300c0408680b40ea00584900c01e90501812107103034810405010b85c503034004000124108e594507803c0203000c0aa114030311281e168402c000c01030420a800b401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 867897005 1250 867895755 867895793
    0x3031d01060803040e0a020903070308130803090f0d02060c07120c351e161e0902090109030b1305010c020102091305041e05030c010c09030b070e0a0b16 67
    0x100c60800302c4494072446140300c0d0504c1c0702017400c04248000140d504540d01000000c0440d2409607503441c0c4152180c0014205201c035409040700024031140c08402c45911400040007000001e0720b18080000b40d90704240e050b03030000024850804c98a0003048004041d000c9075080320b15003003141c07030011070844154000c10003060a03148640141c01c50808030344560014100708032101c4416940140c6000f0081c5c00302d00107096103c0080711a5440401d100085010300075040224a498409204001c60301002c150280350b220441041010700d96030140030800d4051408244143d906e8480d1500100140d41400084007a000c5003400c11401340b1401841502d40e0000b5410100d07424009424400804415030207252140005410002452848080e44804c2180980d51070700d83c0c00c0003a41ca0300078200d2100350390302c1d2207500d10342c43c1d008459090440398480c4000a66640309801161041c3c140006542c0100c02d0101c080348586501025001e100185c2d00020302a1000341004210f001022079004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 867898255 1250 867897005 867897011
    0x71704060509190602030307030b03010e0724020c06030c0d152c100e040503040e071206080a02311d0c120d081509100302181005040e0c09010303031d01 67
    0x9102c5e000700642c0d44c0815a0308000810409500c0400d02420048807070302c3c104c1c0142100840c0301c4020344c84681a908003801c02c2188000041c600781d07034403511002d41a034411014400604009003c03401441c214100940109404041104c4042811230b00d40000b0301c40d01005000da04408070b03000420700b5818000518001314108907004c001400b016004581c0d0b034800c4c0c800005d05003d01001242c00506100c4030b80e4480c0d00d0800d1000300381c1000310400b2065039040c035100003003c4130005503181081d60028680200132a4284120168061a45070f9042d031000c40d0713042c0d04030303e4a9803003030014a60414070350000d84401d1060050070710200c00d503c13602c10009011502055040050070603210310385030a240c0255141d100c1c6c14543d00b40044002c84c3c1c40441c0d00100300c0341c0c1a06000030800c0324825501c86803000100d0704401000d24049850a480c0010b00608111030300c0c09400155201b031020041d030303c00020000c003180c0040c000341c2040c0c022a0301c5501403004820300700b41c81c0b0f4a0000e0f000c020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 867899505 1250 867898255 867898259
    0x4210509041b0e190b13290a20070f26070504050c0d050c0d180317130c260325021305091c0201020903060c07170406050919 55
    0x3801010b52680c426005100e21400f1818610355501164041e0440c4403807607440c0c400d21000c00c0c0200e43e060081d1441c0e00c2401d07210031411a4161f42c400e0717480b0b1802109900304004103004881c42c80044440c0e000305e03180640c6402c2e108800740660809008944044c00c03409003840c103619140581e582a80c0b0920030744604078101001c3c04103110065810488000c00c86486003081c280c1c540c000c2c0d402c0000c100307280209022400001d00b000f48428407036024184009400650608040b01e0300001c042d02040344955012030f8850b624405030b5102d0007080444049081e20307201c0c010f18021a400007070858490f181071000c000c0b0180b45500c0146000002036180406c21800402418603003812007044e0403000303d0703100031950703103c559200c89882e901d01080075141024049684800d00c1e40d00d103003074144855041c0360003803060003210720744240034004107801d80342c005145105512402c4180c64840745182ca01c0e8030004141c00504c0105582da0310303552035000d03031410044541c0c803c0d00c160751807000314402 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 867900755 1250 867899505 867899507
    0x1b0305071e05071b0803040f140a050d0b101d040203060c031e061302070305131e03020609040209030d1e0305041208041a0703140a050103020a03080304210509041b 72
    0x11a51503036070003006a0580c02c4642d206819030341131317604104158000880c012900701103d040b480203c070403030502c02034105541c00521180e04201d01980e42c02c0026280c420000c1a800e880c5150401d00307501d401c4440c541c0d90740446c101d0300d51408001c248840108144000d524040281030341154402c4052803540c20824400710841c00100c1c83d141da41e0f40120300207125540e60401321990300310007040c00e554030841440c00510700c0c3e003c24100c0c510480c6095002c120801034501900c0e515440c04c1007099103d0458081100a4120300e046a5200d42c00f08030701440da031402d01104100c0340d030507110164501e111441d06601e42e61012802020103180400f003202182d40040180d26612903400c0424682d19207040030210000d280e0420381d04120f07101d00340b28460341e0542c072559035501c10f4400c541c0a91a6000181c051721001e1101940c07003800c140e800c1c03000c64402801190440c0c4078884410480d000b8a541d60082c0f00c010001c00301140001c1056011820540611000d0b03040491410300d20100e0000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 867902005 1250 867900755 867900757
    0x1614101125171e0a0b040c061706060d0f02040317040302120a020f0f131103070e04020403050d0e01091503050103121b14030c010203090a1a010b0301090504061b0305071e05 76
    0x143d1511202800d00f00c02c4020301400710004680d00071205084c949000d091041000c1094410320300081d60181b0442e0119110a01e11401081d0040415142080100c1c81c0d1014120740240c82d002142d00300000000140a8040702e0310904644211503155891401040022410bd110f04080c43d048400928010303500c14031852828242110304181d451001000724030841029403501d1185407030204041c140c2d08907880507502c01c42466680c80300303030300d40c1d10184010b80c0203600c4000c3c031a6200340b0207101454050700c02000050300c1032410051640d52071140c034014580c0c00c403180d008680e4601c01070051200c5644650601d407440d04024002d07203110b03154801058018507000d48042d00d0009a5034803000203004403008001c00d01c001350740380d08002101a0300c40740c44000480d2000650300314800c001c509400001e040b54542d8030034608503803030080000e018120091040712a155200a4401e0500c0016481d5403948082e960000d002c2c604000003a1001019240801101703144280d440000c82d8420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 867903255 1250 867902005 867902023
    0x70c0204020706020405120709060f05090a0b04091509020f040b060d1a180f01060810121106070302031c020310061107081e161410112517 61
    0x1503001a036480042c10600024007850f00035541c03040c405030b902000c1690010f000010380da55000108115590342c21492200d59007842010b8000004000040c48644268800b2001010190011610303c40300e0751004c1c40b40841112064900380e44180c1c070015814421003800194070141c40c2000507440d0f050001d940d90245003000c408080c0c5820340c1060b03581031034414000c001409000710b9500d00e080240e458110400b15070342082c0d44a244000286c00c0c1c0305000440c09403091030f94010146042c100c0320310000e02081c1c0140c4501c0c002e89600d5007991104002030109038020b5020b95201c58420012400c0350858550305400580144140302981d005070b0b4482c07003158074501f8105000105007103c541014101c0e40001c0c500e0258004103030941103c1c1c0446004102280700303039050210b00c00d040326141040340c040c41741900c00005d803040d41d41c1424503450781c80c00c034a030504140a03201c82080034905942e980c4044444240c445181000c00394103040580540001510201c80c4d600007103030036540304466 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 867904505 1250 867903255 867903259
    0x3150e0702010b060c1b090402060a08040503131716030302120a14070c060f02030a0f050f0d1b090803072d0c06020303040b0a1803110c0a03150e0303070c02 69
    0x510200c0c0800e4000d40c0310301c444440150246407140342e8002c480307841d0307a81c5419120301841d03028104a41d03450980b420b94491039005103054106070a01c10708903409a0000d20841f0350b8032040111000340030100c0346560062000c81d1180c207100b10380c04c1e851303424a102c500b003943c03080c3c804c001c0502c0042d4004c20080d220006e6582c0341030725515051401c9442d04000c802c000030181c0c001906070103211b4601c3c0d401054a4040c0c48010f95608440d10891b9644a11041540011a000c2c6c0300402648260010020b005e503460700382c0d04040381c00714207408480403880031482018070000c01c03084d840e402c102c400b00100030610165040190130b440d0310441a020005141d40c059030030b0781030b020090620019440540c1c001e0464a840c54440d03001079540d41c4141d6050f2403686462000a492a44a010700340b0b45d0b0522a05181e00d406107580e055545200b0782650245502601e00d850403203032a10700c80c0308010b5010343d8802c2004501a05840c084035801141c100007500304000304260b103500a82036030006541 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 867905755 1250 867904505 867904529
    0xe04051209010c0606080a060c080c0a050a050f1201083307110a110a05151b010e0d0c1415131e060e0d0203091806030a0209010303090602010c0315 65
    0x807440103e41d82485040000d004034642140811081000030f654040584100c1040000e103200c407800342d80300502141c80141e0840c007002426006071003000a448001d80604265050504148040c42d003904580001802005030b00010845c05030b0400c13440488021911007010340d85c40b0b40300703401c452500c0d21564482c0070040402140e50340340700d20001c2c080c5d503c0c8002035413500840341c5060441c554881600b58401c01502202244515104071403201e40c01250010314078080340b203501100e2443c420404c20001c0d56883c1814098050240300b5520303004816030b5001c07010845841d00d406c01c1002540041d015a000740040080690070101e05078200e400c60f10342c0741c03100000345068121b008400c480c480c0811500c1300d411040000f6a00101e02c2902860183d505802c001003040f40e4a00031886510303405035512070752070380c40c2888190b00d1350072040203020b442e20101141c0112300b60100c203a1017200040d08000041180907428032a021300711200380303800c0c041c407024a05c8105910956000d46400640 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 867907005 1250 867905755 867905767
    0x405010e10030b1515030106020d1e0c020d1509031e0801030201050c012007050f0c0a090b0a21020a06080405100c030e0f0c1503061c050a0b090d03060e040512 70
    0xa130304444281c02d42002402d14200a90341240442190400c2c0b0030340d005031146600b6038440703030301a0482d0b0036015000d5040601c038070001042180c00b0030140e0741c10b80e0040d1952180501090441e41c40055403420440c000c80c005c0294500206007402c036000d4442c01a2541d4040c02c41258070001240c11241c091805a44034203100400358014140107086140c0c2001d40010303e82c2003008c6001900000340180103454040c01200b15080d1a01503940403075502c2841107209010341420b0707a1002000c0c07800a4150301502c0d403113000c0c6690740340c40d0b101003290b00440d9016440843c90480b0106003d4002c9261002070740c18030ba07030f8443d41d6501d40c180f0319040e5a02d69034400c404900c694060320209800030111041c105145421a8a4288039810b69010b4a000302c198821181107000312401000e000d002d005501c0ca40d0754002094070b90b00c4c03d0840b05070081101d21404540f400304d405004e10000c0018050421120201900316050742e404040d24603d070a08010124030042074469100d80d1220300665914 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 867908255 1250 867907005 867907021
    0x5090a1202011103041e1d0f130f0b0f180c0405060f041d1c02100c020c09071106010e0f041203110a020106030c05190b09041116020405010e10030b 65
    0x43c4901040e6001407001250000b000404612109002e81c4412241c0c66a540c9507500d002c55820080d162010300004580481c40108640d842d1603400402d901000501001a0382c400041d0f25001c5800e41c4d15403e03000034058482440d000382500118900311304040b0003071400c5069103e5141c0d04143d44182d655000041c042e03101e0300100b414401006004008810003622041801001ea07044d054180c407c50581108031402016241e2542a1940050100e060240314000107854052001401c500400c1c14030350b030300d4817142440741c0680703501d4455031040e000040300f083c94013405a01c1840300c071400d0740512008030903540c0040d4110346c20080c44071820721501c0e0305078044d00c0e0800040070410000204c01182035819400402034920038020207450079650420400745441c21041303503111641340e90007040b030208604010a107104000d04049003240500b600c1c00c90640081114801c04400903004c0802c62905201d060f0140c4241002156241808030b0030005e03209050000810b030700c0600002c1100030b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 867909505 1250 867908255 867908267
    0xe1203150a090e010b1207030f021807080103110a050120121801030506040501060f050c1510030308070f05030604150801110a140a0507060c0e0d0803060f0105090a120201 75
    0x1844094040307610356903502c0c1c000c8000c04251500035255481c20665030564a400400d062220381c4c100018500181140c40d0314011941444080340e0109109080c1c0090001c13450245101d43d20a8548042a41c034505140b14854103030300e41c0c14858000b030301007807100d0380e044820205958ec10320640480b1101ea032003003a24000114035009040701d0003040b5050f17210b03000a4003645010080e0780070320443d00da8a040c042541c400780107080c0864503070002001c4041c80340000e0000c00400300e0407034100d00340c14094100b41032801d64044001149440083c000e150301b01c00c07030580004640c030b45820496500c8400a20500024006074425500c4842034a03d2480c12100d60b805803035808020000840c070010080015030009010300d0200c2c15200c0d00d402c1c4c0f0704600d415104461015110203250414075038030400185005504d18091108609400c1c0198031b403074207000347e00b910800d103495903414a6410400c1160300c0c0d05580381005030030010020726807110340c01c1e8022101c0742c212103124000c0902c0169070b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 867910755 1250 867909505 867909541
    0x2090d06020927010510020304030605091e03160303020d02091c0203060112121b0510060e010906050a0306020f0405060d0501030b06090402030303040f051e0c090a0e1203 75
    0x2010194004110034004141d0040401032001c503040d0a0626401c91100403284030341c00c0103c81090f0000040103941446000c0780000c00c02c03441074a00d426241d94a0a048072425a403469141e170001c007404a00c88408008030b808070507a8230007181400340d00304007144100441c041c010201034011800030285140da4059504503000108610444030717139180c440702c030301c000813406a201c2c0c4507030400011903081080014020355082070485564030b488603000d44400f80d00304009410801c07040b2018000c02c0c41800441b4a1840e084c2001c50394a1501c04407405030f501c185c200c1b11425117090400c20030759880811000480e50f2052016032101c49402910030180100d0780051b800c0712000031450314400c07450740094181c910484056480e80c9811050100301001180c009406501c03c00c040740c0454049244640080e126038216034080311410b90200d8184c5180d00c0c3c1448540c4118050403041c540100f2041d07201000c0c000800090030113040041e910900b00742078500e0b588001000c100b146c030050350b000d0380d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 867912005 1250 867910755 867910759
    0xa020f120d0e04061e140d06050103080d1a01021020190206091203150a0b1b06180a08030709080d091e15050c01090209010e0405191707060209 63
    0x5544072256000d011500002040740c070861401101154900c0c4103c0200109800070001d410b1260500e185102030700c81822000368040ca00602180001e00e00b402020301a40c0324007074140d00c0316043c1501e1401d0703030b0540e042440742d520860440e580503640040e50840701000c4460100b00c2c0724407030748042030a03a461812860b45c41d000140340c10061b00340c4811408100016806c4441c1c550750100486e03101d1b0981d02621a00b00800c01c04174081202c194003000705a40001c0a0062a503034642c400b0602e0ba00802030700800300d4a00720814042036090004941c400d885c10410400ca10906100383d480340c0e9103c400400801c40030000c2000f240c85400c042c80504260030489081c100308510207007070180d03180b09980d146000c0c08102c424100c000d400c200704031070341400300e00303070100198000303070307a43c0e04408030840903503684101c00300c0540c0e07030040c7c520300818440102081c1405c080c1050760410b111040342032084404d030070000b00065030003a014045005001001070701c2d034000341b600d03601920520b00000d03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 867913255 1250 867912005 867912013
    0x1e0c0905010b090a0b1801121503030e1203030402060d02070f150f0c050918072604140613030e0d08071b05040603030e0607140303160206060103020403050a020f12 72
    0x200b0840c40050080114010032a510948140d89140001d0036214168860100c503141201000b000d5000301ca0b86030408a442c0004075030340401301460030501003a6403083d4009801f035801c600d1141440301117040040340940146d451031030943c001c038081c0d104449001203083c2e070014078082408a50381d2080c0c0d6403544800b680b5501580806a03801030b1059600303001201e881c0c19100d02c50a0300610494005100242c080066862103088515044400900b0310050000807502d060440e01d5480301c00120305120344034140c29081034207140e004110241c54000d0160321110510084500005a1030b002c258940303070200c101c0c0c005601181016407503643c01003a100003c2200c404014040090f90160401c0c8070140980c00d655000304004d441461002401003201c00743c081105003010401000024000c1215001d00034810f441d980ca15442100c40f910301001d04070603c090745605000054000b0424641076044c50b0441e150a07890741025600244280301da00c0c440304146c0c9420500018400c03244040e1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 867914505 1250 867913255 867913259
    0x60f18010b0309071202090a150504060b1207050412120e040504030302030703050606130306020c0309060a080a0c090e070e040f050108012f03130309050a06050403110d1e0c090501 79
    0x221050760003c0c1c03409070f070324016090085940846a17108610f40c1d41c005100300d009803102d4107080300401c0c00b024901c1c0140b000680118458407507001c2c5000500130540003955410845034070704d048103c090514400c106003000b04115648075804c9205e42c807600141c0164400e50440b8054415103072b0140c025030864101003c2100303050b0150b000d1841882c0544091205030784400400c005803040c4504000300003200d62050002c51314a6001d4401e1241d40c208481c5003008040c00216640c103d0314520340040c1d4000c0810031724030041c1c02540210070303c9003020514641030003617140041000400b100f04201502e41303e0800e80e07031160040f01d510312508901b00941c0d6120350390b040c00380a2980190031741e008440740c0604441d510901d440a094020182641951281c499103107501d4500d40f419020000743e81800714050703860501322002080d1f0303500c441c0c0c0e44614614211068110b61070a45100342c1e41445e8060100d5000300d1414119000382c00055202803080c0742031450342c4080c0d00b08841d940d140c4000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 867915755 1250 867914505 867914519
    0x6130e010f030b070e10030b150c060106120203040827090c0a090626040320010b101b0b060d0816060b0a060f05070c082a06070b060f1801 61
    0x1440c140d80c040d1403803110301d60b81e1035416202c107244e040096811124040704030941d940707c0e52203125146401080038102142d4400100e2054120600c09291a0007a800400886811281002e480c00d90004103505507d0726480f100068000c24031045021b80500d4a074890141c5c0000b20032085c880020507920003810a07000c45003280d0070030410070001c01c96000001c203005000c5c0184525850b000c401d1150f1103001ca240f00011540c000d0422000e00c00b0303c1c03120103040210760300030b000c13504410710002400222410402400c0283c521081c024000201389110144100903a41507096030002e0b685642501c0d81004200d46810301140501481000710320003000c00c4170049400b49040c000c600912101c0d40c101c0812500510b5072040c080400c1554100d80c15541c0500c000c0e119030350040c21000707903188e51070f00c0300d42c181145111660400302c90f4606100900708850300110a603203040d105e11341405070390b0341d814980b06005014144545042c4e4034120041d92110748030030400f846140315020300c1d69036040e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 867917005 1250 867915755 867915779
    0x729090907020a020411090a031103030714010c0f0905061210080102040b0d060603020301080a0b0712090605071e12020c07090924020306090402040515041109090114090606130e01 79
    0x3c201d11903420070240071040b510110642e00c1c1400020040c2d074001785107990760702075119984000c40c0c01d804140172580214048500c00340d8950301150000c5288024000000c00f54020040d00d01d0a100d4480001d10094545070140c4d0b200940c00c0c0510400e07a19040d1480e01072111a91094000758000100492421401c1c4080d003040703090040d082c00f180c0c1e01c03888103400f03a001c00d002d5801547d106400d40300218942040041d040903031070601e00203000d54891700505888800c0c2080d00d0441d10358092000217980180380380c03d0a045080012000c001c1214001c1c510035682114600098002c198006400d4062201d0302c004c044414040081d845640b038406042c2c455401c0c2c24640c0c482008020a1080c040c0c001c482c46603c0051551426a0300e0b03501b0800209000707040020760360384c0100107041c0c81d1911b105260030180031420581e22407201908000d01000140c01c010b12881c01642d004003142c03156010035402000c00c450b07560b02e03071050182982c1c15200b030340d01c00c10101314400c00000d80031000c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 867918255 1250 867917005 867917023
    0xc05030319090f1202131e1a040504022815020f120705070603050c07060c0207051306030203151b0f1e0723030717090a08072909090702 60
    0x18803903402c025525800501c12407103d101e146130ba07401002031600146007007184504d011000d13500c0010034403d01074002c8424681c41141c003041945d904018505040511511080d01030304880034040b41c0b419902145000c40b40490805030303107900c20311044910701d40c04541800b410450369408500d030000340e8000e40c0d40b60103c4500c43d6030b01030b0b0895510003007144011520010380000081005070b150200483c02480001d05c0301c011311800780070080014a02d400358402d80b444079070007400454145401c11a03c0d001201114a0319407411100b040141c0700400c0d42d20710040134088010b40b90341c0f0b207285003140d0303118075000f46012000025005960b10440000d480743e41ca60080907030100c04270b80e1492282e0b125801026000710440301c1030418035400c0c40948440e070a00c1000f581e040980698070341d03034480c1c80c0d4403410410940101c3d80c660340d410422011401000d07540000c011203450003c4611180d000020a0001034102c440c59240000610044900705100a4089a0b26291400c0000d440780104 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 867919505 1250 867918255 867918257
    0x1e120506130207230715140f0c0105041203150504111207090305060705040e13020a080f030714030f04121a010e160503070905010302090409020301050f100602280c05030319 76
    0x10301800400c4e0700103801c1080d40c40031a0031a00ba1114210280c1d00362408141101c091201040044024039050740513001d556035600000c50541094079010a07500f16055111081515000c1c1d4028843c3d049001041150b00a541c0004c4a42c0c00b41a240710754450022448000c00701c072000c0c8020740390311071050000c6a00401c00d54002d62600003040740c892040d40710b00c5041c0c01e01c00c4007061402080c0d0100c54001c51004140072655507030303911942d09082c24070460030140d03040402e1103024010300310034007024854031301c01a52803e401c40c0030200b550300a40c0503402020071840c0c00a8204007510307225a1182c090008022200d40c6e40d403041640041c000c0b00c0c0400e400380c1c40e0000b0100e0f24021403d6a00070301084d02c8080440e41411300460080d004441443d52040d00d4410712800368070203204580c003910f0490500c1805280950350741815040715401503007198032080400c0400e500361001c1c600d842030b401400e0000b12585080c030820413199a00401da16010000e180360300c031100140080c60081103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 867920755 1250 867919505 867919553
    0x6050112140d0507020118182910081909140114040321060b0307020d1d010e46080708060f190203070c02011e120506130207 55
    0x16a001c0700d80382e040020400011070803d10880c0d0066000f41c2d1030b6100a54143d21000c04035031b4941c00315015a410040500d11103644034018020a00c1480c004009100e1104590100c0069100400c1e01c6015000003c400c2112140208645444070b07031680302845070444040c0a41d400078140a0344d207081450095803290310381805d81c403002395800c07002c510458054072080c0e41d202444140d452601380b40070300b80e0702050ba00e200c08a460300c101e10142d0b000750f070658000c00c03003001254006030101c08201044290407840c5000388045070b031301046c3c80c0c9500e0f60903155441082c00200711007a070111254011110051450b60f0040c40c68403141c40505400118003040c0121555186966103c221602a2000c2504518005160003000d4846150444408000640000e000d14110812a007058a440c00042e00541c0010155a4484810b44900441400b80c010714000c0c0c55014010f01c00006031004e1280c0c45a000644543d1030505854099000060943d81c9413801d2800c442280c0d0030b11881000441 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 867922005 1250 867920755 867920783
    0x120b010305060a09053c0907150e01120c020a060f09030c1103070f140123090d110a0b07021e031b2106150f06040b0c01060306050112 59
    0x8401c1c0116401104090700503003030350b0f04282600b0082d2100510044403000600000740c4900c1d880e41c001c103200c1411250f07940d51110b80e88012808920003400110307150b885450144000074005a08101002003401c10f0284002101e005a900c0c51038000c0b2412075514052a500620b81c0110f01502968031801080015501e1151004104e805003000503000943d58590030000991a60200c2840b003c01002c4401c85a5180c00d0070710840b00a0304052410240ca0041c0e0040e0758000403886444211110084c5642e001d03514030301c4050180422251290141c040084144074421150140f010b2014100003442ca07201d102001550b800382008034011580c03403d808144c0d0840c61b4007540350000050140204a07080801ca010503034021415640c080c0154448018040041500601c40c2c002c48024000c140750000c108044c00d0b1060304114000d000d644246250b96030740b80d00300e809507000f0340151500e030109048141d00400e00c40e0002440c003881c120021902d1031101c451085060300c039a0030074200d01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 867923255 1250 867922005 867922007
    0x2809031e03020a051204020607020306090a030f050414130f05010b1b0f030a1404180f051b040b13090504050c10020102040b070f02060c1f2a080601180303120b01 71
    0x482103c02e40e50004509000c4150704000c10032034582c1003800180070b1420010a0f0700003908205040c2c441581c0796110031800030415400043c0c2000170321050800f18209031622420000c590181e01c4254404c043c510040c440c60314003a4082c0a00d50081081001150386401e03040d4044d9200c04007030983c0f0391898043d40d18203680011f89503060034500f0040d5091165101082d41d80c21140c01050380c603854280404100c1c0c400c0710100741c850340f20b07100002c05c041500410080c102c4401505619002d40340444105111549000312403c559401092541c0c3d20348035406070413200e00b44e411106100d4141810300051000006080e407824008980b000320011003058107074201d02c12889040d5440700c0078001000410007903210350030642d001810284c50400200082c50611510f803126a01c14290020070b00a401224828808046810500c07071402d20010749200a80d000300ca004041004040301c00101c269104003a00d849400303d501050344087e403245405440c901484000102503460320302d00400365 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 867924505 1250 867923255 867923257
    0x20105010512070b0a0e030f0f0601060e040b0a03022215050a0e01060e100e280603061202060d18060509060f01061d0109050d0501060807080111032809031e0302 71
    0x242c4c0c062181d0b41c503007403200340161001c00d90b002d40c007903060044814144440b8002d01c120b81c40541c0540c0a01425030602e00013030a80c81c8182c503244d0080b40392180c940c189884002c2200241d070b404030342c4030821245102001806103000c2c107082580e0750501090304034501119044500707503a81143c0d10861036031240826801070b0000d03c207271000900c0b003130041c001c0c17401d21486e0702100469070300c0d041940700030b8900415214840c4288851069545540d1680c000350300f2400840070341294941440b50700d2505050301e1740c01651000181c41003100003101032401c0c18503401000442d43e1a401018002a241403040c010300003203c290311540541c500203001c04258601540c183d80341d94881030402c6a00f4102c022074594142c035003505002c0d001c040071410f0340e242082a1207052107130300089081c5042c006442e0406d8a00c2e404041d45078106030804c08200b031000152644500c525070400e03525030780070091075011540c84412440721490b045180062507807161f2105c850000040000300c1005440e5411070807 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 867925755 1250 867924505 867924509
    0x1e150c02010e06010e041506061d0306060d170d050903030f0106090609060c1115090f04020906070b100b07030906031b2a060c02030717030603060402120a060c02010501051207 77
    0x240f900540d00501c1100e010480f1113400c01c0c0121000d100c44001180440c088031441d41020010525a05564008040045020461040540203040141421004650140c0d46510002d140d00d500e101000008112403003070b03941e80081031005200c2400c00e00c9042c2c1c0ca0785e00c2514008202001d40340046011401681c02900b1030342183c3c0c441071514545442100c0840084804841c104012190740403207660304d1030030300c40003103900c8443c0382d66640700c5040000840c00026043d0140e4010f000c1c4007140da03103c10507a03c416802004a0245650366125025035a0043d00110180da802060b45400d050380445c001d03056441d075803020480240c0e2001c030b111000080341380690000f0020410b209081c0403010010140d451b545003511007405030390f074540064580c44025600142d00100f080410b10031b40001d03a1601c008110b00340d611318200000800e4540100400c085c0c001c4150b2541811920420000e44010542102c020000302e41c020300000e020304020301c0b6081c0b260b02022800c140720314000c906042 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 867927005 1250 867925755 867925781
    0xf03060f04030909060f0b0c030c0a0b1602011e2304110f0f10050901031d240106020304031e081c0c030218040b19030501020d051005010c0b041e150c0201 68
    0xc580d900d00410203029a000203a0308d002c902060084002800d0208005100d1512a0342c440354240b51034015008a209a8240501160b0400303000324401056015002c24500b41c0c1d00740440c5145420708014101c4180381100c10005102004000510a0304a0001e10400040300c0755854044a081001070f01c0720707041042903110210141101000c3d001b0380c01000c45400605010030060010081040d080c005000d0b0504580c01442800868080060155502031107109402c1959410494005d64134080c901004090b1341048550840600c484400e100c0029400780340070341e4403007000041904001989a14100d840e08085186042c24024025628040e0243c14070f0202810341c0350801003c4d10b103c03440144c01c035680c4520220f003d5084070080020718050307130015950b4020b0170304490440d1002000180441c1d140b030001d10141e030f403204001c920540c03c02c02644c0315446604024030160f61040161341b9856001c030955041200c071030044142c40d00114000c0000017984c140030707800c1c0e40c0b0750302c80c0300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 867928255 1250 867927005 867927029
    0x403030f0c02100342060906021c120e010b09090c0f060906091008010e0c040b0a080613020a0e0108010e1005131415270112020f03060f0403090906 65
    0x3841846640f100c1594040702c40326a00900d40b868844101c9484220054000000c1740b00074491050b079000d00b000100741030301e020000103207806802510f8580440d400074200c91885031481c041407080001940c140b4504d40200910701d40c980205000701f42035002540070324200320004004c0b05010801c4201c200000e8890038031070404a0801c451680700c03400036a40043c040c0016a510f4603102000d99007030741d0382c0c0c807003010342e5045c1030200c12141ea000b86010001201004144000c01ea0602a180060480e040072140340e15500000340c1e02c40003100b08510f0480c40802e20080c41c81d0720010b0070241d01000c0e01e070003c180e40c8130b100d25180c3c0141262240c0d101011918204a07500b008441d102100c007034132030002100b003c0c3c01c05171801110169005600d08940c101c0c402600d01d4004086121126014440c503100c42021010480ca124140b2a0b0780150784041c00344030542d200c180d420001c445000741594500e240c0190703281a409002d0381c00b580060a40200031905824034418001500e89501c0c02c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 867929505 1250 867928255 867928279
    0x724020c0603070509030307080a0e2e0c21031d0102040f0605091c0605040b090f0a02091b0c010c020f281518030f050a08181e030403030f0c02 63
    0x4d407030b182d02091015416220400c003680c0801c990710702805130407400d655044e40202c1c00c0810000382024a85146042442d10004c0440112100d02c03071002c142d64a06200c4140196401c05030b11000007412410054038589000012041e0701d5804100c0c5082401c0720003030700c03203109500d0500301c1c081da00440068241c0ca100030300900d4025805080b029900030030b4007800b142c95005006112190a1040300d04035200c3c4284010844214041680220b17072100500181480c01035055850340c603007501078028a0b1610110741c00c0b03c5101c244e00c6004550301c06103595079580300d0625008003070401d07140740140241051b11031840d00200d0070540f0701c43c402c15054664800d03441d01c4040b40000100840c0c0c480140e03151034903c641303030307009005162222040c040b0100c01c090038082c01040d0b05901c10010040c0401500d81c1c0150041540d64100c411030303024030308444c3d540c00340e507144c010414165070031544441f96194500800100a000760b900c40e40e074011400c69480c8040c0c591186c0d444000b948204c0041034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 867930755 1250 867929505 867929507
    0x105130b010909060213090e0d0c11090a0e030c060610050c0d050f071e030f030e0d0c0206220f0801060b0a0804030c0803070504211a0709080724020c060307 69
    0x840042c140c0540343c0140341c012a00d0000051011b40c1d4840038020b5103400d9983d0100a051000c1a001c04550506008165042d582c5c0000300840c201d60030300c5003941c0400b00b0218035040c2c0c05105950700c01c1c8101c84e07581d59903289080e40c41c1e07001ca078180d00c202240c080504200e84140c0648413268111002840c0e0581c6208080c1ca107904001001c10401030b0510101c008960342941040c4091400d2903608a01c480320b040062501c40142445c0052508109a0000710300c2e0010702d244854013545050580c43ca11840010303410b1059501108880c403070242c80400e5582d100700c4000031110042400341c41e50799100380341801e0700c801d8030442400b60014094500c0060160a0590f40984245418007550798950740c3d400807504255034000000b0000301d028003112541d015802510003000600c4214820782e65030742880281d00c0c1c420145910401400b00722003600075043d00002e4140c910903070f03250342d449040c000c010500c0c60369200880f5098080780380e98940049440b00c0ea0820252036145941c0c0e805034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 867932005 1250 867930755 867930761
    0x360302033403050a030f0501051e0609090406020301050307060f050316020f0604080a1b050a060b150c101805151306150501020d18030209040c03060e01050403020105130b0109 77
    0x10707490201424900410210303007400c0e004610001e10a80f242c94841103c2080202101d400c407010100172468800140712954541a801d412042c0061403850b1404480740401c5060003201c840076000900701d814041040b00c0c03900518141e031800e0f0100c0c0c3c4074a0b6600021240400014038000c049181003021400722524481040030480443c01114981000f00558515000b0201c80c10340d561200446c10001c01c0c0e40c09600c1450842801e007022440c1c0b0070a442d00d0703885082d4190001c0a081c2d6409503050107480d00e02e20b402d040d42e104001140c5604120700082d48a94080d4603107103019250030000705154003001030070600943c0000041c0b14104044a00703151054010342038070400e45084410380009003150041d00c11808000d5070f55542146000c00181c90310040020700000d001c18480410180c004480702c040c00c40340c0440310801540c41d82e08101c080c81d00b0a4101806441c107190b0881d851741015004035009610035030081190390303110003a900403084240c600030189507100c001089901640d0b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 867933255 1250 867932005 867932047
    0xe04020603060a030f0f020f101e0c020607060507030f140711010b040213031421070305041208072d06021b010c08040c1a0403030f09080136030203 65
    0x541043d86954803501d690441141c0610101c030041510b010500850400400b944445007040d5180c00c1180741c0c007000540075074049903020420181c04540308000c20300c110500c1d80f20348d4020300725a41e02c000c03600b00200a840700311000400309080051000486d0383c148141c048500007078403600165201d181d07084a01e83c00300082502659218400380c946a6507510051149491240c00700003140d1541c90210501103510144001a801022544d40d60301604007914641846074100c00d942c6110514003a0f856001c1d54019034040304038110200c0c2005400070050107034501440c0070001c0580c409221014010740003c1c05070310942c5c12900040003a501340c01902c003608a2203007400d140c2c0303440c40c0ba0340c2c00c481100c5a10301c002418642030000b030004402402000d840000c0d0000d00100d00240d81718060320407880f0060400044000103c4074500c288080009442c0e03c80085c0100c3c0714003a030b8442488088940703049803500410f1038650360400b03a0001c2001c15403540155041a110201a9800405603 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 867934505 1250 867933255 867933259
    0x2d0c05041a1309051302030606030d0503061c0b07030c020c0301090213091502030c22050f010c0f0b100512030c0a02040e07082413030c020405102414040e0402060306 73
    0x12460104039080e1500629100d8013405c0446032110711180109071030002c01425031402a00190f0310559195401000c0700d074840e409581489000303042040c07a04a40034500e101400b02c0c0490310502052503407581018603020a55801c9918071154482050300b266800e1a00960021170252400d06c0c00d8080d811001449000e107000c6000708000c03e9442e0180e03401110300e0007a0140010380104034420350708030800d002d184d011607098018140030125007429031505100e4140041d80d0030b4039042142c07503541c140005521059280403814404001d070040444d0740a21480354090408a60881400100350345a00c1820402444155119001d10008000780080202d0f1801120b60100c2c1000041000019000300ca2940c03071265000c03030840358001d4001400303803410000500112000300303a2000c09041031940440b00041d654585102004d2400c13040d81c0010001100000d0f4131515511001081d810080c00740c5900c00304100304203105071117110304d00404c1d501176464030129003d81442e0028540c46940 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 867935755 1250 867934505 867934537
    0x1090603180c0e07030c08010f210609050105040201110a05120f2709131a0619060810140907050c03070c03060519060605160203012d0c05041a 63
    0x50320b48441e1180310b50450350b40341e4140400d0000c8158188500864483c541c58803070f00d2941003507183c4044403c9803044035444807040003d86a00700d90001e544002c1076010804008034511840c150340a030004940617408101e41d006400c0c4046000704104400e641d200d03010308900c824038000c88d5072503001104842c81c0d00000f4401c924450030308103c0460031130402901c604440c20400100020020300511403003940b02284401c03400031700d4100c08a00004000b6802c0c050591341d44001c10210001554038034035440070f270742d00000c0360303608000028003070500c009046060300c1c0ca40d507100c0020581c0c01703c0181c0280040d400245001d100d00c0140032201e1074481601c0c6804c40c1501c0d030520000d1181c0007542c0c2c865542c3e06100492030381d43d440d64510562010b0902080e89040405081400381441e00c03804c0482c800042002c5540c29405402c03805980018110310b16078621522203029004003040603518034002c1c803101d0090060003940c00701d4005000c020f5048641d49031044054102440074a81502 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 867937005 1250 867935755 867935801
    0x7030b13140f0c01050f040501050702040b1314090613030503071103031503010c140a030e0a0807080c071403070b0706021911010c050304020f060703050f0a1706090601090603 77
    0xa450301c6030300d580c04001d00040001d1031007529160704044680c02d107107040c4807040203801c003050301150555040f90b501b401c20545451603800840c001d000100c01440e8081c400450340c42c001ca04581c4a035904c1c0c2e900200600c90f0717a44c0c105038940d43e00815201e1000081c8140d0300b21000030b124400555201e50740780b400d500980c200c41c1406246401c1030320007050351501841c400c3d103a07007024410b158450704580380c800c60500c47d041662105104410820013010f8a4004000b2000c01c20801440a40d07440540d0b10354807402811b0a56480c0c00085080616004113440018540c400030190030403854014040d0583c10314240184590703501401c03003120416002d21130313010154104216000284429211980412242072072182101c2180240b20300340034052042c80f000d6103404280b40c0c3c0d05402941c00383d41c0c4a0031400e050320303903004807210709080b0340300098100c0d03803540e000c280c0412070b80542c40080090b446d607100300314400e2003c07520140020400801000482e1090b0051400b41ca0303416500e50f0003030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 867938255 1250 867937005 867937013
    0x918100b073815122a0301090503030115081e0619031208070908032a07030b1009060e070203070b0709050a03240501081b13020c010509010e0f07030b13 67
    0x2d0001c84103404101c951004000c0c841c20000d60001e04d131101c840c0544918185840b4807484110350981c0c041020203007a0480c110394409501c1022403a800038100c2e503c0390b03529522560b0401c1030220120000e000b200c080741030a078a00008003e402c83c040c0d07420001c0e0b44c3e10030030300026010715050144030800e03024000001c99503d81d1007000003810399451070884c0c0744c9818060009107a40c1e100c02c0141c0c0c01002110940681045601c010500640e400c00d007403070b02250f6903840c0001740e0700003400c407220010920007900e00150010b81203442c800820301c050b5554601c144040c031822070305d140c05071b0402c10100c0009268040b070aa408075070303803e05261250b01d2304040344004000b600101e0700c107079160f070108422900c500221050181b4460083c4034544c101a031441d01e4412000000000c1200c00c0c0c140e8a00b5519a40307030a55080c0b40500854852003442c071294040c003010394941140e075180c4000410140c40102c1c84070700c4005a1002031000e01c0c034503039800b841381d44010000d40014a402c54168009 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 867939505 1250 867938255 867938363
    0x40e01092307050a05120403020c01030e06060a12020a0801020c070825050906190902071509240204091a0906030a171c140402030d260601050918100b07 67
    0x87e07406580104202e00d030341d9001400f02d4801d200001c41907030207001003029994a4400040035a410403402c415005d00c44e2002c01d030080c6d000c0d00024010750000c01d03001180503001880804940000081b11482c0c5000e200b00110340f800f444480d00c005148c20b40038000d82c2025a11542c101901900c0005010f02c00d81215840e02c0443d00800c000e0b94002501d00c0500218418039440c560040b001007003064015034404d40c0f22101020300c0400010904243c1102c0101c0350306480060108810070300c074040c10095800c46240349111414490020000861800e00303000401d10100c50f880300c02d00301e030000403582c00d1b040c941000001c00500c0c44604d05100d034641c401e004094400c04d00501801c8142001d01c101400c010542c466681007000e850f03000003682159039088a030702c0f02e00656081c0282c5459004803000e100c1e8403102508403440c91142d28400c040000c40c64411040001203121003919046030342218400d034280a8914001d4142c2d403d802158500c0b034502c54001086102403240704601150f020f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 867940755 1250 867939505 867939511
    0x702060904112205030705010e2103040303090b0306030607211503050c0913080a0c051c020f0d090509280c17090d1d0402040e01092307050a0512 64
    0x80c03200204030312410710415a503200f2400038401103055200d0410380800c0e40c0341b04501c9180e040240c090548404c680302d40802d8026071521600f03c0000e4100c10041ca950780e8024402240041c0100200145815046080c1e030301551009000d070816456642d4226403a04070060f080e52801c00d5000ca41280c008a07100f04148004601c0207204010301d542001d40c10080d1989a0500406155041060f48280c002121075510b41c00601380ea201c5c100044110b50205050800605512404d0924101c080a0104054100009a003110010b00c1c0c0405400d072584c1d01400400301040080009200902e09200780c1d682c82485400c05040e460070302c3c0d800212403400004884101a0388002d1084030b10f40c0140910360400703d0012034410307410800c0285a0760701c82d1800b400d0070420706030344c0d142c00680321048000d07001d00018415926031351a102041c0740603100f84a207801c0b80d0700e00840d010b0000070750080801e1101d011030341e40001c1d59841e0b401390f5050f41f01c7c0b0300c8002000401c20207086407152604030140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 867942005 1250 867940755 867940781
    0x51306030f060902070203030406110705120303061009050a0b1803190c122a050907030c2607050a02010633080105130c0201150e1902030c03010b0702060904 69
    0x28420380d1801d106001c64201d500702505143c0108072400158074004201c9003100c0051502001c0446000c00c0c0c2e90900309260407041d8000c503400384a0170f190000102550003003408461001d100c5e084040203460303491492150540180c640c85007005002c096101411111040c012208030041c070302c900103405c0c4821141d8403241c1d5101e0690540c14008480c0c035403005000700c01d014a40d107180545410754400e0101c50440b4044c640c09081d04043c00c44d5203850b0000300000340c000f9240b8101000c018020b8205021010f00007120340d4015140428405241c51051008060000301521107503c108c405903c182d1101041d9034984500141144000094a440b01298550030f11140000c0112498180c004030300c8804100ca8030b00140280c2d909c00324420015a9040300020710300c020910305030701400c54082380480d0804040c40018182c07011440041c45040300400030415581140c003d50103d0200390f4400c070f8482d0041c0014003081c14000700504103e070005080c0c0e070524441398001400e595212100d42 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 867943255 1250 867942005 867942011
    0x5060714190506011719030c060c05092403070e120f030304060f1a010827010c02120f0703030902150a0306140a030201170c1303050715090509060d0305130603 70
    0x52040c10f1100ca4054100448100b4640003001c065950301c0481c0c0090000c4940300301c060804040c041e02e01195200c0e0311071820702041072407520180c03068025448003402910b05140c108509001c40c00c3c01140410f11050190860b15010b000b1182a80c0400645801200110030300c10111000c0100707a03000c1c00000011540c070f00c0c1130b1600b5025181090082d0b00000d040ca01c190005000f0340c00f10362a520400e190044055651115004030300e072101640b5100d041082d01c2e581842c032410340090500d04c865801311540c10900d062505010300c101c0b251418482000d1000400081c800d0300498061800201071440c0000600001c44181d07021746074900109075542c030208030341090fa0024140102040310080407280c139640020340000d10030701c440042c442683c00060400c540781401c3d02c1c98140c0c46001190b0107603d0b490000ea840115014480141d4160210032428a200300524810360304041d081c1c41998403624144403014241d040c04038140304040c0f01d103100b012120b14945c0c3c01050242c0c0c000c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 867944505 1250 867943255 867943303
    0x50f2d12060a0c0e030a1202010605041104090c0c02010507060b040f0c0804050d02060c070605060301110c150a0605100e040b03032109120a080405100f020706180c05060714 76
    0x514100c1e030f2220410307402d0003828480300807aa580410410025a0880d034a442c1d4081c104004034010512500302c241c1c05440c21284c603c00400b041d020b072040d580000c104002c00c1038142d000b81e03140108403600070b001981c01c10400d07001548940003982100b0b0060004030b580b507802031000c0203542c0b11054500008400c1802c01c010f0207410040441b00907010700151000b070602e039907449118462000003500301a151000b05546847c01d5008a400400c03208403c0e4403081c3c144c0841e901c0d12501106e0b4040c1b0030031100451110000c42c030a8100325003004041c07406021111600b590607600d000f80d111351242da2500781c0c4000b602d0600007401d50501d40b216001d02c00c81800c565450601016160032070710f512640314080860940000c0701d0410a003400c0c441010b80c0c0e2440c240e0b01d01711003220908000c500304103d03d1070740300880d000380c004148180400c2c05800d0014050f81c401d011005d10103006911050801c02071400e00358020041140504016404a1030302c072496498655560000054003040c0d520f4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 867945755 1250 867944505 867944521
    0x31e040e04140606040504020609100207050a09050f0121030806041404080309012a081f0b1209010209031b04020c150103061103160f120e16050f2d1206 67
    0xc4944d0041c01141c040000d420075401040540c054162800c6c0207104410780d05101c107008020060080c0b20040000700c100e922190144c014003015a10803602c6d855010020940400c0c42c2802c106403205880401805860354408807008180039100310f403c55680e460307007000001d440d802588190b0068030402d5aa00b040c62641d8210f525000da005102d07110859801000840c0e00300a441d04440d07032420441303544036041c0d15040b40c0a08070a80c2c098201041d0700003070350094803002d440c09080007200100f403555409205400d0b44100b18503d981500b0144100c02d400c0e94410032038003a03010150005051014900780c00340740404418a400120320441c3c010400c0241900a4154a03005c0034201c070b0440c06c0411a2442501f80044098203001510918480c001d210f480040e15003040740e14180500102c4280304d60b01c0e550500407003185215100d00c040f5150900d6010300011540c05000d2100610b013100c90000d4902c180120860203030180124110030b507a07448840129066000080d0500e030420b981 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 867947005 1250 867945755 867945763
    0xf061902250f021201020a090504020706060513050411100f031e0903020303150409120305041104061205151504020c0307050f0d0e040606171e010605090112060503031e040e0414 78
    0x9050000b46c1c01000f16011956006913810101c600591b005a00e425a52803ca40905a0f60300030503004500302c030600e905100d040c0c00080c0540c0c01507001c02c0380030141030b0600c004414003140780b601056072003000008640c480e90195180300b980000781d06400884014920030b40c0e03420041078005074000310500003a01103c03070015000300c400311002c204040003a039070040c601e0006030350f9000f03040c1d5a40020301408100c040301c12203070400400801c00c0a490340ca440105815002050751580700d03c0b01c004031132819200015004103481b60120701d0400d00f80003000041e51040401c0f2a0a000500c419070000f0b400304803240f654980c50015042c08000028001c2018040b120003038032071414031008001c4680c03c030300d0300f54481c140209805035603510412508036807030140b2403141003581240c00026402d0351050140c450014241d03504260380c6000842c0d02c00780e90f030f28011682e040c1c004205c0c04814103184404005d11580e0004150b00b02036445a0240e01c118041b03a044d150030440120185e07184074140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 867948255 1250 867947005 867947029
    0xf080105090108120d060f03150f050c1b03040305030a0314071704030309020d0203060408091005030f070e031c0207060905040e0a11060f1b0f061902250f02 69
    0x40c0c0c1486040d854100565031341c1080d94011420202d0001d8089138401d059048103000e0030710002e00224030f560341c0ca8002a90318030041400e03c19031400c4150750300010756000d404d015032078840740c05c0e09083c40e42042d4a040c04840302c0075125484100070000000d04140041c00c01911240c8001a12200f01c09280040405c000e099400704501e2a0030a94030160b108010f5030071a4061030b000078060040e2011952560030b0708c00c0030358584140000c000c1004490002482050000e40b20712032040c6444109071441d00040d00c00d5400020391000151000740304a1900c0c060f81002030071510101515005600c18941c50701079040142c100000604c2025003040c2e40c10000c2c0700c251020007241d5907500016403601c1c0d03005802400b0810305a03803e00107a0b90f40382a5402c2d10f0403001c00560b6041d84408401182c207203a0a0314502d4000e04e100c8003100000810306900c86d00892800301e83d00b40c03045440f00000d600841c141445e051212000454455581588a18a6115020851a00103a80104002d001d695 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 867949505 1250 867948255 867948259
    0x906060a050d17090103021b0105060319050606060a0314040606140925020c0301060609090509061006050904060f081e0609030403150f2a03020a0509010c030207150f080105 76
    0x3074040b8000042c0c01c40040b1003540240000f00380c4440311200124083e01c070340d031040c07610645040c5d00101b00300c0d010340c01107000350000c8040f51500810a0106503c00d94a10700281203034009030f000400c2814010014042200d891500044070402c603100503451101c151419203003d17584203014401c624a00070001001802161444207a21b002009080031701410141c201400c0288d181c4d08229a0082000c070b09840401402480003e0706c944004149084501c1032403400d50600300407d45510300450000c1c01127040c10048401c06041000a448650044c2c0c1940e030040e503241c2d0001080003122910344081c003098400f5160003904203440d0001041c828000d030000b03402a40070301410003800000c903411260703c00c2d82c103185074030200d007490018406a0061801e40341450042c0b6210301c3c01c1412511a611990101424059000f0b000ca00701d016440a090105504004010b00d640c05001002c107810721a104481405454020141080c038400609002040b040031810210381c0d0090b01c0c0314007410003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 867950755 1250 867949505 867949519
    0x40b16030e0f0913030905090a0c0306050406030f0b0c1c020c060f2a07150606090f03030e120f0114071b080d0c050c160e0703140c0306040605090906060a05 69
    0x4400c0004603c20800b07402c280c1101a8802808201805100c0c020018040280340014070310307040145001415801003201c0000703151440104070b62506105d01c0782526004210b18242c038907a0769800d6103904c405007010380b40da00700344805840e001d2804482215030031004400750f25425200041894048041c01083c20402250104101106881c4000300310500b00c3c4600c1540f0410405040020b204142005c0c00001201c1e40c42c050408a60300706504890ba141e40d4010125a24401c03405100281e020080021310031225281c070390724100e82665002201041070b90011441e0342c4906003103544401030003d4407500702040200390b941003c0041c011207640220f43d10b80c600e40c0d0791500803902c903144403407040035507504013000305500c14000c2e9050301c110041261840c1c3c4410f0800740b03001720315204403c0e518000a0010305018864041c211101e64100e81c0c0c0d1071076450301c0180c2c501319080140600d4200d0780d500000560b56445a07444c1d40140c40e6100075290ed030078454140a50f8003059006940549a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 867952005 1250 867950755 867950779
    0x801060623031b0f0706090b10061d0405151e0109090902033307022a0f0409050c10120b121b0a0e070216060201050709030807020402040b16030e 64
    0x1252001c840c3c00f859800c0c40d407503903900340000d5001c0d07907005a05002e0f00d007a103800000d004220f00076811030b000f01505800b40c0300382a80c0d00c030103e40c2c2d0400802e50710a0304109a500c0f403540e04094100c0e64021445091034600c00d0706110101d002c0c003c5040c0c20200d040e4030319081c102c0d9540c11400c05409002c0d2a00248580038441c0c021070768510810b0102d808410344031401e6940141c1360140201d544600707a40e5502a03040c807030b030004d654148da14031517001c0403420715000211040c03041f04004481e40281c2003004403442da07400c01c0004c04448800f40c54a0054105401d5141c5c2c1ea890140c0082c2500d85600d101c00143c0c808000495000c1151140204190036501404400000359100341c41d102101b8648010401c002040440303600f90300500000328654207204c80c00d5000300311090842c030b1807047d20044070f5888008034240d40c07041d5007075400718101d1f1000f440444d907000000c1003e00d001404c098a010b6650b820180543d22480341803811104005e4141e081662003100920740d042e04540300c0070266 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 867953255 1250 867952005 867952021
    0xb0603331b0403171b070918020a03080306011812140703050c09090f030313050d08040819020708060406020a0f0320070201030e0604050d03061a0708030709080106062303 75
    0x201c0390340009000100403d000304d0b50403c80d00b0840b02e8403070342ea00d625809100e011030f03550303030f07800081c09602121070602c01030000d50080c464600012580082ca410a41880c6883c1d90416920107840507040024103c040781c1c3c61100c11445000801180303044002e00c41507814200c075031b85604500d10145410210041010403400130324001c2300041218004610349501d000c1500d06182c10b0109601800702004000d00d200c1c200350725004540c01941600d0141340d41510440704208102d03001410900c0a204030f840381c41d400700c1c4c44d0019255034012a5201c9031174464041c035203d001c0b18129809600005c0740d5810b20340c00103001c102c540c90707402c00f4460501d03281030051100089481d10013601c40081424019a0300c80d82000503003040a0095448505150030610f464500c488014400300303080c6000014001203480c079100480002083c2c580c02c1504980d10001769500c082c0c051410000248400304100800f88a560001c100c0c6455043c03240c80a0142500e035030f2400d2074400d00240040c81001854 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 867954505 1250 867953255 867953257
    0x1403070e16110a1202010c0e090702060a0b180112030201060e070c0f060b06120a06080f0c04020c0a080f040f0b0f0a1215090b0306011208070b0603331b 67
    0x5a00182440e00c9640003034002d2614214411202134105548030070061201a010352000e04a800156180d420341c003512018081e03104416504000140c1c0250002110041c0c00c0d80b042606400c000d00c1c624481d881c518000502400c00c3c1c0100000c02801010503041540910400c0004c0600c01c0711100a4a0101c0010b82000081480a040c000703000001d034040003810761084204400007004251119400c6074043d800d030f034085881316403c92505601040100300003e26103110720740c0c0b00c02480c0f640002070034000a500006040c400b01e110340c040102c0022114000b40814480030400c41c0d0f00c50b450261b4010310030b001613012000341c20b03041001c550480801e07012255038603102d091a99450107020300d01d88c0240725928080060300c80112000c01d94103c29003002a9104049040781e410740d8030b452900b6082425010000c1101604001c00d0001803004054140d1001d0002d06540144d0303601c40c1c41685031340f00c008040046856a02210b00c00d090110b00058124964960b0b43b04030000d074484580312 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 867955755 1250 867954505 867954541
    0xd18020306011514030a0c030c05092110060b0c062815090e030405090903090d0f08071a2a03011701020c0f03030105031e03030a0209010c050105011403070e 69
    0x102510b0b003100f05030035a00a01d43e2180e0050402c030f6850b5640303031104010300101044889800080d08084202001c18890801d807240358ac401820019980440103031074031881e4803444007400300c0c0240c59010380d00500380d100380700041155200c1c6680c0d42200120b050304101000701500c4400b4403810380400419451000d011014504050019a04104940062001703035154803e40100382856a421042c06000c030141040300c2050310780784050344520441c6910307070003034222060b0008901c22109010035092048035000d20302550b500742c94612291100650344141c0e1541800b52881d0324180403540410070800c030440000740392442017078810b0001c262900e21040c40f500741940c503080450a8000c0c00bc6d070480302c0c0a80c2c0310049071401e100c00c00d01c040d02c1e6003007445064401e02552048032100044030007128007c800f100051443d40c1c0e540d55001e0025000135a56078100030100d4072142c0080c0e000d11502d40641040b074083c40c246000e12081600e41038940d084002040c2511051101b1084002e140500c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 867957005 1250 867955755 867955769
    0x3030c0a2d02040c050d0e0c101103030703021c09030503010e090f0a0311070815040309060206190c1718102a14040e010509010f050603130c0b040306020d1802030601 73
    0x280000710450440712401146c030100201850940785641e03171100010003540a1809a4000c843c1c00088501038989441000c0b0340c4400e0b8208000058400340700303a0040c18605141d0311006181104d07c1c011500712807000300c1c120081000040140400c001001401e41d009142a0047c1610181c50b904c2c1078840303001d40710040602041c03848600701c0d400e0074005807000e0300c0010308603140c0c1a0641640380c01d280041d5800d40110b0441200460190b20108805104601c00d00c01c0c0245844845038610043c00c00c0100b42003040704078920318100f0510b2402d0b241c010004c441c402e0f000102c50094090030107450071401890945440d01030206486441d4044610250b0028251502c406440c4203071084812120200c4660000040100b01c1103d03c0424a05070748040c2d500741026a210006c40d6059841e601400354042c106000140302c44070350ba440b0ba1400c52058510b00c09940c1e651031443d07820f801c0781d0005c55500340c000c40c001007511503520038000c0f005509050014010b54035004240c40b00018000c1e01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 867958255 1250 867957005 867957011
    0x2090d0201030917070305091305090304060c05120d0c030509061b07140a08070c08060c1b0715020102070203060f0402180c07020907170f0f01051e03030c0a2d0204 72
    0x10301400a9105041d2114104130f1304103544022624006009a1009020a1181a030101ca041d0701312001d2250500c141c03c2c10b40154685810f0610985038811301c881c007201c00b0b1040803882d0120f2040d16001e0210640c1080012880b5403072036a029090351402401c40d8247e030700540820240346c405028101000460040180c5e484545e414100100102c0c8030030f10b4818405c1c84103004c10424180010150f00b8014503151800b5600c4005a640720341c4195070003c0e4454081c0310a500e540800040428848114011200d51655918040e07010317000c032000080c050f0354040342c040c00f581000d02010b0350000d401c0800000c20728059000440f081001c402c81146109000c0004804021a07001c40b900c0307540046c501d80b050324100300d000b003032499804010401e0040704804a0050451600424007406030030f69185896801c2c074051120443c2e030710009039000381d649840345c810303a142030004010003810003001e011090000d081c012039000200c0c160340005058910381c184040d6044200c52442c7e0350440b408 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 867959505 1250 867958255 867958271
    0x100f020304060c02031005010303110f03040308031915062a0203070605030408070803040f060f0902030606040c021f1505060703020606010f051c050403030c0c0b0402210610140402090d020103 84
    0xb003403500748141b41c40034406140900100900d50411042c04c403219034071044030503215034813420a46a0180d0310008003541e600f4030108031a1030544e9004104220801c0c0009884242c805107001c07007140550091010407a06907515816801d11113020607c50352000380700a2484043d80803940c0ca8489205420400c80c01002080402c60604c00711440c2c01d07009000b0641303034103007803c2002500e403a80e0400c403815481c00c5480c0750105240e005280c002074005001e00510380d681c006100242252940c044114000c0d50f03282015045001c19014051a0138480007480301703031608003410300c09801d401040c401c00c018010300000a86c0050310681c0100e0030b2038000d03598581c0003000c0e9524044c281c0e801c00b02001008015125100541c0418460707802070f41c0c01d028001510900350380f0007454000103041c40384d43c1000240903040000b40d0300060710284e05051003800149981d0707400d0010940710fa50a804615000300400d03503070704140b90b41003030781103400714605942d03100041c0c500045240c0080c1890b0b264011 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 867960755 1250 867959505 867959509
    0x70804050f121e09030d0f030c09060c0f210302220506030109150306090b09060109020c120f160c060f0305071b060906020a02101a0d02060c07120c05100f020304060c02 74
    0x155001e6560190442d01601071504011341507104156000c0e001a284c4485462031030f2149075022b0031078903a5129030081d9610b945605098000ca00c106070344422035403981d6100400d1260b0300142002080d500103840d00031400701c140b201d005402c1d2a1861801200050003569103110450f41140c0c500100015144550110305d03003110401d134000342c078003450010001e050245a04041e4414001d0401380c2e00ca1f03a8940d281c41c0201d00483c030151441d036115550048400d0708000080026290510626003841d04000c1422491011003c2c21244444071881c01c002c116002600b50b1901c1060381014070162900000c002e000070000f000c00002c103080c0b400344005003c21580b1080d030b120f8001c5010341d507130038030300700040c0d6180013110b4200c2c00c5a19000074420592414050b0000c1550010f0100408403015001c00110b0b0308002d01c45038a0740245031000030566007000407059503a1040700d007004034516180400840d80e050b00c0240003488003000b070400c00c0685c040100c400340d61160500354052082400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 867962005 1250 867960755 867960757
    0x61f0f30021903120207030c062703050d080a020903100b011e020d0e010309080d020901141305040c02061e0c04080102040b181012050c070506070804050f121e 70
    0x15001e07400481071000702c9420540020144181d0b80600c440c55041182d60000b03c0e528140ba01c0041d00038642e251086c0300181c82081c0f100100b5880504449034a003804410359015510ba078000c0b9816030280b11103400e0715030880000f56001900200440c2010101d001007625061104043d515165940000c0000d5a0140c892451b00700c0c00c07821600c0800c12035110180da949110320380301c0041402242640e01c02e40c070901403540c016500c42e01007401d000031005800041d4000c181c8043c1070111051300424070403464809090458160060398007018a40000d02084500201218003150464820800c0404209401c0001d070010310985107016900c3c41000c0005000f0307504018001e500000300042c00210030b0018280c070300c0c40540707000b035022020020072440084400c1813030040703141d107841c28840c1d5050303a0156034040c1d240c034600e514014455690350700b05501103e107a00071a40000602041c0541040310246035551440105410408910725816078000c0c00e03440d221615000a410f001c00344440 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 867963255 1250 867962005 867962099
    0x609040216031107171218060c031c0204030209040f1704082104081c0c1a0a0e0705010c020402030c040305330601080a0b12061f0f 58
    0x1021240768a0071498010040034220b02c0c030303010030320030b180d0042a800d40b20400c002c60981558024418a140040c03a200c5c40c1d041000380d1890392030300c42070288154403010010481801401c0165a0f550719400101701003211000a030884144140414401a02c07800801900a0380001d00c0300007494883c90071511012a003089403910300300c04280062030000009011114210341003007802e40c41c400b10f54007000360003140714134410342c4e0104044981c00000d84a521138007401515021f422860b45455424117020f41f100001010303108a020043d04e160507209012905d04c4410141080c1403070702c80002e0040e071024402030302c00c42e070000100300203420980840c0e006562041c1507504030714444001c0385200d19814525140d00081d4180b541c42e640e01c0024151040034142c4400c001030f10342c0c13401c0400501c440552a43c20045010710010400020081c003071050011254200e51452502418104131140c1e0713204101d01130421a0510020780183c043c2604481207088114190b40c007102a11383c000c40f04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 867964505 1250 867963255 867963277
    0x12060509120c070602010b030d05070b152119050304140109030b090703030f0c020d0b0606071505070315050a030b09030d291909020a11010e01060e0c0a0e06090402 72
    0xd44048403040841e03c0340c11254550000c100d1204420107050301d4003140c00384400007502c10400c080004000e0808503802c00d1001d14036180301d20b02c240214034148004498800720b540b00316030901c88a0740800011141b400d1031560310800a036165910341d564041d50244000039918818421a964410a500310046810480030105810003a400c140c4881041c0030903400a13850078284008207002d01284601d65034080c08c50f130380a00340f0f030720303a05180304015012940c0054108800c0300030a482034050784280b806c5010000d200d051946c03014003124103c941e200c0d400c40040000f00496076410107000b085a800c400e40c1d05c3e00e40d03140c1d8074541c00c40c8102010001d2052a0081c82da007030148110002c0e8103200c000480e0000da0a204e0200700a007141c854242181e4440d84e072090105011a4018040e50300603070a001d00485054500542174500401c40002180c1d50303407604000c40800300c14030b9038011580340d120074905621076000500c1000c80210581c011107002030a07100c1c1d074665604641c5c3e00440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 867965755 1250 867964505 867964507
    0x709020c161d0f01030c06140d2306030703080306041113080a03140c06040f03050c0a140601090e03040915030602040e09100e0d0810080d080a060b03011206050912 72
    0xd074903030b07820807410260318a01140d00100000d001482d14502003030503a508120791170500c618020049402a1101c0402c9460500600100600a846000340414016850381c203a950f0111020f80851120004051901c258003265040022514030411613402480650f0f01155410300c030212201e05104000344102842002000080c40c030501107078102113035100e552200940000e002a071125805507c0c070030700f40ca802c031802041c00034402001060125209081250610b20141140350603c20028015500740b031f039440e08a1140d200c01e2040b640034100d00340c1d08212442d4044030740ca40c0c03070146026085459580d4511203600c51400c2440800556202400355503031525510300b01644402950361035894402c0e082c04c001034403014016441c065408000801144000c00000c50305408040c1c480144681882000b00350703040c00307004505500c21561103041c11803e2642a40040b5803e07507100c4c0c0031038a01440140001c009034007036805040e4200602150980b210000141401202c500ea00c682080c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 867967005 1250 867965755 867965759
    0x1303030b0a05180a063609020301060801020c1009050601150c06060603021801030c0e0f1507050a0201090906030215070809030f07050a1a092209050c0a06020f0709020c16 75
    0x119054003984202030400c000c0c171609a4070300003841d483e40300034000721b103134030581c0754070001c0c40c0840807004000702c81500c000c115841a90042421a95076820040241c0d400080b4420b100b4810403042c0c03070491600324200b1909601d51581500c0321010b004000078181c8494030700044030320801c0e01800298005408000d0303a80d83d110090000c0d40458a400b1714490f05440300b0a666001e80310342003071b41d102c075125030f080050880c08101e03170703202d070550b28a510068a0780c245016007c054060000588208000d007401d181d10300001d8000e018650003219082d0130004144011b0706d0f2000780b5040d11b000a5425a03c3c1e040d03d150080715800340161050305032240f600c0c2702003c200c00203008001c4400035101c0702c542c0d40e101c000e05402c07a041c0b6a1144010f0b10204800f011608052945d018402072501c13075001d0124020745c500c1c00b40d80c0000010b80720340d8410440600f41b0719041310008018103480c0018492020100c1d603850301d8500d03a1058002c0c981d800f107170310b0048482c24400b51010030000800c0c0c1d6a025 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 867968255 1250 867967005 867967039
    0x1d0709230a090b010e100e06041103130c0f031a07121a101b08131a07110604030f030804021c0614090f0a17040b0705010207050c0103051303030b0a05 66
    0xb604500603150303210003000024804a05080c4203010b01600e00d42da05910742412032031000400090410303070f0043c2e9a40250b550354813590006d1402005080101c101d4182c282c100907103140320a40081c41c0700150310030200001803540b0b50f04605100805030100d000d030365154050354a00c580c00c0b04681c5480c100104c000203581c0441c844100000101c8104403010000d0000b140c3e1000c030280314406c1410005000c0c008160581d01a000003d03d07030600004498803880c1c0c48030f80d4402803040c034207120000300c0c0350710401007881590090124140c65060815155440303a0444410030307500170341800003407000300d4155240e000410a21902c0c82c200e580c4182c0c0507180c0790000301013040c844020000c4d014041440c40c100410f0484014040c0402890880c02c1925440003e01c017002261032612801c000008034808002c026003180360103280010b854404034140070741000704c004400342c1098540402c00008000d20900600d01d1501440c0000e1448911008208804401c2d04101e501424041c0260510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 867969505 1250 867968255 867968261
    0x8010506150a12110d05180c030c06070602070c0f1409070c1506080f0c0a090905030415030e1903030b03060f010b0a271502060c0d050c0910030f1d0709230a 69
    0x800481f40e2003100c80d2240841c060b102c1c4120124241d06411101015109182c02800f03091010b00813500140340880c0c5607a01542a02c199004d8031194420000401c01201404900503410800f036071007040a00e404c20005101040d4400c1c010b01809803080c2204180e901e82e44040040c003564400c84101c0c000040b01241d40f042c0d1449041d228840c90b2402081000d490701800c1003035640075008605160428410120701501211180105540c504503410803c20070860740e15510b8200c908014030700b00310305004040c1c640d510041d901030b070300c08414044100c0302d00b101941180c04195202d0748561100e0000c4400034418115100c5854405d48611002c80101c0c00d81c80072143d20b0a1064404107076004141c0c0c54040072601161148404d202e03500100d06647c108680c00903205008914007110b0800051b4100c0355864040002955034603107142c10300061003002180c41030b601c901440c21044d10801341d550b00d154000c1809441d280c80da03801d00d04141002c510440300349140e0310035980c50101c6040c070007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 867970755 1250 867969505 867969511
    0x308090a09090203100b01020a050706050304020406060503240102011107060212070c0807020123030405010c08010f0b040302040f18121b03081f0b0c0708010506150a12110d05 77
    0x100d5103061000156070700d100d2203090a01640a0043c01410403110749102c020315900c0112070540c090b010104002030000d01c015000303405141c80f030780d07104e00781401400100c0b8031341c0d04120305200701001030003c1059410107004840ca06007140c1c0501961410040380508420807000f00400d1022400b94104615074010708040400701a9020003a900c141080758280085100544403080c200035180c0554441d0b1a500507014a05d0b083c42c00c1d000c40c1942e4041d40b540212001d80380d0b0395485c040041c041d644080668014812070492203003440c00d0040d081d04510580c0b000a00c82c81ea031322003480c602005070304201172400440c407500a00c0f04080c00c0444c0380142440c4004000740004807000208580b07201ca8914041e09569415070654901a0b0150300c0c0846c50320710380c40c825515a000468410756002000c4140340000a400d8540c5800075480c01e40e500509405d11503201d907900707510810003601c00d4450181e0503180440c0000010f11640c8001c081c00ea40c201c0ca200000100c241c030744600350304a0380c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 867972005 1250 867970755 867970759
    0x150402130204030314131511060619050d150216060f051e040c03080c010b0f06072f100807080601030b0306070e040f020c010603050f030c031e0c07030809 68
    0x1000a20180c4001284164000280860b04030322003010000601c6002c0c10b0ba00c40c1c0c4e004546241900c03a41541e200822980c0a20300044d1002c0c0b044501c400284001600140192451000c0004840c42c1d5441d26036507000e0180595440da642d50b06200e0403201c0c40c071400e400124219a1140e030a00d0100394603500304010b980f00c50401c2e480d09582031081c410070303207d510700d190001400f086c9031740c29284800b00030304181c0d000d190300040400420800c50082401c000030900008892184106010180b0a10f614861040c1014014000440c5940d011200786070302c4111000c010081001c0c0199080c1482110240c004c65104080c005044d000085a4051796590b01e42c940a82d54110044090343c031201100c0d13416400020200381d015018101e080d010b501c000380041002d50040b00c460b42240c202c8800180c240c1e444000c10000e2007418031104048203640700245107003030030422190340e8034450070754464101084448a81c0e00c0034509003e940b00d00031781030151010b441d5a030030044c40b2070300490041d074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 867973255 1250 867972005 867972019
    0x1a0a0608010e013501151e060201021c020c0f0607090e09030a02070519030b040602031005010c0807030f090504050405010608100c0c30080a1406010206040f060e150402 74
    0x4c00e0560500403c072512110810340481190020049035504000b1040240c071150340360400c034100f1180002030040508464005243c405941c08001c0384c2c500882d902200a40e441045410104105001100c0c0d85410301003016958002140b82c4da864400814071008160040c4400c1c401140e912414070002c498480450914036200da5185544038804c15a5100250380b2900301002542444140c0030b041c101c2d5500c20a13042e6660340c03203000d0400b1040750300b110078039400401c1204011080740300d50050882032a2425403800c003691041118800e9480c003400b80312922a21641152040d071100021300400f030030500171400c01d464194003810190042800e01c0c0151200c200142c800c038882c0781c25416007951045002103041c1c84600000c100c0942c2440c1d00c1c941503034081d180040c105a00b410030305075541c4882031460032480640850b200d2481d80d2584032028014044a60b0740010030640264001c0031080f5945458640003005210460f4440524092004c816555000506c82e40d0721460082e00c8070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 867974505 1250 867973255 867973259
    0x2251203020a11270901060b13150906050f0906090409050312071b140c10020303010609090902090403080a0b210c041122181a0a0501080601031a0a0608010e01 70
    0x40124010344500741070801004c02c0c0114039105030002e4903000340784100000744c00c64603415142a0f540c0045024460741c02580030030050200c02c001d11901d00c01007440c1145d061070078614003e120b84210010704d500a24007084800569032100704803a0084c00040c010030003000c681c035020b500c036003109010101741c0d102040080c0c08039000d08080343e0100155066203c00c814165030304001c0703010203107000a191140d4548511682c54070f0003c507440d00115001140c0343c1d8544a8014540b40c126002a004a820070100d0001602c0304403178640c00c2a2f144c00d03c18141d0b9a03d0500e07030028000c0038402c550007400c07480f514a4070206c2e01606c0402c1403226041d1084400f02c40e0910013a20340c5221640c4901c8801c10021030f16984c901007030b020ba680505d120700100c0b03588410170150452422045211b642e503501b00f000c0000d51042e407001c07510030160341000301d0928210021380614001002507040c1912080424190120000340d4a03400d00014034401c0030546a4500422196090180701081028070b000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 867975755 1250 867974505 867974509
    0x304060806041415040f0e070e220507140612040c0f080307050d03090312060338010302010e01031e020426060408090a03210e06040602251203020a11 66
    0x700500c04c241c160210710a4902200c103000091501030660503840f95210001e003200c540510200d4020440ca0714441e540d4200000a8450b0100b20041040508060399000001030004143da50440e501c1c0800d8116510100c804078101e4480c514600008001c2c43c0204410440300b1180141513410170a80030300c2c443d4940ad8015070b0391103a0780f4041c005500c02c1c1c0c25180d4140c03003500446461486072038911402542c02603044107580e460382045601460003034440000410340c04a52620030821006220f002c1184800722450b13500600020b410003904050018071a40240c001d01603c41040c4401c4031411424110700c4020740040c05a03240c002c0d001e041680d0450a03c01e0003440d50541303400509400e4031282c4d92a1169030007501c0d22600040b02840010118969840717185039080713540c9000c212f02a85220082c1450070310041984079080502c02408130542c0080c4e0800c01c40c2c0c0101c3c45d00c10b801d04500300d070043c40c42d040d807050300d60121340c2c003242081580c04120011400d2040c44603420b90005201 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 867977005 1250 867975755 867975791
    0x616140d110319151d1305030310300b0703110c070e0106080906180c040212150307080c01030b0406090c020d03200f0d0e06150901080607200708030406080604 70
    0xc0b034040f081084161003174800400c54800da40140d40700700c49606000d00341c0e0302c00341540c108884070350007c440c01c4030400011101d403085220101c0070070030032000540420100c0d103010004c110701070828494000022070071400b07580301d00074080c03184030007076201c040c0100910798604050080b180025610000045c0982c0941d0300d86004c0d14189000d46203c4d07503142040e8841400c100d00c80c40061084c180046800e031114402030186800000c02d0b200289440b10900301d4000762000d903035010754051182000410800f00b040a1000d00900c0c02050035403544000074003400240e0030500069150000a45182d41c001611000d4034510382c509010180d091045d010441507904903602c00b010080040d0034180b083d400c0100707500c0508810004608030700072041c40c0381810440d0b02c80002c50700e4607881d840c1e9280445500d80144003420040c1040e1030090320090661058003003a110003240c55400780784806c410302c9400c01a010b0002101d84407643d1b03c44c008e08042040e80e1450040d0303c0d000100581d40b10307084c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 867978255 1250 867977005 867977009
    0x203300c0304121104020310171204090b0102120c0106180902010804120c0b100801150f150507060f05070f0c02010e0909012003090616140d11031915 66
    0xc0146003801e2400407901545a00443c1c01c03101041904414240c645e554400f030340c040c010082c0400f4003103081162035007004d05480481411503000f070440700c04100c103d001322001c1d1180490045680c860020050386440c0c4c2d02d011000080380301151403075194505502035001c58070400c0b907049294001184c81001c80b400d90101a0000e041c404c005004154420101c003c44070803032034540c44401c1c0584600f5540402aa514000282d01d89801c018400c400d01038424201004904801001d02c0c0120003a81110f00c0d218081c2c3c1480716044210b66203014905580c41d45400c11424014002c510b00c103800101412599200452400240150001e10441e014090f159040c0c451a45200302c0204000d90082c009040007101d41d2a41b40c2000cc0d13001925800044000686415440303003030075900507042100081803005114401910006910360250168007000d2411050310396507900122300c90302400540d5802400e04100006008041e50b0305130204c0d0020958040402c41d0825016122248840138 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 867979505 1250 867978255 867978277
    0x7181b050c0706032c0703050c1503060d080c100c09230120010e07050928050c090d120306320d0204230f04030c0b040c03020330 57
    0x6207061100134000c2c0d00801404200700148200c545030075040703668412060649035015048000c080080150410014465400488007541184021441d8403038034040109402d11401e06162420240040e0b00304840c03d0000d52000e07107950301c130b2031030003080544040c03000071000451544c8001170308049003004201c0160706a8120072111020001101c81d6243c0010080088110585142c0c00c1ca20074420f001015407403902401103035140104024070520700602500700c1c83c40c0c4420007900f000240c0412003040740c00b1036000985888102400f8510701404a241d0f0b0010090041c58080c00745522180c1d4903503003141d0701403003d5500c036201c120300440c0ca0010a912000c02200c0a40744c58801d00d5529003040e0054950240c000480d0006401e9a80f44100c69002109044a004010a0703001d0301d03070b03030080f1401d405a040341800d681c010840040300d4406040f414001001ca420080e0007407103c0020740d001421101d41c0d0f41c003002e100259440e8210b107080c041c0c1840840180600440054900103250 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 867980755 1250 867979505 867979513
    0x6090c0306220c051207232d09040c050f0103061a2b0903180e0a0222230114090d140d050a0914090402060c07181b050c 53
    0x1280010118600c0000301101c03400d4038000e0100d00e68039034182c84c1121004510086c00c01914080007500003066124807544150090080100c0c56241c2002c040344004600204444190758640102d140141002803a41e0040105080c00140450200480e040e10011150105d8001d148c800540888050340b0858004501482110314a600c1c100003a0101c0d5400c20f151418002000065025043c00240500c046903078400c6401c9c1455840403928823155135210000079481d017486c04000c00b000e0001c0400380c1c900c6c2c0004000e0320794690915451034606090307102900e40c0380c440c15507001c10005484000103501c0c0b1502030000541c810042400c44071065035580346042401014045102c1034840c003520f0504c0b03014003054145804201418280c203656650b2902c071501110018840b2200e5848029030740204011030006684108a864006a040307440036034951007440c0d00c0d820204180d010b40c00310000c64102010545894000100f1001e0300250000421101103080d41c0728028518501d195501c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 867982005 1250 867980755 867980791
    0x90d050d0302040306061e170a020a03050109170a0206060d0809100815030a0b15030109051203041209140d061b05030105031501151214010620010608330906090c0306 73
    0x41c400d0042123003600c414080c0c50360842c0580118101d49401c1d0310031a070580d500c401c0713842404006e41d00150b03c014103990480c41e0551402e00250345000c0500000c0c4200d03642c0c0382c00c0341007000f01021240315840281800e07050240344c1c174003d00f4410f03080310000740382c3d10b4292040c40b092901241c5403400650007048844030b03445140b5034680d800841d0000035050341d0307105174000108d90100800e080c69030100402550341c1c03034246401c0c210f03074105040b000d084c0160759005021242e000f4140e48000c1038103503035088541440e07061600150110140b81c0032540c13a1011031030030b044d600400031410b90388241c00f123480c800d4003901c101440080900c142d00040ae4503030480d50003c1c0c42030802e0700100941c40701c0451040c0e105034034802c52079003e900a4000c501940541ca601064401000c0c4465098000800c01e5602d02a00241c40e61140c003425041111030940040c151070804010710700622910305441c01c0c0740390041c403c9079505011780d0192502d1261107456201c1d4600010070602c54000b000716900360301 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 867983255 1250 867982005 867982019
    0x312060301021c0b0f030115140315150a24020f06060904080d0608010614010210060b0d02071406040609052503060902030a150b010e03061b090d050d0302040306061e 73
    0x46441345520642d6550700c3c0c503069409009007020005045210782185203030000440ba101800080e69000750010b0441c2d03562001030300a130551003004145160203207241c0c4000201802c5130784c1c03c104640c00f140c480c3d900c0c460b1024440841882440c0c2c00310b9111211402546a0340d44040b01c1c450741c401100d134000307800a03c010019046c00381c2c4415000c261217459010107403d40300d1a400c05503400307555034003c0341190381c10004800350304c440310380401c845414024600100e1058904640301da940001d00c110401085110840383c607012038051700c0d8681805d140040c00741c10031000a440300c0c450101000c000030360f40c0c2d01e001e5001282c0703034000750002c0c950764411010381001c40c000c2c0d03030500545842d0400300300d52143e84029006030150000742d01100074005003403c03988840340350281c1d10540800c8521520b07036440382032540302026110389580c0181c0004100ea40d1980c0000c0083c000e500e07500d10a260550080e00c04d0724480d0100303102a549030000d0440250b21079106070048810900c00700085c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 867984505 1250 867983255 867983261
    0x103080412021207180b0405090a2301050f0a060b0a020613150504141b37030c0e0601030e0c10121e05010803030405100e030904050403020312060301021c 68
    0x7030320282c07441d0300301d61480c0081400d080071680104400e01003040d20b5808600e007413140110300c2c00221010480c608000c418940d0303d42401000500865038440c400840112000b4100e040c4401c54009000c41d10300848840c800d94800d81ea98500c050034210081001c400c45410b032203000101d40d000b81055a00c1d62034260081108900540d0102d4800800308018111802664071443c015860140d0780201081e00500e0032505d50345c40c0a800103469a0350f0700e60794540b02500d0000302d15224142031400c590300b02640c3c002420b0032224114003610b500008101c0341c00c40b034004940d00d0040d5142c0d42d84e92080150262220108400b01641110f03002d9009403078440f05280605070786182c000c0c030134032045110784102e4080400c501403030041400802d0005d400e50107001c2c050003904000e0340c20341c2402e41e104e40d40e46141000a151290b22075011144590b010002c1d1044404000c0041c00b050509040281d10790384060384a07120300000c3c50000d25a41414002c80d603666044041e4042ca0400c036810441c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 867985611 1106 867984505 867984539
    0x1090812040b0c0f01050906041208070e0d1110020307020301180f4e0908030a0e01020c1201060518040b04061107020a0806180601030804 61
    0x302800c9032007074600b11040d0742940c80c0c88a204a0b40310f82021031222141010f03620b0402001210080002d9050145020f20001c440c800da408808071a42d41040f110300340480c000c006445c0741d41c1082c1c1b20080301c66000d4410003181000c680005041e085624202e08010313440440c1050035880d0a108012440d00780c440c400140b402c142c1d0b00c0300c0300c00b98215070180c4035000300c3c2683e4400c40c0d648a80c00740c030581c00c100c2a001c141c01945c21060400700305200390150380c0d16410310380b85444c081d04000c4140c0c0c000e07000950421001c55011221501c403518694114041d0310103120054541811645071180140004604a810035003481030665070f071010398000450070030900c4042803007a80c50a4001703800007400b140784030080482140e2403107601c0e80250031900024001580301e4001c90400d0241800401c26900159806c42c0141e44610a000142c480c0c41d040100b00040740880c869041 = true := by decide +kernel

theorem cover : BRFrame.Cov 867805755 867985611 := by
  have h0 := BRFrame.cov_init 867805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 867805755 ≤ n) (h2 : n < 867985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
