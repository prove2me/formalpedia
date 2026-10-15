-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3908
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:01:35.273369+00:00
-- url     : https://prove2.me/submissions/5c3ea445-8a62-46d6-be88-b00f012236f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 702697841 ≤ n < 702877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 702699091 1250 702697841 702697859
    0x15061c0c03140d050702040f090210030f0614181021210f0f0e060c010f0605041103150619111204061b110a150806040516080a090b01 59
    0x400d110980b00c0181e01c0604007260100883c03221910305450b11441c1c00e0101940900000b4148040210003656640c00e002d800760b0b85240c40344000c1c00403540c010904090300e481c05007c1d9a202c0c0d020b1807840e20300e07807500310090b640d00da6101c11002e2402486031240c1d0b50b00d030404401141d5a40141c041803884400c040f00341c000007801c42e03a558000c1030400601c04420044000440306480007034002951007802015540c481c4040e2000740500d032505076070311610766000030840c0d80280c08043c45603554181e400001c50f02401a08001c02007250700b00417404001c075a05100b440f00501c13034251105400d86449003980d80e40d007075070340c907135091030030406151123080000c0c060b016000500083d03481050035552442c01284100c405854240d61010f00032409032800c500541c10f559802c45e14507611040580e00351300c407484898001d020440401d0000c102c050030162510402401460059003458104016003190b194000c0101070300e81b401c8050355466428100060001290090051040100008841d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 702700341 1250 702699091 702699113
    0x220f08071b0602070f05090703150b0711100e0907020322140d0c090b01020319020312010f05030a02090c070b07081803190e0a03080a0201021b0f15061c 67
    0x20a204003038111038880302d06aa8074100c62042c2e02201c0d059043c1030000c1d08100170125003109103030402107250010030302000f5590b000c0742c1141c0c0300004089884002c1c41000c034180d403103042c01521020341800d2001e100405020a20b094940144020070104401920800c100e540c4200a02c1000f00c02c08000620359000d44014403404c5200d55095041c50b059181c1541c03c480c2e050b038407a0308034141900e01840360010303110408000d8150700082c4411110301301454940c540c00001540515030301c113100d80301212640c006030043c0c1f035900c1c10340c60140040d8500044901103603404a03100041c0b0f81c2d4034564503440c0d10450100514020107042801500303a001000c180c0035080743c00c81c186400c070441810556034002c0030100140b210b0010b50b100c1e4640d000f6901d0502502c40904a840c10744d0f1640c4480140ea4070034900e1500603940015500d030404042103640e0003031241c82c000390912080308000183e64400c0c003080f04492200300c0380030600a50320000200050020b0080c00c19907600319040102c1154 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 702701591 1250 702700341 702700373
    0x7030203011d0702761803202704060903260a0b04060302281211040f06150c060f020d020c0f0105220f0807 48
    0x8100c0c00306440c2c0300803041c42071081405034000e0901140c007000d074811110444100e850880035850740f400e200003411608100c1c802c003071002c540c0562107241d01d00e540482030140c4201e828400d03154205401c041d0200d0b000c3c141110380ba1035800144a40004600202a548002c184c0142c00e50421152015540d00040da160102d408141400d88000c0d065070700c40b000b401c1e0030f5449105400290008042d035010200d03581c00303854102170011603d1040560740c01407985000c201c00c112010041100b03800e004014100009a909108451a41d07010031070640608110180c000707842c0031103070390030f6402c4100940102011402252501c500381420000400b151a03114026410411061030341c0801e40540b10440b03010404441e0000880c450443e0460b0325000125119a2103030342950324615280081c0c140c807005c50100603600c01e13419440c545440106c2c400b22039113904103c05c000300c91815072006056107030004607007281c481003460081c88900c0060b100030004800460300d002030146d1140382180d06 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 702702841 1250 702701591 702701609
    0xb040602012a050f0313080a0c050c030c0105030411030109080f070b010905060607030f110616020d2d0c060204081e0606091501121119091809020303120703020301 72
    0xa040c0440c000c2c5100c1200d41d08400410760401c070305a04c52850f840190707809801100d0810505500741c0c1d858005034010141e16000407078020013030307003804414481a070307009004400410303034644c1c4440082d180c1d00004101401900255007004071f00d40b000e40046100d07a5000f0046561b80304c2d200450441900841030940e0350b031198600115800c901842501d010741c2d00241900e007013540d2640c0c02c8546e5400781c1000c0080002800507100200d6040041a0241c1682c0200400d0007078480c40003494a0840581541000300215401050701503680c0055484a050b032200301e0380c820300c6041525140a01c201c0280040d100080000b40c035480800d012075140a449080914114042220b0717075104000c0e01d58940c819505800f00709011140c0a8442c040203043c100000304604a00d1500211030402d0803082007000001011580c20300c2540d108980c10031182421034083c1c0c03d00603c10705201d2522040310303941c4c0c1e84124050941d40d04005607a800514007181800c5868440c0c00100039401c21b100d94094 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 702704091 1250 702702841 702702881
    0x50a170c0d2d0204062601090c02160806010509090715030b011202160308070201020c060412021c09080c010905030c0405060a050301141f030c0e0a060b04060201 71
    0x1060a00029890055404500d240d050045001d05000140586141d02c03080c2c40c08410500c00c100c203184149640101080e00040c2c59601d0008042c1c8070141c80c240c0ca01d405901e03100a43c00d4243c00c0c2d45142c0c1515460040043c0c664150a0143d140c003400c1803682200c0c00451000141000700040c07002d050701e0b002c0e03900b2403440e250f080130250f90b0600b03401a646076028100003040b4461180d4801c01901c1014582020061103814841c012640096134208407445001c40100070700d50007521440d00502c1c1391008500d0400300c40d08203519564050300051940780c00b40c94800b2001c0c403c1190200000c000841581c02074418480034040103050b01c1102121301541500c14000e60084861030100d8101901a103003500a0004010046c280100141d034024295840840c81e52400d20400c8120321601c1c940117054200160403d10300088a04c0d6030051031094038040c0001511115114200c0c0c910050504980e102d000c00701c0080e11031a000908428800719000800544c1504200700d00c001c0b007610003c8c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 702705341 1250 702704091 702704117
    0x2090f09281d010207060606021507050a090f0602060a0c1107090917030f09061f09020a020708061509011a0702010804030c0512030f0708010f21050a030504051314150d020a06050a 79
    0x10700e6078808190301181003cae002c00140340720b00520051104001e2407070001d05090300e8000c0c0110b01203090f00300030700580c0000d0801044810521501107140010709001c0c7c182c62040c101c666458171140150400f00da140e445210412552440d4410202e20b0034485544074502080808481c650455504003144610b82c0030542c0030030f448982514190030a480380c866a030030002400040e60000703507000114810001c3c00a071150b41400b01c140680d02004c20001e61405500c20040b090506800c00e041d4884802c1c410a40c460000d400c442d051a820700740209a81c0d201e04003924014440c5001802f540101d10710781d030700142d220000b503100320404052080d4070388801400f160f070b900d002d018800d210744014030284000107404d504050b04200e5068416069000c40e0b94190608003041c08c200d01160002ca01480f0f14a40b1240b6026009901c1504115940001c404030814000190403507100c840d0540d0540c0a81e128440c99403400f03600a480051120360b1244010030070741c44129060001118512010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 702706591 1250 702705341 702705343
    0x203040302101a1c120905010e0406050315071403070c02011412190207050318010e0d030e01030f2c070518010312050c0a0602090f09281d01020706060602 68
    0x440e98240702d83c0c2e904400c0d24244180101c02c200c0d90800404000140009070014400001012990003190388101c17aa51a043c00541450700c50555144240e0a00d83c082c407060310002003545e14036180010306001c0c1e840f49071b8151082c031195480098413500001c1008011500715a81303071a270610030f80c4c0300c00e1600c03045c0c03000c06101d005040d0203c000c005580041040320309204600c041c04a02880b0040c5031001c160b507110f28550000c2d10806442c01c2c240c40300300c01b541c1c00103d0b10007143c20984140c902c600d655070b001008503801032075060606d65030b080c0408220455911103600700030304884501e0300c100c5581e07285c103220807144800c903054030505c20045450b04100903082d80e82407198030b42182c140d0031aa078110310609003950300420000c00303102650615004001c0850b2850180600690300e1700c854050101500090307001c50f004403441000e01901c8526582a200d0341400e8503484030344070341d898818001402c181142a41010080c6a086046441c10b41c0140f05c01d03403203000c0400c07411b0f584910070b03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 702707841 1250 702706591 702706601
    0x171506030402010e040e0118050d11120a0507020d050a0c230d150c090306060602190327090b09060312031609050a0603020d0b0307050303041203050904050a020304030210 75
    0x14a8008505101140043d4000c0c3c03002e0354031200c02030010940c5080e4007902403c583e10307449003000d10017081d2151002c1c81014043c0c281911014a8103900e41151405074980d41c0e090600b08003c12003000480e200850721420a54007600d134000c1c00102c403000a824999504d07801c00b00161041c00c2d11103000914000c815580315000701c2c01040e80d0241b10450700070403000c99200c0ea4117075600e5801d5460540180068840c9009004042d00d40230110342c10340c10b00d00f0844d903036500800155488543c0c560740702c800d4240307074440311a4180341c07041075108001608001c1078840c3c4640040d12081803c00301d030300c0c0d03419002405400030690350b03410541d40c0c0c281013650311171184032070604d078000400126405402d850303009511a941800c003585001e540c0d001144d042d00e055131001002950228003030481d003510380542e81350560210010800b681c10030001940303a01c03e0341316080c11404407030010020907004005640c024040280108490b2800c910610042d52045074220018040c0340b036204200c1e6460310074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 702709091 1250 702707841 702707881
    0x10b1509030c241819030210030c11030c0f0d26091c020105070f0c021806031207031805030c030d1218050a03020601080d17070e060d060e01290a05160317 68
    0xa844644200c08d00c0544c000d0881389410070800c40d0380344403100814400c2005020911402004042c0d28564600b1641820f250b44484010803502c6d40b06032810741c3c1181c480d0350300301801c0704080096464a00c24149009404007121000b0001404503040c005d4065001600ca0312607521405d5403100303596170032103a503034601d90001e5000c0300c6010603403142000c20808a40c014405402c4500c400c51250f005041601f00440c102d0000b2524016420039a07040a4003000400080c0c0061416228180000c1d4440042c08050700030403216005600010080d03811482c03038000c0c0c107925100307808418200715407101e281c0b00c010342c090300c80c000000404034800905544528040e5892107100c5010022070161554040c203107804000003d40d0030181035031144010807403074050400000d003040c507001207107200d444141d00060145045850800204041c01065400c800240c0a125540c0c09101403c0d1068019425044e105004448001c4101a000051000c0301c00d8020000419661610928084580c074804 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 702710341 1250 702709091 702709099
    0xb0f120d1b0b1306060e04050601030c1202030a0b0603010f060305030415170109021e12040b0a020c030a0c05121306020105010801050411061e0c010b1509030c2418190302 75
    0x541c03007001d0b25001070f41040c031600c0c011403000d0f51004030345801002510141c899401c40c00c01003040140300112800100040403282c0300495a54000075140c07405098042e00780440e200028060b82c0c1c1c01c2d44550040040900b080140b943c8070f0800c0c45c0c1d40d402030302a5400d200b032203e4074101c19038052450300d0340e80307115035401140036801c01001c80c0103500425107452040007105a543d002d4401040984452180441007444a02e090300b4003202094001e4901c00c681881085045000b40020040322000c0800d81000f41104c001031408501d000c6910300300136441d00c40440c028100c1d02c11115004212030003030303009000e1640c0750741d101c900300c1d0001d440050105800307000a41140c202030016000d660b9800d52030100750781c43c001741003505921809070b190082e503562007040c0c5145000c1060071200e0304d01c00d1805040000d0070f004aa541c4c010003ca05224005048071b0901d9520721060044c9000c0b00d000741c00344c5420641d00000118000d0b01101841003403518124050020402108011660024 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 702711591 1250 702710341 702710363
    0xd05150306060d06061d1e07020d05180301020a08090d030b0d021005090a080f15011a16050a03020a06061d18030403021804030f0503010803030403030b0f120d1b 71
    0xb00401000c2c0c410f030b000844010ba11204001651591040c0002900320380302001081803070003420081d400f02402443c002c200d0400e10510020f9980066800054022400d00c9aa035a1002c00c16884c04003408401e035603d580000b0304606040e038403000c41341c02403c168045560300320318188283c040d40d8036003002940100f91200305c0c07005440c092605068013912420302900d0701d0411404070300e0203000b503000008250b018a5208000003020040034021f80401326544015505210036114920000c14643d401c4940200340405000030581a0104040e4810101d410070805854040e40700c01b424070742503500c64a40780c00041d40729001e1004030401200d0217803250b02d546c0c48010072400c048404180080c948004c0c000400182c80780400200e880c0603140f0031540a00d0309207030041001c40385903a05804c014090004002c00742002003683e8110b5418103000c16500d1840c00401d1007942d400280c0c43e8450040d62410002080100d11840940700a0351444000360054911100d41d0b01ca20b2401402a0200b0b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 702712841 1250 702711591 702711601
    0x212010f27091e02090c0a0912020a080304090e0d03020406170405160b0c100b0a030f1b0b0a03050c0a0203041a070c06201506060901030603170d05150306 68
    0x4081c424484020031400191054242e100c4100c1e004102600d030354083c03290255001549403280038940c3c841c160720495171420009500c0140a14082d100d40140740159507100c0d0115039514803c10058141c1904403134642d995910006d002d80340103c12450a4001e05003c040744074030038000c540c1070712055107641e1041c03030080302402c03858a030040043d107050190f10356506604800051820082610b854202d440ba4035416440d030a1a01c0c00c1c1c0c0f141031203403034010214459200c01011800301d9400503211103220400f03040c1690840c0700d201c02400c1c080344120f004030710013102001408805c44103540402036551010341c40c0056108081035900035034000e01c0100120180e0081c00b45c0e04c201c906003d107040200a0341e03000b00c0b071401d81d088000860401c103102c1d0301d402d542038401c0b00f4040c81c62000380700d00901c0880c0c80e00fa049000d08071a00590001480c00700590084c3c0040004603801040031a03032805034041441690000d10100c29039078140360204410011503800030f220f0a0001707014201075169 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 702714091 1250 702712841 702712889
    0x6180317070914030703050706031a09060904030f141c0c02070b0f0705031b0a0302062a0c0c0a06020c0a0e0f06041e020d06030201090e090c0609040209030a05010212010f 75
    0x220030b2420313811321a501010000034014842c2c08010b0a103030303e0100300e00c00441d4401301e418510b0300c002c0d4005c0d00700b001003200035030700c00c20780f660807a40504040020105608007100c0102011407400d221250004210403003048d5144071074a140583c0380f00700b0200c94480d5081b0b89417441c500c60503000c40014046109030340358100c001c0035210300c580100c82c94424040240418813000e00011441504000710300400d0540602c00c1940c00070701207010f4040c46000040c062900c0046105500211401091000c8070740230030084030940d040003e11084046a45041c001e40d1141660021801640e110f40300169075281c102c0340901440b14032040c40015500c1100703000081c00c00008a15101ca801003d4108650445c4014440c8004950010a040c1c1c01c50001420304030b4158010805204240c3c20000110b00100d0250000c10040f00c0107980c2d420444001400b034042d8841c020307814024540010100130055004003c4480c12200b8036000760303a07401c501819100c0c0c40c400c0700b4848a040c0a00581560 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 702715341 1250 702714091 702714119
    0x30f0807090339050f0111100b041112160c0305070b04020d0b01080a051216020d031806050c07080f030a030207030c0b0408030403080604061508060d061803170709 72
    0x5000582c03070901c029060415407031605690b0003903012000c1d2442c103004ca42040146892420000c0c03c050a07450012248030343d4508a4030040c1980039500d1b5820041ea6440d900184509500d0b0303d09561600c000c0441b06080b54020b4480702c01c001c0d40e21a061080038014414039060300d4158a80e5070901c5034a89900403c18402003080380c1c0300c2841928800000c0d03803450fa0381d000e00786407401040004460b00e0068038000c0c440c0300b401000740c014403407543c1e1155050407203220241d041e500540c0901d41ca04e01500d90207411500034400b10510b140104245e0741c06805072000a031110100c0e8900c598840030552642c1c2a1040050f20f40c004000c5000c2480c0079070010031105200340303015018001551512850040e058808030f0704500008244014103a00980c0c1d036801c074a0449041001618145860000f21546160f00b070511400400140d4240c0c1c0b4030100383c0f24150400414081060b40043e160580c1003103200c2200483c601d07000c0c152203252940181445000c1a031119080c081c2400c2804003240 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 702716591 1250 702715341 702715373
    0xb12010504060501050417070807060c110315040f05010e0d0c1b050a230d0605070806011e03230f0105090a020309070b0f1308010f0b03120307081012030507030f08070903 75
    0x8452008001074650040050ad0001e000c103907600e2000c090546404940109100340c82c5200380d200464182000c81d54403006600903a02007041e201043c2e1910708240940b0404444c214035010300c14880d90041c1d0080c5000d0710320303441203c038554640c520310528003819141e1700a10350000c004480922000350030040701c9060700b0005896103600425100003801085081c20226510341d10368040c402e043da0010346081d0011424240403c40844250000e11120003400f0302c0820075885101401091204c1d403401500100405001c803207501c1c0551120080460a12401c0e01801126000406a500900c00e40740070341c0b0304001411003145800c040860170f0704801c02c0041740710300400c010820805191101d900401541001207401c0621513410700446186403c0382d4001d0308080d02002070070300c80004503540220241011001916001000382c520b11803501300700c0e601046880107000781900306018000c864401e6940c55101341d4190030498400e40151000c40105102d92070a00000380b201424190b14 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 702717841 1250 702716591 702716593
    0x60611010c031b080417070c0e010e243c0d0302030a0f05160605010501030605041404080d020705030315040c051911160f081207020616020303070c0b12010504060501050417 76
    0x800c0c0412400b507110f1f240840c2c50540c0041d080290f004480140b9004209003514140289803080d050070384162441d23804c21148441801010403540c448240358100070a00c0b801c42004508545141050150300b0807640d400048e0204c07204191a00d80010700046625901442c100300c9484410340340c121000c0307184010b001c03042c45619000305c00e50448010030350180801140c207525000c0050f08460703d039040035005a0420794080c1001080986250f00241e0005d80c095841f118524110001d0207001c4c0010140d002c000213100030320261103948458100d0488080000d84821542036445206030f0550341642c032020185141c886015158402d04004458242c840c80301c0340300f02d000c90382c103072942202c07920b02c2c0381400c184200ea000704003045401ca0000c810500d41243d580002d030a900030105103540301d803107150021085442c1030040d82c0301d9075070040410034201e4555a030b5400d40c4d0031450f022003034191120b0002a4170300c1c20380110780031980182c580514040c01d00c80b013001c075000c2c240840011 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 702719091 1250 702717841 702717863
    0x5041a0f0304030305070806151b010905010603050a0b10050a12030c050102030a060602120c0705060703020106030f110103051e0a0c110d0519080702030d020c010f060611010c031b0804 81
    0x1800c0c0d50180214030880c401d035000100c1e480c207520054022440545114000d11740008050448845e0354201d07043c91803c10070350f0303045041c1c2201c011b014201e040002041542800390001c00c200340003c410200c0ea1260b40c001d0fa00c3e40c0c0700c00200d83c01d5482442016400300d0140010422111140d480f203400900030304d06090000304680b200303030a84c0d0081e125040340542d519001c0081c590b040c0103800c00c4041c0180054604454030070005d55400440c025140b0640e00011213204050003544100000d660201065a81c80c84a05000c05030340d0061114a022034103060009464441c02e41d042d016011603050344500750748603880c2d018020710008005a00b8003108800325080182d080103080841c004d59507906644c0c00225082e00111984584060240050303041800321003600802565101c40a500c00162540f400000d190b01605456601159440c40e01e6004038034564800071444500071680004d02c5030403021841102152408a40340b0040680444099000b178854404550071a00034ac84641c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 702720341 1250 702719091 702719107
    0x706020d06032418060c1b03031a010f0807051e070501020408010e070e01050108071419021905060c09030c0909010b1305010e040b100f0305030c0f07050105041a 71
    0x200311240c0340c10603030b02e6501c14444882c00500040c03036401a0f0200080c00d100080008000f10300c030302034102c0010b214640ba0780710b20312800c1c45080f000004440b43c0e00058188403245c1806001460707007500660a110076a0705004c20395001d04100d180b030070400c3d5102025691803a0080720260006020365441c1c41c044540d02c03003002505d5000e020320a0081c800169120310b007524407800c40300304c03221150150300130200c204803082c2c2c40030f02181101c40a00340b8908907a85c0180403a561072820b207580058078404511508035001005070221080b40c107808640b05202e0b50303242c441c80c80e41c65a8008005511170000984445408000360090800140c1160a4411104001182c03c4001ca4101c80180e6445480c2d01051819124001e44800c01500400541d410081c480c01c1d1104018406005805090089003054404001020007041a401a542d030b003500ca1400c207440f9801400c00300d1507849070110761400840c0104400c4110340050710b80501e172624000c555028031000103107110b035801081c00100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 702721591 1250 702720341 702720367
    0x9030c1204080712020607060b0414041112030309031e091c1515050409050f06090309090a020f190309020312094e0a0501051905060f010302070602 65
    0x40504800c280086488a050945036454a980703070b4056007140405002c040c025032100d0382103074025600880c1c0403911507400000b0030040d01c001000c0c0d210700d90403802040140004101c041d014544200d400000c81c1c0c0c2c40c0c0d0b41035640c2c1d0200b541e10080c10b8204000c820421240889001001c002c403108260805c802100020703400f500344d5401c110108805440941000700c0005e201c1100010880c003045802003034001121720040d01c0c01540d00641e07980d00600c041c41000c0014010041e800000c9800314501010095141e400000585008107071840104e2030090703060003560346200d03040c1141d0f4102900c00e12040440c4e0108812102032581d12032001002d82c9003444401d84861071502c85a81e5056a6410301003d84c05e8020550b4910b00a020343c0d81e900004030240e001c0b00084051160031030241c0b0b85202164401407075000010744100e40c041030400c6810b4000394031500700b5103035070001e10607001c400005551044650a60144002a0b00c1c0c2196002e075003d40a402c0c00b42c0c030018109400310440c1e07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 702722841 1250 702721591 702721603
    0x120041e05091e010b18040c120603060c020c01020120210c0414040c020a0212010f090b0f0106090b0405060a20010e0601080118020d030311070803040c0501080405031209030c 77
    0x603500403080703075424080350444068458010145e60b106680340c507012200c440001c400c080c686602c02c44d140c00c4078485081c480e442c0850502000d98041004943d203240000003444003078030820241c0a0810020007541c018881c908401d8081d60a18110b941d8a803240d1420350b01c10401c14109036412504507502d803a5413214644900c034a0032849558500340010b90304403110030241203224509181111208550200302c0509003035042e40c03100c08841980c403801c2e0142a25078106041c1624020721007050010000c4040d0041c412400003031a0b0f03076261034044030b000c925805044c4140d001000100090b042c900000d04485000b8a0181210011160103071003661004624048503911031884003403140301400350500400601c4001c000c00100c008840414494441010b482006200107c4080c103010741c1100c1019a046034000d0369554071880c001c001904107403030035640b000f001c100100b21540222032245c02550003074025400c3c145540c0c203003112004020301030041c5000038412039988003030030030603 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 702724091 1250 702722841 702722851
    0x9130506011404140a090504030f03050c0408031c0605060708070809040605040518070608061509030a06060e090c060a0c02060702013b041b0813020d0b010302030120041e0509 77
    0xe1883c40b4803506042000f60b10b0940c2001c6d0519262400b4400020303003003242c0d400184141c1c18089015610880b2280d0103000c0c2d035200400602000a0b00c0d00c4000c00c180f42c10740c15000404c0c0030000d068072070301409860b01070510014004401002103030003160221016000c030410080010504039203ea010606854060701d00702c40565024500c0b00482c1d0080c00410f001d8030b041c1c500b0308070a25004002458585400001e1496181c0004490b405910140312850000ea044582448601d0b40d500c140040c01c902181c0c0f0340580d0088044491151420f03104aa01141c4159a5a4208186a0200403080d806202c0480c180203942071002140b590015000880d4036559808108101c80420070414603209017a030309100360b240c11503e545000f500d00d0302c52000c0f0f100e46020744050345e49400e04da00c092034200001e54000040c0d03380c4810404040410b5058900c00d500900801981b0b01d040c000080000d500306014120900061041c600100e13045220701d034054580e024001d03034910100d43e60b907400b554 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 702725341 1250 702724091 702724109
    0x9150d060906171b0118080d05030615040e040201030e19080315032d340602010203060d0b061302030a05040b0f0108061f0305100905010c0509130506011404 69
    0x1800f0400800403902d03a0601d121508090100e84100f04c055803441c114602c0c5072810300204205400580e03a010b442103015029039811146440010b1101400d160411201c2520843c260a4505150310444c8140c80c21295451407040d103c1d240c2e07900560141c2040b00c400102c0b4070032010019110b00c000030b5030f680706030b0156510580d03908001c2245212603482504980c003d0307201c142d0b00426070110420207000b58801040d500081e50500c3e0203181000c5500d407203984440d00c41280d0807901894030062043c501202034801301840d65683c810303400e03030204070390080e03000703200c584880003180c4203000755070307103d0320042c5403081d4801c02c56408800c90b0001d43d0000f0015a858081004000001700844d81000b40718a82200710741c0340c1251660b403490024a26031488108121388204051007085131006141c0c000141c944404d030103100e02c402040d4068003500e0315801c02d400300c24000c0c00b41040b10300308140070b04078214085120558502401c2c0140100d030400406500003514154104007410288c80141 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 702726591 1250 702725341 702725351
    0x6030513050a03090618050d021e09040b100f05240d290f06030a0207030c080d0509010605040506031209030709050412030e010b06070308060f04020a050c01060909050309150d0609 79
    0x400001c0c00c850110641b01c8254066440510542d6502180940030950480da0711406000c052b2401440044591403d5040058081404100003244c00325601c5501c0d400b841c18626035070703000001440e0015115150700f098a004004044801408076110340c6100c00c6d2140340360041881881048608424030010024401014035007080c890031042420254119240c4911203009800190240300140c81642c200c0e50005510b0101801201c6038484c03590481c20168490300d442d1f91200182c401140c2014055182c00c0001c20545028442d55018820180043c80300d98503144030005107600154000e03a2611820700d000400754034a024040c031030341c8602c1601c1c4589121500c00b81c2a20480800040c03664145600200161111002d8801040e010300c0c00102c41e8070742c800414891050f18a020360890300000b03082030100e401100401d008141a0001c0005964481c1070f00121000690000d1181e08104441c500c0c1785071114140c148104c0303601c40249056040031a050488003664403401080d5294 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 702727841 1250 702726591 702726599
    0x3040314030903071806050a23041119020c09040c030b0c0403170f0910020105090d0203070507090c02030f0a1d1c0204020d0b0303070f051c0906030513050a0309 71
    0xc0c106003095400c00015800c20401600007600e514141c052401110043d8203085c0b58042d16030040c10080c2805040c030301090351104041240d10180204222040301c6a080c901c1d030508140c450065112407003c1c10320f04008407003411038000e1000d58207550442c41001c1c41c1160640e1103290450155104d440c4001456185203025001e0400c010308081c3c1000c030600c0200003064180280041801204201e81d80e921294801c0d0fa05c640515100c0c0c3c2c0d00032605c0c00030883d0482e0150300590140581100b141c1c149504c10404076580e120f0018018526000203030108003400c00c2d5048031000b81541c0c010f40e818070091200300b4034a0b0b0400c10200b0f001540060344c51036980c01d01c1041e01c0f041c20050342c00710003504904a8903049070b4032804000b03000d140e00007410390b900b2032507030300c6a04007080081c01d0783d548900505122600741e8a03418152014080c41c5100c1200294410804018411a440304501039107012000d40044c0001849030100740c3c500080c0c02c00080d001d1000900d01031003525130580c41814 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 702729091 1250 702727841 702727853
    0x1050c07021011030409090206041d01090b0d240e12070c09020301061b0c121b0b09010206070e06040306110a021b060418021b0303040b0a0501050f090a1508030403 72
    0x101e40161020300c91510070b00c003d404004030846064490141010a44403d02e00c0458054400e0b079004080071026070072021040c142001009048030807444041c000300442c07108202240001d408001c0160100600300e1a207220b00080d51011000540000a240b401d8501c0b45420311040d000310102070a03000504604010514040001403c01c102c1c2c03c41c00e40d0305000024010403000c003d10309002c00155402070800c400450018041c0401c000058002107140c64032042104140c01030039411b106d612800700300307417441c4000d4a5814405074014200ca0716110b000752007000110540c00d4002000b0031010012601a0107901060b07403801400c1540c50201c120000e0801d54940a0103000320b00f0220001c40d9950340405480503181c10541c00c0400141c4119507600038441c02850300300c4a84240e4038205556800b01c0594850340c001c1011107500e03034820043d03034202c40c0240182507212502e2903100701d041c284480d0065100c4407004000510807036403480f518040389168080e001941c0001018410084 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 702730341 1250 702729091 702729109
    0x302030d02030d0c1d01051c1b17060901031e02150306041802090c0c1f0b01200601060c03020a050a142505060c10050703020904110a09030219050301050c0702 70
    0x10b80341c90030204d50b000c10780c070502d88844a224171a0400c540441c200e02c07207510385002c000701034660640070800c40c81daa2203440c80103250300c00581d000c504011890001120381c03911091066000412803003440c0e00396625020100700e804104075108800e80840b10040e01c0d400d851601080d08051f06c3c1d0340324a001801c11040d03440741031882c0c1100b4000039105005855044280750011410741c40207481e810001c0c052071901c01d10901c4401c040a8058060400c115a0b911041e0824405c0e0396030180d01316000025205148401e0752954240c2c00180108241e038441d555101d00c04d0b2003803060f07c8068400b919140c0c902500448c060310703004042185100f01c500100240c8004030b0359030b2000b0a1041030140740810031000d0384101406420000b0304030500720400e201c004021a150300701046903003070006005000303400c0100410b000720300c2c000020b0030f5074081100b80d5502498a9492298850442e401d020703400d443c09802050000000038007003a41c9e0303000c0c002c00b8070542014030020b440301c8842c010080701c0c0b1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 702731591 1250 702730341 702730361
    0x91b0d0c120b1206040206220306060905060102030c070e0417071b050409050304050f011107150f2c010e03032d0901080c071a070c02040b1f12060302030d02030d 71
    0x51000c0c082204030810204680e940150120360040e21034423582001c40d42e0928042c1818000c02c14000044104480351740000b0030790755002005c00155640000582e6a446043e6840280ba4000e00b020440d41808d110740550051154140d4094000c8103413020030250000441154004080540c950202420311340005c02848200d07018070103010300784c441e07549034441e074000c01d402044184403069990340200360740d2000510600844007150303940d49801a00d6054000d00034001244526014085803160100341403032502003408559000c07050307007000f20a048038852581481001e0081044985c0c0520203440106c861001c446544840071890350603941c2c50004c0d018100405100b4480307140d82c81070199074003980d082d110700d58403c0d6906040c54034600303901c041010418050304008500303a01100e410a082d1080c0c405006140240041040c20003c1e4002d504040381c0100c40040484d2082a4a04420120101c0000c0fa141c59402003400c000c50544154056840020303041a00e0045100301d000c0c130 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 702732841 1250 702731591 702731599
    0x1207211b0e06040509090f19030f020303010b040b090427020307050a080d050309030c061005090a06080613231612020105040b0a0512010e09120405091b0d0c120b 71
    0x91160340d070005425004030700403640210070103800941d003032000f00501484249034500f220b082d41f203041d42d04a80780c601201d0032800240078050340c408050001040d24141d0f00002030040c2000e0a02c2a2a04a43c2000c02c2c107d5005841d07600040d03858104c4031100303842c078070004002130789040940181890240d07554452030152101c500108411103020513407040701c0ca218540159a9251803046070b2a501840c00c810311103000e0513090020785c8182c86c0c04a402c5503010742e1080000d03038403052084116a0345100b086816045140018030380241c24050100107441000c1201501e42c0740094502131086204c0001410350003200328102d6111a000014010031120380000d0221899900007402c50142e4841c240346c54802091001c18207010304290b40b0520201d0100728850340c2d641c408062055019182d05040c2c1c000c10145d0400380c0350003011242918006000700a403901c8660340c052800200c0b02016810080500c100d0401c0b00090041c4080504660b54541c0d081441039140c00490b0144c01c061842 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 702734091 1250 702732841 702732857
    0x30402060d0207020105130806070e0d05150711070308041e03030212090a09020d091b0321021204060809100e1b06090604081f0b061207211b 62
    0x503039a04084031452070381d612016888899910043c2c03a82c2c01020340341c0c40306d100119008520301500003811845101155603104034842c01d0b1080c400360142c0880081c000d40c0100aa005044000f42d492070341048042c509104c0941005c8860b6041482d250000c881c2840c001a04114004800c6501114408085e0420362041c1c0303945da01a40d100c0e2a1034142c0000003001c0340c88101c554415030124014a41000207554a181e0400c0b0300d4001c2030001401c440360313020003c400d42180e105a44034001c0d680d00081d2001841015040e2100d08401d5101940841c4200c000c48000301c003000300500005e01c80d945441c0000d0038440440340c14030210260040310b2070300e05122580415000034100403001c60185c01c0540c0e9842c0c1c000410540d12440700000e42054001074002400c2c0000a68108800a40c3c5100d240c80c100780c680c040180c40e01001001d41c4034005010035443c2041c1d0746986074000c01c050a181c500700c03140e103079640d03000d04484071030144403503641002c0e585102896510481e1807080386001d0700d0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 702735341 1250 702734091 702734093
    0x193c060f0627090218090109060506040b090f0402040f0611012c0a080c070f050607050a0b0a090501090803160924090503031b0706052a1603080a11030304 68
    0xc0072408402d00c55841c28844500b14210000001000c0043c2040201c150740da40724464640030642000316116020f00050f1000003a080b103a849100103950300185641d28041c030303144070040c00340c001880c101e1340300c580210410001c1e0380350310050004000007004020a40c0c5040c4000d0440c02c00200c6441c283d03410008a44d000b40d9a45201d6601c0c016406500b0b030104c1c05440c0d00b0761a060f90140f0081c850400050406c00005001940d0340071654220a0703400070544a500740700c52400b0f003582c01082031b8040c59940000840c0304440030361103080c4c9000010302c0410354580703e0a40d040c0c0d84065a01007400010b21140c030f20001c000302010302003800d00c040d9440c0f5001d0561a504041003101090603010b4125841c0d0601c6200108000e02006044a031106000002d451030b2001c40011104a4402d640c5c001482c9801501550565241c03c0b81420001d050f01c90604944641603040c0c495502401d04011403801e0002064005540036000a80e10b90880c0100642086194050307030b0519402402000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 702736591 1250 702735341 702735347
    0x120a29010c060c050903010608010b12011b05071716021002150402131424030a0507120f08030f070807020c0906061e04120201080609193c060f06 64
    0x401c003a0303100d9000291418074110489031401144c8000740d143d424001c0000b148041504044451041140d84442c00d070780e100491130032210644080341001842021171044d40b07018801402100f8010032030009828081d82049140d54071100c03140c908250312099001c19820f0000816034401c20f1800188081c0001c1451015101c0c0024030080c407078064184015900002d603007003c0500c91211007140000e05041d100740303074107000c20300180b0b0070a890b226030380d0418600001c80445141d08240600900390600121a0f6088061042964542c1c202c00703108000485480080d8400c50401103d07401c1800c19072401447d03401d02420010855100d20407246082e910303000b800790021400c5441e17550360521002d01c2c60042e24046004008124045400903840740d2821114030041d00c00d0341c4024103541d541080000760a01512088543c416004a8a28850281d03101d103801103481d0119450151200c955602010b251011036550303032026009649101d4140d0082030040c20a14038003580041c1000001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 702737841 1250 702736591 702736607
    0xc2d0914060a262a0f090c27060d05040c0911270d12030c1407031d0a0611010608070303270b030a06061206030510020a020102120a2901 60
    0x4030a000f41c508440000d503001c10406001000040741c400c1c16440140c4010380c40380c40d001d2101d6030040c0c81e2203294a03405d10b4525076141c800d5030a0314440e42842c54140d071580d01e5220081c1c560319181d0703440d0500000340d5650400b80200240051010940d4a0149488014044a0384c00740041358141880305038452000003e44440400901c4510304000020b070302101140e0b4000a0142c0000d07114504030148900c1c01c40c2204050f126442c01c2c03149807a8a9001c84141030b0030016880e0aa00074411a03000910650325610100203501e42ca13a0748413002000a043c0c1e0310160700000114078003009822041d1001e0042d100244001c1d0094000a840c5803405080f20100c0c3c1c6080c02080550301803620035981090883d409413070301d00415502c0346001d0150100528a90050402140c1e0039810418464240d00414060780c0c0c0c0400503042040300d015041000e034102054110642d5000d02440030700c548503254252081114840225444464286041112009100002880b070107250240c20301d076001404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 702739091 1250 702737841 702737879
    0x5100f051830150105031b0d0512040602010b1206131407030503070c2403020c070b0310060f05031308030c040b2d04030c2d0914060a 59
    0x60286401c141000088842d45000e0402006007080c024191810719010404a01c8040000403100001004410180900024400c3c00d526030321990405889141d001c034040090100171709007800081c101c0d40e0302c50420160385e10700111101302050820026509002d03650240740d06481035210300500b00c00b440e0301e030706005000445403004c500030802080241554504140581016200250384a2403c2620b0307a001180a40d0107041144010038040b550201030450003190b1142520b04d05040340c402d0303000c0c2d0000100c001c000d005908000491101510045100391a1480e4103074505060803000340511890340412003c115080c0208407442c0840c0715a4600950843e030b402d922642e41d41c2003003880d80b19a40103248031280101d106486441900000040c1000100490707116030303484d0580c01c0c40740c0600d1002820018404904002110100031104200c000e542c4001d074024014121040d481103c80d03206d0b802c010360721000c240140018611180e0040c0c4222402c07007080c5c0c070742400c1341c60346021051 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 702740341 1250 702739091 702739117
    0x30f020313020109090c050f0903070503060a020706050a06180507030e0109080d060905060901030f0501230405071a0913060f0e0a0e0a11040f0f0e0f0c03010e1c020c0604090605100f05 81
    0x10107241c4ac1e0340c03c001880003000000c04a030400c1c6000b5105001941180104540040c02c210202c0c800080c280220816584c00d400f203003c140840482d200003a00e0058011402c0c10740e00c1134400c10b205028014002c495001d05281c680d40c43c44503141008684580d808020094a844203214595031031501c4541102e0f0030001110b080801820041d0040116103100921501e81c9002054580d0b202c2c406144214080d0055a1510360303a4420803c4112a080b01160180001c01ca203101c0d610342107000250880700a040041c0303e54861009000c8003845030084071441225004100d10300f225401900135044820001e401200059519284121064640240f01d1600c582c8140804d041a80c009681d00c400c04406104000381c5103001c9440348941c90820440340074855040100d0b041c14000ca140c860b00c5a00240b80758000d0201c2410010130388180042140140d2096008540e1610083d00107029250000035090346020108028503007840302800c1401000030342d803210260404e080d03e06541010f4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 702741591 1250 702740341 702740347
    0x906181302012012070507090204060f1704031209110301050408031909020a0b0d1e1b09030b0130120f1106181603050c04060605040b1801030f020313020109090c050f 73
    0x898151f04010058002d241c4003840461300180c4198440b001104040494444124103002c3c22200202c030101180d014000c50000f003032020707081046a2240c01447d025510b107440800c01c500010303081d10b074280c6050b03524520110a2143d1600303050b02505100c0c420f2442048403a0686e404181c0074a510300c17031004000e00100c0c90a00c0e100703680c1c10010070a09029143c1860745c3d4180c01c00303c0281a01e2079000c0c0c2035070025040d010b005005a1503801500d403c4462001c00e07a1801c90032009030115a1404040f1884900307006514160400040361040c0c030552894981c0382c1401c07001411900f50703816440802c00d01d0442240784c1b40000c00d0b1950001521120903d00b03040c1591410302e40701c225001d140c51084242000418802d022442800001c0211414050150f8422003282c15000354043c02011030b0302000014450b0320b0703890102d44201818100481c0000c84083c01c403041780c104032460032450100c1a001000c6613030240c00e000c003405070b441d01002234803c0c110b0010100e0040c1c3c41516001c079400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 702742841 1250 702741591 702741593
    0x506060409230d2a060e070302100504032006162301051006110d03020304031404120201090530070305030c070e0c18090618130201201207 61
    0x2401c034070714950000002c10001c0c181010a0f515542101520006040d4031500540219030408250340001c11513a0181003204645036080104166009034200344600800003006880e80c48a4211001054480980310352131410007000d0348c4d00c05035002134040003000e914515a40c0d06000d035040a0541700c5400421000c45c03801840f41c581211120003000e039582204036607090705401c55881000030f8248000e9490343d9401c1034800c905402c41e41e403071307541020b40111442d900c260301035540240203107044c1c600d0482064105007140c2c03040d0007041c0840c1c00b5040740c03001c2d960450b04001c01440c0980c0c1010000c0300d10400c194450f60300222101c44c40b0082682d003e50a48100700d00406190040d0640f540c078107401d900301d96100b9043c40780c156822203c1c4000380f8610300c248281c030881111002c0c100410130b056001c01c10303200c2004150a60103000401041700c01c1c10490318080c0f0401044c1c0507040710412a0001610440368000c4807001c1101c491031011040d0790220b40d004c544540050a1610b44000b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 702744091 1250 702742841 702742853
    0x3060b04110c1e15041205090607030e0306060d170c0a0206130602160b0a08071e120f020f09060a0c05010e0601140301021801050a05040b0301140f06070506060409 72
    0x840390320001d40c04000c01c0d800d12411001c964509030161002e1408900031400c80910303140c500350040004043c0015002501140000402c00c0c0030803220304e0b01610300a800b400051103a000854154002050180c1d000258202000a580c10070000c070340000501c2c00b40d50718403d0800c6421905420351001051a10b11010100f1007907520541c02040e02d5114540b5103540c200210f243e104035030052007469080c400d0030a8030701a141c01d1f00c490201903454024004400e861050014204d20104a0320659600500251007188070846010707640300182c100f0411030500a85201d849544555441001f4001c045a0070404960f1004402d60340c05455104100060740d400000c000013400d0741d401c05481019014003c40c000341641c11951303c14100c1240c2409040c00c07806401c0700e01020090010608000b980200043c4c42803580da0328000703140980f18000c04070660000e901503036964144260130b00f114500320340e0242c800081510058103108042d00c80d04d9823036002400150103a40e80310001c01c14042 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 702745341 1250 702744091 702744101
    0xb1912021c02090306061e0f31060609210302161d011a030718080d05030f010b0a050f0a0e09251803150635030a0903060b04 55
    0x7689203100707860001c80144880a03501c4104050712901901001421301d180c03d00c0d42100c0c1b10381c01c241c00f003c0c18800d001800810307440b0b80320950340010128080506003628000103030440504401c48100c09a0703003801101034a020381c000006000c8812400d102c084d07401c1691000446100d850402c02c1e200c45d003000d0742010800c5c1c5103542c4540c0c100801144440080b030701861029a40c0300f614032240e03641c0305c0f03903001103810442114045078200045002c0500c1501e044c0300d01d02c0d8403980c000700c4960b00c05c11a480c00c1c69200360315001c00c00100800580410300e450550051003100080c03441c2010710030000300148101c000203024450f0110b9010151307881203000ba071207441e02411188442c20802100488241044100e0f407a00d041d0050310088244115210744007186294a640440c07815030342c83c0c8261050b5200a410031641d01ea5002803462039400c8480d8694444030701e51441040400c2e03407496241c2d1600301407041640208004ca0249038084c411034100da0304100001071025020340010003804c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 702746591 1250 702745341 702745357
    0xf0c010e0411090a03050a150b090a0b120f0705012738040312171b16030e01020d0314010605071a04061d0c090a0203040203160e060a0b191202 63
    0xa40002c4d004020848000f4517a0740d82c602645410040001c0a612041038500403c8920381200b5582c011611800302504001598640107011019a2030881401842c08000044082c032aa215031010841541c00076592070040b8242480030411010081040b84620700310310401856818400144403008ca00c2e10341400e01c184400c4180e640f5044607182c01806402ca0301080e2000d4210043c1d450200d0301a0049452042111421400c280c1c0c036511911130041180b8030001c0b003040e01308002e01846d01155460608140b003502c90400b101a00c2d00024a4034111400b0b0100f81450b05010028400c0031520040c1103c1c05450240e69607841881c000a000e5006240c3c0218400700605210400119800441c080b40d092140c4c441205120b4038401c0c2d54039443e009a0303400621880c0451016481a0011036003d400502103c00c1c0501b1590055107020752903200d0a4540030741d03024802546000302c04280108030042c00f10b410440c0d035003881d40c07000351201c3c0d100060007907a42c1310a400d0300194050342c0101c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 702747841 1250 702746591 702746599
    0xa050705070e0406140106021605100c060509010204080705010c2f0607050f0c010f1704060905060106030e2b0e01020f1504120807080f0a060b0f0a020f0c010e041109 73
    0xf81407034a858005000d200c10403c100340e2501d030012031039a100143c10f41c519603800400340743c0b151510b8240410140040809000c0100600744280410001e00807180505516400182d0311440d0001071801e14030150080ca0420803100c0e5442c2c0407489411110040502c1024450b0710707410341502e003d42104c601c0c80704c91740040b8049522001c1c41340105868002c58001c00a0b500442450340044541501c010880000706003a0b5402c50300000072156410b91042c81450005142c44c016203481e460610240d02502c0000d40b00da009046940050003000d03a0750821940c41c07000c94420541d45001c610100b00c01108004985402c0c1680e85e10800000750044c0c00041901d060221255040020080480303041e21418500302148006c01d2081c08440d105180d0350356034142c25201e2054024550384007030050720701c4c01e4940c0c00110f140e10040c0c005140c52101d03211200d0303a42d03511290180c240109a59000340580040d080020641d0300720002c1c0c0060360084500181c5840c1c1c0042e40c500f1070050410450b08 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 702749091 1250 702747841 702747869
    0x10206060d2010030507020f0f1b04020403061b090501031b032d0b0117070f0c080708031005011205060a0611161d0115020712080903010c0302090f030f030a05070507 73
    0x401c40d01a40017a0180030590b09482c04071200710080d540c0c2c0d03100745d502e2816640c440c11402117140014048407818640040025142c9656520340c102278a05896405440410074510600b0340d640040c2d0380c0008090a08091003506045c051000085603002d07814010b154581441c2d41040501d03000b1080c041c03140750030702d00c0b10340100340040c40100b42510b02e260100d01107600c641c1080c000d51316240d104a0f150380d07640340a801c3d412421501e21403002022640302e101845031000080d100c42c083c1d44196401429030800700d10f40350004101000c402455031010b4a400240500340d1140c0d41e5510039a00c040c00c089040039080e4880d42d141012480e0700c0d540d000c4100c84042020b02d41d01c61241501804901400c94a90f00c2d001c5206e000260301ca04600543c2c480041001004091020360310030b83d0241064a09000184000c242900c003040c00140000e54001401580f51401d0f64130141c1c6030809a000301100c1c5404000c1554900c581110324082c84004510141000030400852001d070969968540d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 702750341 1250 702749091 702749119
    0xb01020a0609033b040504151104030c03030f03050601031406310506010e1804120c32010204080a06091e08031504090b040609050111070f050c010206060d20 69
    0xa528900130400d5490781e02c1010b020100d403401d030103040d00840e04041c02c404680200303131500004100810b452074500030207000000200d450b000403d0000c40c000d8407554140c61f04440020704031040200200d040c1840c1c81c448030803030304c41405201d500010603652082800c6181c00700890000400c68507074145204d2540da406000700381c1e0450b41c01032a007a03c42020390980c480030040c44410051058601119800c0001c000c1090745840d03a18200071410316040030350340364035038189114042800c144c906010001054200c540359525500384040f46000314209810b000444e03460349401c4801a044549801c1d00c44280045403511161901d270b40342d07403804a00d802d881c0108480d00700300d079010012140280031364601c2c01c0501a84070101e40c46040040c41c2e41c0c40b0341c0d0700002003040100a4505650f00e20000340c017101c0c960010620030b8028601d20308000301918003545020302100356070b03045410000500c2a43c1c1c44401c0324100d010307441242100c040c03e40b142c1d910141c400d880040355000b500e585160b5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 702751591 1250 702750341 702750407
    0x304090c090e06040905030a03020711090901050f0109200d0e0102401509090e150c0a0203032403032a0721051c110f010b01020a060903 60
    0x2000b00d0700c000c500550039a546404000c2268000c14018109030410018420f903180320b0b0b401440c030148640080c403e400010030105a40716001c0341d202056a5440045c130008072400d0b124a4010b10001d0018081c07442034420070019214004140b004030b0102003a000c05600c560340001c0d2910121100031921a420042d034086000d01c3c4080b10140900700c684241e42000d030008442e200e440c1046034074080c04d443c0c60003640480040500c800300300405080003290404090198100c6040e0360070081094815220001403c40009000303549040d02c10010000b40b41e4002c401c2e01e44c80980f011000c480d510041d03484c4010010005c4025516020002d4101c1c110710300d00d00718002c1103a10051a685100724901c00c9a5a546a80181c1c41c40400c2503100b42d10052800300c8030404148204251590190000690707000d1090022094001c102860f07a6400601d10070402d41400c0c140303450085c0101c9440c280080e4031005010b0016080d01e4940303240b0424940911004071800e22203012411056006221320 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 702752841 1250 702751591 702751607
    0x319290f0409051c03020f0301140402070f05010b1c0b0c0306060c010204260d140f0408010f2310062d1205100609050607210509090711030a110304090c 67
    0x144400c4c041c565200c01d4114840d10079241120345001042c0c0c50b59007024203950012040540385a800703078007000030b00000342d4101070b00303c40d0901c61000070030341d800300808010440000158100000d8a034000e6600810900d21501d5003001a036201181d9984500b4081043d6120780b2415440715800000c001a822030741e0b4500306070b110314141415803000c1c160003a4035200c503100c0a180d800034501c200b18401070010400109030303404a100c1410300c1c0c543e80311409820b44041e0140c204a032941d69100c1c50007141241c40040c0e44081c101048405450888c0c00220912a82c3c00b803a010440d183d0445180c10308038440d14542e100c1d482030303000450440d0510090140301e001c03c141c60158200800700d59130382442034549080d521903407104403000d8100702c140300c0d094001c06402d40303040f980e00100b000f080001d008081107403407070fa0b51000e540c0c1c0011400e00644c80e9000c2c102c0d008101070203400f83c9109202009640880c911441c2500e06001c08082e4075245000343d4002200700361818103014034107a048561 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 702754091 1250 702752841 702752863
    0x50601080a1a01030305091306080714180709060f121a03011413031b0206030c041409040b0403180509090313080a08190302070b04080319290f040905 66
    0x10861500b2030016821030551820300c4000d010a200f8002408549005843c6116002c0b401c200003075003e6580b01c0701c900d08441c80e845514810388801e010360721802c0c220100304c00540203550000302e500b0007040050004945100e00d208008450684580d001e1046120340b440c0f4007103d6040c8102107003141c14580d8600b0f0b40894610a41c80c0801d4200a405801e00c102e1050f8964248400d00c1c41c030907101942c201c2c1c01290200e14100c0d0810712080182d8130500607500413143c01c01c2035521241045d07060340c2c0c0c0e2100c0703903500d03032290f520b6000b00300010700d146000d190300550500e0945060b4141e6410001500b81c9500055404111142001844c5000101819035004440c0c1a4400d8968504c00c240d00c40d18211009081d80f50100000205800000e42c0c20b004041185401441d0840710340380c80e00c114906842c1150405c1d40041400b2491000807090424091034100803c82c0c907602c46541040048603201410a1506c007415002c115911400701100581c0040d01c148800c0c4858a012034895489041e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 702755341 1250 702754091 702754103
    0x306011b060c090914010608010b07021305070c14070305100b221a040b030703080c0f0105070504031a1003060c0507080309010921080103081b0d02010527070b0304050a050601080a 79
    0x11485c84d02800509003904882d810f803564034841e42400503907503080d0300009050b40c004041f41140400189548103061044410ba515180112131500c0c0c84030480c002d6000e08603540d07105810a0000c600c0c040344c5001c00480140c800210084024082000660440e00701e504c0802601d240400c28191600001c240a9000e1245d100351000c5404001c00c8416442e810350f00756000000500000e6982c00040084c440340d502120041280840b68500390b407011103400340000c50200f002c1007044022144c40c01c20200316580d190b024681901c4100420219120286c8040e4585691440070350246046650071600031840555030b103071900100b80a040c80503400c49803170044105c1e401000b00720a4209518020070343d80e1840903445c41e2035644a40c0c000808140304c00110301301c0c18021000404c1500f45451082e0002314683c41d050450004c9160098100c03540c103040f030a1004c4002c00c4c08540320050b01c1c4c588120f0b50300ea455038240645080000c00d402051407245400115440b1400204416103c0c0310745c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 702756591 1250 702755341 702755351
    0xd081005032109010302121302210307061d030a09140103020f121b07060903080603030f0405091f08060108060c16260f0d0509010b060306011b060c0909 67
    0x9024156102e0005107180b034406100300340c10a509204500500c551901450050f0030b21400d4421001140c809642108840b080113401c4000c508000318401c0e05d0039120f558105021449440d040e80301c1c881c8c1c41c00200083c4d5106440304603600360320745a41c101e41c10901101d40b00c001d5038401401c059a07502440fa00389891b208540070940c404d00858105200b101c03042410010114001107004c40042c0c131025240c2c00781600300426481c00b0010b80081d41c0960300200780310000d82005031100070041c054a009030010000307400d81180060894044541c1a1341d54040342d40d40c080c1d216080001641c80340d02c400250000000c0ca0350b800208603042c0d401840a441c07442e1a0940d24035400d2058418a0125041612841010504007080825501144113401c010b010a10800840d50b034441c07017624202c1e00d00440c0340c910080940c4281c43d40003a28500170080d030600380000400c1d03400020801810480c1c64595643c036801a40c21003500ca80c0d001a0911200c20140000303031034030030a030180460a034071708 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 702757841 1250 702756591 702756599
    0x306110409060b130522021804050906250e040501060c0212060103020108010b0d2a031d030d02090d140c041116081b06090a0302070f03081602120d0810 67
    0x50f0085540c101d10201d404c0328203524040c02d01403061285000d20042c1c6291060a00502c800384c0010003c1401800002c114a40d00d0f40401046840180075000b00f640200100842c8010200303110059102080c076180a0240f803000c00c46040c4582c0c440541c0107414080002203040d0441c19034100300d4801c90f03c40e0300c0303000c00f4211295155424072000c0e00040400d001084000348074402808c0100304840d0100300400200c12582d4001c0c400c0034940905500311004070a510b50510401201000705208040c906402d10900b65590244804244900d43e000510f24003660340d010001d401d4540c070941c0400d948181041c610b4445039080407141c05181414482048264940120303415400e20825108460b08a620f0385080380e005025007606a09681a0040002d881040018459081d00c002002e0703000300c82c5002400c0400f150b206403030001192005000107a040c000780c03107020000107404940b80d842d07400018083d030204100b40c0080e004a0b8a440c0c0140d61000f08144100c600c586100d10302d6584d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 702759091 1250 702757841 702757859
    0x170c0f0601030209090d1e03020d021201050909011404060c09031407080d080c0706050c040f0308130801020a02060a0b180c030603060610050f09040908040b040311040209090f0709030611040906 85
    0x106c07840700400501d180d0481c1c8026014110024030317440d55894018103001426505104a80c000c044d4132140c0407880004100e41d140c22019107510044803c0240540707030703180e4446004c40c10301520040c49980c9503180100351034440d4402c00025034111020705174480542010b00d45400c1140201411400b0b400e070a01d03110760040d11258001c1421459540c500311103a200c4d04000c0c1806406640098010407000031200700401c01c0714081d600a41c9881e66640300300c2c8003d094151640d014945590040c04200904d6401190003a8400301c01d40c804507051200000054034419000d40114401d03261606000b11b5240120195208040070350490f40241ca404040000c1703a003a0300c48042c0002c44c00c22001551001141c0580380340b0070040c0001c65500304a80c0c400d14a6085070308141d107482c02c007240400501c4514074040041000c00e40d001c5207844840c0e4081017580a005180e61500300e10000032a00036880354489000440d00058100300c000c82c0c1050f140000e134014403c200546041800202d00301d15 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 702760341 1250 702759091 702759103
    0x70515070e030705061219020a1106061e10030906050a0605270c0a020f03120403020d03020c060f06010203070b0f01050f150d050601051c060f0b0a020703170c0f060103020909 77
    0x10020003403420891200f213150003c45005021001987c02c001d98010040250300281020620340e407150040181e007090120310b8000d000302828440c001d950002c0700000c21742185802001002e98230164000f800350b1082d400b030074402500a055528240c100720303880c5e0496226900303030360f822190840409100040301da030391010314402c00020040030000c82c0444103c0320041c00d80c0111401030b10700341400c0702005811070f041404030070440017801e01000100f40d414402c1078002c0f240b5082c02c40c240002403640d01d948000051000010708501c001144590b07000b0400c0d81c102d25400b1062214601d4a00d40d030001f031100030310401d40128401c11100c4854030b003003c41c00e80da085410709000d0a1081052402000e08009886941400810040d07003010f00e107e10302c1c080b80422695400719645161802d00b50008145901145103c4c0043c0503905015a0200761179003201e8105c02d5145100040c195044403038820b031000301d00d0911422546014450010440754100ea0003220f030740e000703035850708405a2120 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 702761591 1250 702760341 702760349
    0x8070212150a0c440108010f14040c230d06090506010602010b030307060c090b0310051e030c011805040e060603010f0b0312130e090109150c09060311070515070e0307 73
    0x1109400380b854240200c411301100c88425070401035502503d5114209405003a04207071100d07510760000300741d0300965001e02c2c4070021050a0f00c200e24542921080c80c0c10b4841e0082d0008540700000503100341008155011003984010562000c0c48010329005008220780c907800c03603483c0110b40c0000b40981c0184900c0d200c9905c0a03000d10301d400c0e00c035a40c44008111100c4c484d03050141604000c10764480c10005144100f02207419022094100002c01c8001c00b200307a03040c2c0801112a001d10360b25100401d90451101007800d0100d0703c4e40110700d83e1816162181c0086410038544210500e103c40c0c000b458a0140c3d0003076000f00003003032040c40880b043d251180d4001d41c040e801802981304601d000001401105900512401000d40301c0c1c1d0202042c40c8295141c00032030303451301122010301000036690351000768420010044601400700251018030244102c000340755584015102c0105030104a540303095001c2c041e111904640011441500002e032402e000080070200c1000840c1800a814400d031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 702762841 1250 702761591 702761627
    0x307050d023006150318150a1103060d060e010b100e0414010f050108220f110108090718090b0103030206071209150c02012c0f071208070212150a0c 65
    0x2480d610145145581e101a0148006d182c459458240f01c8406020383c0b0f08900b410300c0c0c4520769050440d480b00685604801008031004100103006850342c40c0f480d0520a0360380980081082c440d51031480d0700415100101d180c000100045540350594088110f1040010482c0e041121201c50020210b15520900070040b0000715030784240659030042050541c81451951000145500c806020800d104d441c80d048808a0300c1d8450b0303c0400985a500e043d400c038003841e007c03103d40f40c04000c1c242d0301c0401e80b00d501007010680101403041c0160b0b4018040351504100ca011003541d40f8500207540b07000c01ca811400207149201400081c0a19004018003c0c0d0095003101680c410100308000a0a80141c100c01750340d03807143c100110808124500e00c1700303140550241014800e82055038200f188483d000b4000ea000450103003e0601d2000004200b20303000342c50103803511024404030740480742c000c452001c85d115243c4246841c00305d80030f40034417501382d0100c00d100000140b41c0690b0414100e603092418 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 702764091 1250 702762841 702762859
    0xc260f0714031e0307030f0f0c0209090c0904051c0c080a0e0112050a0c020c040e120a031e06080c0907080f0903250b010608040203030f0307050d023006 67
    0x550512480301090000c001001e0f91800451100800340d10b003504500c2c41c996400100340da2082c9070b0001c1160520f0030365410300021062104500030050329021200034440d503c2c3d07402051085c2010080329004a038050061002400d060500e19a0f42608603d00114040c0c10407112803c0e0744075100701c13100141d005801d18180035804e40300755030400420004070704211801c80c200c51010750f64080e0324010104c0c900d00040304039000d00000e00f4544e000d000b1500890904403242c1151200041e0030085846880415440d00d0001c5030882c0230b002401c00f8a4054051003051480390405580400100c0d410401155410700340c07203003072280540f4101c503104c0c0403d030b065000038051075379202029407254144094078944000026150380c15000412544440381c8001c070000c08018109007142d01400759800c054040f4034056000036580c0c401c04030321889103000800404d07002401901a2500120405419515030300c2c11605100304010500703041010b000407892003400440080d07045401203d01405145d8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 702765341 1250 702764091 702764099
    0x12040303030c030f09150b0405090a03081e0f0709093c020d1a030705090c070303150b03070f090b03060415050901030f140601080c040b0d0c260f07 65
    0x70041c20b20512480615885400e6a420390b2040d206540700907120b074105940c10000480c4034811a00c10426040c055031802d014081441000914078042e603034503181c42c2d01542e84080107001ca014161856080c0e81c02c451040c031601c1d48151942a00c0703001c0b960b80b0500f031f10365030b50209020350b804035401040c207a180c0000c51400c5c10402c003802c1415050b981e07032145140c00701c002c02422a80a85420725100c0c0e980d8000c0c0300c4002e9000c40d010340070741d4100c00418040d41003100241c480203001d4001811440002844001c041c02074109890b1004181e00510380d00f95140c0e0310301842e520031102c640000f02e419034201b001c14010600c1d8010342e600201c090b41156924820301c002030400c5403c00407000100c0c2c00000c1c0780d684000308a400f95100d81c1c210501c84051b4644890560340300c4901d01a90f41014006000c48c80c400a07000c60380e0b02d400c6501003040c0c0742c09008602c0340d9400da80060844160203901186104011480c02d46000b034211403261a118840e1080d0b44a0201410491a80d04143d00401c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 702766591 1250 702765341 702765347
    0xb21060d0f02010225050111031c050612010207050d120207030e09060a0306181106030702121602040c0f02060901060501080103021e19030b10050108040b180102120906060312040303 80
    0x1e04461043c0100c0790070015013041c140940c1c880500032041940b0710b001c24080ca5900076070100860070381c0c00c0110709241c8030200411010071000d0400514590b50380009155688811a9840358540c103030003190749040701d0903d075481d00e80094001d070104141b0300d031940e8040414030032500120b405a49480d40c0b504070360104140c080000c0c001a51004c203040c03011002c2243e9124007000c40d1400d021101d05101d031440c1070600004111482446800c2c00d0040016194020035491a0302d4110b040c01d6036244e04142e024406a00724840180d007107440c2c803110300011600142c0c0205030480b19003c41d00556254410142030b81c0460085334001001e0b10f00400050900105419041030b00394108a45250307028041307884500d1541c0b044048081c03e2404100340081280000e80000d48821a1a400e6060000203041c0500151005000a00e03140010303402c00c945204100c45110210b000b9036a4009000201e0b407070302e4090b50111080c0c010040403a0305841c000442220800901c0002d908151850300c0079 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 702767841 1250 702766591 702766613
    0x2031908010e04120201021c240806150a090c0c03081501020c0405060a05190f0e0f040f03031e09061b02250308070f0308150a12060f060b21060d 64
    0xc01c15503400380a100c032108680c8003051018a042980009c5d0022108410a903c200001c900d070701c80d4a00c064140203040c008607142e0f40c4000001030304550944100003068400400383e1080c1d4000385040e0316080803990000f4101002c6010741c0d14070030192a50000c245883c40070b01416400340c0d018031980021818203400031a4080801841c9030111541d0780c0c00318507400001750f07800c0c546980c070300001d110300d554102040028003500705024806150207940f03c100141c0c0030b030014080c5e0240c40001c60400d0b120ba0400d5100582d02e410340480c0c401c0e5904048060725103400122443c60510080880224031030180d01c3e01d485c85a03000703021480c06e07203c81c0c0c403c103c46020b2140e24610781160200200b03c0040040c6025480fa6030010345016050038002d104943c0030b004a00b070400d8141d644007681d5220403810080e42c1c9510060140d10b452450120000d0500f120b04018207810550001292100c0101030b041e0304600762004001c0031100c0c010b0076091001140c901d94410207020501020561280300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 702769091 1250 702767841 702767873
    0x21e0327090603010b0a05210f0102030414060906010b072906031e10022116091d0117070810090309060906170606091309060c02030c030d050a0b1002031908010e04 72
    0x3030144185000030082c18089c03844032510440c0c1d000400d001c2084031042c600c900c00704110026000c9401c022107819100c0c6070622455500350310100d600d50071f1008a8080c425500c0c142e90a29071703540c6442aa6443c2044111040d83c824090402500420400d034074010146042d8407002d40112040040c00c580290001c0c002c4844e01c8110f509128030900002d0355050040d51881002d402994146100502e00c154a40014456026071919458580c60254074203041d52a10602d9503410740700320240c14a010059408034100d44220219003120381c400f0b9000040e080d000b962800e000f103031038150590396241503218543c001600300e4a282c807280585d1a540c0c4c1c001304c004010a2901007034000141e20f11295200d201c84469a0314080d604010b520b07c903a074420000341c0080c500f0003102e85a403984900a80b141c0380c210740e850b20002488280d181c1c0c0700c003202c009c00802c62001820360a4009540381c001400d4107a4500800300384030074185c001d040040c1214840c001c24212640e4035a03599014070071143c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 702770341 1250 702769091 702769129
    0x70302010e1203190b0d030c021315051908120c0a0221101b051605070b03010906050109180b030a200f04020901021e0327090603010b0a05 61
    0xa2a00d040038420701c0c8450503106856a1603040060340c0c0010040501da01c00c0115260244c0e814507500d075105510b206c40d4050503c0c0004034514000f040c03418541c55500140790303113020309290b00082c45403d100709658041e607070140c200b0309106074000858482d00503903007140e2024814050307004840e0024000b101c81c03001540e020102c0c07039000c10f0307007501c180140c01c07007501442001a0100c98208a609002070500d4014020307030f2200349051182d0f6002000e4402082000602d5100f808503c12041d8045580201141d000655400c0040f2454001780100410751b405e00d400010a0b47c0700324090000e503054200740301861f494071000341d0010040448002e40502405109001140d02008044500c1d004005074418200b000e5042040d5000f0149020303208510501c001002c40c0d0f070000b40003200140c0031072b1a0310300c400ca031001c1d5855401507048540425440010740340070b803505032002e41c100010640d10000241c8038102014262007558110a822140604041201e85440c8040f88c0800089003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 702771591 1250 702770341 702770351
    0xb0408151e1803040b04031401050402130b150f0919030302120a02010f0509010e0106090203360102030a140c120c0a05090a0f0303082505030a0e0607020a14010e0c0607030201 77
    0x60401c50444d00540d02c0b8041c201004a010070a2040054414102c1e080c407600030045031a29a0007d009501001c01c20702c240c99a898040000b522641030358240321184100c01512030300c2e40d0203c3c0442d50301100c1014000e03a6485d07900c0032081340c3c941c0079609484e8980c0140002c4405228041001c1e080707124000115034903048590404203081c030a02e4007030b0f50601e0011503490544007155094400c550301a101c294410020041041100e1800140c8140300c40040101d02420b0050f40034142c140e8070050302d555200000744403006015a20103052503106602010b050b556445106019000700b01c2c1111840c21810001a020241c2100821001c911800c115003403002d4140800d280c1c81081d0001460000701c52000c1c014540c0200e07085511041140307080080c040030780031069150140e12114000c0c440e02001096500140317401c0b03110154034803404c44505107051800255074007803024064442c4800302100a600000c18091000c0281040c401081d400140e4402c1c000c03da030101c0410740c1103560311 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 702772841 1250 702771591 702771631
    0x708040504050a02210103030915270f090203041e110f04110a02070305060a0605010219050a02121509011803210606050a1b021315050a0b0408151e 65
    0x307401c0f17004511089040140c0c1507066150140c010341c00d54000041c0194480c03982d0a40c0d91b804141511000754a512006400d0171660f201050491142c0104800d140c94540c080f0b0001884e5014621440c05025a0002105130b140c0e17110301400c0c0300101800749003014000c0e81207070800c0d5515494400010300f0000b410b401c1c2c2c00292205811502d82c00300144c101d00c00c10000e000c1d040100c0303034000e4a0040104246490000040e686028046d80d151424446507203040c1405414081c0c00c0400b600030f0104c0e090b00d03441082040d2501022083c05030704c800040f01050300300c0b00520903440156030031038003182640381c60744044c1c1b0340303206806060041d8040e040c803960040d505401103100400d03d0791140d03900c41540c1ca0003e480c2d0322820346403130b503c1601e07544c1e024050b90f03c0540c0c00703101c7e05907500e00007100000c8240c040b260030400d4003da9000400110006816140b00c030003441154120000d540301e0201401180b9114181600d0420075090804140800041d6004a1039004a807081485080101c0e07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 702774091 1250 702772841 702772867
    0xc070b030106020c03070e070e10050d020415030e070302011409040f110c1b011403070c060c050901030b0603010320060d0e070e090102031b090d020a090914030708040504050a02 78
    0x742c2001c001a0090010340c00c9600303081250720040c01500c1c1c2c5000446c502590010b0404407616135181c428a00110710030407140c0240200c40b2520090207040d5550313902e03000000f030350b00303245500c490020b40780c05140e60b000c80780072507010182d81e416914045181d40d180d0305481c994120100081c0c0c00303903407500c100c00c81c480a44100350184401d84c9007651078083c4d55041d5410311400f032401d584684220a082d0303101c0c2c2c0c3d2000c400a155603007907180765125224036001301c0d604800d43e0001000350303161030192140389400c44003400480c44240e03414018089800180704c0540020311000f00710750f055050182c0c403040c0b0600e14642c1107601030300780d904003a080d455080c00e03990060100c421981215030144410300703a101a4030f130b00038140c070000e42c91030030141000540b80a45251802100314081440c0c00e00c1d5583c0401503112640090001020302c2d1128205401080f44034403c49410400c404c54090160b0013100390344240ba003007140035007010314050512001d4800100002060395081020f01c1c84008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 702775341 1250 702774091 702774097
    0x609041106120f1005060406052505031606060807030512090103111801030f11031512010e012403030503040b0a090b09010b0411040f05131b050a03060b03060d080c070b 74
    0x420706030003d80e4101078803000c2d0310301102e4101c0380c0900343c1004240320b251b03000802c17142851035141e01c10000940b910031181c50340b50150310051042c00002036144001500c070390780010301c0e401100200607850755070540c3c40e40ca00c081d1200400582205080440001e0395801a00040d101030401160141c0340c00c0c0031100540c04075266141f84441c908154810b560306d8841e850b1241c9c0028010031070480500c01c141c1c05d030300001f0003001a03450200340440042c1c843d04c00c0142096401e2009104621403001c4c5d0b98064810001381c121102e10f60b44081c180ea140c83c41e1704500702d94150300c036149980c5994170f8000000000402c8252002d449500c50b400041299410ba846007111400010b00340305030004003c01e880d005803031011440824070003880918581a052011580102c6002100101070484070019100e607042d080c112200c00c0b2480c8a0858009000f0300c86e030300c8140d03400c01400c3d84500003d401400155141d58214404c4410140010011001015018405030880306202e540c0d094030360080d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 702776591 1250 702775341 702775351
    0x72d08060106050a0e0f0913150f020703021b0a03080c0a120309050c0f09240402070c0302101d01051b0706020102091518011b0b15090f060904110612 66
    0x407800a010381381660310004502032102c046030038100f501d00d080e00203840c1c1c410241800b100c6002c010107060401c4010144240c124107070034001d000030412901a00000d4100c44019000350060451101640c01154007255240c08000e0001d50b2150440e140c190340c1d0382100105002c5803080081e8940816400394291180000d60754000c12603803c280740c8141030991001c04140129000c1812004540d0b6510f55140d1005460112098800217101c078882d14222042207517801501c00500481400164240c80c003e4074001d4480c03003054513020400711a8400024607800c0c8074400305c0001d20a03588140000c00710003843d0f010802070841a6500c0b2424100682c1c802c1c80582c2d1f00090b500e40e141043c0451501040d41c1c90300d0b1504021141901e185d0116080b81c4550402c0040d01d980354000000c0c88041c0e6000e500402c103c1000d2034103691880700340028441143c81154000d0001d41d0360551b8080440c4a6080900742038519200d6580e001400c200d00e40c2819031200301400b20408000c56180074510807 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 702777841 1250 702776591 702776597
    0x22170604171e040f44010213171516180b0307032004031e0303020c0304090b030c09150d031110021b070f0314010207020a03050307050f072d08060106 66
    0x3141ca4441c5401c10450090408816042000c41c035564000d00e195400e90304c0b0002500f40300d441401318262500a12580700b074070408800010009c9401d52030860941b80141c100c1d0700725050844003502000f85284100d418070f407480403040d0303051000c52160341010080c83c2c00300302403410381c1e40b5410600400c0d082124220b0000340d03901c1d41108842003402920340da80c558034800514050450300c4a0000004014207000c098514421010030103120303034121020011a4400d880e122a121140640640182510701d1312030b03c90350340401074901d8903440e80c3e405640d14240c5050700b130000c90180b10507000901d1054043c40781d104058005000140541114420441c03001a034640d0190036500d84a9103118403171409500c011018052740504420210603241c001c05140381400ca41059180a881103075402500311a12210010812000001a042840c400e10030f4901c14400e92aa4565441040c8943c40288540c1e04450504c1c440b00044985100350a401c207070815034440201c90300d04403081e8410400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 702779091 1250 702777841 702777869
    0x30f051005060f0a0e1801021204050c0108060612040615080a0308100806130503040b13060e040b01020706120605030f060907090507050d0e010222170604171e04 71
    0x140038880c826503500c80ca003112a10b46107800940402c3c82c1010b14001c03800d0000c0d0700000304011504511212081080c03007030080d543c5070009000c3e180d00742d000f902e046546108550b403940c00c542c00342510a100d560701a1229041c150050200410000080c0059a40e0356035001800719100b481c071002009010760f440102000e16171840c0041c002c043c0100801075202c40c8031003e0140350004030300036800c0401d42c5a1000c1582c5242011b90440c452940041440d210000c0c4000d5039032024844881154a01e8032401c904182100c1480187e690402d07541340181c00c1014180281402030364401101d14500000186542e101c0c004240303011429165a829a800002003100030300f0b04100c464090072806406001d181801907024015001c0c0400c03225003a9180c28003061698001d5058400580b10881025032000125042c0d141070171450003110010001c50705019182d02d00007915601450b48424420704845000701404e59603001825165102031074409680c0c00c146805020f8809407481c83d041d800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 702780341 1250 702779091 702779113
    0x70c030503190c050709091a012702120106031a040212150117010612091a071b17071103061f0504050c0702131b090f0e220c030f05 58
    0xa030510450b0203900c104007080104000061000c180751007124a030076008500b000c0700e840d20a070090141c2e410b00c0303841081080002205003200307400c1d0703041e0003003072250080c2e403034501c0c0051050744141c804044051401200400c42d0030300c00c0d44564900d00c030203802101642c100e00c0c0000d0507640074018909100260f10148010420b8540c01c5550105090900c0011090440c0341c681e81100144500c00511400c910b42c1911a285608246200d80d800390080c840070035203120320a55140e0650390342c000584120182c1c4001c0c080d4400d03010340a030700401d100f026000c2901544002c0e5000300001c40e00900000340c0f0a8403600c0c00c1209a000342c7c4281150881c1c2c480e030103100c1180301100e5000d02d1140c0d0410080c000001020822902c0d456015118620b0b01d50b20305480d41c000d803030900008030309000081e5203010300991244041e0150340b0344004048603259543c01d81c1074201d5003038402c24002c030801114000c0141601200c60a01c62046403c0031400b552030f12854034803031050b4402d0740c1a4006841c804 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 702781591 1250 702780341 702780367
    0x6090d0308420402030f04080901020316050d080906010605160804050901030b041104110f180915011e09061107050415150228030c0c090c14030402010c020f0402070c030503 76
    0x2100031020f88045055103085400050a804042c0001c1e080c0342d8002450341059109104a0341e902d1003134100c00300740a841d454001e5503012110f203184009801c440c08070300103600200e070041c102c8100342e541e5400d020b52070340000401c00f0b2a403c111038541c1c00300000100f5460f44202a03000318000c4609201500c0d00d07041c07052404c005c01160510891a00c9040d4a0044000b0705944190144149490703c5d0442d14041f82d006035110105140d0045510003001f06542d81c8111b2802d0391482039a6203101d0807100030a480030100111102e1000c61407414091101a10650b00c0207851072101d011586591b0360b480102d011140c400304c0460058600c000b06000c00c98400b9018004d144c4584000d01481141c5a00585030b9540004d802c105460301e161031405141c4140402c030801c81d000b00c0c2546c0c00c01d0351690604020004800e01e400480e1040310350302d041c00b40403810381e44204d80684681c5903080d0240e081081c4001d009103036580c066402d12405001c1070800070164080e502c1440119946c1600d00021 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 702782841 1250 702781591 702781711
    0x1008060718060518150d150e0105191a0a030b01020c0102100e010902150c0601051e010c061103100e010902040b180105190305010608010506090d0308 66
    0x903034180300c40380c0704041c07003441aa2104011110385242058558059543c2920441c560803075644d8804000581d01c00d801e6501c6000b0510000113a4007000030310b01800c1c020051840358031683e00307500400b200400803801d24a54a030740ca045400c0d1070843e4035485440340c11802c003007003011a401070700c041040b400b2580c1610030021140c0b02400104800807650340000c1d5610f0030300c00034428403526142c55647c01076094002030180c41d80206084143c0c00c0d010300b07501c0150000c010a007190b107d80030000866040000700e000f03160030340504407112614003400540e054042004102c859640c3d41c070340784907100125400b45000b10070b2500b484481901d000102c415001c01038004500043c030400041042c040705c042154503410f122208404181208001071b92a40990341491100310000d071a45d2041c80c0e410b80c03285041e6013040c0c40304a013990f240e00900800303009a5440e1500048103848a2010078041d002c00c0794800c0d42441d003030990109040e00c0b41501042c0b491003031445406100d440004c41c4102001c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 702784091 1250 702782841 702782851
    0x60715090512070b181c0203070c0b0309061311101e050906180402130f18060e0402130603140a0c0e070e15120c041805040201050a030e15100806 64
    0x1441d4103058540d10313820b501000c0a061580d12620402c0720355000c400034041100c02c40207044180c5a03406101c0c10183d12070f80445001c07030b5480c10000c0c010449c2804501034078050704551300284450740c1d0ba5401700341d820b560b03041c0c02e4502c50a07003888e0604550f104940300d040c1d00c0a44c0c0c3ca5103915000c01c01e148074a14200420342050140c20700940b4100e48868043d40c481800000328140510005000b10740240b0036800885d58180d40204045085542004980100e5142c2012066250380d413229601c01c5801500448070b5100721107010030098a8110006070079103400c0400022540c2d9a99a40d110007802d0702e200c000541c100302e410302c090011106000c401004401c000520310b00d008a0010007980001881910580183e000c8a10102c5944181c0e6140580e852042d0681c1c140301248020300e03081881013005601407035101110b411281e0003031501960b41a100d89090a85070075060b4054844100384500324481d6410341c01070002130540c101d0003552059101d11a150400100c0da05010000340 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 702785341 1250 702784091 702784123
    0x906080c0405090c0f011101020f0403050d05071a04080c061f0e0903030705031b07060f38030a0b19050106080103030906030f0f020c0c01090618140607150905 70
    0xc0003da030a01140c80404501c2c1214070031505e4442c000140d603808149941d44005610105015002081d020020b2058900900c00c80b0520502c51004941c6e610604500801d84501400e0074105200420602074000b80300b01c810b00e08000c4140035651504100b229003240c0b05046020203600e8501414a61009d0104804040ca03240b40409140d507032440060888010080000000384a01c003c28814072400d00000140d29070310358080c101100a004603410801e1958940b07614081d8075503110118011810117406410444111645000c1100d480d00c0700041d094005e0000041c00030341c610390705500c40c48000300342d051941040301d001c008556050300140e003400360010040c40400d80243c140c2c4212415445c02043c841c2d22340e505030019041d891a800915400825041441100400d9100c840d643c03c2e030343e03081800c1d60b8500495049030f200c40102020111080240540d820494411000319005840545011038036540c0f104844d002c084134041090703a5540042c10404140012017081ea4455 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 702786591 1250 702785341 702785351
    0x903051006230108040209060406030212030306031203090604020d05120f0c01061202060d050406090c06050c010c0905180a0908120a05090c130c090e0a06090b04023a060906080c04 79
    0x26002904003813020304081c0c4202a2000002c9090b1340b40d8003c2801366178050036808850702e802c01e0003543c1743c00c1501e14074480e0213014090000249110305880c4149040001800e890f110794091040454a058040c0c0380c40c0100e12040780c0c0044607000a1203034000700059580d5400c6454801400c5503202e82007039845601d0420380401699415003600c81e072844100d00001d580c0c550f898540005d00038810000d01d0ba81c040c0c01c0001e681034201c0003400400381e078103009024116152008507040e49550081540c000b14407002020940012001c072940819a40d030001500340864444152036009640184c03200c02400c0100030b440c6c2c0309801815040f9071580014030080e50440005041c003100c0c04000c1da040b5a940410880701d6108244240040808401101e0142440d00a10000d0640d90090400540c2400144c03440340c1418400c03036101129403600d551101080c84a603100e00070300750841018104664540a1f01e490706481000d0060840070800a601c2c3d01d403200c000e08042000c10104d102d14681 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 702787841 1250 702786591 702786659
    0x30c03130e01080c270a140a150b0c07050307080d02070603050408070f080d0e010204090b0a03170306060f0c010227150a030e03070b010611060c0d05070903051006 72
    0x403004e50001c4229044107080351040c40e480e040b454409032040a42c2d9224051004e086000e5104050849070100340290a80d50743e821a002c0d50000042c0b1054003026600c1000f080710350501034803007000d0200c15541d038150b4403400a868810780ea04508045e400208012020640401c40c1000514050a00380103914094540c00f42900640501406031100458004100800e80781141e121a24031081000000a5031203164003c0d0024003612000610301400c5019502e010080303017080700c0d846072402c00b0700720714006084400d80015046e5038001c50140081c01c41c00d50590060681d00c0c6003031000584800c01d4100c650440d03e00080c01111130b17450441e10f581c40c0c0c0c0301c9100000e821803034030940a58515102c042140180300d48081e0803024000800d8003010011907498140c102ca4240d80d4102e0f0741d086111100d600d500c82030b105d002d10180100051071a08840c2d4105c1548103555080545816580f40c803003078100f402100c0b550b84e8885d901d480902c0741e106054005104c4c0c8000041c02141a000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 702789091 1250 702787841 702787843
    0x141e070804060207110301050a09050d090308160201110a060504060501060306182c01020702090a02091c0203070f1401080c09010c0605040213090f050f060432030c03130e0108 77
    0x18001402c8260009001014032503082c1078148900b0b40034000308058940880c1c910012310090030300b00c3c0c2d02c2c0517500108120601c14002d1200344c80e04288103d141c00c2080b807529860f40342140c0d04906004001da644079290005100c0700407140d000702c202064900c0c2c0b501d4004103c030016000b00040c1890083c0c10710280030f031000040010340d220100054400e2103e00000e00e0400c0b9580041c00d001b2101e10007070108407045d0003900c0707094400d40c7c012801e45c840003030701001e074050741000f43d40003224000010341c02500340c03c00040c518000743c1035a140a403180341ca600308200c0b0f80c000c100007200032600901c440d6441030600758003c03540403030b6500b06001400024540104440c0107000581c490001c1400d554036200d1400c0300c0701642c6401c010035111813501c5082000450002d586500403040b2844e10100c01098652040758405a43c81c0300203031500c001e40c0300c040224010b908a001c1e40c110046001d20800051561003141001162101607004000b100740d0503e8115401a01d68030380100610130f0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 702790341 1250 702789091 702789107
    0xc0702060706060b1611060405010e06130317091906021b03010e070801140c0301120b07030b03101a040e0613080706060b0304110f0f10090801141e07 66
    0x581260041d940c0d0403203080500140c00c07203810001c08402c002440c1500c8a41120030107a95922806480c800fa00e098820098540120311859010a400841c040e900b850034400030724000c462038104500c03240d00c03610340d00d5883c10000e904140784400002c8159451a011a101000f4404001d00d5103200c5c0c00c0c400002c0d10f489220284810303810340002d58120658080d0850040d200c0c0450486020940d01e049440c0030309103203030b014614208114081040301c200181102d050b82d0340e09020079404103441d5640640860300501316020569148000f491558080c0b103c0720320b1440c41217001c100103400805a2040c07401d80c0026921440c40c08421848566002c148a9480700c96156211051011405d090084c4d2040c800c00420007460401d0114000580e00040e41c0074a028001c401c008601140511161203e10214941d209500030f18814082c604500c002102d0300f2180781c11003101e96603500036030940d07005c444501c0c0d02c5c6408108000c00c58894004440013001d0102c6003148a00306142c0c060f040607 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 702791591 1250 702790341 702790343
    0x60f05130803181204060306150f1b0602030f01060311072f030f1005010f03030c02040c05090a0e0411030a03080c032a13081b040509070312020d020d080c07 69
    0x80400b100003840800241e00038892401e042c800e80d4100340360000050340030703405806140302080c98600e0110310b103402c1e89690703454081240c81e024150068101c042d100072101c15060f1000b10b415050045c0041c8013800034600900b401c900e49400d23941044406416920407040c0079000740740c02c0c818007000c40e49031000a01060f501400151000c05585445401d030040e98000c03d42600c208050381c0750820000415406802010900b000076980710b80a1030400c20355848040c0010340170078440c03c050301d410b03400490041c1d4141801868501c001021a14a00d01ca5119803c042002403c01080c05075007915882030b0b4900714003420802c00300395009070003040d02902d40302030420301000181030764040c1451300071005654980007801030303038903d907000d04d541c0500541c0c803c409040707200288100b0001059075140c200b811880603100300f060240001080300131301261140c45004c4c000008100550891800d0302e0840c2e01901d4002800c2c50082d14001402d20300d01c04000484c0104180c0110940980d171103070f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 702792841 1250 702791591 702791603
    0x2030a0e04050a1113060f02031e0a122301050f181506070c17060411130204090e0d08010807061d04091a060a08030903030a0f05160f060f0513 63
    0x703521060b4001008013000700c001c0c8003c0200090005200e202c0010400481d0301030360b1202a0070314034100403030f01c0e4042c04e0659481d401001882e40c41164406026000c0e40030f00345007030a494103541c03085209aa0000032201c8054402018800c20300c81400021f5014200c2580e0701c0c210418010040b800720340210034401c2a030214070020503166080980042e1038010028121502e5a08a081c410700608041c444d14484180000607049a0034000c91045c0c490750b0080d01c0c6002001c4540d041c031040c03044c0c003400c4c01fa200342d082002049200c168896020740c0d2580d5402400e42d0505003501812a540c180c1104681e940078030404c100c4c1c16807003407911410048540008184a00a101103005050403580042125040c1c203106014107221070702c843d12400049803c040b0040e0b8988803951a4400c402909405400030400c007101240070308110b1001c00144c1c80d10360f03d02a5503580c0200030301e030071583c1150859465510300303062003a503024004510410400400c49400e00d04a00c007284d1840f09001848 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 702794091 1250 702792841 702792851
    0x40e0c071a0f06010c0506010e130606090212060d0b010504090303181a0a0b010207140114220504060e1b1303050105091e1f02090d150c02030a0e04 65
    0x144004641640d200d1a48811a040c200e64041c03105070405004a0310300000a615400182ca0340d84500d4000c0c3d021908140942007590a0894000a0b0340004290030300349005070030014002802c0344200d50040442c001e0040e1200d409440b2840c2c440c1010706068490035074403003298045108800e0a904495084400140300c02c650714090340641107070313040e10354042d0b4003110960501110440141402c052905031390416a82c0307411100071a601c03200000c3c0164402c2200b841011a01501640310084c141480712881c80c56201541e0180d11001101d5402442030148201a55003419184c02802c0225018004142010309418000c4801041d406200d0321300203d2070b011030400011298800240c003403c1800301d0301c4c0c3c140180139090503120021113102d5420780b00b1503041042042c0c1e90308010b10001e001000303680c1e40c1498800b0751503184141c819a00304100342e919a12242c0d00700b21103102e254050100400f80b4003030411110628031100640d0810440c00740d80c02d0780b010401300d0700f9108a500080e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 702795341 1250 702794091 702794101
    0xe040b01110d0f020703120c1713030b150303071a010b0a17071404090c08090304060507020118050a150305090f060c0c0c03010c05040510110a0f02032509060b070503040e 75
    0x3c034062a81d44040c3c1f0842d100c50107000041c0e800200e00b220b031401041e802c421604483d903440c40500c200111000e4003261314606000142c1020850764100d222020042541d0310f0300c0d4000b0342103601c42e40040752500302d2102c94243c10f00040e00824010601001c1c1281440d91a4a0140203401c00c0e14440c031a1103c0c030313400600d000b0302400000c041141c400c03d6160708e45889101900013003c401c078001c0041445800040d407a01d000001301c07403d440682e5036203070030084650300651758040710803440128603a20f400003080a4840038030f01c1c0d0040c046000d0b401e14800c800c10713015003145c002500040d0290420f610f40e460303040d00081c02c0b542040d2070411035982c560803e403c0d6420181c8032040781d070b815402c0200154000d0383c002d002d0400d440e4103e4122404165000e03007510116200041404150040e420b04400b18a15a405007400c60016056506030303440e0390000100101c400d0850149501c5c6000b0a1110004c01d100c0d21020b020301025091074603d154890315541c1c000c0e40303c0c2c400c080145000242c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 702796591 1250 702795341 702795343
    0xd020d05090111100c020f012a0e01090812030610020604020a0506130b0f18090106020d030906020904020307031b0c150c0e0d08070210080c0723030a0e040b01110d0f02 74
    0x1001801072403802c220f604985c5000a4584070b505100c3c0c4c6866007400b2110412000f2001c0541203c4140040c00b400d02c50425000d4400826000c1400e0600085020005130044207024a8100540b0345a01d19070304d282610803c2000904d1140303e80440d071150042100684030780303528030290360045541c181c0360001c05506400501c074a4010304041400231403074460b14030802c005490035190003501400d50345800c0c03040c01000c0009204800050b440081d040d030529009034450b21190b03009000151906002401207410b0360300966a41c000260b807042c801d0004008039030342065001a620f4444254581501e8041902002c3c611842c01039507148100c180b80c034002c15100306030b1000500031140c280d019040149981d0440303c4c05134002c075500100490400d1084074410f1042605c400074034100700d11505c0f13030103011240a485905030201c214641c030905004002401c0b1036209603641c0d02e40c4012800a0005a512500c4500c0c140024030242070f00740c0001240a02804e100f51500c4030003c0c074000700403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 702797841 1250 702796591 702796603
    0x501080c0c1e030f04091d0d12050618011508180d051b0703050a17190309111e041404120804030c0f060c03140402031b240a020d020d05090111 63
    0x14800c20380c4c0c0018001100303400c03600495459901d80010800c608040b02520741c4440c0d0f0504800002100440b1280440700960b00054010b0b9001d00b0010303150303550310982901c0c030900783c00c0300b00c0d0405041c102c0a146584100d6486d4094008500c4184407203104d010240c0d03401031401e0100610101040141c466000780c403020114404c04021200c801e9600d0030855145c0c004082c06035200342c0400035500d0100789031070031a80d0782070321151003c007950110300c41207004202c0004216014010600da5258590300c08492007261604600c5070345043c1034000c1004110f40304011025a40c55100040001141c4041d070192000d0f10390f41084010340c0d4075480d04907290400f8000003018504450185020700c0156405141a051030307407020000c000c1c150318841c0640c0c004540096056000c058070801444041124007011400034107130380420108903d44101e40d807400d20f034882c24110041a0081c50b11f80c1023060381040e1105002514141810303040c000c05601c600c0c1301060602149021914500c0010040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 702799091 1250 702797841 702797857
    0x70f140d120915020303070e060d0207060f1b0207050d0f08160f20030d050d0e0709090c0b030106090902030709080a06051b13140a031403040501080c0c1e03 69
    0x510040c80001c207034003030300c00342141c020250180044081c01548600000481340500d406803034040b50728240300b00b0052154895002960b80c95020701400c0001041d0780520001943c0e040b5001c140d0ac2000c406604030183c502c43c0080455004090400240d00c409803411651500003070741803150001400c0c84540c500c201c8032065280c0d0220201881071114803807201004520031034101040350301136840540500703210b81000741e154012250b010241c6000d09c1c0144800c00d400c4001040310850001100e0070000c0359400403a5440c0c031800e0b002e0803c11003600c070328090245010f40b503045504000000f0700172050740c0100b40c0d50340c0d40040411007090041d00032100401408007242c010808030710b0312801a010507680c5072901d1518034500f50560b07003220151452600f442c401100701134900000d01514480d401019a000140c042c3c020011070b2a00c80041c00383d500c443c1c021540e4a2401d00014145d540091101c004410140044428410040750400158100c82811b85a5074040b115060441c400c00070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 702800341 1250 702799091 702799103
    0x13020901090204030c090204030503161b0b0d112805070204050c1902060c0f16050f1c02010b0d1104060509150112180b04050a060507090e0702070f140d 67
    0x852a240d80c0083c000da0b84106a0414490b560307040d1041a07018900000b482ca41051042c2c45880691000340000980120f1058100d04040000100a212140c1100c113003d000014500c0d0b031020107005101c58002a1010709203030008071500b2111611489400700e0580000b0f482e00c441280c4160113031041190010010801c5041000001900783e000d11200c01174107021a03682c000310b80c00403400a100341c2c01103d8651074020a1891584030707521224012400c0c11101c0e01d41404183c04002c4181000a41d00041c42c82ca52003850b0044101030290382c500031681400704c0b00d5001e45500e00310703101507948030400c40e801c3c45401000601030f0115802c070360b400078200d00401c00b820301e501c071a2029000d82030b00c2d241d1544000f894144207030380c0f180c00003c42200c4d244446900041514070a242e006004005031520f030041a601c0105440007510100c00040d8890024080c00b075403074480b07d4100c40140014913906180c141840740b10390360b52041d012812500f0780501591b40300c0d0b4080b81c130b4955002c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 702801591 1250 702800341 702800359
    0x4081b010f02180405090712020d0602040b03060310110409022505010b0a09050402150702061b0709050f0403020a15060b1b06070521130209070309020f15030c031302 73
    0x716a400080d080b000000d201e8403458800c100b11810a48180c6008210316009403816604001d002080701c02d004100326041881316004030b0116040b440688007410b030301c03104541d50741040e100b010b143c040203070121450103142c041da800003c0740e000304640c200e5950740405615115502511880c4000354410842040c236000111010000c0650000d00350080c00c8404604840d1106640d100711442143c2c025000100c0030301220b0090408000f8004151000345000e18154500140003505d603034500d00c00c00f4a0b40300b86001d0000c540d280c0140c9a001c1c11035440d4600610b010313100256a21104d81001c0c00c4145c0403441e080403c9000c1d040360340039280081d08a1781c1c50a039200c0007541d8181e80f074050003160113078801254400744103400b2a04040c070500030100380c00c0b101240c1050000006040381c4c1040500303001c01d0005032198080ca078840d20b21074400041c80d048900511280001d40301030300d80b15a00c8107001024820507541a02d42018100d81541e89a0380c6182d01c0f501450300c10340019602107445 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 702802841 1250 702801591 702801611
    0xb0f15091008011e0e01060b030a020f07050327010e0303071115130305010b06191110180302011a01020d081b0c0706030609181e020613061806020604081b01 69
    0x1440100d1a600c13000701c42001552140000a402c81e4107602480382c902d441040441e41da040c064000d80a5042a200d000c1d01e0500b507a07407024596030203186800050340100d4100300640c038500c840582c4004081c03c01011040c2e091300040c1c0c581c400e40c18001d040700d040d5219480c858640c544186940c00003481e10380e9443c200300307183c850502120700c011511982490218140c0d4141002520b010320400710003541c09480f4074109443d0249000203031000380c800c2155841c4000f840f0b000d44c0000003a02c080002e0000703007600303009094415000d10010b490800829100b02079a0004502629904501d0049015140c001400280742409401a54840004a101c0c5c4c0c24260100d0031070121061078900b040800d0343c41008000340c070104803000c10103555804400d4003092401242207003035039600c0801c000e420144d9002401a07000722089071a45c01100704c1c140103d80d086258074000e211410319504840c0c1c0707051002965001c00800041010b400840c0c61151003000300d040d00740e011450002030054200b1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 702804091 1250 702802841 702802871
    0x3100e060108010608070e040318092702010e04020a02120a022409061504020c1501061206030210050c030d0f0c0f0f09051203090d0f0b0f1509100801 66
    0x4461440051809a00000201d4020510030700003201d100c0390140c02c007103150201c0e000520700010300a4080c00788540b0360040344040750151038041d040e604000a030303100700341c5c10800501c0071454034070001070030003541d100c0540e030440604a000d8008079170140c3d07122542c0404034108541d135100c11891a10114000207107540100e4071040701c0401d452802800c10800e150030504541c240d4003e0840d80012010440e0700310400c20488000304050409481c0449040d041d13481d15608840d10080350080340c0060160540c0304041e5040c90041c1d83c02030004a0446d000900100d00887d041e074280680051b1240c0b0507541071090340c5104820120400c52081c140380d810300540000000c020004000d0074400200d6806905584140d070450317614941024108014070200b05a0304100400380c0c0f000380f0986003955074404c0c3c1e01414a2040740040d0140800346031601820b24007030070000480b0050710800c07803c3c40c1d190303200b8080c882049544000c96212000e2031a41094582c01c00e1016509008140001c820 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 702805341 1250 702804091 702804101
    0x20307170f04200a23300303220c0e2401050f0405060313080d0609050c0c03030721020409020c0c04230703020d0c02060f06091018020f190906090e0105060c0106050310 74
    0x810110401c02c806e440c401c400c0d49a100c01c03540c484012002c0c182540c9200c0e07501c100498010300c01c08802c51320646403101040750b4802110320000b00350046140081040b2000311840524600382806030030704005071500600d030701640c0201c0d401a4000b000103010309085595840c401d5400905441c0d071100300c0300d0b05101900050095030600350a06020131503a1a501c4110f0300c2c1c1c16180400b030b44c2151210352007280d08054a8024044d0701c60740540030117410b509840100003d15180400581c2c44203240c24140c10509140403c511031464200641400600c4002000b004094040b802111342d031841410740c000c0c018590030007d901e04e09806400f01c9500000c0c054050988088102901c0c2d80d42810000701c0101160f02c0d0b40fa4036150101004040c107140401340301c0d001c2c140c07009402c0c80e90311000002140c01501c41901580c64081428a507103030881d400c08050480e0380b404169050800da16010300c803206124260117070000041e1051217500a50212000d428002c050b50a01c0844a90f60310180c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 702806591 1250 702805341 702805399
    0x12050f07050f2d120703050c030f060103080c0a15291c0201050d090c170604081b0115140406051e04020307170f04200a23 54
    0x110800c0004580c034600703a801c159564900030180c3c15072480d894001211103500c3c0c151205401d2400b0101d185980d40c4004002d0141c460340e00410005255050861610b0807011050707010350008800034920110226113181500d801064299544254050061900842200c081d1801c4021202090706004a80100c00410318070f261411607110404007001c0085a43c0c0d0b0f241d640001000e001d601403546030107050010f140141030031402c0c03e04000000f0140d8041030070460381c8010f540c5040c0a800022504501200e400d60010329551406683d0381d09144288035259100d030814220341c0031040c409402062500c08162440c6c248a60b0f00d012003000c50011201c00b920031410a03001282d0703400c240c110b4003c80100354040022407a00c8405010003540054100d80412007100c50300800f410320205401d02131090889000c4480c903082c2010312101c01c59076804101c516855001c0f09244e40c0d844a04029a500080c02c80e5140d0344103c008030b00407001e07040903500400e10502c50f20142d0a000d10844c065 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 702807841 1250 702806591 702806593
    0x1180602150c0a170714120f0c07110f0a031b0503240f04030e060f0307030c0807080612100f05100f03030f1b02060c1e0115030204090c12050f 63
    0x1e03114a01041014010f603210f02e4000b46400da01d001c0410084070845801550a041103010794520513050811540001076402d00d20f0440800c4c44030315200390381c0450344480f0031070b151818214036545000314007a140310a14031070542800104c0e801d40e50504004025640000c0110045100380039400072102d00e4864103120313000710200f840b4403410281d64960140003140545105646000101c0e41403c005801902045030241c803003915501c4050040c126800051401c5441e442c041c030004094480341c000032403c000012052182060f0001ca9654110307200322280c401444000e42d078240b0b04002c1c81c000554013030802c2d1042c40185240d0b80400e000e040ca000c0c04000d85a103e0041034104011403000500145d2400303070414038030740300d040d2040681c020710040d090400d40c55000982c035500035040d020007940050447d00c0008000c2c015001416014000074482ca640740900100d00352254400a40116220034414003003083d005000350180903a2a01d0750000c5419050841d50bc4040300044005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 702809091 1250 702807841 702807883
    0x201051503120a03021b030403030203071b150c030e03100c0e03160501110c0409030503180a030f180e040308010608071b020f060d090305130905090a020f01180602 72
    0xaa400d0114440c01050845800340f4540030200800b1002988035841000d01e00d000313a40320b0194030030184005c1000318041e6001303607100d4440d0704201400f0010084070780560100351904010402e0000b40c8800c0c40181401c00c900c1e008400c0c00c003919a002810b0409500d4010b880200103000c03810b44c005c0000061564492119200c0d14051507a5481e8035030401d014002c00d18000c003c44d40c810710381c8021802c0801c0a03104900300007004102a11920401180800d2010080050b00d06800041c140c040c940b00c40100904000b6440c00303001c80140b0680f2104000c1c581038111907203801503684d5001000036650701c0c00d881c906400d000307103003000078041c1600141501d00070441071031042e4410300c80c0419012421310788031166801c005090b107074501901d8000d00140324580004e00c2d180700c0c142d40c4a019440381959602908804504105107800c0000200c1c90a0148001a50001100340b4119419102c0f011140010001a0b03000c1c42c03140412a40043c0c0410003040c3e182e0b01240751644403c40d8004500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 702810341 1250 702809091 702809131
    0x70b0a0c09050616060c2705040b0f0a0b030615130305010c02030c071806080d0807201e01090209070e01020c011407030311040f03050f0c030c241207020105 69
    0x1031a04c01d0000b0040c61113030b4000410301056856102c1030400800f82880c1540b18170080d0841030701400441040d400c2030580e90f0420030b0b81024000d44100c80d0080f184e2601c0c0c007000500003401a58107010b0b56005200c04000145581c582d0702500503001550404ca54849441c0c0e41d003880c00740c842c0c0c0812078855080c46613140001e80000103644a440384000540410b90805c400f19901c2401284106080c40d00c401000402c03010500c0f8041200340360b50340d613403690300d801400503080400c60305100002d03135030300507000f000e4200203d0304038045690581d18040750180c141c0f4090244c0170310b0740060740c4034100906004041d90400b0300840915000e8007660200d070301440055071443c08229488440f00e00800007500080e00c20b40c09501060a103080d081d040584030301c03402d203450240f500111020780c0114203e840d40c030703c06c204d203c4040404038010141c07240100042000c048a1640c050310f038160a105140c4d000301104165850040c1144005443e85007009000f406800107540000c4200b000c641a60 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 702811591 1250 702810341 702810349
    0x2004030c050a090612080a0e09180d1d061602060a262202041d101a010e1c020d21020f0c060c0a0b010806040b07050418020f070b0a0c0905 61
    0x300f1101741d002c41e4404e86209803a0780e1603544c04000c052080110b60f105800166444401c418054194062504450520106034500d40944400d0780c2090108503034000200c01045801015805001d0b03c0580c0c40c0c079003461142d011410b0300311000354003640104080802550104800705882e81e07040d8104280c1803038592149003e02c0c26122090205070304907440890300c99090509650303901c0030300005814018071a2840500b4011202250b032900044107510748ca54040c0660030480d104010a036200040850001e0680780074481c0c0d0314015002810700004a20200d03031110b0613540c0250080c203400c19107107485080110402100000020359102c0e441110b84006412085451400300900d40e80da90342d010450160040b55a20714a480340038000c00000c0c000030403880c020071302c4030000c0903141400c2c40c0c11408150000c00003410001e06120030400c103004017040c200541c610500c016035420f000d00340900c40348150400581044a0f410a122030005103a00c0304510343c1e142c0c1d44905082e0b4a0714108 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 702812841 1250 702811591 702811601
    0x80d0e030d0e010207030b04032c1e182508040c0806040b0103020f12120306011e0e1512070903060b01030c1e02011e02030708010e01030b0a2004030c050a09 69
    0xb0b0380141d10050301440001c3e00d80f02c103950403034000e04000041d185005061000e003c603003001044d22700c44104c0490078030f04118031407050951858028590442d500c0011440c07440801928004840080c404641d500d48680249036150b002280403200002040c080505000420382d0304a40808038420002008000891528061a8849030009040c1d00c2d54007001892008825016485600b006851100d041c1c10007900002d01e0900200e0b541f02d02d4458001340482c0d240c018060400d64541c1d1140700301ca82d0000c0d03d0744c040d0000322000840c50740d9900113412540122800c4601c4070304800113012000e604000ca800031a480744e1024002042e00200441c01d844140501c01c000c0745e000d003004600000e07031070043e849030103542c400020700344101c105480c0c01a50314140c46480e15400020301079401e9000401c14050900c00003481c14a514590b00c0c01d402010080912840d1aa104650300c9900c00e1041c4d003d44014031520601d844580340c3c10724400500741c03407145a20954a51000180079006c41c054 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 702814091 1250 702812841 702812867
    0xd0e0d03020c01030b030123040b09010501082a10080f0702030412020d020315180c0438061c0e0604020307180f02190806090408040915080d0e030d 65
    0x2e40070b01d80c0c9200c01513019007201d504050b8155290b0180b01040844101000d0b21000849503182542c101420121408800901100aa07904210042c0480303540002c2c00d0341d08004196250f0744506100965030489804900900e074011405d0307004142d426801416903020f12003d01e0071002c251104039050382c1e203101d54404c0603064021504004054540494411b841c1d0b07001606030f41c42d0000110504503801c10807100001c85180c04241c80d001c4450401c480081e04000742d401300003410700c9000d07424001aa1130408010400c0c5424144d401504080807a09480c501030029515401600d4042071440b40c46002982c00b51325000002d0000f00c800901c040c0100d8000c0c1c05000300c141400c20448000c258404040d1101e91034000e07080c80e09100d880100218103040d100c0306001400584000d002d00c0001d40154460001d940c00d01c0003140c1c0020031502211400307440001c0c030714249010f41c82a8178041e448550240a00d090f5048841d800102e52615034800300c0641d108490300390001d541d641e0140364 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 702815341 1250 702814091 702814093
    0xe0901060e0d051c030207150c020304030b0405010207140606100306030215130806040302010c03050601021b2205040501061706010e0a1a1207080c0406180207110603090d0e0d0302 79
    0x4054407080c20428000201c450081081c0c40c6500d20003400d46203c1d9103e0041500000d600082400a00514480500f41d2100742e00d4140401c20001000035a01d00a5000181003820f03090007003820464254112100305520036004c0c0040ca000c844082e40b80c05c0100c42c0140a401d00c240015895403091140c030050302d90040910520b0866820102c50f10341105a919040550140002c1f6000d8410444036108900c41e900125070301540c007600074251900500a82e05540c09070300915100801e022510404801c281c076aa0322000c602030106c0382c8848100e81d600901441c1000f440144035040d01f00740f0544404140c000070184035200303100da03140000d00c01c0b002001c10030b00c082a94050a50402103e0302da0303038025004c6000d00030000070350081030101402c0950380802c004000344542848904005101140d007040300c2d5141031041140b0812484403080c0042c0d00040e0301041003c03498034101b21840c0a0300c42912880c144160b43da070391280d000101c011500054a44c1d00c00d290080c000300e84030340d040d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 702816591 1250 702815341 702815357
    0x90303040b03060f0d2f0f1003021c05041e0f06050402192616050d02241c02030c220b0a03020a03180c031212060f05010e090106 57
    0x700810340c00760006030a01394400101921036860307554500004840c107009010024070010362503030300c0d00d0702e2541142540010807021950b11542d40c0b120309602c01120207443c00c00f40c0326941da504030020711540080040b4901d10310b45c00038811a05a102510aa1251904816111120481c10b034400b41c170280040c10055a0003a03200020450b400564000b0301c0a0701000722095844c0c4c42d0380000c0d2007604a40d101da0300c05c1228410221405c54002d603000351000151200024440c081003182c4440d000b07444c05003900303d01040464840c40340f043d1106c002d40751010444268401005100e9020140c80d55001314076040300400d119691003242d00078503829940501d444048603d40a081c2c3c241c52240e03001c2d1002813070000380c40460100400b2001a00d07640103a881c1060a006811541d06c0c03104102c40c002410b500900080b0380001e24020340360010b14140d08081099000c49440007110036250300141408800140225443c8060341618003d032110701c01990314038103000290a0074450100042c1e405 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 702817841 1250 702816591 702816599
    0x506040b3103110f090106230c03030a1d010c0504030605041e0506090106170303010303030b150a0c020a1e030326090705090c07050d080c0c0114040309050609030304 73
    0x5000c00c0c00510180507140e9001080c0020007001c1d00015482035a030180341000038a4107181608921018a100f1214019a03506000c0000d158400b140040c9800c03191940d000341441d061042528074010010342240c1c0c1e81c1c50071070024009889809465038520500b02e01e001d09201040c00b405000e5905a42d9860804d03180d03480b1070001d0f120152040c2c0701c43d08910404983d65121580300c1e0941c600810080000341030140da11401c450300c035442546800a04032480800a0380401128110380e010700c1c0c046a13940c583c100150641c3e05054490300741c1400014030412841e003000c00801e010380211405031529548231b50146145405410a4218140e000c400344000383c09840260720303140c81aa180300b0001d085040700214000c040c0c441c603115a00c20441008649000079a4540c4005021140c50410b04559076044d030b6000c801140c0018001070000003403600540c0700640ba10b007109a0700a00440c194400e40f541c04c040151001d400064590f080402c00d4107042c0d00b01d52900c00c1c003800039440d080c54 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 702819091 1250 702817841 702817867
    0x1030506032d28080a110102160b01080f0c10020f03040314010c08010803190e0406030b0f011205060426040e1605040b0f0702150a091503060609060c0c0305010507090305070506040b 80
    0x5a4480c5c14458040e46000e090b610034401b5200080501d8454403000c00103080c01c4400305416880307107265030f0040208000e0300d000071641103d061805d40c2e11b40c01e0841195801d03810000c00e40340d0340c1402c0c44041000014000c0e811095003c0d40b040700000c02041c040902c0494056009018800765a4400c11a080d85d070f1580c5044190034040b5464410751021a5100190135511207500075154042d1407400c2c05410110b1211080c010320291080a200c55200d90790300d5255000104048c061038124000d45a10043e030043d80e682180d0050010ba54586d00ea034204a00524151207044600316600c10040840340182c00b140c06481c0310101d41c0b800c10140c00303101c030708507446254100d821000c461603000040e80848043d01c24405240c54801031b42d81480322104150140c440d0b038004050500714104080c94203c00c51505841251170070310751541450416001e041c0303841d400200b0319844d1004115845922040032002c0c0d034401d1042e0703003840340c0e00d034100001d9002d140603030b0351a8242040000c5120750 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 702820341 1250 702819091 702819097
    0xe010813031d041d060f13080f09040c05040806060a0e191107051f0b0d0303092f0a0602060c0301090213090f02030a0e0a1101030506032d2808 63
    0x1502d4a14150904050340803a09403001c001580880000304c2800ca10020418028a81c1c840303019080d0030400d152503482407900b2550060050908000011489611811035040f40c03203640340030b4802d00c0000b521f200000e1241c0d015100310090ba0181202250b00c6141010000b400c4a02e411110102d03074803034628404c20360000d940750850f010395401d000e80a070361450340a002c90500450140c00c0c0110f034008070320b4190030807030780e281d46862804401052603540d10356040781194048c40c00017101c82003442c5c11054448030700c1418565004c0c0d451103104d200e10011500803244400e5800801041c1c0c2c0d903074182daa906007501d00c0704000c5001e01c014044540181d019226120b4800e00c042c0e00d0690f0f8695010031104000c0c0070490302500007040000d00c5807180038040b040c480c854000c0090041a440f0a81c1041e4140c040904041d09c0314041205503a00b0071980204d2100300c00d0ce840720108002260012400408d100800750040454241c00024440c08018801c400d201107030881c80d101d13a403402d086034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 702821591 1250 702820341 702820367
    0x162105100f06030f150b0306010b0712300b0609240906030c0408010614100c170f0405090f0f0103030e0d0804170c0f01120e03160b04030e01081303 65
    0x142d0749000c0000403807502da50846100b8050405000c00510214424040d200c0e48003000c1d010742d01030710040204e000354408845085411a64041518003144400c070355400ea00c08000034840c08904003202c2c51654a05c0011711281d4000042003030402000500015000741284541d00070100fa1011040da0150394085800c480c1c200b000c180703490702e408000f810035002660724400403003003c41c090080203024070918000e844001740003908042c0c070b540090301c41e4411240302010030515a44003070402450381c0030301080b1545004c5503600c90f81c02c3e80103224190018490280714000007070119030251012841d841c012403946200c1d0741c060b800d6407020796030507031341c2100640c000c031030359186001040b40707440500044d01c140080b80c01c50200c0b00d4441841c1c41148030045104140040c51003016030707000b0000c4203040901203004564011003800581c194060b6501740100c0590300c03200c00c41000381e0740c04074520907480390b103401b240e49145030011510f40504590400a54500c2165900424052402c1500c41 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 702822841 1250 702821591 702821621
    0x102040302040912080c1309020d060314032a06011a1303030c291305070e1501080c0301030302060c070203100c0f03060605090604031209030516210510 67
    0x96500ea01080840d0704412041d1034460320f0802c2d030f02640381d0184c00e10381c00c41142d05c4040c1c01e020407800c42080c2080c0d540301d900504e0354006104102d0191540284000710740107090400c00c6160802515160740c449a4030a4416190001c500c4d10381a100c2e50211a1503402c07001407020380c0c2071a0030110b90441007000d042d5000d00902c403d900c40c0807544568000b03184241d4030401c8000991a01000c6d840a4490000b4200b14984002001007445039006a000c00b5503002d0310360b00c4281d0308150b400c1604642025410900d10002c120303140d008051340300840002a070b80c004190783c41c0001502e90340400e000080c0140c11603008609458404000703001040d00060039152800d81c0f880032602207a88480040011032505000403010f90b80500c6001c00500301400c106213001ca41c640015264899400011b103006e03201c40d44c0394a100c1c403500b1040060741e80b2908580e98074002480b80528201c0074800c0200e0340c030b1303256001c1030b114000705441d00f54580c2c040000c0c840c400405c0446400f415000c0c0ba02001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 702824091 1250 702822841 702822847
    0x507030c031101140a0c0209280b09011a1218031809070203041a0c01090b070203030103150b061602130f05041109011508040302100501230405010f0302120102 70
    0x10803140900400114403550a40603058940380024285540c0c44040c00c84250701448a42d405541000b40c860301982e044a484c0101c0d40c0d501072400c1c0030500152418404024918410703402c48080d44400440b90b0201c5261010307a91304c17080039000d504500f0005480140a019a0507401048070545421900c001100c5580c107214100e068039642003802c005660801402403203030036044c240101030b0084c4085c800b0314546428000c44445200c0140020451604c0010b004880c584007940008030040c0d00c000c03161840d09014000030b41d290401c0c001503c140880c11803450030b240c02344c0304000180c807001d007806041c102d40d58100b540c1c90314020b4047c0c1e0003d92082500840c030700321340b09245103100070b031400140c10304048c1440d1800c0b800200c0c80341d0244075440c005103c0e812030b50759880a6207056182c00b40155a40303140880c00c049420f10605015410100003160a44c83c04401016200174103042402c24060881000283c0d4000c1c070034a450907544c00340510141c181107000f4000604011b0001d45 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 702825341 1250 702824091 702824093
    0x201020a260d02090414060f0d0510020415020607030207030e0108060103060801021c0e0d0207170c0306130605070f0807030b012a150501050616062a0210020f0a0309050703 76
    0x1210b510420060114550018030204545081d115a05180320b441000031824038043c0301080c8951000500144644034440300341c01080003c100a2151502586080d9100d03660761684030241e06601107540e01500a001c0010f1030144603200b0f070f5440c1500365451a200e40034540041d24401c0d0007505041c10182c491001184168007400109410381c03201011190801c0d0200003c0211107245c00c07002c4603070b04580f40c14a0b4183d17000510320141c400078110056110002d440c80c903c1c1003942c102440d01030040700100004024480000d60b8840d019500c144402e54074254100c440c1c0e600c9103c640c0c0403400c05c0e0f01169909200b0380c026088400103040c1b1440d0000414500e001c241d60410344580b04903c003e01543c02c000611806400c3c1c1c903034005003030016504010024915028110301205504e43d60100b030824418580c01001c2044000402d400d004d010070785100e05500320b0140b804001d80300300b43d11503000300d0480c070031117086031000c554031420041d0b5a0f0040b4054404e0250558017482941c40c044 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 702826591 1250 702825341 702825413
    0x140c060f09010b150304080906070c0603050a1a100f0c231c1713060905060a0507090308070b041b06050408060f0106081315110919030201020a 63
    0x94024906020060164605644880c0c2074420090410f40514107a0701a00007008843c81034907040f43c1d0046c007440d221007254000c0340550240c40d2018282c80003000b00058441d03016405036000700010f00090201c0500780c290b640584841c03141c0ca50b040b100c0544084c0c2500d01c141180120000b05203025110881507803210f4505004000c50941040c1c280c0051030702c0703440c0800c21169283c2060244032642c440740c1130040c01380305810006100c041800c01c002031200e03801c000058150b40c0d010004104814090401960307440f021150046203614103c08030f200940100c0d00e84040700d6011240600d044850354030203260500c05003089481c0320190f1340740c1050000c40c5c1d031b09030054a602d03914103071680c2c50650040d18058018000c1420300e0b6604c1d005020321035000d240a41e102c4608224052100054a00820034030308407005006050b10300201c00403a03602500c014801810110b4550704912400003001c08840303080e10000340540c0c44601d8113000181076490140080070b0b01c909200e10780c11000c0303442e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 702827841 1250 702826591 702826603
    0x20d060b0a3c0e04080412030210052206020d060e07052814090a05060f0904150e06011101091704030510090201090902090301180b010806070f0e01140c 67
    0x9451401c642c607106400c400a01e2142e00d08074049901d1182040040500b400041e90080c0952081d0542c403900140078064a2001c44000b01410340c545440303030005080003515400003600c0d80d04034900700008070b0f500b00014a0201c6503211301c07151400a40c91190307a248002d510001408261a8a43d1030010300400c0011f401c91080748030b902e545a071008080f548001403032580310f1540303500f483e281d0505da04235406229400c8941c050301400c0d5503184000005081744640341e1220b58800000070f410080d280441c405820b0b03404d82642c052104040c50303808038820044074041d11807000781c00000204198490b01c80c00003c83d04e00000060700d001107865440e00800710850100303440c080005c0030410407a0070411f04a9200b40d80c0e001300401c4076280c2c0000e101020f00d00c03410708448d4010440700820756080d031205114221544502400c211103151016003980c0c24401d412040c06408009a2031500400c0110a8810a0740c0c0d1108110340781001511004520070040f0312410086c020108019010084 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 702829091 1250 702827841 702827849
    0x80306010c0201090e0c0306010f0201050f0c030414060a0b031b090a150806010e060a060f202a18040c03080f0708161202070b0327030a05040306061d04020d060b0a 72
    0x105d5541d92800100240c0300ac1103402d4854111781c5080d00b04607102004880c1d1a070040c000da48099601d1711203043c803034180d124800b12801d141c05100c1c00d00407680341d654000b000c1d4100c02e0381550420284911182e00c080f01e4150001d80140d0500c002408101c80355004808801020003e00412900c1d20711052904e4001d810884a404562043c08540c0ca07242001500038821890b000711001d9400c4c41c002c200c0c17074651469032441010300c0301e4040134100a000703141002019030b05004403070f08488100501c072000c1082aa00900a101184001c02010b49286101d184c008a0039111245190380e030b91500e82c4100e03e583d482d54014003005c000984100020912180c0e22410a0110050b608020b060003031140303c4c000555224183c00c0240560782c4094983c00b440e002d400342c590740984103000002d0040201c8420b01800001042c65049401c10041c00c1542e0140354201300564541c07068450241d000d40c540654506000001001441c01102c2e03c0d200600c81d03c03012983c000880701144028150f500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 702830341 1250 702829091 702829111
    0x408010218040608030a0804020a080a08030105040f0501080613150504031d0f010c0b18030703110c0d150c03060302150408120909010314150a0501090513080306010c0201090e 77
    0xa00207251070200c140c0d045081c400322030421000380b034000d0351660b0340b00f5000c004040c0483c00001509654908210b000240450030036901d00202c10320b441e001c0da5009002b500c0c071403490709540058001040c89258180d079034400c010201502d03080c2d80009a807401e0141229103d42c400038242201656004440c012440390701d442c50ba402c098040c00029000d0394174498000c3c0116061042c050303034000c422480703140c2c0103414150740d5160712401c13006010714110f00944e6440001180700070541d108040381c114880d91010303282445101d40400840300c6000e00e02501811084001d41000c0d40740740e10212058603e428001107155403623021030004100c02e0301c001d840300804101003206010074410030281c0c0007010b20741c5d0724016071100028070300035060002502d989100c00c40a40240700c208004010001000c80070b00691608cc0c035114007420090091034183c5007000d001c91111492640d04841c29030f4450030742c1d41540d031403400469000c0790005090f810000d107180c00040b00d980b00b41001c0d00400d101d02c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 702831591 1250 702830341 702830347
    0x70519030f030b09060415050a080c0a0905091c051b07170313120c080a0605041101081603020d0617010515010503040b0c0901050909071106010f030c090f090804080102 74
    0x4100030700100d2000c81000c05160522502d5401d03541e0740424517a10910841e800160a4069000032014641603080150050758402011408200008a4000d03807101260741460f05a150042c8200fa1a4281c41c2c900080c1d0100040410540b25054070285030faa00d03103411420180110000703801141001c84405c8550051b0405100424142034040810504080114a020301507125410718520500c101850f150700a070401d82049446d4840da80241805400c4519a0180d401d15000410040d01e089512080d40c91441501d540a698420300c6610b0220540806185c80308050b0042e50141c030000410a40d140808540d400700311110a0001c030010300001241e01d06001e11380341700d410410411f030501c10705208010001d50083e1520f5440048c0002180d21000300c4001600c041c0100400c44e54442481c1c0c0400803050741c01800049080e1140080700c0050f40ea860a49401c044240805810519440024001780300903412208400201e1000010004100d0301e42c04040c2e0465000714026175000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 702832841 1250 702831591 702831593
    0x1506010207081b240708190c0201020303152209061128020a0b0103080c0607030e0309041104091b03050601020c09040f020f0307060309140604110d0602070519 70
    0x1040210081c0c19850000d142400d4180311480081c0d2002d14544d1140320101c4042241e5140c5402c0541c107414040b00c05600d07a240c0385041c0126030000442110b42c849400010b202ea1441071550414142c0c0603005103195444a80445280031080100c207a0040580003002e20301c0340e059003a01c0c5411b0244500000c5900240c500f040070346202c94250f6400354014800c0180a6445400d0900301c1d080c0031811004541603008180d0801315242409040720542000000501000c2c000801008403408103840217035940342d0b000d404907001c040b5154500c1e481441803001d98101030f8400404250000c0c88141400c0e514503c040660b000d42c0079404245074600130103224503401d07004058018100f4006011003409400c0401d0800b0f0000300301414405050b6108025919035036480806c03140c0c06000e44020549800c0050060000c0c1c0c034046904021003c04046a1200401c849019903401004001000c1880781081603148218805542040e420018807000070310404c00d411008202e0541c5400728002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 702834091 1250 702832841 702832843
    0x1030b130b2d0105090f07140a05120601020d0e100e0316080d08070f0311091305012102090a020903190c0f090c021011090a0905010e01120809100507020315060102 72
    0x2080840014110b0038001485981d0f41c004030070380c1c000b80200540d6095a101441291040a02d2140c0500d403600040c80b10040d42e445401840c40708030030082e00000d0b03140d100049983c0c2d9481032030b650010f80300780251032070b9241010b109aa2890760307207031101d00c19002000190030001c2c11650034542194003c42007081400500603481000180d0418048138a020740c00502000083c5180108050741d4040814000c00c800b826a5507481000c0c0c407240d0070111088844c0c00504080c0105034680c040701034000d0782e840c40300305190026a8054022501030700e0b01c4511001a410100002c0d81c1406080c00f002c403001d48401d495841d0901480e0703001c5800d45401e010403a10304080d00032800c81814400700300c0d60160000389450181e6480c00d00012001c00b03005c480189030113500e207483d41c4042c01e0f020000d080c0c1c0c403d42000d03040c2c031840310140c0c0c0aa40d840c003074843d129426100007402200c1c140002e100d0303868000041c0300c0703104041c18000e15000d01039001a08088060100d204440c0030042407141c9968 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 702835341 1250 702834091 702834151
    0x70317070804121101140a080618090d020609070305120a02071814010605030705120601020c030703061b0e011e14030f1807050d08090a0f060906032301030b130b 71
    0x2000f0b0901b041c14080d69640301c00c0fa40301c1c403040300040c0480b21020500301e45482c1c0300340c07a24209440c505c3c2c03c80d08144180d2030304c60400302c426000501c0b901003c59003051021800f03230f0440340c2c040010466803581d200c071011280c010051800543c001d4440005402c4004e001480256802c0000002c1550020500c140c0841c01a08160100300c824004c01120507000004c543d00c9080034400b40c04030f5540c04c00100c1c40c1c40a2008510b4160041d10130000802501d500405c084003410388031b01078a000c0010080f1410070000103e20700003520114000000015030007080100ca00c00e24055440d030740310400410b030030340c02a02d07460903101041d0200024446081144000d4200d00e002404011345032800198403a06c60400c003800514000940d40910750b03030081880300410202e03075841c000b160b0750705000d41414403074465440132a0600007074041c0b403403900c01c04940c0c0042440000b18182d007591500c5034410002480d100f56114a17048040105032044c8200384207a40754000c60340803c03c03003445001080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 702836591 1250 702835341 702835373
    0x60c0403031202030604200c072c1005030a030e010f0905090a0f020909011217250503090301090c0603060b030f0c030408120f041a0907031707080412 66
    0x1404103000081d0701ca0304400301094075902c0540c603500d441001a008214140c0880300e440d8121406d00469180c0d10058074803052600280c603052036541e00c0d0a8140c018108a11000080d0846040310300903540000a801201300038003018070944a0001ca40340a86103a020f0f00071034240f8200c80300a60303001c0f0b41070701d466a00e0300d00041c0d15458030010618040001d0308000c5102c1d00e94070789076840b02242e0305598400b13000421b0f080240d40d45c0c040100b4485007188003036404008050030460f180b40194112000000c00219600c000031000c9505041000c913100b0443d0b50340410001c00d14555000d0007950759182c02011003041c07061500c0400b40460b03a5541c01a144488107204000c1c611034a400e040f41d22007034100c142650f0390b03244d02d41503d46200e50070051001015001c24001c8504070b1191143c803d920507010318100042d04403008001505c00c6941c45026881030b041440050401070741080c2030300ca045c0c4483c0c01e0440941e81c40350030340c115400c00e0544c1361a40030340a0901410380c3d01c50100c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 702837841 1250 702836591 702836611
    0x31020070f1e0f1202030f040e061f0e0d031103130623070602090f030f060601020c0427060615050c011b020604081309020403050102070b1f050d06061a0c06 69
    0x40501d0352584510450795102030903100d02980c0c1c41130010300900840c0d0300711200c40c1f030041d66182c4078400765010b03400a941c10740c0108a00c40041501d01076495814180602c0741c2c40754484003800100f00040344410800c1201003141a0080240c080e0003007028001c40381c1c82800105d403103818168021300465000302005556a030300d10403c5c101030400012150490740207200540d4410410010500c1d04000c00100c9415100340c15840e6240072011030603500400090342074902003209003040100351040c420041d0010404010a4040a0040354030b0303e07000c0d4842d00c4080340c0c00d980c2d44a40744e41c0c0000d4001c40700203d1000070b1080c030054000c0c801c104c000a141c0310b411700500c0a803a0002c6d81d844008100502441000445100c80c00010340700400920321000300750355658a91030b005020317402801c2c040300c0105c0c28030301080ea0f901c4143c00580d40040c0c00c1803400805c034a89401c110b2400f60008003641c0c0c0030740e9000003144031070030840314260f104026992655511681d101291401da8010401196 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 702839091 1250 702837841 702837893
    0xb031510021c0516050706050304060b06090a060305090a05011a130515150c01020a0512060a1514070b07020a05100b060a03021b0109030e0a0f05031020070f 69
    0x7919a500c10b214030001d001d1070800e443d40450011030444259101001d442d80c412414006061503005006620076440388a060100030b0684c2d007400001e000d450380082d40031041c2041400001d120b41e000d590300c018042e003140c0b0080701d5602d8903400c4580002e003003a8031782d0459120100c0e0b42812500d41002103449070040109213800d060041c0c142440b200e0a602c00c1c1940c103c01080080450152201c01080c00000c541d40c214540020308940d20500240520038043d10001d084c52170407110840491704000c0c64410381a0b03071164211950308e8040c60004815000f4000000403980111b080b5201e00e895800416211350079003482c51402e80a110039181180c2003010707081140d00d1b10026506004800d0401680b00d8401e1103810004200c61083c0d400c0760361a102c040c10074507500418a8080036070a80706144115101c488500c0385040501510780c00d81e01400310081f01c0c842c1c0d030b40206101c6117002d4005105104081c1c1c4040c180e401602e066840e82d2141400006004000303620a122480352544c0480c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 702840341 1250 702839091 702839113
    0xb031602060c030a2408030306090106030212010b09040612050c150c0c0904022704030e010c11060708070f030c03030623010c1104150e07080606030f0606040b03151002 74
    0x89610000313042280c1943c0b02c2c26551214038074008410340c881200ca2000c446a0385602490382d40741c0013124918070a0084000000d8603501a2007200c0000028291424841e030806142031034651269015640040c0d84420002e41484085207003035103640700740007070400100801d0402400b1906000100303441e0108101da400c1c0d4400025002c035003050242d80303100265603130b40005800b015010101608201114007108207080170440d100d0701c15072284e1164210610b45900444100408070402810b4421480d2482241d00d4204d000d056820301c1035036614a4240c2503603c01940008241045020034203c600e45c02c1056018002c0030098000c1031a01c007282040c501415644200c4401c2e410b0600c4031817181c0405000e00300b030002801450181040c00311280220403421030318264494000310b1592100412403203845a0300e10350082e0402400340d0b007941c07650308500351940000f424059108504000c00103c442c41d65010314132408040900c1100841e0307203010310895482c0900039a0854118807060030b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 702841591 1250 702840341 702840361
    0x90a0608100303080405010b040203011e08031306050708070212030a08061801060c140d090801061a0a140c010501181a011b05070f0b0c0f0f0c090601180b03160206 72
    0x19044a403d4a85907001e41c035a401d11500420755220205e8020380000004204030140340001c0802d1416686910304c02c076900e101e981c0c0c4901a442021403580c20041c002c0000714070550180260f140070303582c010b2806d83e41d6400144030b110464144462500b0204032043d070180c0282e030b4507a011609840300401420249e80101c1c0d80c4c00140103100900c04100c22407014411103082c0380b41003818943c11242c015100c480f019010305250f209285040d0300f810000b2030f44800320303480c820800040c0d42442d1304060440708265040741815048040503c07043c85440c40d94102405407500800310480800340d5103c03204000780545481d04e912080c02d20801d6075215541e60300002e02c40341084200c400500030070b26498210f007002c0e407651003840c441c41d46110210b5a22881c900405d80403400fc4220340840c000302d117041ea03c2c2d010b143e40348400c1750001c91031240c0500b4004a056404541454042c01903441c440c1b0104407000300e9000220041d10100800585450024a00e050800b550004007007510b07060081c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 702842841 1250 702841591 702841621
    0x6020a03020307060515040f05180102180105070311060a0c0e0306040515090a0609080306010323060907030b030a060c08010f0b030c3007020c0904230708030a0302090a0608 76
    0x914042e56040041c1b20100b080b9121122560010010f2005010300d02080014040036070394000c402c03010b10b070380b4000040c05108444003168003085145150380e50600540b450341000c0c2090b020b111a83c0c1070281034a005215a9100c0d44500c800020f14601d414001080c420710000f8850081c0c0c0200309100200f007000400c0300c41c4420000d00705143d5941c0301c0c031250802c0f0360300f1001440d403414400818100000c0c54059440303640c0c282e0b001c000a410440f240a1688041d468070440e0a41d201c002c20805d092403698103504c83d20f0740c00e0111f414020940868504110792509035402c55941c041092000d9202c004a0b0040c11851401e41c07a0380e0801c4294203051001803d502c55080d4000303111a0f50400810102d41660382c0d00c1c1010102c0405081d0a00c201e000031280000107001e13024500201d860a20b080c203008580140c440c0204200d19070074204611059003500140344507814001442e080d0030401072416803d581da02603100c42e0b0380d800303010400400350400d00900402c001040240c03d030315070385 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 702844091 1250 702842841 702842843
    0x9060d0b280c05030a0506040f02180f030c0d030e06070c080307060c050405030d031508070609080106090501031a091f2306060f0d14010e06120d0813110406080f0706020a03020307 79
    0x100040d07076119080000d002700f0550503010f81c1c581c004594000c6100b44c513000c6446140055415141070301c00384080503240c04200601c1a80314405880842c0071030b200300fa001c6140d25029040d18540301c0641c0300d00d40d01c60308940c010030b110b91000400d44100201c81c01a1420104942402d0f82000e0618000a40f1042d151414800301076841c4400480d80c1070700e00c0064000c151900c140e803102611100000c1c400728803402141e94039070030090300241d100e00b28403c0d0b9040302d4000801c40b807400511304c006200c00c00041c03c441d200380302d48107203130007030484c00680e40c50040c0101c0d1000903403141349002001c5e001c0a892a071001c810b01c42040242c60f07100c07881103400c403c042e80d18a9030b0300e001d101040001003110700044d40d6800d00450020901101107081c50f0301951080302d83e82803401010340c00540c2c13514801450000034580c4400308410045028032001d007d489110112040011000824200c41c0543d018025650064404482c111014008140944560700c05010407115588010b5528410208 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 702845341 1250 702844091 702844111
    0x613090b19060f05040b03010b1b0c030703172a0d0804020f0103050c0d093e1e030a0501091101020304030b01060518120606090a09020f09060d0b280c0503 68
    0x440c60310300d0f41c0b0600855025040c60180d4507113a50311821252440e80088800046901c0c4d0315aa075159004001510700c03800800400810310300b42150f03201418011103400700050310f6010300070b0343c4a91300144000110300b417841d00c0c0ca020000001c0131252070310b40c4920201e8240000c1900f40b1000d81c07920b4105a40c152170030f003008070341600c829660103070703506c00d0b40d90303d83c040c0d40390102c03010400040c0300c0d14072100b001c400b0024407402d500580038416014076502484030b01910075001910360405980180c5074401c00402e0365515060640424208500500c4c00c9600c0e964a24141040055030510b0001800d409c0c0300640c1042e085681d0413518100c18002d1605000001c600e01e14129422403d602501c0405004152240200c0a07416500c501c195400c034441e030481e1001a07082c0b10280b0415031741c50740040c00300740d1200071081808841d01c0c2c0603008607002001c018070f0394081080169410702a0079108400d5080c40d08411216508440d03c1200784a424200544c10000c07903401415a42c221441e00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 702846591 1250 702845341 702845357
    0x9060904020c070e040807050d05390a080306151e0c010917180f0d1401020d14090c041103010302040513050d0201060f05030f0a1704050613090b1906 66
    0x1c928980b4041c1c3d81d0b80000d10189144080000b0403400c00080c0507030701e1042c001c03918110720007001681d4601800c5040100b2110015800318240703c504455a401070030b2448581c6140fa035040e405083c4081700500340d60a201c004140320b540c2c240540038403510340100d6a224286200c0c4100900303491092581c42c42070b2000401e45448c210350a500c5480c210f60300048009182082482001842c0c20150a10140c1110401c100380c05040c90011203c48880c0103042c80300340d0005030ba42d00c02d921050b903c0207019640c00e001038101d11500344074404880c844810000c0762894844102ca02d04404018083d0041e81010030b0a42c4220014041c2c90540e1381c120303400f04841c0c1c0d980c10a40f8585540c1c5002815a01c0340300a500d8141d90190301400680b09561480804076480d01c0c185562450100b0285040d94403071040180410707070710381c5c00680000003805860300c0c060b5980000796603900140000061041094002c00c440c51484c03141c0c40040000780c480c08111744200d003013601403411038440e000a03c01e100c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 702847841 1250 702846591 702846607
    0x71a121b0d1b0f11070603020a031d0106051009050d0b0a1b11012007060c05041505030f0a180201080901090c031119230d060e010915020906090402 65
    0x8000360351501c0007841041200350018040c801600e00c01d018030001190304002c0090300640f28512132903181001c9401018a0341c40c0200c100e00951203080302c40c0c01c1568446824030042000f410041c42000f4481c00416224104002c000712407035016038036014491803030410840c80d00e03a10500000c25400c01c80010490380c031032020f40c0c0901000810034110744440c02d41400e417140c002028154142400008104182640c503104407415620f01e090352001c50140703d5600050041e81064016010303031702e8218185a910000c04042d0101451280c010520200070469048100b01d88650300c80d030543c1c000d000101c3d1034100700880d00450074019040001000014100340720940008118a0348540d8800756682d49007012002710311001c103131a04c0340500c000c011b042c007031416002c607042d84c0424900441040d047c0d20b81f0309075902007083c07290b04050701e0f00005010607560301c140d0b03845c420302600109400d1403c0c0b4141d260343e1100100003d40e10301c180840341c0c00307495600564900340800d0300c0c016614441 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 702849091 1250 702847841 702847891
    0x9020a0e03030a0908190b0406090f0b07080f0c03070c11040b12010f0501050619080603150106050d0605040c09120c031e050c06070b070e130608071a12 67
    0x3240d02203a0584400112120030a5020141100b228400401d0780c0e802c40030401003900b508090400505008002008200400e200d9400011928400e0b00101d000e050195103012803e0012651080828003003001c110400750003041040d440030500347c0d25461850f1100340513000400840d000307070080b11540c4101d161a142e99000210044005040200290290019a01030010310202d490710307034203210000900c0e040c08400c1da00b0702c3c5860060210180d80b620021181010700404050b454441c2c0400800d0f0352040c0c403a00ca029000c150b58146c2d841041032000c0054441c1c0c1d03400f0394043c0c0e01e08452048a03640c80034000b02518154401c9103141c04003800c0c41000d00105400107410340c00c40481e0301800d00c0303512200c410440d00c070340140d4806040340d804100640c02042009001c448041000a95041c4901003140f0b64440c001e02100c080103000340e0031012104e040c0c000c040c4661080c030b42407046164450794071480521412051386040013150304808107003005080c131140003079000252209030007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 702850341 1250 702849091 702849107
    0x6130f03090b1b12090a0509070c080304140607080613020d06091b0f1704062408010c0905031c0c0816030e0a08010209090c0c16030c090608030a0909020a 68
    0x1e810881d450f11107030500b43d00000e143d44004a4900c0d03200f200d0b0504c280c40741d400140c0340c50a4004041c440100c0c50401031200f0300c000180a05c1c00c100b542c86200c0c0c00242c1201c003850080b07005da019901d140c06030600003880c2c01c0c0040e00e41340621400700304000341031f5a416910111404010400358907040361816603805001d01c1d0308800240c5041c40a001c1e219040000904024503c82e9102c0343c00740395202c0e0542e0184018002c0384040301d003490010f40840c0b01500100d0060161a00301c03c41a990405007604030111230f00f0040959441e103481c0d1000e00d030b01032813060150108a009e4801d0480e1101c1c000301d10141905a5418003000c448200c042c030100303900303079004000ca1140c5010501e04070310f00280f40729107002c9014802d50300a4130100d2500d41c14030070345050400190007500152201128510143c000600078000c6100385a0051071000d0f0100c1120029445501030600503424007010b0001c0d40c101c1c2c0c0001405500511541d40600e5214801c2c00440b0300749400141c0c2d80c80710040450380c1c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 702851591 1250 702850341 702850349
    0x201020c0606042c0303040b0f0903040603110f0d15150c110d08030405010b0907171f0b07050f010c0320130f06120c02011b1214070f08010806130f0309 67
    0x88080713204c9110000001c00154485c078850365205a80303a550f9800b00310a14800d03540d952040d8802d0109200c0345020341d101c0103042010180140c1800501100601241e0001d2502248162200c07480900b002c200341e0818094901942920b40d0900c107040d006000030744142025041c6802c000d0b180819884e9078001204260708043c40c1c40e43c929190138203d01901c4551001402040da190002d05103070721074080703100c07211404040e025280d00d9511200110086034030103080000c010420001d80100e407200100300052040b8040c2030400d03038080449085904038499402414180140181c0f180e9500140c2180d40c1913541c465500c95032503c00702c5488041c0381d002848807500b402c6c40850b8490b0450050240f10b80149018000158505803ca0a986180321110038030394004106504841c02000b40d105a6241c8403400210b801402e00401b81c90300c42a81d07940c000c90300c68121007010342e44c001099800740150700000c000c03d0401c10720484d42c0440c1200080e1003000c003645000c3c1054420031011000b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 702852841 1250 702851591 702851651
    0x602070c0e1f060207060512062d030606150306060706021204060506090703110d020703020f0607090302091311090613050414071a0702010c080c03040311100201020c060604 76
    0x68a0898182c401c07110b44016524600b650002000070820b10000c1c504090310341690303c6505041001d540049409005400158040030b100301200e0f0303030011002c02040700445010280c0c810b40703c0ba001c0c50f0622a01400081c0180400c10b071340340140c0c05101c00c80c0e410040507150144e480d48242404d00082c05400c5000c1c00051061007404240245c0b81c00c07090040400b00c40750200d07915146002e0301299040c0c401444079142c14007811880121650140901d180240151401d40c0f107882e82c024207049040311b5540200c0c40c1e41106005604001c0070345644900003c1030740501e20095143c0c0c3d0b01d410540d1000318800e501c1c0000082d140c0e00d960400410300019032206010350b081510f020500e0b511302c0c0030200d00d0340c464540b0015144400e44000c408108203c000300389840502c1e001103c03c1d0305004003c3d503102000b00315400c851981003005000950086000e04000b059034020031110240d40c0796000216070062044012145000c1503030b030f80002040340c00060144920880d5114420423a03881c64070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 702854091 1250 702852841 702852869
    0x5100f0f0e131502091e01020a12050d02070b15060a05030a0207060216030207090506100e09060303070b10140103020c1e07050a0605070c0806010f1712030a0b040f11070602070c 78
    0x5211007900940420b038401c4441a20441c000c90034524914007441b00c841c0140c2c0001c030390703c0c04038551450010080d03100d440c0080c60408948281d0b0240e901080b01110303407084074810405005200114280064000c9a4032407920b0309034071005007980005064141c03040e50000300c04d410810305070b04445101d03415000380c00c507418050802a407151040d116040d01d1900700000194246440c4241d03808401c3c2c69110b000003000e40105020707e04200514807034161001f0400304012036000300c4403500c110185d8543c0000f4a05090814100305200d01005042c50700500020a0100002c1140700046c50f81c04001c01e040b04100c150f5515004503680138540081050300c000c10425807100017400e0950184804072a4940d4030811030340e841c5424401e40041414140060100d05c0c0002042d119165040c070031540c0c0a400c00c803269060307910513503040900503074520340c0502606150040b10000510a2400c01403001c441002c84418840e8510090040c0e03400610841004a80080340c0d014249849400394 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 702855341 1250 702854091 702854123
    0xb03060102010621020a050901261603051c09060f050d09080a030b210703020105161b0806090c0306010b0703030204183e0318060a05100f0f0e13 64
    0x4881c0280e100140e00036004418042a80c0c28034590707590407120804500ad0011400d00091010007500c40036282c0c41e0700403a0303e800c044403040714451000e507001d5006402410038540e0a43c01f1800305040d0a000c2c01400c1c58108001c5803c5201c90780310b04c0139810011b03900e10303581c1c00c200c00505501000a00720100421540310880d4580d0009000368030541c2c0d03900e511401d080d419800904400d400904560040d1000d10045d4800d40240c04a082c0d0401404010390a95455a8910001c00c0091075146502c83c02081034000c10812560003e100d2800f4005400d50400400d840382014090030f03844d01c60001d210310405101b54100d40051100a0300300c810101002c400401804210302e400c4882c40c1001d5400d85000350141c280d105d0710280304000002d4204c04640c01700f241c1c000608880c06075458201305100c1642c18800a44140314440000841385400125100d44000641089010078003025041c00f4440c052591035041e108c2c50000302500b540d500780101c44095124400801c581d5288000302 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 702856591 1250 702855341 702855389
    0x3120e031203090d030234050615090c120115020307080c061e0f130c0b0723121209010b0a030503041409150433080106120c0b030601020106 62
    0x54003c1d241007003620b480700341d610303412020382c000c0448910f0740b01c035509149048031409407042c050383c882800344081120395a48585060203c03c881c1c11202e0040440341411500e00000140c1e402a002c1003402e0030a03c07440d40680c10010140126400344100104000d0458001c001350340c00e4682c045401a59424a042c02c240c6411007540d480110410141c9550721581c40da412071031203508000d0307905500d66900822034859146c004801d03201440000300100c1c580c0c034254000d1007501d000f10910041001401580039000880985285481c0c0001d0100c0b601c0402110456400501d12100c8111070707100e8006050040503403409003640000780b00400804c01c84040302030400c96080c01d07000e101c0105032201344003103030404813845020799960000c1c0222078640382e4001c1c15203950316007689402e00f0004441d05041010300300000c482c0481d42c0c0b01007000f100d0034003440c0c0180129502284440420343e490b43c0040c0024010340d02c00000c00b00001d40c10764800d602c1003000301a1421243c3c0721020b210303481 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 702857841 1250 702856591 702856597
    0x60907051b0715030504030516020f04091b08010b1509190609080d050f03012106050106200307170a170f042001050a0c0f140304061d0a03120e0312 65
    0x196808507080c2d61200310190003845124070a98144c0c0740d1278030b070107100040c40b01e161140c80012680f00f14280a0307000280c481d0310485901e28480d00d064401c1c010748048070041c020141e0f0100e0b400b40e0601c44a03100079104c4907210031034a40c2008032680c90318000c10005003141003030030400821160390780000074410b9202001c0401c0300e4040d010384084042000d0215024454041c840303080d2042000104050380303401c0d590f0380780482d83c0342417a00a001e040da240740a43d102a13011400007110b01c1c607800c04160410140c0150b20b044078005600e400c900d9951807003803070316007480c3c901848000f0403040c0159002d40c458600c00c00c01c0c4480340f1000d143c08460a550184180c1d0107403425407800d13079032090020381a00c0e0310f042924141c40c1c0c3ea0030f041c5a58001c417050781d01d40c8011501a24280c4040d80010500884915601d00b24006143c545003080e10041890f00c00e4a007021400c0c80f00f00088840d03844070b11078003055a070000e130a8401110086030685c1d2004c0411542e07605445500c418211000040001e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 702859091 1250 702857841 702857849
    0x50c0103021615021210150e0102030705070e0a0f0203040c060509120106060c03030506040b010c0204050a180f03030e070b0910053601020c011706010c0503070804030c050d050303060907051b07 85
    0x18610081c0c46e45281c603800f50459004034030b0b8160418000803103560050b0040513410b2414411a462f050050b5a802c1c1080c170140d002208108240007403000c030407501d004070001c15031140b100b14250329042c0c83c1c10904511910500341803150004040250b51214019046d0020000009010440c8e94010051501c0c0e6211004e800091626012a046141501a50140c800142d440c03c002d89816000c0000400001d00141245940d600d083c40e6800102e03504e12044038024400302d4144400d506028082e102418100401a000000140300401814064810285e03094480099441901106860382d116003990140311038640100c005104803681160a44548680058103000700c140c030040ea45c4110006100740442ca041c0c0c220304000d2407007041b60380e01040504d003e120284040c1c4640b420365000c1007003601c0b025000034051052080c041090002800181c0b01e803c0b1510494070350715280d010140109201c0c0c0c07104408510981c1c443c0c000e07100c0310710807000c1a016000c00c1c40c005640d11030142c0300d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 702860341 1250 702859091 702859117
    0xc040c05190c0b060604060c060c0203160b09070f0e07030e0a06090819080601050a0c020d0803040b0708010501020a120f090302130c020c040e0705010f02030d06060f1b050c010302161502 82
    0x76115003400811b039001c0300d040b501c3d80d40380c8002c50355031540030742881203140d421841b0601c031044031881d24031a0b6210650150039008802c0c00e19080080c105070054201090b10b528a43c4100510341116000e03950000c07261070002032100048280341d09050700004c003c0c00b00743c1050501001d2001d840010b0855900784107500c056542c582c201601c840c041100d240d800308005000400003d40074000d055034092000700501d04030482551200c81c66041540c0c00e071902040c510070000750682107840c144c00341c60240018940380c4e00c82d42c0c441c0d4a5607108a800c43c1000300040b6131540c0355000b022030308082c0d40d00038080d488442d007140c1c490b40240a046e80d64001440b0b844100e080764140781c80f40e10742c0508440c02500201782001d00640f49503050710000800c40c801000404401c01c241e102d6a4041d00b47c640d113444c0d4204186000420004d000c00704c40b0300280340c0c5081c1800040740050b00c018010b40038200541c0700c07803a0411480700b034940407001070146040e1041407007401125600622a41c5a80e030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 702861591 1250 702860341 702860363
    0x31b0f0b04080d110423090601180812030610022d0c03010515030c331b03031b03190519090507030b010608090309060f091c0c080f0c040c05190c 64
    0x3000c01010b501e01c1b00035054201ca00000414210352017030700507100f40e80e403082c41030001550342c1a80c207207422020b40c2802109000801400418a4901d51a480100440c0b005014041410303c0000d11240789030042d919a261b102d4074032901e19000d101d03054181c44000c0081002e441d1006262140f0960481c14038403d000320006d00e0b0961600705020124440c1d05686034030740442e07205e400e0030344000161140d400c241c0180400f07680f644852440780340100605024517180d0400f1250141404501742800140c3c010070700400c03522010b04c4c0078060440c05400b40200c1e49840d000744203182040c40c021490200707810400880240440003446c0801c5074810314100301d103a070741e810046810040a03207007030119030420071050b035461404501070540c0e10308111443d0320b8017054034001410f6220000003403402502210307804082c02a0303460148020030703d20740070344031428220300d0305074807035124514091240d60748030965200302d40300300300707458001104608601d410680e24101a142c941d81e0f0350100c4050001c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 702862841 1250 702861591 702861629
    0x31101090b041b0621020903030301030f02030118020f040507030e0a0f0c050a0b040e1012050109030f020303100519090905160f140405070315060c031b0f0b04080d1104 74
    0x503c003035004560040d5609a03d181e4404524034646042642260b0b116800b44400b051642d0140b0045000303600c02d00640815050b82e10525007074520286003140d8950103065200d01680714041c0000350010100e800041554a03d2810340080c020880000941c0c8118440401008a0324054180d503a015010303a581150307540c8104440d14220340a640e202d0b203400e000800100c0450f00303d594105100c0100c0386455611061101d075100703049030f000c0c1c078142e44a07103038002416008a85030001e081184080c5180d8a8a40d20b801416865480740d075000e0b0002088000705850b43c2100380010340105001407115400500f0543c0e0b030744901008a111802c40004005400c02d800340303500084400301c3c41e074a0300c01601c0700c04020042a00804503010700d81c481c2642c902000011503101c010344066101c1601031422810000c4c80903080c001e110541080c4824010701003001d20922100072a80106074800a5495141c1003206014443c00c40c14418240386043c8017041c1440d000d007041e220010f0030b580b400c070a8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 702864091 1250 702862841 702862883
    0x120f01021216050403150209150703110114190e0f010c110c090c0d1503031d01030b03070b07031e02010911010c1101030203060123040f1205030f07031101090b04 71
    0x40d0b1060100460b0302000700300000703a03221041c404c0e201c0050030018100b6280d40041351800c85142c187d107010f06e5002405c8820180c200b0001469100c0000c020403107049100c2d0b00d4004000b020340510300150000c9900301180d6099001068848401e106032071a40e0b441e20100d5000c1c03c030000c40e02c4081514502c490310315100001e02d583d040d240c0113109804503210201940004d500c4110b00c601d840d51100000280300d0000c02c1c001000b144695107000c00700e030008808500c03c8201c40800350400d07090091028065130b000412070261034084400559030303c042c2c036054901c4510b12a0172041c00e401030a09280168065004004641c0220280b03030b410000600111485c3c1008031008050407840301c17030240c0551180e40030b168000810b04046000300003640340e17800c202c031608080c0003c40100140030b01c1190508440c039401800b0303116581142e2000e80e035480f516402500c106441e202d00c0801d030700e018144640c003688500a042002000805101d08000080302422601521660100c9103881c0000c40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 702865341 1250 702864091 702864121
    0x708070b010614270d030c050709180809011b060c35280b0415060504210f050f010e0c03210408060f150406050d0b0402120f010212 58
    0x35010403914603050045100007034441c0c410014459103842c150038280c4c140c0710150038101c1e00d4040c0e112407242c407a407840d0141c83c0060323582141d0ba0080c280b180d00d004501026001c00d50540e80311b40d031642c5410620004840d00b0101084a96514031803207004010700c0010340c0b0100c4c190041d5130b20100407203c2e001881038441c404c0f51150711160b410300221443c600382201a240c120300c80c41074081c0806128211240a40f041308800019190340d0b005900180c6440d2003480002424801003200481c078040018001d400f0300d1088041c40c10015060000a07800104950b991560090716a02154090b0400305d5485a40407c600e141c0e6183c0a08181c0030a030002d070b01008900f0040c001d0054103624280c0e0200e0300c070b07100503841c0315420602c0003003034640e01808040c3c03007800740811840310380c60000e910b06032607868085583e000750f00d40780c424460740d2605185116a1504002c2d00e00898980b032000ca00340048038004d03075110b8040c492101628140640040c980071141c8680e13090580c85124070303402002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 702866591 1250 702865341 702865367
    0x130f1a0a0905040b011e0f090e01050907110c060a08010617010b0a031d03070605071e020c01051b0d020c1801080601140310062912010302060f0409020708070b0106 72
    0x5504510200b0451070b00da00514400003061600f82c6180c0035140b50300900e05103032400140414034200032003060710342c0200b0410040c0f43c5065101910752404000c6040d8032405043e2400300f00b902d0000c000064000c008000c00301e00041d081a0740c403281742c0700c01880d8001c02c1c0500300010b00c01070f00c4049241c02d1604440d060b900034040b240d00d0107450342c07015401400c0860a4900441000c01d030316841075414805000c034036004400c007041500d0b2030803004014602c9410280e1104480c41d5042400a900140609c070704a0217081c015904c4915069414410030300e00400d0407107100e03c0040c8482ca5034080740030b61030450103680b000488200c41c0300e040c407000824011442d0a074014401080840d0000070041d0120700040c00b0b503017444181d0201101640d082e44c00c0100820381c0248061041c4034800c2408214800038503600703040c1400c0801c00c0c2d8580c1e0040c40040d1180101282c00c41c3d09141050484c2e005196003101190b80c3d80306860130030341c20380040e101a50303950080d0000245940c000c10550001c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 702867841 1250 702866591 702866597
    0xa120201020c280213060504060b1306260702011d120316090510020c0f010306150f1e1d011106220f03120e0f070b0c0102130f1a0a 58
    0x2070b55454082055040f900c501805031801000100005a214001e03900500800e112010810a0505052000b6210240c5c0000d401210030010340d110a000e1600300400d031840e170b10b84404181d102d00341e201c05a00c8040c81c901d020307004100130700024035015489a80458071103002102608003110b2100d031104a4480004c01100f8200009103034000700d51850a244006801d050003481c0c0c80b100805e2500c0e061000510160344140646071351361074404200c1100322000d190902c600384c03d10604c00c4a4141411a020a200c001c1c801d5680c00c43c01203c1d101c4885242210f40b4420304203410300145110280500d8520010200e14450465441181d600c0c4918031401e000b80880d03243c0110140404804146035108001240060300c006050203842e910725500075030b506c003004c3c0724000c800c1007202d460b040d0542180d84441c1c07110704402c0b40440c072081120a00c1307460644880c071480999001e07100b0b400946207407181040004c50300e40940940e407025a2421104402494450076164101d8840d03405c2c04004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 702869091 1250 702867841 702867853
    0x9030c09193c150e0106022104090506130515091608070f02010e071d090a020306061309021f110d050409021b060f061201020316052a0a120201020c 65
    0x10001801403800d1030b403081d00100044802188182060440036900048400f070408001084915410030011103100c0c03110500c580c500d0041c014103207403445035114914625851b44002403003a560101d180c0a00a2480310a000c603281619162040391302d45614148246410000300c1d00001402103420058040e40e2240d5045440f9038000340d070a80105146041159240c03000f1000d541000e102440007050402c0420200303d0300c030840c1c116900c000410a000f07592214007840f001d40d4002a140c0d070414001d850030b2507001840c0c12214040e016110003c0d42000d0401e60207204d00d0106500d604104180da603c444440a000050034ac0398502c0c0c1c911b00740018410f000a01c04d00003560b0050200c4202e22050503a1000300054580c105031044820500e8441100300b0040b142c14810b240c0342240300d0800c021441c0d841c15207240d491041a0800510400401052a2101114502e0300c2c1d150108066000359806c01001c03c080d81d110300c61001203074101004290000068014002d48042d108580040c02c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 702870341 1250 702869091 702869171
    0x1c062909040905071a0a0e120705190803160308060105030103120509060c150a0f090201050d150503070e150409050606010c0804050a03150b0a0f030809030c0919 71
    0x40900003900c030940311130140c41c200184030f808640a448448008102007610303102c1e080b40c0503001c040700b18101802207403202d4100d1880540444d6603810b94508032166400e5420f48031026205914903081007a5501c40080c209000100d0800140400d030300c250f07155400d03942c0342d60044a50b0701003803100904c1051942013152040e4002e0020f030180c040d0180040717050140c00d152003460410182d42a410081c000f106129001c1c1045c080e5044800c1811401c2c450850709900080c0b85219011000c2c5481daa6101480b01f03c1c04d12840303600040c0700c01401c8494803529000d840d070100d00103540580850390100f20b0a500360901d03001e041706d0749070000c0142a11390b072a0300064580300f58025003181c11090030807010469940c2c140d8102c01840c000e0343c00d881c0840d1032420440c00c4404a090a501c21802040d08002c03c00512031510140d030350004855032591141c40c0404c0ca4100c80409156005110004004a040c582d8000c040300034203058061040850900c11564803001c05c040d000740d107484c01c441001c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 702871591 1250 702870341 702870349
    0x607080313210e090123010309050f06190516140d0617030409051f1707030b0408070224181210060312110a03030e01021c062909 57
    0x52240a10300c441c18041e04800040d6002d150360034410003060305400f40c0182801c04202450241141106034510314550700e40082424001000300c604068951030300504006041c00548860f0b9090412036025060103004002c0311a1907087c0717003207590b1a290002e5012080e2000c1c41c03803015001c0d254036a030042111207094295000100007a0031a444d07500c009131400708000c0820140403644051511a82000070f60000e4075006010000c04030180700004013400320781c00014088852010340815140310207001d490502c0711030352016110020002c100400c1c443c00600900b42141708440442050341d4401028488004262031444958403c0c0005004204aa1110901501d0041c0096803000c0c1c0da589032071a24820300c0804a6581e159401081003040078580d01c840704601d41801d132112402d03c450103640303904801010781050b4680301a106800404c1d41140d16410340e100300c03540d003540c4202c6400003904051095040068035604031025140075202481031000c2881451032a280c03e1100b00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 702872841 1250 702871591 702871621
    0x1515010f08151905040e031206060a0c050610170d02070b0306120f0309030105160f1404090c0e010f0c0f0b1803310605031b090402040b1806070803 65
    0xc0c85036092032060050803a0f45032051440110290340303140084508081c14081907075901d4407240002d500c148030360714201560760340315540450700ba1203494032000d240c00c00312036104200401812500560702401001c9413071b01720303801c1610610b0b10b8442d1120303101d461072a5a04103001c51480140c0000b4001d02120714450700840c1c001d14007d00450001407022045401c00c5902185c25200740c2c00050040364030b08003805519404031050f070f040c40b1301580514001d407406221030800c0c01008003e0641c400548a00700540e00548038002040214401050020b4200c1e032084010b2404254900c08100d0003038828903004c2a116400000c560144070103640d80d82900002500a4281d218008070400c0241e0f8100050800d4400346001043d00c0084070b04039131500e961100e074040040c40303018014400f45820104a0ba00b10510b8000c8003514004c1100c001c9403030140281c0c00368000c0c00010009019000d44000d002c01c090b0000e80c078085c1c08001030810a2714890160010400c3c0700c24000290490260911 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 702874091 1250 702872841 702872851
    0x3071209022b0215030408040905060307150c0615080307020d02150f03011a03011a090111060c04090501080102041d07050f1306020129041a090403021515010f08 71
    0x504200090304181e9642c0710034100d0001c1e2401900e098540701540f40520350310245044c905103840c80e50500b51540000380c4918000c03403600300d0721180402e806032010420500240035007016000315a07000034004151000c1c1601c1912103c2c2003a01701000b40c0c50041d42d010031a030050b8019881c01500b81c3c203124034000580800d9030b005c101c050004541ca040e0100070b100c0044c01c07801171a540c0d0b0400501c91121511031184000803401400144241600c0742980140001c0f0105807540310000200101d41198481102c05690b01a40701030203102d034510409001512140e0500303001c039030388a1507010700300d0090780300d48405e84488480c051808500c0c000095000100c40c6025403410074040803c040302ea111400c52100e0b107400c8103081000c5c55081c85190050802d2900c0d84480b00e815030004001c4004885915108940e140740800b40d003018200d281c1c1001201821800f182d1800303080103501c44590940400703a5400c04e40018203042c19504a18201d2a4140c503047d1052018800403030781400c004203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 702875341 1250 702874091 702874099
    0xb0405060414280c02030405010207121115161202071d0402400506060a0c02060c03071505040302010b0d1a0c1c150f030c12050a081306140307120902 66
    0x8009400d9425400b1324082014240c000355643d40c03620000a28041da1940050b0308207152510140000b0300030780f801d030346284003221054404c003000c0d0803980840c410641c00d0424480010201420481c0b09040950b80c0d070255000d99400d00e031f444180685c0d030035076210078010000c12600001c5c0185044055000340a4921041480a9503040002c00340b0161014601da20703d0101c03084416078030740e80e015047e8440760541d005402c003002c0d030b81c6c090a039400c0764400920440340030550120f80e40e000c10903640c2e61031b04030b01000581e80c00380e10101d00400017581e003a4010b5080069103521801c0046000300c0380c582c80b00007a482c40c040c0001c500044c40b0090105154480200181800c924607110380c5482104031b0400018004500c4c0010606610307035901500c02010f40100800200f0b481d00711020440e007880040720f072054003501e00749080c20013400c0028000030010440c81d003443c604144117000e07200e40e912a250345440c01d001d240c481e4003044071114000341280d03003081e4500f40103800800032144094 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 702876591 1250 702875341 702875401
    0x31e02120c0f160302130c211b0809010b04060b190c0c060302120711030904090f0605090a11090402061b1203091018110d0f02030703060b0405060414 66
    0xa0724a00700035050860f000c81400102c1c0900c11352038082203060010400c0c84013040313132102c000000f90080035003110481242d90540f034030103029203e41e0040d80c1050b4035000d01d40e240e80c14a80300504000307000e0322072408540c070700500400c09050030b20401e400d444a001790b0b0340c1032014200d015000c08180603000810090321082010011300740520446c041d01007504c1c09a210f040035030342c040c0d02c400018510710800c180c0c1c0052440d01d01d4040121101110155404200e50540e8240388404212080300180024501001c0210000003c0740c0c601340b107032054a00c440c1140040f400c1211850058401a5103d04104250310700103000e04520010948020b0941d040c05110040c188d51540080310f50230056005044800c4004116204800b03094850306c1c444040a07160751100190085105031580c00b82080c1e115400602066051400c400d990040c1100c007034a890713140400190540d900018041c03030030000411001c1c605806205d40001c4850840700c80c1d41d840c504008600e507001c98125152a03952 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 702877697 1106 702876591 702876613
    0x10320031f090305131514030f0112060b1008180f030a080606190302070201090e060d111504170609031e09130c080103031e02120c 58
    0xc0140002c403180c0707514003030b01c15120346550201c00d019941000a141641026100b1900003180e803158218880a890381d2854003082d0741e0404521941c5005209540c043c40100d500540207134408901c031034090f40030a441d00c40c403604180004411030708000a1102d0040c40c090140101c0000f007204100b040034170340d128080c80504030b04110700100423803e1540e8030720680b410307040c2034151301e240d444050001400a40c80b0b17800403404200e030031744005510307082e070f001d070318400c0c000030307100c10a07981c09a5100b807254580d004080750b101042d040b1203901d000f038001c040e00c0900250714801c800442d140c064940b81c010300809400e0b00303a008104c25514400b51141c81c803c2255024103c5868250303041c00118018400038240741914070b0401c05400342e03a40034034a203040740e000b5120100010a4500401400c1506d00801c001580c00b070451b508031500140300074445598080160344a1a0507 = true := by decide +kernel

theorem cover : BRFrame.Cov 702697841 702877697 := by
  have h0 := BRFrame.cov_init 702697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 702697841 ≤ n) (h2 : n < 702877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
