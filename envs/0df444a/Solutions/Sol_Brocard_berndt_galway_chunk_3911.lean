-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3911
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:02:31.965977+00:00
-- url     : https://prove2.me/submissions/d00f195d-fdb0-40e3-94d6-a0a0b3b88e0a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 703237410 ≤ n < 703417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 703238660 1250 703237410 703237417
    0xa0c020d09091a10050a08090102070b0403051b0d050406030e06013f12020d0809030a0513090c0c02090c09130b030c090703050603012a030e0316080406140306090a02 73
    0x1070f0882c850041104560015136261613411640c07000c114041210004158050140d0750321030703a9100210b1800e0041e0310f400c82030802c01440141003140000350384218440205400c88180c01c900300311403152912240c0942103800600507500081e1520095810746880040c0050403990740844100001114160302c1c101c20031843c040000203550000f919106008007040410b4480c0160403424440c3d580401c02801d00304801c61074000c003c0c40c0d109005401e080072045a2040b109818410781d201302861002e090011203070720069405150080740500035030850380f083c8031148201c07400d590555440c0041400d03400740c0160203400c008001900c1806030701983c012140d2001c0181100c00500d280d00000301c2101d4120b42c1240007070384ad071082c0301050609008501029070705440c02a4461038001880140400c10300300201015180c84030b908a0420030300c00c031840d640b2100c85140c01c005030360500d128242d006111f61400504686114240c4c03c428900756801403000400d07a03100751701c0d440d0001c0043e40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 703239910 1250 703238660 703238681
    0x90f2a09060524340503090901091a01050310091d06181c03020904240501050a080c0a0309050d0908070e070210090510061d0f0408160f08040605030a0c020d0909 71
    0x7540b02e605030060890313180340d01c180d40314000440c3e44190807020300c6112941a8400c1c0030711800e01a1888460b2100242d903038513080c00b882c21584968500c90550201d180c10f621940381c2510704211600752418501d00402d400d0001e600700c614541307442ca1809031903611510040540d410101580a00300d094005160010929280160078202504009030403144202880c3c224140e0b1205540310410309407030110024502420143d0030302c510850b02034080e03000140f490400342400941c032075015019038400044641c0010032215a00b0280700041c0110545000300c900c00d100300d90000500c02c12902c14140304545550142419010703002802e006410f0703400040711356000d507014903e0070074a9403151400400c02e902d126400440c0510a0b1085140041c0c4001c2c0f240c41c9410030440486c1d0301100301c900c0d10301b5040c1e499400e1415810030060102213400024110400044d000901c80c0d4804007950148400c00c004100c40015480c050340e071200c100c10000046280303500f040091140b103034044400e08 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 703241160 1250 703239910 703239967
    0x619080415020307020a020a140f06090411040e1f060e041d1b1302030403090e090c0409060e060601090f14060f04090203010303020709090f2a09060524 67
    0x8900401e03800300340e0b082164014010380c060310001b015481c000782050010f0880d041d40102c91070300d501c0402e104400c40328425001c0d01b0005200115911107911015400d0740c080700c0c40380c031241c546d50750000c04a03040d01d07052406e100301e522045100030361305401021030302562100c4c0303c0c0d0b0490340b0500014103544200c0c042030300c41c00082411518018808014100201141c10240c1d50328032007000910309d09494104000c51060042000003a0003010310710540d0b03050f5440c0700c2e0b41c0d0b84443c0e5051070508030310070140d00182031010750420801150400e0712004074440c01d0300c096a450500440305050148200604040703042010004c40703d19019001102c40090981440c02031811603018403540251300c06c0100650010040040c194180700c800082c00038010180f144c1c045a407203004a0066241d000351041c602440011070a45044043c2c400320240a4000003001c0c1e560f8050f40010300881c45114040c141c40b906031050000341101c0b0700d10407851481e2207400d203904140940c24902d48085003081c030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 703242410 1250 703241160 703241183
    0x3040b0a140622052d060915060f0f090a090e060609100e0907030b0709150311120907051e090a0e03120f1b04030f021306120c031106190804 62
    0x7009541c00b07254480c200070819a02c017015140704244000c44031141e4989040d600c14103224040d078a500100e904840804249200700c0700c3c81000494a1080b142005804080010b100b800306d2189405001031401c21079480a61596801d4540c054458a000c2c46020b50030090015040e072502041058001407101811005580c50304120038a810043e108054145e1010310104100940f070b4524070760000652501c605881d140c105100c89007954010082d09068a58107111282900303203007921132040415036552824203100103a00d44441007805002d00803000541c00c3c24000803d2120035034990f10260103c2c03030750740d2016010b20042040900d98604c6000c1006a000421010065036000d0440d0100704001410208415072020084552000882405000400114840504a82c603a40e010388981c10702035080602c1e8001008590410700500c0e030210301010a0211981581c0300b0390384202c10100c0390440c00410803603c1d010381200341e41c8043d4810803403c0028490b1803c9504644070301c412400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 703243660 1250 703242410 703242469
    0x60204090e0105060a1202060d0906020913140702061b03060a030b1f06090302150313050f0307060605060c0d1103070507030f1e030f0f020f0304080303040b0a1406 72
    0x81c0c0c0c1d00120751405980d10350041c8611803030401c44d030300020501300d240c2d441c2065113030340450a80e00807044182030b01c5036550b00c0d080c20300038640c040b1071081308028001044155403914001c000c00312038401725003000380180000c041b240005895401980b185002c04142902e40f04015159030009113426081541c01d00d00000103180900d0541c005d0820306005120002c0d80b40e041c810740023899100b0010000204410009600c0d404107800c2d846100c814490358a550740c0d020910074003d40040200984203c0809065000010020341841445828248111a83d4504000d81801024070743d00d09900060401640c030b9006d00c401440c28141002904e0600149445540c02d0640a03403050f00c9007444d02c4040001c00100c03003c00c3d10031054141680c481d80c50252001410100e417007003580309000d50b05c040220541d000300089004803074180704881e13036940c03251040d50300c0c1e8001b92806c54201c0e6142c0003245024001d07020305100e04030504a00303501075840f41c0400007a0a103d0002d281c607443e51081400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 703244910 1250 703243660 703243679
    0x1d06041707210b071d040b0d05070b0a020f0102031605070f0609080711030303070206042d110f0a030b07030906110703081902090a0e270c0112050105030c0409060204 73
    0x56200c0c220b410b00c0020a919400c08511648004040e98204120764000100b0304c0070350160409130520070303100055018400350124490010341c03580038086100743c03a0005943c030410402050540745582c20340b4200303030342401c1e0542030740010345030000e04540840d8240000c40c4610050205507005940301d00d8041051780b6044c0071142181c0b419180030b03030009800014401c002c0c00e00c504900b015001946540780c0100700035107a5002034402800b100c030a13601d403048500c05101d030030070f03159060311003038540a1940340c41d20094890160190013083c24448140361840d085680d2400c4a4012602d0720066448500480042044a008170b0f5201e607100c3c0c1700026800f13980d028152480c420b031514440c600b000b0008400b4401100c0c0003110803401002600c00645803107000900b1280d150580c211240c0f5a540e09180020381012000038942844550900991001034801303030035070080e00c4441c1544d802c84050015500240100e0381c15511502d00c4a91a0070203501a89206000c5c000050400d40c0341c100a4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 703246160 1250 703244910 703244939
    0x2100c05150405031b011a09040818130f061403120a0806032e050c040f060c020f042903031e030601110d09050a090b01090b0a0c211d06041707 63
    0x1e440c17983d51407040e081a0016482504681d90084694072560300d0710360b60f14412880341e04816011303c039242000049640b0354001c0000b07240100142072200900f081001c1c001007260380b003507849001c4028840d0607241030104160481800e80c0540b2450071f4000001a9888840a4042d50709441000b4003100f50004d03207a00134920700161441c0c50225001044124151000581501513906040108100601c41010341004490a17030a155059080c54000500f07060084981917401c2401c02c42040d030b64a00703040513031010345040c800d4002000c428009050b540d00426032000450010080c6038030108100c1c0780910f510890514201400e0b10001d100c080c20200c5200404010400c0200180440e2410341c54010103000c45040820032510800b00007000e4444501c03d01c1085e01c000580500420320500245002a8110120b04004500b60001e4200880700400041c005000c0680c044507d90390504d0324084894000d0141d4186414900c001022031011440104640304090340041d072200820001e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 703247410 1250 703246160 703246207
    0x1106161505040b0a050123010210050a05010e070311040303031e110a030c0302091f0c0519030f0518060d0e07180e031c020f1b060402100c0515040503 66
    0x11803903081070700d0304540a54003e13007101c03411410b140c018403403401c40501c503401000075507203004100409200140d00304145105110b04581c2054200010405180c1045048078200116842c0a41d6118021030803242031095a690b4500104410004644039400080801c01408041c03e4848404480441103074034614041c7d2445102245203864190503100f4402d0454660400750310703240007000011a64a20213000f00650850324840d0002c451150f100c1c65070480c1d1141c02c0301d0800f80d188001b1a0118080c1c2070840016280e07208c2d602d1814400d0068901214421000d80c003004401401c101e0150000820310b0401980c0b005882030241d8100258002081070040300e0394581c000380e241c030054401c0514641d90360b6004000c6080d100825100484100084080041e1141c906a0a0300c0c0c02d03224030801c4c6204910002d4180e1380f1501c0214402e80294400c803408610070301000c0307040d100003180b050050520317003101a51038201444860324984c02485041070f2403074070305a66104511f01031003c2c00c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 703248660 1250 703247410 703247453
    0x9030e04140106081f1505090607061401140d0f02031c0305060a0e072007090c03020a110d02030708031312050403060509060c040612060f120209060607110616 70
    0x41100541003089070343c212211203171490078010f000f4030f030b4006042d80e482a141080a12014011410f02c6003055610065004106683d501c070507040003c003420001ca030b030f08808060000009400400803000101c1024080d10810f5072003940e40b9094a1091074030700aa805d4080c0c084510540c0881250030240c281054500081074180003062003480c048a401ca80310a002c113205000d222500003030085401d09074419151810000c0441d02c900b0100c890707018144842c01c00b1181d10000b03815401501e440100c641d10202280e0720800307000c0e42d41ca418404039016030410400c6501080e0441e00441c2e00030103104032401d21160396612400d0340a02c1040070400a000400c00340200205070142c190040c0c0000020708250610341d031b8091484c0310f2449050107014660886020094150704480c0040c69210a0070460381da4411980880f1128150304078494201040001e44500c0e0510070b072076096400561100911802406110580d072195410710b049030035809800c0002415402000340a441c1440c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 703249910 1250 703248660 703248701
    0x1721041a1b040f260a2004050a05060f0d080f07031103040f0e0906010e01052e0e01030c1704020105031b0c0309010807030c0c03031104172b0504030609030e04 70
    0x141c8100d1311204003002c4108050311540e5020383e0002807a108926000215a0500000f038007000100180440c0c4480d04641814104034529003158072891041c0000d460b91108030030054104684008110002045c0fa40b00740a405070324880480940301461090038500d440200c20040185543c11581c80b5819580c04c180c028400d08031100e8045d500010610b008202d654140700e07c1e46c041e1101402502c0c065808440440159009061000c09a020340c0d280703051a01030b0701e8802007a625841d0030150120f820f021104e0050380c800c180c509203541c001e0800035030381e40350b42d401181c41d94000b40c000314040500711b03100702c4c00800680c01081742d002d5442c01185d8a050b860b00151880c0e40c028003034010702d4544075047c40241d1300304202c1c0c2800d5074945800113421201340584550781c000d0350401c1302e804103100c0d038854521000161041c0c140203004260009600081d0208801c402400705d044006482400200002076040d00320861142c401c1c00d000b5071100800001c41c0c00c4884c0f0b0344c01403c0105004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 703251160 1250 703249910 703249919
    0x414160e04030e011d010e041404031d03070806010e0a0905070909060f05070c02040c031b0203040e0a0209030d2d030902090906090c06090d1721041a1b040f 69
    0x75018070075080f0a0801c1140c1128169031140c00040c501c3c1081d041c40400e2454100075640c43d030005020740c00c0660003002d00c0c28a401e0080808501c0400c2460f1400c681814241c6482e00140e2142280c0c105402001c050b0300b40154081c107000003800d421015511000800c0000c0c40520104029002c040b00c0040c0f14211030030200141c81c210000407203028501418000000d62050091506a4058501190031480d130301d0110010552400d071200c1c12580307201e4070318100758040010011541d074007105503016107900c1440d01c00ca1090b502d4142e415030055522000403030040444400f5001d00c80c2a25142806003c00d16022001c03070910786000a50b0b40705040c045262401005801250000c000e19203071400b092000e0f031b1001c00041441c0304503404122002c1903a00c003034000100607800a2003403041a18840c1240361908050310522221040761160303c2c4040e20300100a229039004410900c010720010804c3d030f804100a03003401030b10704140304000c208410700002400140980d107517041205241 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 703252410 1250 703251160 703251167
    0xd020d530a0507050a05030406020307120516080603010605031c03061d22020f04020702220c23040b07030201020c1e01060f0b0d02090111010c051b150414160e0403 72
    0x40000d404c0c13100c180654860998400190390380325500c180c00590f00d440c3d0810039190100c00003403d1008500345420402103043c0001b507401c0c200303225258600503440394010142604c0e582e00642d80c040d8842181e502164507131801ca05c03c010424100019615110116648819040b0042c005ea6144440c00d0210810250302e41e04001d41040d0a82062643c5a5001070324441074450345500c034507004102c080555440034900241d8400710501a0300070200c00400ad0081d00f0068150b101080300307009001c5a80404070031100410814090042c90681843d0031101160005181902150360a2100091160003002881441c00744440014405103514501e01c2c25240550011840c212031030b20100840055a030031b075031880312410009a210301503103004a4072112000142902c0b5803c2c050b003806d2680e0000c00030144503440d6441c00c2000f40c1c07404401a40c40c000c8803091011a094480090301150040e10710114800030141070364401c405044940205041d603410852581c0d41400c02e0008040c0c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 703253660 1250 703252410 703252421
    0x3130b0103030f1b0506010902211009060e04120c0f0f050c150915070203010b100c060f020c0d030f0e0a03050d0f0e030d0b03120c0d020d530a 63
    0x500b0141058408091791596102e001c10b2240000481d0003144501c6920841401c449079518070017110b03002850400720000d54050070744121014940b030400c01150119100449a00c01da406c01461809121110f03012a50001d04030070a80c0d40c1d007521004000050085000141d00c14090710040420200319020005010f00800091354a0082001542c240da04c0e90380725880100c40260815445000a001003800340110b4010307254401360f0410100141390304521010401c1e401201d0130844040e0f102400c500305d108580400030a1382c0168401030f21240f080d04000051448520089003010700028014548000401c048000c1000031901041c6e600181c40f81c000d41c048882c40501c094006c0c603a282d601c0c1d00c02c010080c02c50544462501141e0784082102c051041c48031110301c2d55410800301003a44680c402120b01d401409100d0900800354403840c1a240c0d01c246d21110300d194001c803082e412000b116080d280700c407050441207803039000c00b20700c4e42c1442c40c82844180c41300940c5010321a000c101c1d80d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 703254910 1250 703253660 703253687
    0x10050904032c100e03012007140a02090f10080304060c140105040803041203060b0409021c050c09040b0a090f060501110303070c0b06030f1e010b0a08100203130b0103030f 75
    0x11860300b4034102656800914180790342c080c01e1003960300d140c100110f40502116100c102d101c125000720300c42e8426801005001c3d06d4003580494030b50300c0000c04040c2d16403681302d41c007079070042c444c2c001700d1541c6640c801d81e190004085421200f95a940c0e0f09440e003113400c95408003011440a90004007808083d40408044840b541c00800c920300d404d0f038680d842130202620290405948030707034840c03106010340d2254010781540d111107611030740d682041001a50002083c4040345040c810103046074081402014050070300da0385150b00305521881800300900303882c520707103522041c109000142d100540c403551000c021103501c00315400341070800241404058a14000b8140d20410400140e10b03031042c0720040207a40103410440540b2403000082c0b0342600090711040d14091010b0780214042440b20040c81d0b545058020300c1030020800c100600c4102921075041d094000407000305205009034015075020003020103114898806072500541070b50240c201320040b030200340e80d40450075040041440c040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 703256160 1250 703254910 703254977
    0x1080d0516050d0504260a1103070e040c05040c050c06070e0a0b03040809100206070c291008060603210a05070f060e010b04050c1e0d0e0c1903050303040b1005090403 73
    0x212000f20000d5480d000c00d20003405480301107034501c030127980c144054401409804001202820541443c2603450203a1040300c2c80383e40341141c0602c1031401901507403007000e5260043d2003a5642c2c8602a108440c0ca410500d07400b41c2c0004001c02c60144150185016038010b040a80e00c4004280a12031141041004c4034150340c052004c01c4511035100d503d2411142d80800c200070707401e180f1046214200254414000401000c0c4200b14040c41819025030884096800319081d40d1240c10a00d9100d035060f01156104645222a0680c0c1c1400d540007403401c120140b0380585007141a4a0380603020303190500841e80c1c0368540f103031310381c803018240100e149041e0122402c21240c14111b01401691090703200600d000c00c10300200e885010800380503104092450b8a041c020b0209030546c0f19100c0342a1100c0b82d10848148018240803072b2104014403d903a88040158036544841e200e9440002000f040411141c034041c4005c24162906000c480c02a4842e4650300125010b512100384000220021141d58 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 703257410 1250 703256160 703256219
    0xd0305040c05010921151103100e06012705120f070902040b030a05040c031b0f0b030105211f0608060f04051902011115090d020601080d0516050d0504 66
    0x341002070135aa07148400800520b030b10417410f0b14040c0d1221049070810a4810700c2c10118403040c2c01c56800451103070181d41c0301c80881d240c40c0c001d000c038040e07001e0f15a240040e000302c80b40b61000a0040700200c1421400f81000603103691400080c9030901d0110320081540c2004000030603c00c0d007004a030010781a12082981014103010b81901d803808010840600e41c0c2c7c440c4081001d22185140b00005140c02400000b541468240081a131180c0b6105074540da5000540002d000c01420058038142c0e10300804c83c90321007281e10780d0b07080c6c01340c43c41842c99400e001e8034160031918281e9081285030b40c108042c0116000e481c0c0100541890001009401284000ba0400001503000700e181d030804507000241142260080c00101d6843c45020000141d41c0b082c8482d400030b107012506110300c00c14059049800d40e203140300c4126258a420700c40c030302c2070707a01034405480e216002e2006000714041c40003400300100310742d840f076500c0d04c174601800c50702040000070180000c140d03618003650141c0703212240696 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 703258660 1250 703257410 703257419
    0x31e060b040f2310050c0d0816030e0604030503091203010807090606032309010f291903020f010509060310081905030715060f090b01030f09120e040e0d0305040c050109 74
    0x1d1000c0f50700e002900c601c0c142d00084000c0c1c1d004100b9911000441c3d02160034040c000f81c40039140580c00c5e180c096003a00003039584468684680207482c0584c00400250030103895590f8151000d80000d4180032050103940e00395800c2694520240d4000c0c060701001b80101881c0100c1c600454200307030491810182403220790820030030001c0e041d80080100c0c00503000d044d524900d141e8014040d001640c1d555509003002c901c0708142c20820440071561000d40910740510b45003c0207d442000481c202562803103840c01c02c054607113411700828090042c10401d01c0d0003240c00000c0c2075a441140e00268500c02074509105965040101a22000040035000c800c0e14a64071201d9490150450081900745181400d407256503482d000040101080364564803001c3c2c8030102c0c40d025210003605940000e15120b41a010507840e4002c810901e9017040c0c42000d0340041c02000c881d05500c44510035002500c0390102003424100304003d003200e0b00203a80003c0d0034100740c0741501490901d039200c01c0c10400f10030020b01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 703259910 1250 703258660 703258709
    0x108070e030d2d0201200405091317160605160909020d2003070f030506061605010b0303031609053c031f05131101031e060b040f 57
    0x840c03100e050802401000c00c210500c03030303d1407804140b0801031204980685250750150442044422150340c40808803805924042ca030780a148180341d4411804000302e0040300079813403d12041030068640c00c0c10100112082101d0398841003d0200841e28040d110050103120301c1241e401413074055020040c42440c0b04010008501402000078655000803a19039994a50b4010800d685588445007000d030043c070014401074004662280c085110840b004400c203101340305403031042900410144c00e050310b06a22a8004100d044115850340d41c0b4039480419503010400b82d445000c812054660b21017002800a0880c9202d0b0b114a00540b44104400b0900d8030301501c21004000d5480c260039a0b0f1017034030003113a20b8a180041d41c1d4140c02070101d4105240c0e201c00070701c0c10a10030a1b206104640300e400b401c1e00344c0c41007104090810411078410210343d40c441e41041c1c02c8a20580c0d802d4003017542000600040340c00541c4902d4030490001801c010132402d40450000800c22054851641d45c1141c5826 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 703261160 1250 703259910 703259923
    0x110d02070510110c1203071e0201021005071b12030b061c051003210f0e0f0f0d06020d0209011106090a03051e03100911090a0911090d060b0108070e03 66
    0x9040c4048400e03c94120001008100130005008107007050225018a500b9200e6025480c156404c510b100d03400103d1140e40c0c401881615811380c024800c10110280c5c1070b00402010308040e04001c0003030141500328441544e080003450040004140a400c01c3c05c0c06001c54202c201c01a00a000078800240700380c1c0c20f68240c101c0029906400f051070396800d0a4020300c05101c1d0002400080c9100201101a815a041c0d00c126402600c0d12100705005640c10f5030281c902c0b00c40c17541d22400915401465040102030034001c0310010302035600da10541e43e50300c000da8104000341c4545076800302d070f155250760744624100150b03800240500010b0070040a9a034417848003441c041c061040000f0490000a42c202031990114000004940c4900b0100398a10900001d44218005241802040041d00360707010704648006200900440c1218030b842144009000041240329503070400388801241c50b00e032207981060940c03040301d0003d0341144000c0050004540035180f8070400034403c078418010349000420 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 703262410 1250 703261160 703261189
    0x206030103020603071e02010903090e04050607032c010b0f04150e06060f0a021e030a0e0f060c010501030302070612090201080712060f120605011e060c051507110d020705 75
    0x86542c039a50250165130f00c030201981000086d0b040c1803800e10480d0f0640c82042d1441c0309a0321040180d80e03416504050301403c0c0c0e4040e00603041503002c03803180c2d4002d601c1200352204000c400d0a5088406943c403043c4810507140003242e035110010744844e440d0890000c040058100c404002040c407a8801e090071040d2805030b0b02c2001c0340c50f00421401d590f441c0c03e0700c014400725400c0595907041b42e0402900c4000d140e009107460f0f2401000f0b4004124040141c50360510039a8440107a0040841004500101c0070441c90b0846030800954090725030a000c2d80340a140aa0000d001552600d40001c3c0000f01c5c42d44c00d0514149001d00318401030389d2100302190003110750302e031800f1202120051100248503e9010009030f290050b4000f490741d03120308000c29003c0c003400c13080010342ea0b9007109100303680554206d04d034000020501070090342d02440900d00c000b40034504442221004503800b001040042c0e80c0c00d8007007592540c807581d010780f080200e00003204080c0f0140c102586880302044071240301224 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 703263660 1250 703262410 703262419
    0x72103141308120a0902190302090a0b0f0118091a01080709060804060b1c03090512030c0c09100e100f1e03170c0601180c0906020718020c0a031713020603010302 71
    0x4211191340b00d40100c07000c242c004002d48444035903040442821340413031000724020814100040c1482045103d8400a050050604208203a08030300440b42d19a0120705c040c40401054004600b0800f0b07441415000c0141c0d64032b4800300c28000b00050302128000700117608001040000f40006a44008556005075208102040244000700010b40300300040010100b40d80003403142c60240f40c1c0c001010f40445805a407140c0d00000000040e0381c07240b10b0000b8404442d07202d0646545141841e07019150300c1110014201c8007a91a180719805039003080e100b0401191074090306000f0f074004c02290310001c144087d8940440403100c13640e001d40d948548400b60416884814400030100f1721011522009040c0d410b0f08c240d5030b1500603085030144503507001700b51a403400e220112258000c0f803500c0706481054004062082c6011103890b1600c1c107a040407011241c003440801d2000b43c0030070030074010310712a8440300020541d1244406081e01d0080c00c034109921884a91070160f240d280403641540d40544 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 703264910 1250 703263660 703263697
    0x41208032707090f060b120702010912020c0901230906011b0615050922050a020d261c022d031603140c072103141308 52
    0x80346a00c4140c209001ea0080015651004a0401001c2182c02c299820300c01c0c100000d03211119500116082070244100490b410880d4240d00c0300051481070340644688004100e854155603000c0c0500e100040780c0d40136030f1040b051a0310030700d0700201700f80c050514560001c0d9071411050044103181c2804d014680600c0700b88003c1b03125039101e00c1340c590594019440e59041101039103444402440410307100a5400078486002c15076150400f1080d024480d04054144a00040590a052100c0294086070b0380e00c5116003120044e1038442c4d030344840b580540e803520340c4005a1404440001c0c5041c003a0003601d10204490300c1d101e900c02d44100c4410a40311801615034103401800810300403080e030b410701c1401340300c58007000140d1384074011071003803a103403106001c041c08500c01503050b20702c0340e40b00701984480345000840c82c61804018000d41801944c4042d409a003414220280300da80c0c00b041400a501c0d44074454044803071102090300030015a210070510f10300c0b07880e901b1880c011300598641100300d82d07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 703266160 1250 703264910 703264921
    0x8030304113c09240d0b010e0c040f0605031501020106080706270e0717091902130c0503090f0c03211b0a02010e04230603100504080d06050604120803 66
    0x200c5502e10710700806059540c80b070801000c00c00701155a051585003c0802c0301c0a42c3d01404c102204035030075640054820704690030b041205d41000402012224145001d105c00109680910820343c000c04003a01c0d52552410082d000000134581d030004581561b041901c10003031107000042c94000c13144140340001a01e61412040c9480c944141c2030a400c0841c4540b020688101d00403071766018103090b80b00d4507101407480c1503256014070200d076011040c1d00480d08403005046000d00c060700c0584002c01d10005401c1566051088500300300c00000040d001104001b2500010803150002c0b807040c000408400030180700080d074504d0a11140305101d80324052040c8420126001e82d150507010018003011007410001e06541d941803080281e00288030788200050f40d003028426511000c0b000a00c0340c022034800c45440b004098054051034040c8205100c25482c00c06c81c0c070885001e14458030825a541d1000c1c3c16501c00e91ba1f032500b01074031840041000300083c80140030411400d5030b00081c0c080e16035585 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 703267410 1250 703266160 703266259
    0xb011d06122407090608010608070309080c0a05010b120109020a03020409050c0d0503210603030a0f0216140a0801020307051c061206020a0201060f0503030a11160803030411 76
    0x1481a0900695000b000041c9880c100341580714400a0f070ba001c900c1c5990304c40850704864280300d841c010035500000708180c1e03840f0b81c02090300c007402007441c130789003803011020607107080b4082c6402d030307840d954a1010b91102c3c501800780b095035054031002070084100540024100050500c002480fa5a8a008501c100711090107800300085004002032550302503030070200d071268030000d0043c009107001310b0103041516512070381074000c1102034001d6082c40340302001a00c038074104254100640c403a01400c101406003c4040202410303034001e554000310000320901c41400d605030428040b5034018000c0042c1183c1c0002514440da440500e01e039000913268170350f2001000e49400015060684219440c1880841d800608110781c0a40c0204202aa620004030002505010f541d900d90002c001e1201d24a104a4040121f002050251080041c3d5845801c0a404155204101341c0e04007000300810310028000c0c20103402010360300044108001320248546001d488011034030381d05500c0c402a01c4504 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 703268660 1250 703267410 703267423
    0x9010e03091e040e10050c0301030f080904060308030a021c110a0c0f020306010b09030c03060c04050d1505071e0203070c090c050c06090f0f0c100806011206120b011d0612 75
    0xb02400810032840300080709519585143c1145038103904250100f8a855103031000c49048a0300706d0300c400711070900c6940d080c4807a0b0203808641c1d480303500c85d000440440c00d4480158010719900d5001aa11709091981503d43c0d114613407810491843c2c500e180b00748182850072181c01d4082071038500d84030b21131458000d40c00d41c81d4402c0650140308000012031301409910042c00c10500c120110b520000300f02c41055901d5008680028040205100401c854206041e044400c00e2090315000746881c48030070140200c81d8200c96141c000340486c201c0340180e100c080c0b101d0702d031150701c0d10107141350450341d440c0c1d00c12400c03140c820004203079922184a08031510450070740d015048148203440c03580c148144000e0b50303041e900305064024011034107281502000080c04500222025100040003e00070300151040103000301107505120b0910343c0c00007402d41034803030700c000ba02e0601030708044003481d81440311401300142c0200c20b9071020b032580c07045484444800981d1220341112444050710684045606020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 703269910 1250 703268660 703268719
    0xf0612061e07110a0305071a07140a0201091e0303240308130b0703120b030f12031008100501090c0906170405100f06050319031d030307080a0e0909010e0309 69
    0x44c2001c4d00c040543c4407005088040c0505444c154048807043c45501d41c200a8a1500219101c1c20403202c17502c1100c006040c0760031580c000008c0e086101d8a41020100c0c00b00e46090b110042c6a20080c2050f4262103520050345e0310401814602c00c62580d28214080540009041c6080101c0c41d075440100711107984d005089420301c1c1c80c1d2030340304610340540520080078102c910f4904182d4941201d0400058264dc01603103800101f0091020f10550607240c1c2c0090484501c0d0100c40c0340108070719a007004411001c5e04800400149503241482940403600ca544941c000c20010310700230007480b644040c5004002103c04850313040394035a0b213849837502d40d502014980e581c2c00c0208084403541954400b07401c82d1004d4098440c4c41740300c101b1401c0944540c203801004581101011010702c11450007640100c400541200c0c81c042890700c0d00308058011041c081c002680b801d00c1d84005041c10a0001e4120a01e0700c0207012001c05c0e20440c40c0c81340140304503240070703401c2c60104c0d0501c807a002406601c00b1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 703271160 1250 703269910 703269913
    0x80f0405100608241003020103242304050103030509090a0b090a060632070c0e13061505030d11030405061801080f040206030c07060f050f0612061e0711 67
    0x15a84804490301c9804803007500f594610180f00e24404c90141d001c0d510b10502c1c0c0c01900030320140c00c0da0b0041d40102405051000d810090806020a01c0e01c01028113000d803091103000986c129900b05a01d02d044022615203001d1403c140040000030b8010701901d105140488007014240d64210a500040800140d5542d10440290034081000110f13800700d000e40703444d9038403040e410322190520311000d080040003072a202040a41031494a03001005004028820170400081d281c3c1c07101901da4040050341d1491110034601e00590400903030303108015403452002d140108481c0b405000035200d2002078100424412000d010b40c2c40302105004980180c00014402034030355403801510b005002d03c03400ac0c2c501140441c0040341c00209078064140c403503980104281d142d41e44182d0700f400345821a0b54221000c644482c0106a0480710b4052148500d9540da80803015141c010104103040504211001d05a0040c809000340600740c06119601c10304803400001850301d400c1c1c2e00703c1b0507108110061947d07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 703272410 1250 703271160 703271171
    0xc020418050a0b19060810020906040b071b1d040312330e0c1c0b040905060601120902010203030f04030e0315100b0906030610030b04060b1c0507080f040510 69
    0xb00f01d840d201240c09410612080702c00c0c06107901011040b01c2c1e50740501e40b81a0311046900c00e44c0c10311500140050314014200c0c0e400d00c3e0341c41d00d07802400e42142404450300180360302c01c0364031310191440700300c014280303001211840c9844002900840002800140c108400351b412400b145029412800410302c00c440e502d83d4500c240e001188811101c51816502d0f030702500e07400100c0f030340c1641505000b0000c43c070850745440a006006003c3c1c140d00c0c021200f00f281c8810700402c0d5681c5e21300c20b5803100c5003d60060005842e102c400100300c0410282e1110303803180b405850301c002d030b40d000058070390040c501d440c2600b04d42c40b58103054448039006044030f68103104241024100c1c000c2c078409140074045041003880f200743c450301c0744003481c01b4900d540d60f0040310920000c2c035a8541615850030000080c02c0024031103c40001090070b40d1500d8010742454100040c0361040c3c800711441c58010040b1030303403003001b0500b0304400003880580007030f0401d502d01001c40c002c98203100e81070040402c114034043d0100034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 703273660 1250 703272410 703272413
    0xf14040510170a090206160c0b0703050705010c0801060917011409030d1a010c15090501020c0c03151506210709050907020607021009051006030305130b0a0c020418050a 74
    0x1521180c14110680034081d000800c40329a501d016180790750745d00a144608003424031412000c02e18105200f581c60500301c07800004ca040e010401032010b117000c0ea440503521015070800600350740e40090040100540c90004210311944160000155220601c2d24a20109100c03034580c0500343c1003030381e0341207087c00e10300380907104000000400f0135100340d100030300860314039a400241c0484410000d60108c0c54a1007200000340304215914412100c20000254903c00c40d260305089030030001b0102070582c4642400109440d08000241690300038052004151901c950040954004140018000c000c041442c1d060740041200200b141c5c0300e00b4501c9003580c030709444010075100032803062501440055021070441440440c215110f031034281c00a0000c0607100d4080c3c0000d040301182604c040c090010780650b00f1406005501c01035010b40c1d991526858002c01001c190740031139006081d442c3e0204501010590880c1030a4000d40e01110000742442c412140d54080c0110034400400600a1040180 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 703274910 1250 703273660 703273667
    0x213120b09030901080708040f050601230303040f092d09030908010b0a060e240c061008060c030604090609050f1212010e06010302070c0f05040f09030f14040510 71
    0x1019009a1a11669858100e51070752070340b282c0c0d1110f5001a072800001742c2e055029422094015102d031020001090164490750300305030080e00f000c03411490380302c074050070015511215000a0b00440107585085d15041d10b00c114800648a5113060300e854149404651100f0400b0070300400c00b62007003420705c1c500d04590900810440c0400c501251410b100410803220500c11200580300289c0b40018413400c01c3d0003516880528802c0c0d5511a0f2041c040ca034071000c0180030850a08130743c0c8411038481c2e2800c60814101840244841c04440d41e02c1400c010300d10000500319080030038101d4040c0d0761b80319180490040c2669190141c1003030306080f110410010001411443c1035071001c16110040400c0c1106160303840380c402c05441414040c0018046111040c400d25040031050400510b06480c958441c04212410751001b8002610401d080003d41054010032030a500c410070b0070090110140c0d009002403000307400d00402c0142c480d040e051302185540443d009018000d000d500780350000c20009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 703276160 1250 703274910 703274939
    0x412110d11040f090209151210050105090601110d120209060a020a15061203120b0904051608070312080601030905060108010f060509040f2901060801050118080607120213 75
    0x450140d072800710150034220181c40340d40d13501a4014070284c1d40351128601e12010082030001190b00c8010004032050520080029000c0c4c03629240f00800c86600d04000c005a000300105000e0600a01711003914010170301250b890034640250529254a40e24030402c1d100030b02a03400c1c00c5400c03040010b11034091580003c0e80240a41c1700da6840040e01c07480040700742c10f807041c034410851040c2866140400081c0a8500c51030160401400013500000d1280015644c00040e5010f6513250040303108040100c40e4206428082e044220040c00c00070718507900c2c140400030500007502001988004200c2c40e80c4260071041c00c1c1038003c0b0440f000e41d61a03c02490081c21055040b07015903181000005181c20110040b9105641100843e0300719466501ca00d070603000340d218850584000903007810003444440301928041c243e00e80c3d0382e140a42c14100050144e20005504180301b80d00070008120701840000c60039070040c02803078044940c41400455a000c1d005038550000718954800e0045114a0f2003910b8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 703277410 1250 703276160 703276193
    0x806010603050a0e0a170a020307020910030201120b030d08181204080705190509060d0b10091404020f0f01050708040e150a030c0302091e0a0e0c0103110412110d 71
    0x108407141158248036501d175825400207240ca02c0b12a11400f0341250307803020b401d0112081c016a858030800d40c1c0080c1030389000300c0713180c4000001d0140074000e5590010080e800e0f98801803040042200ca803001030b60701c800c0300e41c002017000a134070002000d40001c03052400140c8145001c0b203490800c44005035800307400c42d00030103015100c0c2010000d031629281603e80300c411440d007401c2c00c036182403405200304400010540f5402c146034114100c0022109001107105860311500e809846040038182000c0e50711030780a81d004110468203000240c0e6511a0784005404200e41d0400d00707481001c0181c901c2d00401c5000b91650302d01041c0061b081e80e0718004d55220781100081c1c0c82c00141c00300c0802c0400406400040d1448810000c18001070a14446458110102410100550100c004100b0200100f12515046240c035041281410003041283c0b22802d542400c0500c00c0710a00c400c154414019440f51100c0c0c4001c5030719800030300043c1818000381c0c4002400707824018255041a1191180c0c4001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 703278660 1250 703277410 703277431
    0xc010905071a0f0301090f020408070e0103020306151c060e01140103020a050a061b05030415030c0e04180b06060405040e0703120201061a0c0f030d0b030f0c010c1407080601060305 79
    0x1001001c420048203d6802c00000c00c010740c00c0d41d003084540c200400308440642604ca500700800325604100f08032740c600605480f91800220340c150310606041c007201030440d64600302400c0801a10307903910f03880d00c0c202d03d503100644000802c003070030842c01410003802c424101c1d51a00000c00202c000840541e03060368000e54100364442d90f903506021480d030f9039200f41000500a00c084040b11858151100b0042c0d005034100c80c103050f141d1421003a24034043c080c3d1804266110200d02c2219040000c001c0c0c0b00c00100c1301000001c840e07001c2244001d0a03084018221104400000c00541d0b406050300d001e01405407003041861391000c6500e596684d80c1c00b065071640035020001e2a00740c8140070300401c1d82c036400d100c0719040c414402491159003160054030380d140601e0300c0c0c9031040300c03081000e0034042034010400306208880c8130a15007000f00d6901742e0981e5030080003c0705800e90300000d0480c20580d0280e00350359188020388203141006d95581140d41c2a00074800000750096050300000d000d00d0005e170707 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 703279910 1250 703278660 703278689
    0x203160f210b0f180105150403150203010e0709030b0c160b10030311010e07170a0510021801030204030f02090405031215010f020a0201090e10050402190e09010e060d03050c01090507 80
    0x400b04513013811405568012000315500502079411328098a4111200d0848418205070b100e5469944e02440d07000d00003041039010004100203a8a4580940c00000a003820b8404605503147c99207042c400070820141002c002801749030040c1c17281000c00070141c10078180400d50a02c004801903080503488141c00003031450401d145081b5042c86051041c0b101c1200030716003585046241241004d040055200d02e020b00c2e0000e802285040c800214207402c03d800040c0d480c600340000e10315503aa00403d907030415105020134400948950601d01103103404665144166071186021455481240301c440d03130f0351b03501e242030050115031011444400d1030300362200683c440e2247d0041381d4922103044003038000741440c203080055020300a00144c100c1c4030300d691200c101c5d4844000c1030036603102840700103118031560001d03600290b205a00400003141140d440401d5450b001528000b007201800251003080440d10020806000798121000900d401c4028400309036181000c03521020144a1800300d085041c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 703281160 1250 703279910 703279939
    0x9040e1015120303050a09020d140706030c02030d090816151803022a040905100501080d0c2a0914100b1b0a021908010f0203160f210b 59
    0x190311500b07540a40c18803035880501520100c3c050000508018044c03596406801c002d03899812407c9006406207044000d512205410203150030360a6004604051400b10301600003507011041361064984408046205403540c108208503204416801c02d412105600f09410026070440300c4003c101613000401c2501504140001e90080001d4000c0050700641d040da8840c4046800072081e1401c542d0341c58410750140000301e412501c4985050350913900a0a0341d400722102409018050003001018200c180500040540221901d0400419196035894100b5600e441b040001d50981440c410030100160b0b5a00b000008001c03c20355000b0904450000901c0282420f48860072500000c3c116840c0014129100c50f100811020780c0c04c241c0030315500c40000d0f07600e20800c0600040c00c03040524295142221003800c4500003070001d400f1600520401c003003a90040204070301c509480c20500e4500c45c0b855021a00340c003550800c1d0000c4101d5201861100c00b03241d2112281305d400380c840c0100356555 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 703282410 1250 703281160 703281191
    0x80d08060612010302190503030d060929121c11010c0c0b06150f0f120121140c19080d0203120a0b2202031b072609040e10 54
    0x42d2000201c0c011141c000400c0141403400301201c61040c1d02d51440c4200d503c42e00004e095500c8104210703d0903441e60720522480350944034074040310301c0c20307208084103900401c2c00e0040308180d504114813992004500c1d481b2144d052124078204005901117440300c0c034002001602d51440003084e078086628210003031a00f50300400c0a008503a0b040000d62180b5582c41c8104100643d10b450140c000010034031810b40c4d0507600102502e0401c11450085844d50150b80c00300450110580c03220754205c0c00300c1c0400f1884001180790040f0917810520501c15100d12011052501025002c0c15400020707a0000400c010304900001c0d041d240f040098522003280858100d03980d0241c02ea0b0400040c125502003001000315a00010240c01c01405856100d03004080001c44500d001e03960440440d000010001014045146040c0007004190681d05102d010b0725041c451040c94150208030303094180f4644074807080182650400c13a002081400b4189103849225183e041072612850340c0c40c2070507506520400c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 703283660 1250 703282410 703282417
    0xf0603050405060c0a0e1f08060a1a07061d0c03160e010b131208070b01050d1212110a031406040c0c0f03050913021e03060a050910050a080d080606 65
    0x4002c030003040140c0301c414080c40258032091503e400d1040d008a00200c60300c4110f400a070341000c2c688010301403107600b030001d0303c1c1400080910380b05401d1058180a084141400d1444580700090086e07160200c0389004801807a09401c11380b41e4019038003007180da003000011840d6035410164182c40c10304000c1c0c100c3c1c85040c0200d00881142001100040c41600448000f500541c0c007442004540c10703540340340d5001c5184101d030080e24030400024602040c048240100c500429059642c00244040c507101d0304c3d09800c0300e0710701c40c2c00c1184003a0305c0c1d4135014013a0040c00d5041000340e400b950701c000301480500144032100b10010380a0300600012914035240c0f1425810704441d807a0214845269980c5d2030781c8102c0400124203201d010f21003545542c803508c9290307030402109203005070340c0c40e4010f04000e0b8080d82c0210480f9186420410007100c0c3e04c3e415075100847d681964018000c0d252400801c010794800d81010341c015081d0107000400703002c00140c1840f801c055865640d202c0c0c0b0707001c05100c458031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 703284910 1250 703283660 703283663
    0x1518050405011a0d1b0905131106090105030406020730030b030616140c03032706010b040b0a021c0806091509280606080a0b090f060906011206060206010f06030504 72
    0x84d0f00c81440843c1400d5501e0048400b08402c86070701586454000080742c40c256038001c1e40503410840d02040040700d90307010000e0a41181e1060401c820100000d1441c0b1005000516940d00800e0150030081c0c4945807071007001121001180030514a10744220141c00000490300207420002003000310704000c11a81e00401180b100ca644220680c2029240f400d003030b6281000308074040115500703415051003c0c0d03000b011580c2e9548020303041c26070201c0384031241d17280704071140e0841d02c010440e180c00d04089a0403280c40504103a2598071803002642400c001c0c1c88235054009950f141c00c018280d00045031445110100e8109440f52101d1070042480c0445d00e1000c1d8000c004100401d54802807503420000006074004169400010314a070b05058500ca6444000030900304d0301440003112490003a0b0100720f40548803054180b4040c540060701e2070b0041c081c1405655900c0108101da44a100c003010200c0d07400006000780e42d0b9480c4000d51307500003485020764003034070343e480802c0c410f20030701a071805a03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 703286160 1250 703284910 703284919
    0xa0f030e06070f09093606090f020a15020606130908030103080403050d0503090d030518030c060103031b1106091c0b0703110c031801050c01060b03011701020c07091518050405011a 79
    0x40c0f040540b02110b03030013680110485060104181b4000f80190062042c241d10030011034400703c182d48140000c0500c00e1b04141a50309008100d1450650b00180c03165004034121004608462460168401001803c4000d0122480040080103000c408030090017241d100300e0407101c0d1a900381c0c2c021240c1d07000076030300c400c40f680210b441c0c000340ca0300c49d8114940004801280020181d100d00b000c034615400686402e2060300300714010010f02d030b0003103036090030024050f90340101507841f07a41e02c1029941c0c0d554802d20402c3d010401c4a103a8651900c1d204010b540400b0141007000107051152032120100e070601d000074240300590300741e154030030252507101c84880020f504141c45c82c5090080802d01da59254104901444002c44103a401d0040a0090503c0d6010702c2c1e81e541042c02008040ca01d00d07a03141c407540c0c01008220721662000601c00304456050100050240e03101e01c40c02000c045070303071121218500310072084070754200581c0500d0046218000070458100319440010b003084c00c032081720354031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 703287410 1250 703286160 703286201
    0x61703040b16230c03060105041503082101030804080607020706090b0d141501090f03030507120c0804060905130603080406050a030923150108030a0f030e06070f0909 73
    0x34403500000d03000c035070b9104070151040814160440160403d000d92902021340c056070a001c01410700740701540c01341c4001d540501401d194401c0034210292644001082c0c940001072000303600807584510600403144008a40c400c0d40e4a0034441101d400c540106182c41c040c0d200460404d0303000080d100c0848681c0e465000000f8034000300e03040d50f9004080300d03540c0141c4030a00f003014100161025449000d25030350783c0c4c5440b41c851000400d40080d5800000303110000c0d00052010071740007030a9520060340020322009202c2142c10031141e5451652005205031000320740400c030aa0480c403200c0a488040c2d584950101d0003401d044180e070103070f03c4080d10440c1c0c104014058603100d03c0081400a965040c080b610b40042d0f650860058019010790303a41d2000101038414001060126036501025410040c07959410101d82d103480c2d10031146100280300a41c003448030024040d8002d5601e05450380c040e07400c0d40c40d0040015110002d85c00c4d46000241500001150b111003900c02e01034241e40c2c0210a510 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 703288660 1250 703287410 703287427
    0x801090213211a090708150a02070c0305030301030602071703131712040b091905060105040902121614040213050618060a0c0203120a0813081c061703040b 68
    0x18400c100240e45540c401201100e002240303a030f291020010340030595103405860708204942c10580250441d21168200c08100c48110617003081d02030300024041d100581e540700c03610700070400c1d9229500040050001000000500c07807180d0181003524003407845410f59090000036404180b00440d0034585145e140e841c0074010802c600c07810240805280901403900d002c1980440181000329422103061180004203d80451306022119000c4283c1054010821056a03801c1e16040140101ea000c5e568031110340b0300355608c1030451102c6140b12410b440d030702c1140c4007035582815058081e10440e890003400c0560a41031910850310b9001340640c5694000e810700c420044140d004000012000135089807422056031640010543d548690b00e4441200f8141e00c145401d20143d101e80381387d038010600280624a07007240c505603100c0e040240148105095240c4600f030b034081c0300421a003040034809001c0d100e4000d60302c1202a59480c0030754001e0f4045213811035590380315900a000409106200c03441 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 703289910 1250 703288660 703288679
    0x405011d190c0503030c011e02030c041710050a09110109081231030c0b0f04050d1a070c0312111207020f0a0c03030e090103030f0e0d050106080604030801090213 71
    0x1060791003503207001107996032600002c1c13554000001da07680e00e0355100c100d00101080e00303419408982c1c0b03424065045140c10740c0051071501442c800c65200c03401c240440c0c00d001d0000d01220070199170002040205e410451448401449040c0c800c079020504085442450742c01000032008035511a001409c4600012440c500c081d00104c41c4120280100340011a0074a4080034031202047c502030500c09562070740c2070144041c4803e600080495208201d00d80e0810096012101601e10a440614481e409460f00c40064644a03201400045038141407110040e40050035142c0140a079951822900c80804402c0442d001484010041d080c20000c1499908001c031400340cbc0b04803280150b8420b0701c0c21641007410110341c400300b220081da8018050040641042c03000c004118243e9200403598110782c0c018140509070b662007000e000f840c8022481550340e04100c40d0005500c41c000b444481d5a0391022580c500d815a800c17030210312114004619003080d882900e1401c5240404450500c0c0b03800180c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 703291160 1250 703289910 703289953
    0x90a02091504090c090f03020d0b0402210c0a05120a0f02011701030c060f020a030e010311040f1d09150103030e01050708220515030402040b1f05030405011d 69
    0x41d401000001035804000641c5014000626209401003285258100000d08200c0e00340c20488040100c0d40041c00540c85101400804c0da900900a00e080d81b0703540002808002000d0480c1008070307210281c94000c0c400410710360f0028009441c001e0555031140204080c003d00c101001c00380d03501200c883e002107440721011103c50790043c1058008402c1007000341902030401d03081038600140c032060801800d0740c84400c081005c290341c40581510310302a50020f012483d01e250060415440d60740c44500440700608507401041901001d0600c6036581c21030020900129a4401211071510b0009501000c04101000c0d164128080d00c181030303082d0b650546010700b608c2c00b1a810031109200807800127030030320b004092610407500750ba02a000c4603191000c204446800082c060b150b0980b440f06507808407000d598120398100c901064580d41c600101d00c0070915024010000f900440e03003c4c24480d00000110b00440c0118024459130020002603040c14100844000d2640d020250b807071603404420030613 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 703292410 1250 703291160 703291177
    0x1b07110f030a02090c07022806090b040312030b120a06050405011d0d110c0a06020c030d21050a0902270a0209090a05100305011d0106150e12010605040c05071b05090a02 74
    0x700c95036a08d042c0d0703106c2652525196503102101c1c140e502404115044044040280390050665241c00e0039a65450305a10180e00e0440070300d41c44039000c82c0d407035449000112804c01c4010031100080c0041c1812805010281c8055803654030706000d5402600e00c003944244060110002807c060f81c80040880e40c440090252012501400001c03a405a9891214400400444c2e00078066254a8010141041094036031141403201c09080c0d05c142c10070083e41e810b003816140c0c82c0003a41c1d50301c000e100c0300a0041000c000358032180d49200d42110036914100202030b1010a0516900c650b144100310080780710740084103602139050400030302142000e400281d07101040b548a010032540e40e656160940d0900304552050001d500264100b80e2002d2040600a002c3d21455a20040d001c0401405040c0c034291014000d03416140803124002c0c094002100601d0007500412400d00300704002003868003c4d00007100e042060942c3c035410310340c206040200340c41000300f00500584032001d54030700940c41040d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 703293660 1250 703292410 703292419
    0x3040b030c040302180121030e2413170a030512150d0302010f15050a120309080f010b01031b0e010320030f07031b080f1b07110f030a02090c0702 64
    0x800145c442e004100b01942d04020100410b5061800700d520b4420700721303080055105a52804008a44c0c0110034040141040e14118031140c402400351450200c50854408942400103800b4400a0802d0000080300c4100500f039070607003050b096058a9030f01d11080078002031000d201d44a1400b886000346604440d11f030a4240c0103c001030041a202c2c4c4d00d003802030f000f6035900e410b00c1c20b500c51503010b0440c2e1002c407614600865410b06000840200c40c1d4091110703c0c1c07601480b03c2003054062042c49010304105d404960140c0c145040080c003804c0154540d0380081d00b0111f528035500d0405007403030120b0351140c0707503031400c2404400110004e188621086400c54068228111607401c00f80c001c0d4000c90320f44005252a1500000c003038180d41c2008454600e0300080701203009030a0f4002c00e85900210851041803145e1a1800003444178100700d00c1525040d10000780003410080107007042e10f00304609a681c86080646802010340f5503c0d0503038065000701d0a03400241c0c0c0340081800a00e0700a02c001c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 703294910 1250 703293660 703293667
    0x3100510020c01030605011b11120a0507061206030b061203040b07320307061104150c14010b06071106040b160c0801020f070b060d0813030c051203040b030c 69
    0x400140c0449020a600c0d405a00b150352103008550381401658081c01c0c080c01c0441501485174090200c0ba81481c1c80900102c810b0031986c2c1580d590721801c030402d03282d000d04403084c0c501d00f400d085880d103109109080108010151800508038280900b104880e000035000e420355170340c01309020640d030001e250651540401c100114030486080068000140181c1c0117100e41e50f40540c16103000c0d41d00034484225005500048c4039003140000460f2249640220042282c00d0410081001c60182d904144800e00b241000745004961010070756840e240038005018011445803451804c8944806065070401420850b03030003c55009440d0381034180003d030500e07140c56a00c124400d1580c1000d5801c0c50701c002071a0032074040c46408070201b4082c100c81402140b03071461441d04220140700e00000204035110310000206035580c0c8107841d0b4080c54112981558945000b018029a04081d020449031040440404169400d0410803444e407981000c00031803810382000070407030060b000140381010926042 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 703296160 1250 703294910 703294919
    0x12070306210b1306290a0e01060c0c0506280c2105120f1014100806061e0a18260f0708100b010f090b032d060a05010804080f0310 57
    0x70300c01d10380c6442003c0b00d5003e403d86840c40180d001c02117044454440d0790580700a0003102d01d0011034604503071060401e12040035440c07804d495151416807041d9441000414072141480d052074010b03071040c00c030b078401c9207000d503501c42d09845100d0000c101600c0324105494030703080c04d20b8008014107a882281080d0307081078140c51498aa41c2000c43d03c1c00c04060801c07082c0549071941c00788841c09000f1010100506206000101c1c0300d03015016890f40800c43c42d200800c3c3d560716400102d80848586840301100a1840b1030302400561241c04c16a0008d980f43c43d01c52403001c0c41c02081c4040ea122081140c0d00300710009161030005041001d07d640e00c0c080c400c40c0720a0801e04002290081040b080603200071400c1c01031260407075866441107410b004a81310200aa41e80c45454042070715112144c40e034032078440e001c580070350055020b6003980061035007424500040030214501c0c442d4604a4902018688420046880d110191001411200144a4079500030202d00145070b1155188008a802643e00c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 703297410 1250 703296160 703296173
    0x32c10051f051002031c0911010906080a02030402010908060703090219050f2e110106090b01020c0120120304050c0109030f0f030c0c0603051501230c011112070306210b13 75
    0x100e41038000c140e51030044502300000403da0300038118003424607050803441c102000e00030480080c5003c0f8969400400141107a0040d000300d0042d040c844100e49a91400c200068000c00c0b0301078050b4441c0c8074000041d80c801400007a180309843c4c01400b0302e01801e0b101d07020b00c141380303400350010501e5182200306040507280d54002002000352995910b02040c0001e207850b821074903160080740b486c07810602284207903600003036100d520940030b00e0304106000b2480c10660300a004080701c49064010b41e1b0001362140f19403070149d4051800742054804130801240152040b10039440028100ca00c00071080d000700f103032584684c148601900300808020440e99075941c0c14a500d8101002080e5510180105400c403440b040740692803e081c10902c144050051010700600c2115840c031100c400140a50845801e4202409041840180e10740320842600000e12501c4111540c00c00a454044002100721210300740c0383c0c2c008050081f80c0c5d1009180e0700c8009541400400d00c400340040c0b2400e50f40083c10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 703298660 1250 703297410 703297447
    0x12020d0501050f2202010f0c03021c0908070e04021804050a0b0f151e131803050910050301030c05060f0c0604060b0301140610032c10051f05100203 65
    0x18002070031280d616000c0c0391360396001078241ea01101501c2090001006076000000601410690f0804034000401c1789012850300d207112035504031a89110a616101e0f40c1c01004001c203071140380007952399258440340c0d1901c529030204e4000e075015101c01409105484600c840c540c01c50300800541e036442440707446590104805903948094002800c0400001c0002000c8039084081c08481c070359100c0b80c5003806500301c4d214401c0c500c2e00c03e4811400c4425000201d5012030302c905011600031032503078003d04010b0850b8210511003802076120142c140c8580d4880e00441c0d0503260300800140840d41040e0500c04540c20250b0070b003030800c0c010440c50b200b00c8000c02c140c51050b84a030304042210400d90b814503007904c030407440250100092409008840d62498484070485880d8a40026405883d81c1d14904110241c0b03401041d0406c00a4142900040402c105040c011441000c2c021529042c100c05481100d0111106212a543d00c051285140400c400380c0d42445520440b8100a14a9a480f03001e09 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 703299910 1250 703298660 703298671
    0x617042102150c030105011407050d1404091a090c1201090c12140412021203180a0210051806040b16032705090601030b090f0c0f031501020106090e0712020d050105 72
    0x50010004011b10b44e40401500b00078400903014905102c00365603265600d020844145003400704034502d100c540b48108064070020250756800744105001d42c18120070701c00c20200620f00444a510016100300c41d0a8110381200c0044000c10300d490303180c411003d0050421040e45000c0000c2401e003403c0311102030165003040e9164011110103402c0619044204c0001c041e0086d06540107070186440040d55481a03e9100919000e1469075a0f000300c0050704150042400a40c015944550402541da21201401c425038903080364044d1070312250104125401107203e0060030600c1001204055020980d0b00c600a0b44203017802406c0c41c146011100c56608034241000c0b0307d90003942c0030042c0d4174210b46120382000003030038108030321a4004c01041c40b00300c00138100c011b81036440340400c2c203d0303035020203e0f000400140021034407814012000440c80303014508180c019801e003903011030300f0480703407140310081400c03e00104551850064004900d44a00c801a0b0707008046c01c5e80040891400c0c00b45600c6070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 703301160 1250 703299910 703299931
    0xb0c0f0408011d010605010f11190b100e010b030604150b0c030c16051c050f0114180c01020714030f0d1e03020301050a03080315030d0306061704210215 67
    0x1242109401c0ca014203408140c00302c580c18203408010b01d982023007901c1c0c031a110a1400c0041c030001062500c1ca05180c1800c0d0f0304400007400c10f00020300000c150218040c85d402602031902c90355030304200301000340a008142c5040f400f0408030b40545820b40c85503401c001c010458140c89903070340507003540681000c04c0e03000340b90b0000a510103400d903045c0000301c602d500c001280b48205052101084102d0906800d800c00340003001c40403000d01204002c400d04900041c0300030320480a0300e0700e841700800d60030f55250f08000750b120071013071500902168910050178103900902c0658030b8102d03803059a507081001c3c99090b020f16094400344213000d204640d0183c0d030945a480c4040e007084516000d0703041c13000e1100101441880140661340d6581401c2048075000460035889407100c403509015003100324445135041c852501901042c6402d80c009008848407031303c6100450800b002d4000b501030044030020407800c40740040c501d1640b0442c00c450007407602d502c1150102e1482160314000c11005441ca034442 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 703302410 1250 703301160 703301171
    0x50a0c0305070f0602190602280c1202240a1e06030c050613060e18090105060306011e290a08060f0406120605061903030908010e06130b0c0f040801 65
    0x190f0000085540c020035403840100200400500b061400045140c4c0090905800143c04620891703804591006440d0423911200000414075014260311200041258000c10100da062106400880d20540b544d6024010031810041041c0d503550300d0354000c002d404180e5a4080170f00b141d09111080317031031003510600005000360075800e050310b5000030380e80803920546040042e00b6140c40c02c0c0030f01400315200b504018610300749400c009000c0304100d0141d070203555441d03410000c0c141c070150845401080c007981907458617602c403500d11003100728126a6400c0b08a030b07440208141c0824019440ca4681c00820b00d0700c40b4a03e000c26860b00381e0098005400007003044d028444a49080d24400080c01c40031101000103600c0d00164482c80c1600a5010300682d640394005001030321091510a06070070911459040c254881c90050100265800303401c02940c81d190f4412960200010254002c030128803110388032150300d030b0354540851402400c0352184041446807034241d2008001400c0903004080000c0791 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 703303660 1250 703302410 703302419
    0x5040902330a0e03070f0b0a0f091a0a0306061d060c0f1c0306290a030f061203170906010509090a0f060e0c04050103080a030b0f090c04051e1c050a0c030507 69
    0xc1c042054000490104000c0740402181022070204d40484980e401c2c0b10180d4140b218052b94001d040764441540b42e858008910546425100105005e01d000d0301d042190329183c000c1211100b0319441d01c015185903c02c10400703149880005000c2070340c202011250113117442c54016040200c010428441c0e03a83c8144d00b6440241c150003900c015003110303800440c801c06600342c0d60303404a21600301e2003a091000101c80040385d02c00d4001c04221500c445040c4803081e83c0e108070207124041c140e0140c000501d03000312182030100d4011280e02810940004100c541d00302010098a0940641075108070310400401d00001b450070a01c05540d0f1303005141c001070a11a0241541c10b0440e00b500d000c1c81a80f900d001880000c1c0b69809a400010041c60005884408040419100310300702003440e40c03080100c5c0c00c2008403010207000b4826103406403116800080c180300c02c091f483e03206d0010349900648802c2490100002e19610b082c8981c0100e01322101401951108d800f8518a07400a03580c90b00001c60a11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 703304910 1250 703303660 703303663
    0x50901050714300a020d030525021609200a05071a011d0402030a110105040503010f1a0d05030403030806060702042f1614070e07050a0905040902330a0e03 68
    0x440d09400800524004001c64021b4a0b020b002d000d0a05150395500412505001c01c0307404455003c138030602c201d070f51212002c069520b10300e046050b80303030304880d002c04035000500740500d410102c2c1021506104143d070b0103003500540c00c00100d07202005000d001b614081205413183e451040d500600baa542541001407007140481440d00154a20080d40c09010040e2000104006c01c1e54010490802c10110600103c4440c425a0b01540d0301d5800c0a80713030000301a0562060309101d0340303030b25140219410700b402e11098080044001c0d000b40c0082c0404c00100307001c3c20513145d2000004041600d001980c2d400201142d13802ca0021131001180c1c9400c10000c040c030440f201c903800d900b9180d2400c08131481d000c0000c60000900081a81c50400c3c41d4480d090820400207001d00441510316000b0300c1c003500000c002d0b0f088010520002600001d0004844c207140c42035030f9250b50040d150312000d0106000c0240d402c0300004142c8900c1c42510429218050081c006c1c1610b002541c1d00e41046501500805 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 703306160 1250 703304910 703304983
    0x1b0603061409010506070b090c100206151009060e0312120f1f03140c0a1d131e0f2103050c0909070810050a060c031806050901050714 59
    0x700e005000940062125581c0c80090343c3d840c56110003400400d941e078125081c00c204240c2c10080d04070008444000085d9008240740d8810000b0f0900444040c070820b0401c505501e14020400c0820500c08040c400079200300e101c60503040d0081c04441e00b070140702d04500226802440c84585880d0340e04144021124240740294001840126101c04a840d840204229641901c8010b01201030303002c1c0c048a05800b80096440c1b000018603401100c0e54131300103441c84020124000076038000400024980e00440001b03d02c1c0785421540241d80d0780c038440b850008020b1840e10035210b030240c01e00381c600000c411010f4034051001c56a00d60400702c4901c0006000d50b04082c211440d802802c3c0000121901c4024409a11030600d10788079020f40c0301d0b800a0419410070f40c1066401500e00040403a00b1600202d241042502c280d64280745900020203450148001c0e02a08000800402c805c121662183c4040c2c0310040c0584e04902c1400140c20302e2900d0540101002058005a200410005038444920 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 703307410 1250 703306160 703306199
    0x3040e09060604090302030d1503020d05030a0908030a0806100e0a081b152b02070507060f0201050f01140111030d051b0304080d09060b0306040501150602010b1c1b060306 75
    0xa02210413642e6003c0e4680c060300304041c602c980c0c0c8030345180d442c8000205600096801910b040c40080f1182080782c0c0700d9010203a035001150040e10001826000002111034030002e50b0303601c7c40240c07140003c0000c504009000c0400304055002e4144055581c03100f8140208202001003000e5692503040035103074060081d070144510306000c5149042540901160842e00140e8a0082032842c00b112030031510790780d804492041403002c60964100b00d400100c00094031100d4071b5205007001c00c844101e098074000c450001d14082180010400e0340c40322481640011014104900e15a01d203100043c0b07190008061012045d48400034800f003032402c0d0002d140c100030407030708991540c5480d84a0300c42c20710441008070b0300c65585008403818400b042e409030a030100005c090f0b80c59403c0c5814945d005e0010f4526a080340b60386014006007450051050003084c13180988240d8840300650b038125501403055005403619100e42040000c503040034488140917241070f03100018004e08201c11082c50340c052126 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 703308660 1250 703307410 703307419
    0x90c0e040c0f05030c250627051509030f0d0605100903030503011712070f03120e1002091c050a060f1406040209040905031b011104050117130503040e090606 69
    0x10100ea0260b03c041102c0d0b01000080b441c0d070759569000d1192a81c401913000700c0c0c14088000540c1000c010194106200c849500781c40b44003040100c0c0101ca0041b031000708000d005520001c030300c82408822901103076004060740162801c042c1b404030144e107070350700258411451581c1c80c0d00c01d10142c07a00e40308200d4103034440d2800e0320180b810340c1d40c09042440103028020800704055598182c1120400c2000c880401e051a2140c66146602c1c1001c0c10030b1144070110003051071000c06c8114145107101e030240d00070903080180703510340301c1224110080d4030400704107810128400b10301d5000448a180e10951a21a400a10b481107850404400725030f107080107000e0b41410034407050f0208030a010003513000704003120010303610501040003400030101c04c8c50007031041c00301003240b41054448890b048103e0707890600911602070550041c6296110711b00a46003c101504540f1540c21100454242d02c41d2056850f1190201700b501d03241d2a50300141c2c020400c040b4000100082c005007170081c190003040565 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 703309910 1250 703308660 703308677
    0x3171302030f15010e100506041403010b040c122007050a050f0f070312021618060b031306020c031e030402011e0c031d0909070501031103041e0c090c0e040c 69
    0x10304007030500f036040c03003601c550800705e001041600120851650050100030302ca40d54665980021014106000004a00c25448c10740007142d9401c0070300500f40c4208107a07031034541e00b00e0240404c3d402000f01940d001e2212000b51000801041d810008201c00c50160340202000e454528003e80351801c00c0b010300955401143c2e003100d041d0b000040103000d44c0e44c031251103a60300584060032464419016800601260031010000b08414403032006c41c0000f900c103030144480c0f0784404001e12140301c2610581d01045030a104d00000c50b4640e4003a2520f401e001040e6450030303000c030701580d900300e02002442c91420380c00000d000440d84c20030b0b580e0b4414014104040c5403010a1030000d00311106901e0f015052090103000c04440403000511504980c000821500407801c01c10740310307030b510781c01c03402601d010034a08014110080c080000340c0303100c0c031707402050b41c01c1c00215202003000801c651241144c0c007000a907404a0450704038090310081c04a50340e924003010004a00300070546484a0080e0184600d09 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 703311160 1250 703309910 703309933
    0x71a090111161112011b080c070302030d020d06080714010912030f030f0b180618060607031116090b042016050a02060c031c05060d030c03171302030f 66
    0xc1c0b501220070307000850b0425140c409804100e0080208035a0103143d46000042c20411180c0080998555a96035507180d4540c0e48000d806210303c43c030600500940d002f806403a0748116240c0003001800c064000c049000d0b691b0700069468103040d508428009194003603541a45e507070003610040109080326154500c1c400769200034102d0401c504003002016200c10070b41e4440e551940114841013806480d80e0f0034030b40b1064503219107150540c3c2092040c903140715503200400d490201c1078060340005024510700078030741e90141c0d5900c4020902c1d000a0042d401102654039042803160002e051201000c601d00d10f580040004889041d04001d806084100d2019521a60381081e9031441412340c0c03050540d500075081c440d01e03040c0070140080d8080000951079100b04404005803119054a0150104000c06214070000f038a104072031090f0000c0340d02e031820010034860a985c54030180a420191010b0810710b10301003590790100c600381e0440c4100786003401182000c1100c8801d0a4103080540004c0700310 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 703312410 1250 703311160 703311187
    0xb0301180209100b0a210603030827010609060524090103090c1208070209220305030c0c010606090f080c0d02091e130b070c26071a090111 61
    0x380c0c003034010b07200080040c186038018040c4001500c1c04441550b01c80c3c3c40d844000380300d4030f06140c41d00d441c42810404a406d06100d4011501030341d40c5622041850341d0b42c041035403c0290042803d003943c203858803014110f400e0a108100c0509030700f100225481d414001400710022440c030042c00201e40c00407a40b4040c0c40018161204a2400d281c04903c4148030709002040c80c51680002d10200c400d1440320080114810017065114400d41d44460550344440760181c000103d12035140040341c07002c10b000300213403090340150b600119100c882401c064031418800e0855240c0d07001070001c2450720105114034204550303140018960800149448684c08000c9000e034540c40b50001d001d0390310132000c680c02c09080745101c800601da0666040b65803510881101a41c0d440c00c0d42626449565004030300074a00c2204062000c1d60003410501c1e258100d56000840d0b0700c000302104420780340501400700000c150b10042c803004444002141c0d003030700340150303103d0840d14840c01004580b0003c02c1301c2141b5081 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 703313660 1250 703312410 703312451
    0xc0906010203070206160b06030604050c0402030a02072109140102031909030b1005130209091801060503030a0c0b07030504030906110709140907140a120203030c010608030a030b0301 80
    0x15500051252505801030389140180d003402944a140450380508424440501c0707251603002d801d085485c1d03200c20f801e260712004203440250454100c011354800d54201074000395004078111100600d030882c280c480d01800034040c00c071000a0010301540b4a283c503030080144001d40800110706848480060002c0d541c1e201d0100c0604441a0600140340403900540d00710000b542c101200880360307d00011041d0f8186d5160040c1803099140c0c045840240d40c407407003540c20880020707040e1030041e01c1c2c800c4900c0100b00f44690360b0b1090f64036490041042c2c0ca0070300c00b9100c3c89285440c2c29911284500d03120324090401842582054030f041c0c01c10000c6503100e0710717a8080310b0107401c01c0ca0300c25102c00b102500301100c6070800320006061012804040001509141c89103646400343c17503105403140c2c08408004050b6511a90151401e4410302040e90318124a0142c640300a04482c540b0a02c00102425100b10b0342c03103401c55800108450f051150980190b501c5200210000c000001c035040d509456040d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 703314910 1250 703313660 703313683
    0xf0a05150108060301020f0406090801180201050909090a210e0342040f02010f030b060904021c051312020a0206070303023a0b01090807140d142805 65
    0x404040340c3d00d91002e60485240180c0411480d0351240c448c580a07007588040c0c4140d40b80c562a14840d45684465040b0442804d68140d482d24a0003295408100454101910350600c0c0c1c01104400c5002071812140a103500c2040142114100c201110207020181803c827501d00a400003c4099082c0402d042503009031140c101c40190190720103000302092202420295407003182c0b45051000b80803d074001070020703502c00d0b41c421000451050044050340d11081c03800e0b8101c2002d0094003200d28003038024003c01e440d409c0d820068164101e1b02441a2142070b2694050704c031005e111a0306000b1700b441895803e80030b0b400281038410465020580c607200f140b0000d401c059006c034490252034140c50740045003441d071118800780009a00c501c0d400b40d82041003a4462689040800c40076940600410003c9503200302c0941865482c0141d03a0080100d10002c1075840100035240b1000100c03200d14214100c0001c100800c60103414041c1d43c1c4584074164200c003220246c0c3d400d44000150002005030640 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 703316160 1250 703314910 703314917
    0xa03080c07050604050303060406080c010903020f011101060b071e0b06090403200d0f02070f030b06030a02090c09030705040b0f0f220b030601060905010c06150f08060f0a051501 78
    0x103654203160034045005550000340540101c00620003480000006140560011242000a5a074880d5860b80e529440c00d0603e0201b5407d002c1000507103005031844031040e40604003007503920940f41c041c41c216105900302007128100030814005100e1001c03413924146041c0c90000e18400c40319102c0a2000200404032481031510300005000c241c070079000340b0101c030101d40e0310f420800200e03041c10b80c42d1040c0c002d1240004080d071079004150ba00c0003401108403455803018406140c103503154202c0882c4010b280035014030640c0803500060f2204014181f02e007450282c11500d5009140c20142040e2072980024400e07418010004003541d034100c0c1611240c04201c4443e40c090a00c5030110300030f00a0100c1e2000c2a0043c14542c90b00304020750030000194608505070781035a03881e90700a4501d440c59004a60000c0c081c0c2c194840002c4e902e0340084c13102c9810046e1480d4440da2178a01ca540ca0f0500d8008103415000030b400d20040c810507509e065003100c400c0398140200d01e0420050f004c043d0340c906496042 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 703317410 1250 703316160 703316177
    0x9040f0602040f0b120708130b0a020c061602070b121906030203010e030d050615040b0f07120c120e06030a0c0c06091407150e060a030b09010303080601200a03 70
    0x100006681114028500c0360000303c030056441004034015041036004841c03044102c1d0008141310f208011043c860741420390171141e1040303941c888070701e1120020004107455508100c400103400040003424403502001d0400c1d5808050754000900340b00c290717401031080c0f04e0309001c1030483e03460843c81d5a50003502041c428a060a40030440b00c0600f940b44c1c00a50154600740b0fa19120880100040002c070402110900c80340c1c0781d82c420300c02d500a07440d819103c2c600040c0310901801101d071000f481d0210941c0300d86420440c554482c1103a20b0a41402400892903051020040000401c0426103119080c10700c120f9542c1c050300800c9403884000d042104181d9a2007442d55640d004004103243c00e07401c05d50400038001c05182108034010101a045c40b01c1c400c7c5540012002c4c51203814030000f030600e03547c61651a40380000d000182c0c0005901704180b644a010501d01504c6030540c03140214026139419086042c10000900000d01052000540c06908400314804d01030000307a600d403d90341031070030094 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 703318660 1250 703317410 703317413
    0x9070618080a03271e0e010e06010507140f06010603050a090c0b0c150a0c031b05090f01051c1505030f070e0a020906030c070b0f13110301020f1c150509040f 69
    0x10a0000b4203d040f180c0c0a001c1010490803840e1742c90712441d010581c0501d04894403400b0800c01401d0034412103006200100020310694454005010503510605804001444460f0200d0404100c1018002258401d600401070254103000309602701103210401c2090606548807480e00011a0003601500d080006219030199010060580803504004401140741442125a40580700214400c80064102810107041d9007951a1400420415031122498907117000b0900013000c0b0f20205c42c1e41440300c240458050600c8034040d0200001c42c4031000181c03004040444141707550f0300c2d0042402988005120b161102d40014410140c1d0b5034000700c07019a0703855060a1010744540c510107030700400040244800100c01d07030080c00d4207a2040400103a5941c0d05c0601610844040347c031240183c1000252102081081d01001c0000102800141c50f1807802c220030720f80f69000010062000c0c8400024000400ea5882000c01e4204601070001d0602d203071400048064402420141440080001d002d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 703319910 1250 703318660 703318697
    0x9061e070507151d010e150c0d0c05010b0f0d0b06040b1008040317240f1815240a0216060e09100608010e15100c0b100302063009070618080a03 63
    0x80031600448e0481c1c0d124100400000c0a44614040480e429800e02005030000e2a04014a0b40a001c0c041c00300482100303076840d400d8400c035010341001e4005980709034420b0141c07540e1003c01c5240405840e4504941403510f401800c0d200c28150320082490a40c0c248103003100c000300a45101030805485a803650086800074100210001c101c6030301203c544003460311710407000012489050304401c500301c0140200d0070310001d00c050072070366a881c6100904080206641c04040d00d00180030b0300c102e130721410003480005150b0240341c004030082080d12105992600e04814104e80c0105c880c01044240e614020001e004c040c410300030040c6800c45140080d40c401300b81c038001c0d90b60b4140141580c1c08182e070004090849169078009448c0c62038880002002c002d2110603104c1241e41c054655403074800000c01011083d6007c090068203000ca143c0c1244024480e26061400391084c0b00103000e0300e610b0050090f040c0310110401c0c0c014103202ca0303402c12860341c02184a400660305410030010a40c010b0703402c03c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 703321160 1250 703319910 703319917
    0x10e250e010c06061d04120201020313140a060e2a03060708130539150306040f020408030d15061b020a0815010302040c020309061e070507151d010e15 66
    0x1581030a0f14003440c2c5c2c03214004d80d4814041d40c05140c03080720304801d2160403800c0c0e00c02291040301107400200060000303000c0c9542c50006c002c242c0705803003001b06250386110580c0d07501401e08200c2d41c03029284041c1003450050314419040c5880203c180340340c9600110b83c82d050000d00700303000d0080701c07800036046031586a80002c00950102c16103c0d00043c00c00c60048101c5100d81d600380600480c12242140d0701e03031022100070010b0040c48004602d915540703040c0ca5500007800d454120351502c500118a0309240041d03c00b03030207030704090341d114108001c0000880e242000d0300806043c049804200710341d002251f50a000d408041c081d140241d2030b001003031141805602c00012489100030041301c80c511140580d040c0c0b07108843c103011003070005500b240d9034011116211b9020f03008019200c3d00380701c01c00190403414551008a0b0811205484803400c014a5078022442c0c4864113207600007039540080320a0b02c0300d5100031417801c043c0c00c40000800b031b41c1c0900b600c28000c02c107200710780c011880000c0c05d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 703322410 1250 703321160 703321169
    0xc060306120209090a2102060f01050d06050a0605040606030b100e1305060f0a0305010506030d051e070c0308070b0406050c071a1e070c060e070602061306020f03010e250e010c0606 79
    0x6d100741a10003540440071a10820f480c20f0040c018207010071900050024402c0c102d80b0300502110f103114a075140c0000500d1302030f0084092a9485900040ba600da0f40100801049903481c00280221040103011407020041c01c400100031b199084000d15036110aa03c00d01e05072018400150380e0b5440000c078059100701541280d1003074110b03100108201c8150000c500c01d2005400b40c9441d9000140107441d14011010503144425070b0020041c01d801c207000c0600301490013030501c0a8030a5603502d4518465201443c1a40d00c0c141d20400c00091001078021143c024141c000041c2c50845540c40f00f218044c1182d1140355070f102d0314008640d48101040a409540558903040104c07401d20b84005445104000400c40e5110300b01903c0c01070303c07100400d40f0401c540064001d02100d07903c0b0100f0f0b044541c42a0421200c40b41e0030300c07031581d0100c1100007031800303050311410201c1c05040c5200407c118400107410340c51030740d0491600040080d4895820a4821001c3c2020400e14540c0d1604002403c40c80c1c02 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 703323660 1250 703322410 703322423
    0x31709060304060b12010902060a03090812090319051314011101060608180303061c03050c0f060105010e0409031706180405010209120736050907030c060306120209090a 74
    0x140b109001d1980d0084801840454007400328800d1000060b00340c135981a0040d611840c1804000603c5009800001c8d0070b034800c1c05003031714000345444c02c0c4050010541d03c2022039840410032001000104c4118040b01c0301d542007072818013101c250314014080c0ca0703024607000c202580d40035241d117900ad202c0903d0000d69140c000e02c03120751103400c01002e0840c11540640000d0184001c210302e4600801181d00462026140c080c031800050755107440c3d0301201008408200e8100540c0000c0402402401c601d4514000603011a5140100060184482250940c8210300c2c00050741c00083c0c120078650b8440000c1d0701912180e996100000d4102c8103540f4050b040c1600304000c0000304027065000f000100380c1161074050100200c550141d40301e100e402011807a4141e41107880d0300d01030160106012503030000031030144408000e81c200541d501511040720300c0d8440c035030034001c1010107444103014000754a0200030852074200c0f141c441d8050408080d009a9503840803608840080c0000400c5617005003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 703324910 1250 703323660 703323667
    0x50f0706360b1801090623090105220302010f05180f04060b04180e0303010630090b09010606020f03070f02060408030f040e0108030f1b0705030601090f0513030903170906 75
    0x350b269600782030008183c0d000842c05100803442c1401040e40e100b040b0388150001e41014100f1202804e9507001080b054148803003400405403000326440600c0381d580755080c13201822032840c40054030259084840009110083c0880d04c0c1c01032007240306030801c9108441c260450740140003c41d00402c610342040070310040014000c00c5d13038040603c5081406a50700300800c5035a501d1007945407680401c1c000c240000303401c186204144c0506980301c0d003841c140c845402107442c200e03031903c0f400c07142d84c01d2040b42e06030314480c01c109040c1403e2081100900c0700d400a80180c800c02510261070740b158900007414501d200c0f01e00070039501d40f0420340d0701800312102200c0c3d80d0181c2200e4820f09412a01c60031a404100f2000072a5128000c8140c6160b50011380d0404d0504d50040e040700804042d0300343c5000c86100309500014903980402c4828000d0643c0040020441c0d0507102c0d09081c7c405c000c02070491901100c0d2030800082d403250301c03c42200d405c4408192940d01c19000b14140e8801c034aa115030100011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 703326160 1250 703324910 703324927
    0x7330315030602031e0112050c063007080f1b0c070306051008071703070201030e0a02040626010501051021090312060e06010c060c0302040302040504050f0706360b 72
    0x2120617101140c0020720800a41e83e9800c0200b0050440100051240e0001310700b24000d0f06000000c0d0098641d0424200b02e01d41b4150b100d0345d04900400000d1105241e188140030380150005180ca800501c2508065543e151030050030108561032007402041c1c540010312444805424030842d0f011b90f07840541032081d03003002031490102044a024400c04d44c0601c030000100400d06103100380101c8000d0700a5810301e13003160010b50007808000f15101c0300307000b000c448200680d5103226000c00751094030782e10003407003d24207034000400c0e086000f50441070385004014002580c4548410020048a10b05a214000c644160071081a1310203021114a8100703ca40070805030000b8074a00d07580c8003010704024881e0b513601100e40000d016945d050204403c140c2c010085085600300300c4541c1142d04015140554903404242190800c440a036403a802600340e000c03018400340720340c1004152078a814215003029000c0c04d071a660542d5107030011014030603000d07440084400030721002407000c001030035191140e0307 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 703327410 1250 703326160 703326181
    0x1a34051006030b010605120a0209010e130f0f0204061409010215010e1e1303030b1f09051801060f08040528030f1d01031a0d050733031503060203 64
    0x81d0000f100c291005a00104e0454402c20a5a00c100061405285c05441d0310000d1802940038140310741c1004030308400d485194480700803c0340070f08040f04002880508180c0d0f00300c00c564034441c12802e218010041000002e60082003008107000c005c0c11035545075002070050307140100c0301a4140040116500000f0031404110700a80b0403a01d81311200a240061048552428401c848521159060f1040c0c103000c284290311a0b1903a000c0540a500c46401c140079100301048403042c1c003000681600780500450074140030880a209001d4442507240d4101440500000c02d0042060204000c0c400000c041c46020452107a009207188040340f914607603441c0b41070214004607016004a404188049403051140034030000c414042e611010007aa4030f80011000b8100041011800140190010304155034840356100002d00c542c0042110510340305103040103100707015580803012000b640f072040103102c05d10441d41128582c90002900c020f00070b20616400040e40000c5c2c40745201004004501e0701 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 703328660 1250 703327410 703327421
    0xe01060f020c0303040e0f041b151404080a020d050a0605040b0f0f07020d0c14030a05070c35010f0c0806040b1507080f040305030703091a340510 64
    0x80390760a8804110100d41403541c1d9110354450084103080540001d03c020310b141c1011908a44581240c2c05043e0024a03004c10250841d004001c0c15003911340340d0303200c140d0820368503580f00c0024410f05003840d1604007141d0321240e0b450006130140d15030102d130303c0800c02c040c4040b610031580040e04002d281814240341c400b240048900c01c58030200c4c040030844400e418011710b8410003456004040310750008100303c500202c40d0808980f8032140074004424040188042c00642140e55103842d182c044500b803c0b00280c0e01a4800c44008030b02c0301c4644098400079184625590310018100d15103a04403070501e00400d11411102c00c400e181040c03421300180d00c048039031f003e105c0c00c407428042d01000c0b0007000a0311079420340356580d08504005160000c3c41402c0035088100204a40f18109a034070303205d244c1180d101610072400910700c98000d1103050102d034070039485c07810b007c2c03443c80c10070b4142c51a50303500d50398002002c1c0444100f240c802900c004042400c41144da071007801d80d248801201803140c080d02 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 703329910 1250 703328660 703328687
    0x9090605090105040f031202070b1e01060912170403060f0603021908030d0522030201150e0702100b0301020d060902130b0f04031e020d081e0f07110a0e0106 69
    0x90a110116401d410140034060207a80c2183c2206005c820990303041d45d00c240e64900c4410f890307800780300c0c40c00400c43c0440e1061142145101c03c40c0c0910142c0102d007404c03141604000f0900c9040d840501c031100382440e441024641c002c0c1c5074090800e03040950095801150300c010f1500d41001d180d44050340c0c030360b04010202ca01c00c0e2001300d400401c1c03c0749a107000006003e00c9005500c14414000c42c0241e81c0c111030f0304615040f980d50710559884101030000c4030109415005070b910303103065040031107401030800c008102c5540b43e01c00324244403100945801c2141070500f24551101141009503400b035040301c0741c04401c00d1080281d01d5413001001c000e50802145841c2a80b1141c00010304000424111480e041d413012100349410b003142c0e01ca01c01c029079082102278400645d0703a4100162a044e1050100034040c0c8030702a160400b0f4201c1345012200710400d6020403500348111200210188140c40c21603034842da040852070040d4010035911003165002c005071804210001070403c3e0000000c0b0b00d0b04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 703331160 1250 703329910 703329923
    0x30415210501080318100f0e0d080721030b0f010507050f01021c0501050603010f0e07030b0303070303020d0b01170a1d070b040501022a060d02130e060a0501140a0e0105040f0909 78
    0x2400a05c0801101d21640d06114021512560080c140b061080d01e2003401050020034100b10300c5191388861645403c07004080b1066031040494110301c907500407540c20800250714040c006040d40300d01040c0c0350650450454103200d408116001000b4052004041001001e00215200c0c161421440016580d2443c500d100a14003400824a400c00034100c3e4103840c455044408802d00d01041d21407840c078010701c00000c141c0c0d2201c000440361b80a2005003200381c001e80e13000d40c507040b07548010030499030415111414006035900080400c45080e000315848414010000342d10025841c0b0109803481c8801000030a008a003000b19108015030080c105440c0280d0880c1c04a00321506421285484220300c244032101c0a5420a00c52a2040043c030840011450260522550b25911121040160001c0c001a080350003044018180020004001c000c2407804c810aa480191a410f003441612514010004401c42003c226401401190010200051f0204040c0e41d80d4001000514203081c04450b00d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 703332410 1250 703331160 703331197
    0x20109050a0809010f050c06011215060306050103020f030a1502031003081c110705030702040b0a1d0106110d050405100c05120a03050a09020f2b050312090304152105010803 76
    0x10740700f0007d4800d101c04400c0103160f644d00740102565810701c2c040c1b00300e0720300707072581101c1d00c0001082c0544c000440c81084045000e50551040085c0010303075007010740c081c0c0c1c4400030a402140d0303013001c0803030280c401803c01a41ca4440d581c5120041d59a03800140c17200c0340c000f448900d5207440344528403402aa0310030421000300c440001049138880c2020180c015401408078402600d442d501205e1003100080c0f00c2c41040341da81003e2251003282c260040c00001103840100310f4250080741190200744000007a01c032100f0b15070005806402580a414020b41e4019540e40101d030166110001311508101160300516501260900700d6001d1411440001c2c105004900044003030701510140503070060501040c1007900c410b203d000b081004184080c0600e020705901030b4808402a400c01d140504091907494140f804441c0c3c1d04100588600400d0740208001c011800c941d959030494800c1618050b451f02d064a480d1228414609813108107030380c58440000343c0b00708004001c1081c940140180480e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 703333660 1250 703332410 703332437
    0x3070c110d23010c05071b09050411030607090b1c0b090c07060b1f030f0f0c021b0901080309090727050f10090603020c030c0304030507180203091b01020109050a080901 74
    0x213813001ca074001000702d5400d1004100183c1c002030910801965400c0c05486141e40d00480e0781904c10a48054580e402c2d021340140305410305002c40c4e43e02000364145001c4980c94002c203400c0e1482442130400c5458a5003409000d02203054003c080f2140c0014039407803490070304071400011980300c4071f03049901524020800c0da5605117501d442205482c4440408070083c1030b02d1080e00640030801c030b004115540c0d107165010345900c9104090040003180d00405241894844107800c0c50a006c401510a00580004010203e0004200c404052041e01c40413a50f880341070045d41c0210b840d00130700d014924120303c0381010940c03001100048030001c44141c00f10b03150220030300c0b01e04803e84807104002121a4400d101e01c0303019400410500420504a0b8038020545c4801340c15034115410407504d42d0450350007040030101d240580340e040e035042c04c0c08601c2e50402c00407007650390345081d0390f4282e14402c200d141c44141c2c0c000c2d0301c00380d0301ca9041000d88140300c5180c41d02c903031a54040000d6501091b2014100c09 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 703334910 1250 703333660 703333663
    0x310080f070302032d0a03090603061e140120011401090e1e1515210705130204090e010b01020118110603250203090a1a03070c110d23 59
    0x20201c0c3d4016000d0161400c1340c20001000100045020320410709038a180c6082c030a0422901910500030340d40d03031046a041403002019220540d014400240000501c9600e101c00d00340300340f00b264420f11516091810b40130050f101c292203a04000221640c81c0e140c503c64840640104001e49216a80d6000b140e07220181030381118000d002c035268650102c1295803010f088000396402c8079405100b255622404103059418006084070301000104248401070aa41881c03400c02d407150455000b0591a401e0585409564100b148a1035216601105003807030751180d558111000341c1074081d8240b0607074900c0c001440c0a0300c0000e028034010341c070344402044040c80020901070400e912000e0020500c0b001e40400c200d6805c082c0004200b40d02000d0350808031052919a4600648550042c6481b04828000c104441003154071020308510039015041c0c1100c0300d03208490b80556142041308118004d0304080207400700c112255600081883c82400502550103100006541000d00040010395600e45c103d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 703336160 1250 703334910 703334923
    0x812070305070b0403140f070501060e0105130b1507080a0f082a0c07151707080c03040c050901080723030706120b0411030f07032c0a080310080f 64
    0x103000608244040000034410f4040540c0050081c503000c0c43c01d50328482500070690042010f20002c1d480000c04a040007004e01448004043c03290210a036507142001141400101011101c80241c0e04d403002441e41d174803124003901c0075005261444e180c4070180f400e220140d1110220002041000841c0862648518001c5108440c1c0c0116171024071400c1154240445012024041c115018880610b44103800c1206000901802c590443c2e90041c00c94050a40032003030084074bc0409800c0700300041e242c2c000c2c1400f0b4000e0310002820b0350300c0c0da07682010600d907a5540c202942c426031040c0009404d810016001c0251b555030188041401200e0740d80c00c40c0c0600c1c9401064140d0090b200410449010f65039040c00042c01c00c0010407403416110000b003c0b900c00c040036880342c0001206004029100301074180d40550b490900708101d43d0f40b1071041d0540c1e0541080e02000902c0c0c01808210303c0307014010050300d0f41e0f000c90010703107c0c14600b0205290322901c0c09514507610032501d076400b9199000448 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 703337410 1250 703336160 703336163
    0x105061905013204031e0f020f18271c0305190504080a0e0f1f020a06060b0703111b1e030d170105010905130504052104081207 56
    0xc0c4002500d03000c01581c01400c00c100008010000000400c0e02d03043d9040c400c40c8502c1c01501c40c03a0f90341c0c2540761820840b045a9484400f56030340d842da505c006890301d00704400701d0760119500c141001005000403801ca0465255402c524040c50a0182c268008003841c030005814032009064030100d80e11480d6210700101e000c02c0c00040c0c22507010540ca001c0e0f4081a002005241905003044922900c402520410f40d022506035800081001c80c4a5014011080c049800c45040d135004103424001501c080d91003035403980465000e04441c507028000c0244001407a0b00c00814406d0580c0c1c2e1101c0c1e60b01c0d4000700019070100f40182031045a03104080f0300e40041448501107481c00401020500044c0076600810380d080c2411414403c41300d0317401704040c80f030000c250baa481c1c2c2e407000e40b0000142c0742c0702c060f07100c5410300903070400c144045d40e2040c0701c0d0b0000ba00440c8000841e59524101a0325000c2c4008402800402c1c0001c00c00150b25144c000744183d41e013080443d68403040354400c44042e4801c0000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 703338660 1250 703337410 703337449
    0x1f0f1409011d040e03070809011b0f03110c030706031b0521040303020906030906060406050f1305040804030b0f0f0f070e01050901030605030304060512010803071109070311030a0509010506 83
    0x76140001c1c4070382c514002828000741000810011010901d07180d40d0010300c050b911141701065401056a2108125031021540241c035804181d145e42c4070208540f40103002130501c0085401c0440004080080f41103074400107084544507a030300d90001c0c1c010140d1462a1603401c44096010030000c3c000c03411035540b52080c2c1c8054011000d006071001300100c025000314101502006200e00325500e11000d5402002d17144060716150034801c04010480e9100c1d1300190040402402c44062682d40031618006107014000114007642c2c0c901d0700358142d20440c3c000422082e8040d040c410f1040117100c10a2207441244410103045d2130301000308200b04412116480040d44d00002d480c0d06510030300242c04150f8040c10045810345e201c000080c115001078000100085000c5000705c01d552160182038010950040603510b84451500c0d40031041042c80d070114018028030000c502c806110742e1241d03c15507107042000380c4a05095070303124040c10054444100541c2003802003030051500c5100b03404002c03140030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 703339910 1250 703338660 703338677
    0xb09030303070f09120b07030c14041203032319061422050109020c011d070512070e091e0c0d06200d0903080c180d021f0f140901 57
    0x10703084581d20304801c0040200541081e0010b05541802407417250f1911500d26144540b406070401800c07038014071482d1080080340103031030302c0c0c406090f422101070307031510703074121140040e5030034240d0207803200403511010904c00e502031090300909904268010b10130241109800d4074241e15800541c4c03004c1c0201d00900031a0b688181c2e0625150075507041007d07501441d40042c50f40c0c0f075100307030032104241c2c00244000d40009603101e00000030310a13806440980c001c8041040485218942d6405a501480e405000490296100c1c10810404a001044542d403d2000351030142170a41d16082c0c400c41e403840c088a480349018030440b01082a03855030b0005883c0c80c450402503103c1e60f01400d10094a0b689401e03000745484c1c0c007000600000d0150b02071845012410001c185001028410001c10791004910140250104030704107290784024400c08850420301445203000145030000820944141d40c07820780d02a40f442604a0020340b10359010ba1a2010b4100f02018090410f107e02d400d01c038000751802 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 703341160 1250 703339910 703339921
    0x60c06012606010b0a031b0309050f010c0503010918080a0c030305012c06011e0503090d05040807030f051c18060e030c040f060e0f0405060106020118080a21020d05010b09030303 78
    0x20054517984000380780c04252580c54003040260301d1030250503030b000692a81c44000c1803010400c089100e0b800e562008021750258800010160300040c0510343c0400d4403840c0c0082e9249440c00040c54103504011480d58501d07081d0b601814a00d0340400403000b107410400006480114608103005100409080802c405c481c155181c850480080c0070380c3c1807142c80d014207444690f5a00010300100382d43d8a5481c0c0d00e0901c1d002007860301d40b080d0f10481c1046000c000600c006440421107004880c0d104482490300350a5141103814483d11003e0500c24200021030021401d60001811011103c1903150f044400d450f4807044904e606401032481c2c2546c07250303109030308900f4264003d10203034154003000109640c0760b4040b00c05408081e41c04003004480c4806000038890207003c0d050040c0f03040d0002f044003507542c0d0030505407184400780240c4084400714000c5c1003c3e0042d840030003010315a01d181c0010120a0b407110000303400c841081e80c185441d000000c14101100c008403014420014001c50171523403072 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 703342410 1250 703341160 703341179
    0x2010f0c061d030717210705070602030f010303030e010b030d0c050c1203090a09180b09150a1a0d020a09051003050102120106030e1c1805060c0601260601 68
    0x1040c000711445030340c9119030741008190702950001652080080e660b200c0680c02e001100c2041880750642d070040c2000a000021481a403040303814040c010200310903594001c013610140904540501040c6c000410046066001015641030fa4403d4904029a2511190042c00c90b40d0700060580c01d079020080284100d80500c0e1a03990252060040391000501100807a15010700101c1010440d400460000141c0c80c008400e00b0141041280030440d2a001c86002c01071074050500c041d001ca0604400315804101c1440344804001c202004d086080c03e1029414009040b00c4a640d26009903410045c4014a40980d00c8404540c00810f590070f90740c20001c02c0030040030701401c010501080c11500000081c0d00780007400d2075103d2038108824640c50518090150f6600d4900e05106410180030443f043e01c3d402d9170f40080c800d5a2034100c2030f90080510500307420303041c0e0700425400100802c12664548001405505070349001c005000107081d40343c08103400e80140c043c00341c0349402800c01401700248 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 703343660 1250 703342410 703342427
    0x12030b0a0b0d05042108070c020d05060f07090f050a0506180d06050907150512040c0f08030414060a0f120f02041707051c060e10060e2202010f 63
    0x40c041203240d41d8038810800d4a0b0302000211107036030744400800c0305010f2002c1004c1c450701e80d080d2000e0303444e0b200048024174081d002001c01080c0301400ca0074801b035480307000040b2510356214085a0044c01c1140c2a6581d06104491080000d10755410201700c14070701620640c03c90f10050601030304c203418001002502d810074046903124183c4102910a503548240c03000300e4050090400244909000140783c4c140300702500180d011600e145510130030158407008131400c201e000342240071a9100c03403814100c1050554402442c6404c403020200b22080040020800c4a182c228a0307101c2c55207580c14042240145149000401e5000031000442d40c01807484c1100d80144410018040c402e043c042c404030b0f082034202d5400c80340204ea811001c20300400208000c3e00b4121000c0e0701d0000030b02160003002114100041249488500100304d41c54100510307a01360b07100e14028054140c407a00350b6100444c00b2900140d1400c0b544a0b144580041030408005068040c2d443c0c0b035004030b810700140d50310071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 703344910 1250 703343660 703343681
    0x4020a1719051f050d0309090203130606080309040501050d020904022b080c0c01020610170a050a0f0209100f03141c0207180b030606311b0305041203 66
    0x16150384202070381d40050301c11248156402c00c28002021042d6200b100210320075040980100c00d0724000002080d04440068101c8425841c0980d072680c0d42c400c0a882c114000c10014592820500e000c540d03044044044c0c1160b03038090f01d080100c2d80e030b20401c01080030042c1034081d40200c4400007003005402e00a504108190199105404e07020604418414a6055a40c1540c05c10700220385c06030268400c0c04041c07140a024401424a41030001e007480352005540b1617243c1c40c000b030243d030b6003170700c9014013000d420036030030906645200400e8107204982821508080707114502d1040040d400000c202e40c64015510041540e0180c3c40c103658510103a140e81e00e5466506200310400d0210f101a141c91000704079000c1e138058002d99103044480110b4400040b00050403d00348011404640c400150070303684968102c403529a40c820514020082d90f50010b800f000095440d84080400552500b242c900008036180b480201d50b04110210111389003074400800c01e0b07040030481e950007880380e0031a88201 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 703346160 1250 703344910 703344931
    0xb0403020708070807051008190e10060e0108060f0403020c0906010c1b030b070306081011070206070f0b06060f0d0b0f2107050d05060f0703091a0402040b04020a17 72
    0x1e501c48000d2442c0c05840d6001d40c609600111060200d07040206000c404850700741001019401c2030282004114140340032200200d070345403400303401a00108400514501c020b5010481140c5607440d11310481da00b40941c0d07440d4071403c40452044041218101d10440e00750380a000380a100c02d082040c03960014110a042102c400f0842c80030072002080f02e4440300f01c8a207949541855854607444d01d50009190406141c80c010040201c010b02160903402958403500000e0400300850b1681c22a00a0381070113034105101107a40c60800002050503591070380070705003002003a900c50007048070030300c500341811081e54402d00c1542030340c4200fa0131002003c1c800811500b0151454400700c2d501d040207500e900d0199a1400c50400403400c02d10040700544020b40703454a0500107915110798510000e40000c01e81c0c00410001549503129900c4082d01d5584840c10100c02038046e8009804c80005650a0384924540710742984585407510864081240035141d04904607030b014100008804000c01c0031200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 703347410 1250 703346160 703346173
    0x12051213031406070210110a05030c1b1b04050613050702010605040c0f0801080607020322030f060905010b0108040209190905030721080c0906070f020a060e040b0414040b040302 78
    0x151600000080c02d03000d5200400007803402140003860402161054100300789030181100090900c0c4c011548240c1e22414070a1781d0307032035400d10780d204c52082004102c0c512000c07664142000e20003141d68803005002505041d8018001c2e0100012590700790780e8540d02104410039411211384c140c1000b640705607240000240e030b640e1440407500b901ea00c001e007000042c005031702121181d60003000d81405010744200400951070016030180d03480c07090560016486100032100401021070511005c091079009513141010542441e08070040c1c0794100045590b9401c0a50b005c2407544540c0000b8426900206888196100c102c030041c0d41c054419a5200c02a803a84018800302d00104002c00e00c0f030b8814503620265014504801000d054512101d01c104920442885015507440090303441025080385c0d500d64504031860204506520440000d401840303036039002030b1694003c041c0125500c2c0644080c8070010044007008111001802c000700e6244404d00442c4c0801c000b05030203035000e8400d0040300d50 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 703348660 1250 703347410 703347413
    0x203010e010911030106080f030d0b1207030b151e1c0204060f080c10090311210f0c03030406022112040b07030c0f02191b0f050a1205121303 62
    0xb5212018030a81d00d030401c0f01e00403165418240700e040018a0218050075503480602c40d100d0301d07032082882440c1c10b540c441d82c2c8940a555011090601180d00310100c880c0d0581c1ca20341030000300d508640d082c008040c0c40f01a04450f00780032051403084814100e500000000d010304004050740300307035929524145400038040040e161031080038041c0c000d01c400002410300c6d10409924010741c11500702c0c010800011002c02450700200410107603544440d000d06202941c0c07010502c58044985000501c0c40070b04030b404034100000c0741001580a030307201540d21504000040c1035692003980309680050f070003821020440c007100c1180f002809508100b040c608400ca035681451100b0a48042d600c00301c80105220b880354140c031594101c9181420a00c50084600300041d403502c1da54807010301404d1052815000300101950021205c110307001208400d00d8075006042a03884160080d0350081848203000b0500700715000821107040e602030004d02c80c091403125442002e40101c54198500000d4110200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 703349910 1250 703348660 703348663
    0x10815130605040c0203120702032802031e090a08030c0d180b0a080708060f0607030c0f050105101a030f06011103040902041202010e040b0102070b090f2112091c0203010e 75
    0x444141131540210345078140041c504460b01e030060200011b55208110300343c5040a00104000441603840842c0000f0302c2c9128241d05501c160507800c120306000000401030f06002c0406000c50310410b64080040c07503200c418550f070707901c03d06440f0b8600740d00c58420002c8840c0310310039003804200c02443c40360125541c1c00142516822100e184004601d8090402c02030316070128005610100c200c1c0c9400f14a042c2c0f002103900d41c4560390740070b03080054428400017408000391000110a6004d0003c10403440c1c040001d590818940c0503510300904240090301d40e54892405483c05008109041b0410741c881100540d000501c20301c41c0066400140400035004070184003a00080c010a0101084200b26200040070003110100c141c1c421032802803a00b90990740054008180c0344a483c04c659250b034007000043c456483d40c9001c50344070700d01e41103144440504822a00d11983c12900312810411410ba00c4030a90140402254200c0c5448024a29443d4801c51040c280d0380050000911450694070300e6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 703351160 1250 703349910 703349921
    0x180606070c050a0b0a0f090605090609031e07060e0126090a0501060f0504060632070204110a140a0e190e07110c0604030512090f030706081501081513060504 69
    0x200c1130b80c1c3c4007184107140c1c2c0e5048284500c4020031460b1091840d23040c01c4000d0194058005c20a00515022414103001e8804008240396904d81c4514520b22190582e50303e550b41805006060020706910302c01001c82d4010010034040c4211041c3d05001001e40750709a6076050002080c0c0280e038402c003410354002c80d2081c8685005081040758846c80c09041a0a020541c1c1503548800104810007085030f03020401c03412600700800e00c1c40c010b8003024030340040e070b185240182d2a000e0345c41880c1001090084d455000141001c0c00140c07580e50050f2102c610300c9103180207041551f00810f408d1400e9140501c0c0c10402034030024001c0012008040d1140c0c135002540c5000c03640903000c6880c4199684600c0b00030818201e12403000c403242031078a4151f90381e0300d494920010800c0302036400810303821a156604990b0540e13105c0094115987e103580c030500145800f0044c4d41044034031040491908255200d00306880c8200720014004034012400d0040c0684418070310f04a0300c100341e0303460010805903202d0048 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 703352410 1250 703351160 703351169
    0x120706050a0c0f0f03050601020106080717071202031005060312031311220207060212072c0d08070f02040e0d080906070207210f140c180606070c050a 66
    0x109441c1038440300040740d0200b110b210030b0140646601610503448142c1c8040740c000c6180200d0152101c80040c0e01529103038211200a00841401043c0c048044c809550f00c0700403001201d035040e40e40c8080c19418440680c0c06501508080c90103403403001d8a411054103c1005012524a130803203201000303003a0002d81c1e0300703100c88201c1d00780003003400042075a140c0f0841c012601500402000c0c2c00d43c01e201a41c049800e0005074001c07510405010103581540c0074041e000d512194145452400186000804081d4403159900104612030850700583d440300014005007025240140e282c0b10059190441c180443d8000c201640032070050700c56005013821000c4076002840b041c00003802c0a007259100030100009903001c1c008000075241c0c0040c0650480c1c0030400c0c02c017803504203207a4592f03000c1c099000141103803070ba00703100030108500741710207400e5101d5402c1541c812160750410000120a55100b400c0d940c1e0358000890501e140101c018036181d0300c18401ca082aa030707220b012804000d01e5500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 703353660 1250 703352410 703352423
    0xc17030103051b0a090c120203090d111f090f0609080d0c05090d14152409060a052709060603151018060e040c06090902040f0311031207 60
    0x4204009081102c0420700728410080c1035070683e0080070502d10000b074440c46500302d80ba08110001799010f424815240360701514199924901a01103654031507110790244002002e2840141513564003180304400d000100d41c0e40045240c15110b0107028280004090320f2409004841d02c002485620482400360710a01090f0349174000d00000d0400c46002d045054180402042a01c125a0714040c0b044441584200780300341070440c1342241440c0c1074202c0140818001c60200b8050001c0b07440e0901012884421100b50315001c85906103e00000d065515542003008a04140b01c41d1a03d95420500e01d6615419075200c803c05595a16207100152036900302a00310b1002e10070a82414814500a034800c1004480d9500300046924a170010718440e07500c00e4021031b40601d8900c4482c3e0000170007042113000003407031810142802ca0490041e84510300114a500c1c900107003d8a0360300a580803100071b00304031f43c140c5203103442d900705140c0908135155150080281c035084101c0300b28040d1443c50301411 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 703354910 1250 703353660 703353667
    0x130b36130b012003032a0408010615050a05030609190f051e010303050f0f1e0d0c030612020609030c030303010b0d060602070b0714161203021015030b04030c17 70
    0x1c0c0050808800842610624128110400300850700041200d421600800e05503c00102008401c00e5041a0f0a0700c0071910f03000180c0040e17a118150000c900741d031100d801d0092262207032241598184905100074011801c00c0c0000307459454030300a4298000000c0b5a0300031402c9203589031108507002e149144a0b030f1995242402035820720501040100c00401480300415410340c1c4010b403031130094198a008a0358005a0b800050310350b507040d038540291408002744455000c441040310b0ba00f201030b0144446290181d1002024480d02030300003211448400000141169001c4c0b1500e640011101a0980305881601c80d150b282000294000c05250010540721032003494030310143c8038070b540300400b15400400f040c404410880205c5240c80d90100d840d008000190b0328160814a6041d0326049c1d240d00c091000901054402c014001d581c400d0342034504283e00304141108803000005019a44884c003e414400103a81c4100c2c143c00c41d00a080c4000000360944d5400818072405410a07540c00020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 703356160 1250 703354910 703354931
    0x70b0a0e0c0402030a021e0f04031e0203030409050603060624071b0b07050d0804020f1e03060f0610020703150e0f010213030311010c120213120503130b3613 69
    0x104003508582c5100705596107001711020103040c2394042c1e408060280340040302c036407600e11840100440c0031070f40902078940340d070f41d250400401400c0403607003240640613550018003a45401861189844d04031228240200a60484280c5a17000034800312440b00c0802c41201d80b8146185114000300102114642e60f003901d032034141e0601414102450500c09948144030069403010a01c099080044c0d80e0002800520740c82040100d03c01d442e0309030180604010302c0705090805125034841c000c141c8945208041115013241e0354a0988800b030524800061076608050700da4200c00443c880040803911514580c0d42002d08903408443c00c592003590200080003010741158240e40449203c600070004074a44c3c0802410414801c003080d010b596000074510029410020300c03001070174000c07130404921a030b0381c0751699603030f07018180c4551000303407007240064100c0324801200c0c60318a08031640032404021154141c0b030040030346180554030b4040c10600d461611500041e5000c02041300c00441c5a0028 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 703357410 1250 703356160 703356187
    0x3021315111b121b060f12070f09080c060912070f15090f0506090d0203070b0f04031703090a0f05070b160b070e010921060e030a0212070b0a0e0c0402030a02 69
    0x104400b00d107007034015152406036a11003600b1400e00003000d45400d1369541c5801c181b46142d100f0701d039000041d8400d02c001c0c00395017a80020110b46242054881c03141007a215159560740781128581554840d104001100301818080a42c5d100240ba131401c0ba10724a07122005038440804075003000b03090481c1481020b06880d444015000100504125142d00c40e003040d0114506229410405015030054010401192000c22030980100481c030750081c1c80d40d90302c2d00003440e13a500602c01900c020740c00940c4504158448411280aa40088010080c000e0166030b40c1c80b01ca5841c0c001036030b00f8010103000144810702980245801000e075401c1e88000c00507840e100b0b4002d40c02401103010403201030500e94959820141c000c05031103050f01180b5140e95640d814407034001c48454010111820200301406980c0004050b200003a0700d80c00f0385034500d81408040d0301c2030080b04005440309501c440410040e80c0140c0c883d0400200c1c22050342c10742c503000d0001c1010390780300360360079540c13250f001a50b10145001c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 703358660 1250 703357410 703357429
    0x1d0f041109270a09030c0b061311090112020a2a080a120c021506062209020702120a08031602190b09010c08091e03160506011503021315111b 62
    0x105030010001258591170052014500d000c0050101c0340540100b0301540c0c03241c1a800c0469042e203010301c00030540c15489080d0f03801c0380a0540c0440e2464088280088203030080e81c51001e6242d5951103200e006a8070044d04485403024049495115407020700491501d034001c1895041e940c40d00c5074010728242961040b1905000c00c681190004400035060801005906401040440f02142c030f8118954204201483c40f88055072162000b04002500c401d0070340207440c8440c02166150320540c0042c4000d61a11010a002402c01c8002c00008401442c00c040021000c10148115859001c8641e0760040540d102c04055800039021010080c040300c007406600c141d078806150106032800c00d101841e6840d00500601126070314103280a021600040094440c880d1041e0300c2410110a10f0611580390b07030b030078001d00181c190101d0380000c5070b50080c000c41d24444a203a030070240b403030300d8000c4100160140401400c00c000080c1038203910007408008107241c208071220b04501041c80c0d281008074144 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 703359910 1250 703358660 703358671
    0x39030806060702030a060f02160515010b03162a0c0e0702010c05090d020d02150a020115050f040504051603051014131202100204080606011d0f04110927 67
    0x1c20800001e00141c42c0407030610f516503480390022546002e48000800640100207920410300c42c01c2d000c032401d00000080f801414083d0079480394080c2d0f2244e050704564402122900c9040306014202c1d80102c1c4a85c250020640480124482282020b901e130102188040b10540315032038a98424032400c0300d00314041d900002640020010788070142c00c0604240100c514451089850f1100304041d13455510200c0281680141403801c2000048012000c0390460794007000158030b001c00100d0740ea0355070f030500800d0b1a4003d06c402c50040c20041004040c00c0c0080c011102800344811000c00203180c0205500a14070903006002c189120b070210394106d034001a03d01c01c1c07001c1c81209109500035400103010090307030421242000d1881c11030003a0f01e003200d900803034201d444c0300080000b00460040351881c01900309907030303c0503203400141c49520019446036001354800441341c0c90f14403034030305644000401111026968202418440010031015108540b1100b0b208100039038611040c15a0b01f05600c030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 703361160 1250 703359910 703359919
    0x60206070f08060f091909050303070201150e01050607110303030c0403210912080f0a050304060b030a05030d2408060f0708040f02010c0204020702030610081501030b0739030806 78
    0x280390180000d03d131140c0300c541c1035000c0c00019001c990104114254480c43d4402c5010078010140d030352800640d01d503c126402ca00551900c100d0010f01000391070400225001c081c0192a00e90034003040009513030150104840ea00e90601d140307a06034405101071440b03081442e83e01d070380b2586581001da13403501e40301d0f1500c80c0908085180c01d0203aa00b210708207040d90900200d03106000214074010719540710341081d00f60806008515203810301e912100541c400d901c210b009004210b01041030582c0c6050250005108c3d810520807800d448080e64071190880041c0d205c0010b803486030f181910100e036002d80000556070060307420000485070038541c050700007600385005100ca11b4242c860002c8681c5000009041111240000040d991035070196a0140d8000741a00e4060070002c1c180707041c0e400140b00ea03641600411508801c80d10103903800c0380c100c070b40022101d4190395583c003048911401100d04038562400100403810b58031401000c0c0014600004154120744150b0b040181c4192002045c2038800d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 703362410 1250 703361160 703361177
    0x3030e0102010209102319030207030507051203040c0902190305090a020a0e1f060507080706020904050f15010c030203030f280605030715050d0b150d0902180609040b0a15060206070f 80
    0x1f6128891200c40401c4680c3c5001070f2583c0705464212500d104440002d4903902c039003410700d07101e4180c010040d40154821440c2c420703499500d80121090b400703107943d52a5035005800c901051103000740c114070360040c0c101b0103642e443c021a50000340b13225070503044826070100e03010070032040d044100351080390022074035000341e0b500c2e240800080203441803005c010407082e4003085580130009941c06132081319200400600c82450119003006602d42e00b25150403182203d0030607131007203500400c409020369405901951441d6100800100780035009081000c00781040d0683c81c00000043c00809204c09484034042a80c9107440d0805240c51081c1d00b140704c541c503004200041280d00201100c215903401d06003c00c5d40c00c50200020380340e0545c8600707003414540009111a000711254080e00b607141c822615460650704881410010910460b00d580c0c110045030089070104500d940c80175401442c0703480c04118040b0366003002c0c040b601300350f0200300541d10603400c0c0052543c020300480b440e43c0e9180303407080300d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 703363660 1250 703362410 703362427
    0x110c03010b0a15050d020a0c020a230d020d0212030d060501090b03180a0507151b080301180902040c0c050d02160501030207140a111c0c03030e01020102091023 70
    0x4201c043c0c803800102d60414400072028500078002d81d9942412808219240c0040038009020b203c03003104100d108001405001c148208410705444d0500300062004040d11011401e00c803124903218030990740200240d0901005170b40e060200810044000d01445c0c4406070100750030165145a0000760500c604000c00f4400d0101c2c240030340380d102e0040c0c002c820382a00360103000b07402c000e4000005003850146540c08a0180342c08040c04e400508142e80c1c099a0a0483e09040701d5061b66100007045400104010440c1e0b11002c514030000d6000d0032000941c10a01b03074000360403036134140d1844000c02c0e01c4100000c240710083c081c0d00380032659800604048403400059440034001402000c0c1855408180320b810302c280700368501d0004816000301d80107003403281040401e9a60b070780030304c81c8248402c50744809100304103041402566802412800001d045a4007990100251618103046650a1246400569440c40c1c429000c11141c1c84142202e84002c24228009014180d282c2c9844020084080d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 703364910 1250 703363660 703363669
    0x5151015050315011d130e0706030b0d020108100902041d16170c07150209040b06040e0a021602030a150b0f180702030c0609010501230907030b060408030a110c03010b 73
    0x80601d0707401d1920403094617002c405d17140c0c0441452143d5410814494a4085d001040c3c1d00c0800c5c0300c45000121012039503580822400d84290f00c450310b40100b00c4456810041d4040d81c41c1a0b0000c411070010b02c9450f80f103185e62004c9800c41c0d888901c070915003801035012200c1c1400055080105a00900b40e10310341c1c1140a0b04c50b05900e110304207540d03441b0002903021919401903a11280d40611011211101e620540740650841646503108910300326441e0a5480d140040340c0840b07800e03190110340c0740d98440140d0004e400020143d031208030303400c4005d001a5414031084141e41d00c1619100c803c10161264030040ba00304500e40e50140c090b090408003203a9800c10041d1a0310b0214201d4445542c5110007203080d03014920443d012480740c0360500c00d0500e0190031030b6042e9000302082d00980d15270340114051115800c142c1c4e6421030170785400310b02c85910030b410004c528440074294610b0181c0c2c0d41c56651455210340c0e20380300090f0310700c28901c221341418410b080700c0c3d0004600a216540072100080c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 703366160 1250 703364910 703364941
    0xf02010906051215240c07050a0e040b071206030521030130050706080906060109060e1e1201060311040c0f050a02010e070e090d1119051510150503 65
    0x10407100c2200c000302110381c0d60042140c6920320400320b134031721410311100c0d040340f5412191905c62640511600481c0505003003030f00038100c80d154100160345444540307074a07007280006081902007050342c2c3ca04603914040342c0190300045118100908a042d151005581d44a84142070030f10542c50400040203900b415820200c2030080d010b99402d0340b00c0c100601000b2f02e00c2541e00c000d01d2800741010008d1865084002503214103092001c3e80c6595079640011a505803180c06108040340000e07400b0b0016080111340c502002e0700e1044044000d100d6480003441d04070b2038000000a582d15580d05000304504595003143d2818166002e02000c0900100507000203040181181007100c00710f02e86501c103100350040c00005010f44152800ba03511040c00d4290300a04494115881c82003502ca66452880b6403a45440e0510003006003102d451048089101100703040e005640d03c0c07003003407a943c5c01c44000304242030060010100054100c0c1c500003034072041c1044107030a8002d0180610401c201e40300c400b040d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 703367410 1250 703366160 703366171
    0x3030c0d0c02060606043606170a030516080d09060c02070501050708121e0c04031218031b0e091c051204030828090201030e0a08070204090614040f020109060512 71
    0x21f20352030041d0051410501041169013211750081290101d400142340d0080003560002c4260442c540f40044095980d00004000200003e02c1080105050403818002000051154014610303100350b010028054a4a1076010384419603540c6c02c094101d90104a8000102000c0c04c01c41c2c1090007548401050780110110b101c410003085000414200060034080034440721010000e0507030410205407a8940c100f030004070b500c10000e89880b441c031070240d8902c00208040b00c100c0c900d00d03400c41d909d00c040c2c005000c0785466049050200401c8010a550f8046d11421955005090011a9043d250004407000d80c00005000c01000011a50183c5040d081d40c400e4050500d90003584484000c165800001c056070f65001801e0308550841c9240c5401050195000360f03130900c02d0492291001d51104d82c5010000d00160042010b280141800e030085402d280c040d42001584181c013045410900c40c0444044410700c01e2a100041150b811a050401806040c50316604100b030500c017062400d00050803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 703368660 1250 703367410 703367429
    0x1050a0f031704030c0308040801150506090d0501020d02070b1f0312110a0606060c020405060406080a06090c030b1305070b0f1b12210108010b0d120306050303030c0d0c0206060604 79
    0x240541e0407402d800884000b1070f80219108540d903503d003000caa030740d00710340a401c04650038000c0b6036480800e82c80c004802e680005054628000144007040b1621010300000c9455540178880441040381c5440075001e81c0740907450000301c515007403001d449840da15024802d070b0181603586c1170010030b100c2c2149030380c00310443c2001107491600741a41e9150a12883d40102164241030340480d0740c41d400041d0081c0d607442a01c00380710316102d51080200348c907034901400c0307280d521800c80200440c4583d002102980c0c051600440050745a0321020b00c1075500b1500c2800304400314004804100080211100400d100c080d29402c10aa090030200703984902040d40c0d07200c07400c0c41c24041d006030080c00507010303100d80000715030b685944260701c01120045001241c00120364a40002948003018000c0d501c03084c4000703048003164090713565405c40070400100308e03004150b035071407012038151010401540102840541d40b80c0f607103444140e4800352a51460103404641000c01841305a4540c0070556051354610071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 703369910 1250 703368660 703368683
    0x5040c170c0f04150f0207031e1104020403060b030f0703170903032106010e0d0c09150e0a09200f0618091603110f03191404120801050a0f03 62
    0x200394801c54051031049041c04200050001560245000075030391100407610b0300055040499401d0303899005910004d40042c20501d01c405041005581403040907104401444020741c001002c5012030b040b640007110fa09540e4030000079a1306d0200410000c22603003500800099043d079840102d080004243c070000c40b02c011900155a035030500c181d800001240200406078068410102108403040d51082c0c00b040c01d280300b10605013001c21540714819003129440c3c118600e080324803401030a2205080b9115002200086114004028401d001c1d0040702c1c0040780103180c9013012242e600101c2d0010380d031070a28020b5500d0507190f6140100008004641c0300f0b0729007005280c241d2114184001941d4440042405c02c45811200701480c0003010059404000780315904425012a00c905480b0b48005032062000a242044860447c01410252980401d20003010b19940d0000f01d01038074111000c0b0742100480c8040d81c2e100000e039004003001c07212001b103585062241c07000c842c01d41c0405060045640c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 703371160 1250 703369910 703369921
    0x101a0f07060209121c0201060308031305010e06100f15020c0d0c080a080c061e1902090603130b06040b15210103031d01050f04090903022503050705040c17 68
    0x3036041d11811600601000c40910310340b800e030785d15071803014242c1450285001c2120708080c414410071060b039601550051854484203184c41141ca4600011940d540d22550f000030803013030602100780583d05d4403640a2040b4104030700c4440751103da8004501909084000401d071540c001026002c225043c3c172100c0e554507080c00c04150f444040e41160400b40715550b01c540c2006070001c018451003190009564968a40c0880a040039032200c10090101104102180f00101ca030000c048540c0d181080061904003202c020912070741084648030301c0c000500c401d0005002c0d80e04001e55214030125010401015010300007410401e20218481c9148408298040c0285410340c0f10342c031204991180900542e0b40b881d0081030750601044e000b01d800d25020b035501003940550181d40c10109100c03411401c06040088050003404900ca0681c1107205071483d510180c1c519961055013115111403001b001425410480e07d4440240d10047c007961401e48402146e40d0701840c41d281040c2d5041041c285502c43c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 703372410 1250 703371160 703371173
    0xc1f030f060b04060806030c0a030312200301090f050606040603090f0614061801080a14010f06060201020c0111130308030601052704060e091c05070614101a0f07 71
    0x10a20038524181c0350400101d07100c66020040c0040b240c1e107544040903907032004281500c800d009048071f5080307004d040b018000240104211503400400c0130380041c01c400c006404400246102a41e40e00c138003800801030101485c00c6c0602105050540b00070f11040c20550040b50451040303101301c0041550382d1a0345030070485101c000012213508800c0a001006041c03020100b4010160342013481000901c104a10303080008007814100c91520340031b00015449a2620414100c0040c4000070319543d07039003c010082e017a44604c801038490b641c00140c58803102496075086800c0c1c51f551180d215401d0203003503003441c40601e13114180c0342d120b00041e0b1252a114016610f0b4021441141002809001112070504c820b1150000c1d020f000c41d01440380c0780d52a0402440d108082c0c5600e699500054052202e9401482c1e030103002041d2842c10071702c0d22000b512140c0807619800070012016524400307000c91407442c0320540b000340410380100380e03280c041251202042d10807040284242c0310007145060500c080d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 703373660 1250 703372410 703372421
    0xb0a1b08121b121923180a08071b0509090c1e0f0d14120d0605090105100c030207050307030507090b063105130b10140403020d0f060e07170c1f03 64
    0x15213004842c8160301000c442d0142404980c0b0300740d05103192154102e1b20600207081814182c00c004254544003140c3c40725500120b6042100e0030f42c1001000028035034a90b038040c4d80c0304115840240c032000c441841040a0b9015059081d8224044281074407240d035501e000444840b81d040b1201c1340e9010b13651a10704c450716051804006c01e80514100b00001140040040550303200700360003045541c1e00c40b41001074040d001e004258205920f610800101c90040b41c034540d88034000d0048030304040c1d0301c40000f843d2501e41c1d0001c54464100c80c000700100e0519008040036407508907481c41c01e01c180c1c042000110718810040b61110001c40b649100103100e41b89581c00a480301a01c03c5040396400c00f103441c06000100c42850082d4460041900218450494081100600b2510350303d018a183c00b0001030498550088d40d22010652820700003c1c034a10461040e81c6401d0082c4c0507261420b6503c0501d46401c011107510b42e00036003425402035594500c43c1520b41c40041007031b10b0180800404400516 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 703374910 1250 703373660 703373681
    0x110910060c052803111c0503090111030108030702210a17190302040612050106081b040b0c0a03110708060a0f0b0307090e160b0a1b08121b1219 63
    0xf551801c0f0a00a11101004110a00039150016081c805d5140380340d8582495024012a805100d0030055040c0300c1c00c02103400086200c00801c610754403c1030481c03d039000307030f01281c0c040c0d00000f611011070600c038081d03a000d5200d21001c90503542c550381040c0d031585144003005081c4140038a041082e4840b010a65110200c405c0d0103079400000700102400030741c058002d10020801e46180318601880501800b03059620b00e940d1141c0940302c0c009943c41640d04519100100d000030311020a440c0c0c500001341c049000000001c055000c144c1c10041c0240e01400581441900f0442c0140042e02d80001c3d07040d0401b00042c4000740034048400124000c0c500700510343c0c2d00d80141c0030009407142d01030b0001c800080750001074800c141188100c2401600c500d20480d101800d040c0080e219840c05800d5405000f40110000000b65000e556040341d5036109102c0010005152070610400142d501000050b462844803650714104c088903141d0340c01c1c070f00203004108441111012040c10045a045500102c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 703376160 1250 703374910 703374943
    0x40207020a0f030803011a0a091a160809090f01030f020d110303070b0a06051017060a1e0e0112031b02030c120f06060607080f2107030207110910060c05 67
    0x143c40303141c141c2c0729a000384201129403154505907042501418201c54070001140c8915815519140b141c00495022000035594100148900d40e4400002194130f00d0709441090126a10b003035240070843e24000c05040c0e5180c4020060040c000525842200070040390120380c4c1c2d041700300c3e907860048030b00c070f0405180603010301001c606a810400d80c048071301e000300d0802c101801803503140c1050041703a000603c1600d0000354112003000751880c1401c8510b03009000a05160400c40d1144860002111090700b882d210500d590390410042e078510040d01c0c054816800c00d4074072425240c81c0103040107121007079940c642c01d50100b90000c55808012004001c40d015043e500b01201d02c0c0c41c000d813100040c094045050042600081091030900100d0fa945548603000c98184042c1c1c2d800c469942d00f00750341503216480d540400080f04071030b100c0620307c9070703049a4016a8070480c2e17141c0b2140c020703542c2c46440d002e803d0f140300307001c9504040740c00c0d00c2c241c0312549820808003490341005850001201e0b00301c2d0340c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 703377410 1250 703376160 703376189
    0x10603021e010f0206090706050c1006030c080708160509181606020f06060102060403080a090204020f18040908040501141b0616170f130c260c0a05040207020a 70
    0x14a051095590303200074003620b0310110261250400c1c0c0e21101c4c101ca00e89080d80107513005000050040010302003e070310040032503d41369608038080e02140c489070030030f64400205290411030044100514800350140001030f00c0b0a401e02145818002500e010b9544500320f000d000507800c5240c05005414080703880c00f29019111100b550201d5040b2501609005008400b90030960340d10001e43d490081d0742c1139009000075a5580c030120303100a009004e030200c16803900350320000340c2d032140080c0c03100002e0848042d6940074030245180c00c045c1400f0300240541d040a42000101e80031005840c100c542c00c0c00e14044854260700446e00e2440341003c60807000f18003803030208140c20006020742c440c80301c0300d84044020800007015644110811103562062a075440080e0440700c000c3d02c03080c5c00c484115071065200400b9611a0305082054010141068421b03a8040303501d1202c3d6405035041c0d0210010b082c00016040209444161a004450145400080b92000c540715003a540c001405c070001d04204 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 703378660 1250 703377410 703377439
    0x7140322020a06031a010c112e0f0f020607021c03090c03050303010312020a260906030a140112021315150305060103231306020f131d0603030703080901060302 70
    0x20b00403c00c8900349162290f00c00e05c071650241e0351032a0b0b800c1c0c114540100c004108010060744981901195030f80d0000c401005040c4000c41380040c0c022607458980d82c081d1009010020b000380b0300355269208661100b000e000381c2a402040d40341c88444d0004051031444041c13807050b406804821070007040c0b440504000400c1c05804400380d81a00e01c01c07d21118110340046049035100381c11003024040c4130060101d0568a0f0303903484441482050707c401c26041441000026506400841d0340d0410607480d035090a604880141c840350240101d0710f01d20401c07030300c65000b0410326140b41c4001d0320216512940c051492400801d03200c01002983d9a080650300b4014009010348402d440f11408a03052000101d01c5e0702c54103c09101c0000125450440b50340c89035005504205030000036103071070742d0070001c2c2d20b44500c4000c014032684060190701c2c0800341c50201303c50340f080d0164081c80c0020507030380240107440d50080202c03404030b178041c50005c106845013030045004201c6548000d601800c841d05105 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 703379910 1250 703378660 703378667
    0x522030e130501030209152b0b0c0a050a0e13060305030c0709050f0a0b01030b120a0219080303010b030406060f06030f180809010513090507020c0907140322020a06 72
    0x14141070300c81c007035440d0030180800281c450038040207611140401c0081d11981c464000e015a0720b00040201800110401c412400e6445821301d10180c40c960488240510480034981030f04102070410703503480c00044800082081c05051041010400c6c980c003030030540c0c2d4a40c404003144a82d02a82000400d40e42d1800503074030340c00280d00210b5809810000107044005110781440340c1c000b00d0b1030380195030329401000c00034820028584e041c16940c650506850b20303507a181c405080058401404010060700420580300e01c2040c58500f244c9140c0403d2100817408000d80381143d46c09200541c403031310340b85040e02c0540f40b141c00003210901c40301f41c0005d81c140d15420404a01c0707203501003005800108144965205116800600120010401e0030020351080c0010311070032102030640300f40305480e40c00500985000f512400016800040080d98a02e070401d13140c0e800c5034250904440c1c100940342d40719000c3c00010440e02e140121036122040c1c042000310000c400c0d544c020288582c06403100300c040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 703381160 1250 703379910 703379927
    0x2180f160e0306091e121c02071a07090b090a03020d0309090908030f130314031801052e063c02010606020115060c0602030604020903070306050906131203052203 71
    0x80d9134105d09200c80e0b416240010500c010720007503141e038444c5030002c0c101c1401010041050700440c0f2030760030418003012501c021800d0340001c410030101e200313609050000400d580041e4002c5221004100861080c0b41d880340c0740c0fa41200c0e81030318842503249031400c054401d800c40380d002100d0346c0c1c2030001d10b01c03c2003146002917201d004180080b6505403600100804c003038440358001008541c9441000c01004518070281d94050b00002e20301c03a2141da600415404d550b01030743c814026003428882411840d100400340c01e4440c0031004200c1c1c0203490844000c002c0400702c548101c0c0c070b00c10048080e0700c1d64104020a502000c0303400201c1c21000300c51200a0081815110b084015441c103d008142e800340404100b0032288665500e100041291702d6000083d840600803640c415820091920152410300a0b14021405030000003160300c0c140d200c1d44d0a00e400200340d0b042500954140380300196114401800e001075a107800681940c0f00c1d081d40844844420f5001d41c00e4200003815400c055010014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 703382410 1250 703381160 703381183
    0x230913030e1e040c081317040803070302010b0f04020922020f042303070b0a030e01060302040608031201050411032202090c0403060e07062003040e07080402180f160e030609 76
    0x80021429800d011212050309441b01c611a012400c4130301c000c206c40c1d14444041c015943c1da01860300c0c0e62030031014070315400204110301603516034084016604c5c100001595802056400b54a0581c1c900001030040950300d0b0180f0701c460070018500d42140455060300d00b0360600055455803140c0741d05003941c901c01e5030000c420f003102c0e44581842481c01e0128040b001c441840606a003460b8412400341c0c0070b00b01040344180f2940d81c0f0107000016030341d5406032000a0600d503001c2c40d07407908180e50240c460f2405030022401a401c090b026510f0002c85000c0300d9000800b01c505543d03a00a0064012f0058800c0d8400ba42c4a5100c00a000070540c0034401001100d1103a50b042141d0009101d149484880d180320300c0d00800c0000c0c0d400c00001d40c0c1061090490318159060300d14280d00d41c2c6010f000f03414280c172171000040d81034040008509009180343d1810b1068185442d151420b411854035aa5004001161030800e0041002d045d42c098591010351480c020181c5031585002e5185e0b2b656014485c59 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 703383660 1250 703382410 703382419
    0x807030c030302090418050d1d011413030c060206100602060106080c09040f0519090c1a040305011a0f090609011419030f0c061805091905070306230913030e1e 70
    0x501820391270043c2407404e607001d500f001650b944000480151039440e41040b1a003940305003003180c410f5030810045100003640c4034900c002039982c00c0c21002890203100a011880990445000b48181071300040d045044441b285410340c8207645810341d5010701d02441d04207582103404e190780844902c0240d00164480d01e461680310400140c8131030b00707030180d600c555409029101075200502500d241040702d02c0014402080c26450b141d41ca0342ca890841d04580703c0043e8815010308000306174a4028590284060202c8003400c0034241440014034140040c41080030f181640307a8010002c0d224080e00c0c0420120032000c072541c90b075503400e00e00080259503c04680000c101400480c0040c00342070500b010302440c00703041b000a1300340301c00d2000c810b002802c0d41032604240d01d0020311403c1d080c040d42d841400107680100b411407034800620701840c0c150b04040800480c0b8844c074505511071180070341e84a502c580c0c0030300c0340e18030354101a549040c401491a070420131000090030100c5e45182981d0b10741c036050340c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 703384910 1250 703383660 703383673
    0xf070b01092003040b0601030b12160902120f090f0f070504050108010207051002070206040302101809050610030b0406120f171c0c020f1c0801050a030807030c03030209041805 77
    0x90000142c01030580081820005002180c080781e011940154412018100081c15890340400505400c080100400042d0312520308046400e88040311400200341c90300e4294285000d0b55216400c1e0500242004403400c01000014001c2200f0040c0c0c89400c8600019550050f0b401c50455071514481c3c080c05004500b0a800041c036182c05200300d40001d5005006400d1501c14410002c01030740c000d80041ea4044400d210100c0035071344142c0c00030644086034403546172407801d400700190340c800d003075120380c0d0214902000c00c1138a883c0c036134170f07c40121181d00d4009040110140050000c011070b4120000d120041060b003000c20203508075411009000e400c0c0041044c4103e2940310341482101c9598003071660320301d03505c6040110364210203078550b02801600c0642901c06500f500c0c2142811600c4a09503a0301c0907825100c1d0400000c502602c020390b5804212400e54507220381c0e6214040c402010400e000000100b418440d03810b45020010081c010f00081c00b810102c151980711034001540c1d01c2c081c10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 703386160 1250 703384910 703384931
    0x9050111030909071b0506070f02060a0b01210213080109032304050105030924100503010614060307050c07180509030a0c12020c0312030103060c020d09031203020f070b0109 76
    0x400d9500e240d000801c4280a6070b151320701160484240c3e00d0095090b10680c031200c000820074070a803417050480f43c2d15001030f8190448004d2034480040d00344086186807504000859030702c1041c0780d40f01e00124003810700e4030480c030780a8002071180b00000e40300144480c002148550040d0460107416000b0358170200c1c0d000961042c0c034240c004081c5012000e1604000402095018501440d8070020342c00039581445082c050790414551002c010b0300c40150308900300700b1104000100d40c40a400b003a0000c0104a08000b80742031b00140d410400380c41058080001450b03076206008076103e180d079500aa0750720542c0c0d0150b20080007000e50381c03071490605050000d60312503000419501d07c0c0e0300c540c0c4e91550341082a1264007000d03d21240e04800c6020342c000b4030344d854904011810701d0a510090850b03407589103052803021141201018001c40d00701d9100420102e03800340e00d101c2aa50450f800c0003004688410980007031091f40000d1800140100342030007881107100c501412600c0d04a4107119080c2c42 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 703387410 1250 703386160 703386163
    0x311030f07060e010f090306020d1e02130927050a0201030f02090d0201030f0f0218090112020603040b060a0e090318041e110706021c0b04090807020d0c1509050111 72
    0x12402440b0008065948800f55580300e101843c80304880c508208258039280d85600040e640100c1b0710701d07046515440c04465500da40b104003003401d6201d110031410020690200c884090152007500380c1c0d1500c40c0101079041005c3c1c1588100c4024000c204c07607402d9401c2c80e10345d8a410440e141680404c0c50180144400407540c000c0341c000070401060326011507603e50055006010124002c108a56544036031246002c4503c01082c0789911113483c9a002c010300e070308100703c1d190141c01c0b0a14000c000c07030001c00143c541d402074035000740d8030420326001c90340d850303002c140301608590000d0404c154000c244220024007100415601c0000540c07495807040e9003042c002920a1a550184055400b941c5450102c440342d108881c1c0c421015020707850001c00e0f884190a9030021030034081c0c001c0d44503c441c1c64600c40c0748143c0d010518203440c00d000e04481501c0c0c15942d0b02803908003034040d241c19105001085040c080364000740142a842c2407a6280204009001e943e4074060f4038042090703552181d001050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 703388660 1250 703387410 703387423
    0x210a02030601080610120216021201020f030c03040609080a03020a030f060501081812030106030617011112130210050306030f06011523040603020703200d0806190311030f 75
    0x180c550503c00e494520900560032940c89112040080d440f0112145240900040c0400040c8000401d602d07880d60041010329184100118100ea1040200c1040c1120315001c0d00d41c021058142140c90355540e00b0440050300300c2a0000340006070000300c0e160744503019030290030384200c04d6604106085a00081400b01d90460044030301103000e10700040c04c03140c181c4071100030500c0020306944000c41c0800d014003d070303042a0005030110352a4071003408074240320080c143e0910500360082c0b18a003101d9102c201c80d40325513200c945001d2100c600046c1c2c4211510460320501c1ea014140f42d6005601e002c1c02401074009840091080c0541c2009400c10071001500c68180e5640c09585c040c1c1a10706d034805d48402c401c0002c4007034000c0081e0900c62003c45180082c00050000b234401680c0c0301c0c40f41c40c0003001c400e484c0a02c46003030076183d60104a4003400061091001c4060304281c0300d03a441d28000509589402c1180442214081c0e10200c05c01403e44004154240207074101c0e841200702c0c1c05055101d04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 703389910 1250 703388660 703388671
    0x70e0604051b0f1605030903010c1e1d22181110210515060403150e10110d0e0a030f1b0f121806020c061b0102210a0203 53
    0x604040b40720160701d6142c006014907941c1c55040d5181c14410401103c0202c01040103035501c0d000130a5440003800d00b0700034036003190725519044444080300101d0410a180354812001000718044118420f000c0344d048075541060010108010751240c0d1008948185c600c44a401c0b01d0380c28440e804035030050710060f40304503560041030090b045030900188840385c1c400c43d50280822042e1100e082210910024907444c0c0016400089024075008210b1402e441d01440958082c03003040104001140740e5002e96110a50070f205c1c0898050100540913180c0b0a0721400c800d962850b0410b46224007405600504115100040c10300000d8a0310802d592038011090001d004201b0710302e01000224414145201c0400e8040c03c1d4181c1c00070580c880200d40c00c3c140600310f640c4004000c00b443d6658000864254406c061652841d0290070030170b0003921404138980d0680100004104038880110b002220020042c031080215122a250310707608042500800c1c103084418042401315140240e14000c4078840c6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 703391160 1250 703389910 703389931
    0x6030d0906021515041e0b09040c0605030703060b04060905030f03031302060c1f022101050604181d010203160507050304060f0c150510170d0e0109030b0108070e060405 74
    0x40c0f99905000c10798001c02803042c4052052404044940c0e5240c0c13040540c0e09070320307410505460000c5000c107800c8401030460310344144031300401c0000150f0051842003d8491510b0155120b0300c3c0d03c8d0040e8042d01141e0400741c542c2001090101e03d0303581c009482d40403202c01f2012031707400a6510440380c1c4c91303110503140c1140d5540f01c6d0382081d0140c01c0041c014044140782008846810b44503603c400f20320101c0d09a0240e031180c0000c0c0ca02109006000760045c1601000e40d2440d0741d51425001606a10551040c03030010040940e5080c1102a50f80c060700000041c42078101803441a080114002c3d0b108442c0709a0241c81c030700044944070712890513240041e038004020740c6010b09100b019101007121414803000c00442440300307400078100302c4080544501d4580c000c10281040f5240343d244564030f4114007189044400c6116001d0800900050b030211203041c02580078801400485421040da00042d0030070b0003a1000241504000496030308445ca00500c0d0b10480e00c89504000039681d0544425824 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 703392410 1250 703391160 703391173
    0xa1202031306020a0c0c0b031e07120f0608150f0906011503050c04120c05150f18060c0703120306060c2f030115081605011403070201110d0506030d090602 68
    0x280b0650080c441601e5605210f9079004942e6182028400c0c40e80221001c42c2c0003009024014211111644107100f28858007070042c0b501c45002402009840c1c08441c1150b21840e500c081030b1115030084024001240588064230240741c1c01d1000c00d9402c7e40c41d111550300d4040055819070300070602a0503910380041e404d00d02c004200c4100d018020103401d107001c1c20700400001a95070040700400029070310645100030400d00d05410030020454030018071808200070024440e055106500b00e6080003261008102420200b40c0840e0240c041c118060400d441450400b1041c051030400030501806c0c1a6004c0c02040e07203506084a1050071600c006000300c41120011a081d00c12112020030740c03d036600030a0003c2824000642074551050b444a00f20115500910420009120050200c0d00c00171030a02424a4100020600181c50b9103000d1014008408652aa40f003900155408a02582e0711602d170841d9540c408014213059400078800d1080c0388400c4025400b50701c03c841200da031500907125 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 703393660 1250 703392410 703392413
    0x103090c0e0901140106020c04050106030c091e120b0f0702030a05044a0f090705150c0d0e030c10050a050a1403100609090603050a02011407170a12020313 68
    0x8034000141c0744000b07554842d41540441329104100c1c0340245260740c02001010b10b1101803008a82043c0c011a0401d42010400100c032a0040f0210301150403200e0322401240c256002924801c001c0c1e0040045181d03030010020a200d20f5986090154035065403003902c94071110000ea030f491043c04402d6020820074442005400c1c0c0c00708403006a000b0750040310b203604619550300ca00a140e0078012003014130007640c2680302d180180c4c0e101c2d50302036034519034019641004910780d551403805110f0316108000450340d654040b2035007416a80018054021a030203400d0380d41010f0b18140b030b0300017054001d12030203c00388090700d400821926046e58a441d40351a003154894226015409103d143c0240400300d01c956003c40c180000031072060b0008260b100d191400c1080c0103007150130035030000811a0400c8000d00c085030740428144100d550900703000f041d22611140ca1070b4a80608080509039220584204440c80080c070700034441e01c012941c0303400348024030801010032404169178070401400307040ca9040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 703394910 1250 703393660 703393679
    0x610020307150506012d17011206050603210a0e030109030e21160f060f05030c03040c030b090703021201021615090b13060f09030203181504140a050103090c 69
    0x1900120185440c6080402015010f100034180300306c403da040725182510401e80d5441502d000c01210b84840400c0154542000f06111000000c4098010341e540c0700480c0a0b83e070204003420345a20400c001c079122090a104500e00d540001601d0008500c625610211525040c410142c0e01607050b200d0030b1410054000703001c403801811a07c40c0440101d0040d01481c15400c2103020512102d2000400e0824100410110390b80815400002401002021640da4942000903aa80484142e81c2c103a01c0c0c2d9158100011200001d0b4800b4000300c03408806d114280b48049000c10a41c2c2c002d880011148001c00035003030803071040350342d980b07005c0b100d000581d070024044900300200802d040c1c60100e0020308035241c80c624440161424224401030f13101e04000c0016074000c0341c1c0ba480c40380c5410440d045807a140a0b40303a1182d02c2400d400e800308541441440d0380c0344280000c000c0740c0c117010543c44548802040842c50b50105800b4401c1c018504005441d620900590030f140747d00c955a00348180c03070105500b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 703396160 1250 703394910 703394921
    0x60e1803040911030105041a0102030301091503060c180509060a182a090b120601080402011205130215040f120c030f11091501051615060e061002030715 67
    0x2021503000812000070101c91a01400d04064410b600682e501d5140c0000c10045440044103400d0500b0030320040301850ba00401600e044641442c000708101101d41620292015580c00040401d80383c0550740000540c0a0360036440f0b01019080c070b41c0904d44802c1000602d24049403c83d600801c049070601400503004443e000c607800a60021440c1e0700b14410382403080c0f00398864641100c042408124950398030002d81c0c8000c02e00d80d5901413510b9120310303043d0260040100100e05001500300814110791051300c4007003080c0d48107441040541081da1003c2c07042040c0341d6060744036065103c9105001c5550404850071540c0d50f1550440007890881d5080319021042001da4603007105000010100d22500f18204000d8030a1502183e050004400c102800390094204264412070311604400f590b0440c0c12205035000030304c00210003841030718000c035004c3c000ca600500c07034905142c0005058542d41e9807807409a03008440304819082103a10480ea01e002c0c0e4cc2028164044000d10343c5a85081c0ba80003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 703397410 1250 703396160 703396201
    0x1c0903230c19030b011202011b0c03020108070c02180912121f08070602010209120c031f09080f0c010617060a0203040609050d02102405062218060504060e 68
    0x2c81140b143d803921021500c0c5001d9001c0c00703407600d04015250440da8040c48413120407084000100340d030702d81a140c0c001e4582c03050000074103018205000c5000d03072380a548111221940142188c15038550400356000310001601e0070f01003880382500f0b100c614905001526014421986014032556070003542c40c50468101c80b04c81040c0080300404501c00381e00307001680c00f800680d0009030391003c0c03030030074006508141c801c8100c0b150455010004540d0303000c503800005c0e5010705140600500b15520380402004241e02c014106400001c01910f0042c040020301329515641000f0458241d87d242100c9564030511811072041d0030003000243c9200702070b130165070401c0c040c1c0c000041c00940c55546500c0d20000c0703220140980d20940750341404540600801203a00d00301203140064007148071603a81780c0c1d421406654802c1d180460501c81000614543e2509003511003885c0103920707561141e4608104c0581c000000240c00c000000c07449081030700465080b03034104c0315040c4403030ba10081c01c0001e00111980 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 703398660 1250 703397410 703397449
    0x80906040b0a030603020906010903020f0f01140a08011508041523010b090a0902090a12020d170c1c080420211e03030c03091c0903230c 60
    0x41007003007012015110402007600d00052190450040140041c002410303a4104001c1090034001038451804602c14800c0607244045040d403400d00683d0071203840c11150501c0e00740450340240785640038190380c0c101c803110b403c0001442c0c182e01c011103030103000311006010102900885281d07403605621240f00114000c0034406244035054554440c00700c02c1e03011406003180410100e03418908103565100814001104616017034608010501c401e013513100d01c2d0799a17800795811800f0764440030f54040c1441d07441000e026144c440042416419001101420b840c2d1007132503000400e500c0284400c074400d000741d45890080340d0ba04d50f81c1d0380c807504c5d50081103440e030381c1307024229007154498402045101540314625203202c90a00380f094908410401da1240c40345c0300300031102d800800442100d030032100305482d55a50f9034400c0f840c18580f101ca82d0603085000f5070041540e20999101448205072407180c1107170718102860340580c0030102012208403490380c1001c1c80c07404151030b218170440090b01d03207040c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 703399910 1250 703398660 703398667
    0x80a03021c0c17030f1503060a09080408060f0f0c0c07210b0903030a0c0804120e03190605060120061f080a11010e06030f01030803040f0f030306141c080906 69
    0x588403045031003806500f60309182c02106100c2182900b50032a5407020a24182c00d40151034540040c1d5101c4018100401c02071342c50410a0038860794501b1900a0403040c01202c0103824001c0c3c62100056040fa03940d01d0804051000c00c41d00800c80c0129084a46c000c0000c04480d42407880796001c80c412402d4842e20104950034000015908014251003007218a02440e16032070456500c0040d070300d1100045d4100003d042c02c210000d5020012006150000e00d8280d842e03041d6080424600440c241e0381880c002d0f40250b203001084042e41210380701b11340a90761300d809404031116166420f810503042c03c00a4015400207602a00000c000c1f0074801a4241289d052560781c010310303400c01d8500c2d00190b94189400e110700c0069600300140702d40b18101902c0301455490a403044189559040c000286030020020115051100c00c9520308041504902030341001c540340d00e03002d0002c006600c41d0103d52100700341034010030b280c00c20125199500412100401058540e2008001c2e0b115481c026400031061 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 703401160 1250 703399910 703399913
    0x9191a0f121314011a010207030b0a020903010e060a0c1701080d0e010e040c0e0a06050a08040f0302030d05070809070f06020c0d020301230906060901031a1b03100906080a03021c0c 79
    0x24554840f0911030840001488030003000e034000d080e0800319545040d5481004c0410026007010200c9500140e5160016101c80420b80064054a113a9100b0b06491095605004410807198010f40340a501a100c1c1d6040d102000503042c4490403d22501c840360700215195106a40201c98001c1c090005150490b500700c1d2640c0001c1c2110f03031021400700040c042107404802c6003421074580c0064441b50030041d0030449801c0340100340480040006103980042c8940004241c000c00503105060385640091100f03103840c0c08000e21171001112004030922404400158201c2d8040074002501c3c202d5020380003481c12101800412280034800720381642d42c1c1c030943c0c4150144194052221661559008100e0070092a0b20345401d101038220752040d0072041c0100000f568490004a031811030180b01c11040e620700160b03446d065804030918280d81800400c204032603000d030341480d0036100e0548003080304940720520705660300c40129004000d6482258140110681e001130341150b00715614080340d030001309 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 703402410 1250 703401160 703401173
    0x2030c1509030c07150e04290f060c150a050402030d0c06060e0c27060a0c052b02150915190603050d17040b060d050a060c030603020a0501020f070e070509191a0f1213 73
    0xa1544668940c000e03504080400180d440309541003370082000307004500b068ac0010351503c20f801505030600542e40c41003403c100b15508940300805202e0b00440c00c51070b143c0c2c0d11249540c00b524150480106040c800ba0a218410914120301e0034040d04075420044280c1094a01c040400301c10b640c0340c4034a488502031448800c26001c504040c0d1601c406030f01720f210501a15050305002d000b0020303207040341001007454002030301c0000b141c039050090140307494290303801c2c021040c0c1680c410740c401e0401001005105001840301400c884550b07900101c6a01e00c103045a107464103907401003c4419010202d4031611388848520300c924000e40540e42c0810a65868104860b0000606008641c4410080096150004d440401400b0a0025088060010784c2c110b45828040c0260100c01c0701103000714248500c59030694400c210007405690358029007241a290b1001c43d0301c1113111860340d00c20000f607800505401d640c020300d211900a402c1480901c1101c00020009004500132182c0c40e44940c086101c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 703403660 1250 703402410 703402417
    0x306090e03210c160303090203010c0206092a0d0303060f23100503180f0708010f05090c0a0608090c04090609020108010602030c1509030c07150e04290f06 68
    0x4500000750b96500080d4054080c0c071020440d0055002c012004000403a404081102c01e03400c2c01c1c681503004201289010340062040c124060b4042d0f117801084072a054000480601404c0c40070115000100700c00706c00c0796140030000d00402c0ca010250030304c1d241820f15000e050070481c030038140410340503101c200d1103090f4070180c2d001c1c1005000a00940e1285480200c9030f001005041c2d0b290380220b44d2139000030b010303444060300c25400002c1d51102ea4107450000e11110502c0350030070040e100000c1e990241540039003454180010000d151034045128100d00007041250b5a4003e02408400c0d4901003050341c03441e800a008201c01e0040b0000c00e0200d65840c894080c00605c500c02c00192052a0b00005041200582026080d503004114441201000007052140e0528130701c1e000b00c240e0746940440b41103004050404000380318600010640c210101a0081d0340c102c01d170769080002180b482044251a01c0c0c0d54051410200582428a6024440e00c8040040c1c000f909480f5850011804940030f0703030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 703404910 1250 703403660 703403681
    0x140415050301150806010806010e0a09020f070b06040603030e21060112050c0a050a05040b0301061206052e14060c150a0c03140c1b010501060e18040309090c030609 72
    0x46000005000c40210515030b90000c4000386000822403425174006015000044c01d01e9041c4544031031180b00d15070700c2203108005404a60015511080b02108401558000c1c4404541d2070003404c00159050425108250840ba0903540e060003200011051103041c50320a06407401c4405402c1e81e0304e9841c14100034031402451034810002d4641101e00b040c0c0d04110181c0da215100d080266000c0007207a03200c000f4102521000c440004034840c0d500d00085c01080300758042804c400c40f00c00302100703002c00356000030b2056003031002d40b80d040703201404602600400c1d401240da50881040c4203010501d0f9000c00c103840c503900903103400e1511580108040c9802030002c8411021500c4000304269042a8015441c440700f00d41014485d1000950911022308002030161600034804201380250b0344000444000c1e00320f0300d038020440c070350711024024070640c64400418069903070808074452403c69984118030a0ba056030300c88034900c1c1400e25600182c20110401c0b400c158441e400807410381080d00c00d1a1009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 703406160 1250 703404910 703404917
    0xe0408040e070c03110616030e0127060507081e060409080d0c030605010201091a04052d0606061c110c150a0f0c09062f030c1c020c01140415 62
    0x11910751034000c0824500f1812011305d50058002e0001c0481c0380f4940001680c000d04021500030081701001707005000510380b1070a58060300082d006000746110041c001540503903018130150b959040155610314055441c800f5000030009880045005215029001440100b02141c02140c1d51944c0c45203801540d21400c0140d56400c0c00c02100d5054803402d801840d082c00240320741c000c0c980b20640d003088070355100d8400d15214400070342008024020800005031441c242030103610203110781c0c0403c81c14802c0b046c95a2241c0030100304c4d00c4c0380507000d889048a1200001a101d2400407000c400345c840f108141011400c24004207540f01c4051000541a0b1503a018100c1c2d1031030011150410303a2000aa01c4401c20b2901481350300c842d60007050281556540d080c04a08200071041010084200441c0c09001a40c038801c151000c000200040900700180400c440d000080c171404040c840c450600300d040960300c0300800000d654040d007440003140c40740c0704c803840c1066a039030b801c03040340d8100d4400c85000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 703407410 1250 703406160 703406177
    0x9030706031b1206170f1606020307081308060112060606030212061c060c0203070302010b0a030305030c03090a151a12031c0906060f0f15020d1d0301090501020406030b03030f040e0408040e07 84
    0x165201f000103180140b1408001241c5514040d0040c0d1a40b06441c6e000e00720650002d480081c10b29041c007414000e0408400300c0381d86603510701b8120080b4030300304c80c12a0841d0400c007001401d00e00c0381c02603520074802c00a604a594640700304101c0c800b01c00c280e402000e0050100d03441c001c01c3c494404e1802031089a00619518000c82c03900074216180c1c841c584d80f080718260070902c0400d43c004140e95000c144860a15602d032105101c03a031a00c09000c0000f404c01c080f01c14410418245908070703843e209624601c1c1000c0780c81ca24100004000c40b01000402c5130310510250010502c000c82c45000712080440004407004a611200180d9083e0b1300309000110051100704007040b16900508002c00749915010074050000710000d443e000c490b40341c8020020000b40711100055174010703081c02440010020011401d0324500300f03010350024414100400d203824401e011740c0c2404001c1f2901015050041454603061030325104102d88050010b030307400c40c004d00c40802c7c80d42d140c0034001d02a001545541b5007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 703408660 1250 703407410 703407433
    0x90b040b040b18150d0c1d19030c030f060b0609030a061e110c192a1d06130c0503011a0403050304060e03010b0402070b15150d0209030706031b120617 66
    0x70303169181480020498100c7c50700d8200d204d04240b40c00c01c90003c40e0800b404540f1000d038030448401c1600041c0000c1800c010000070040114044030009201c1e21050103030000795010014035004070109250103400803c003400018070650f0011121001d000800d00d035016074000c081049401c51070b40801300d01c6002610140d01c2e1010001c60281d2908409403107103086903540c4180410300010b441c14041510884211550b26581441030701130315200e001c03980f03c59480e09101c5450b0b4001d60700c06c8d008400079440404051740e10300548540006640310306285901e4451005200d0303000814040d03442400740000320001c1c0051004100030700c26136803890700001e00842058211288165170f00e101d10320403c80080000d0403080c00e2944040104100401c0c04007034008a050401c8041854501d1200060200b01100d00b582c05048149419400c0326880c80d1a0341c4254200c510468402d1a000c415095003070f0400d01c901c400e50141c1c1e05618003c1520b0750788501e49010061258070840740c1c0d810084038243c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 703409910 1250 703408660 703408687
    0x9030207180b0a0f12060203040804030816030f141b0f0f060405010c050310060e03010b0306010603060e090708030f0c070b0d02120f010e0112050328090b040b040b1815 74
    0x81c04282c015041d0952030008031805c2020840c0d0000c00c441d0b000f000142c2401501010354005640010840747d443c01e2545510180c29020f11040300851500d08450f0b4503d48142100e080c41c01d051106240340c40f8060300c42c0b4448074071040704070105108509401058800c20302030803040c1400c0300000e00440c1030614005094555400c110350400006100300f00f80b80d160b9a050034210b401a0500c0241143d42c140864050b151000c41c446e01482884c0000442c1581944030f00105e41d0705010f107803caa110788e96401c0d02c0d50014480c204041c0e009004c0c040c0c40b50418030050520a000d441254441c0f50b544600c00c3c2c15400909403082e50315030118010f54004002d40c03d450303000101d0100c002d400d60415214103d10072040c01142440c114000d020000c00a040040f20340f021050700b041c96902d59211107a804400400101c0000205140000103580801e042a030f41500c100075445802c050514016056681214034902904541c10208403d1b646407031080540041ca981103c3d5503c0c1c185902c2032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 703411160 1250 703409910 703409929
    0x3080c120a0e010507030201090f05031804020313061503150606110a0b1f0305011104140a03030f0804020103020d0f0b010f1803020418080c0105070f08061309030207180b 75
    0x811014410046004070769800985010880802d08001c0d4442e405420300300d00404012a00a0011030300118000502c1400405800440e40079034111100c008910b09006c01d9000944285105e02d00f282d010348005105500145030700c3d6078812401d42007235070b680c407680003404c03c05142c089180c0d510881400656488801001c2ca00e03041c0c8010444d450300366030361a812100041200112a2070918560080380d01d1400420045070820020700c541301408040c00000e078418442c04003241c00d1a00c420346182052410941142e403d40ca684141c0c04d02c032003094903a14002401203040550030810030340c84d84928410503034403088041c070001326405040005090003560f02e09403400d1210120480a400c900d41d444e040c16240e060b02c0125800200b100c082001b111200d8009050120104284004940540c01144a04042c1d41c400d404410303401d4054981c0b034015203040f070f00034080d680c7ca2018042150420340e0418480d104444003a955100d89035028043d41d465070034815128041000649440c070980c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 703412410 1250 703411160 703411183
    0x216031115010308071202070f08013204080a0c02130c230f070804090e030a03240b0c0f07080703050f0d0e010f0c020901030c150f0806120c060403080c 67
    0xc0d08002d506503280e0350254017840308018200da8900c1c917180012031080c81494010030700031600d1b0019580390700c01ea502034500e90301504101d030a010b82c85070300b400480400d644061901104841991a640c076010155441003080c0401e002d09107180c2c0005072541041c0c4040000705c804006a03190003914001c0c440f08080e5060b0102c82003c8101c54138a07000c01048070340c4a00041c0101d95905800c0c030746245240640c0c5d000810803454580b19018818000c40203006042069a0802410340c1e200380e8040880301e810a0300c1e550411141040c0441d040490050412210728400c494030360010352555460b1200c113400c03020345608950820801c014082281844151400c40580901143e13148000d04e10001c1103060f0303040052a680c002c02c0ea9014003040c0ca981c9402416610140da102e007001004c10303c83d07102d1038840e807031252025441d0b5845080007c0340d100c2190340e41142c0d600ca000c200010520560340b20b42807801041000002561410020f1006500c0360050a8a4000c401906424030340382d00305 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 703413660 1250 703412410 703412443
    0x6020403021f111c0c1406040303050609100803090f04020702040c020d14042d0b0c0a12020c010801030303020c10020304061505010f020309040c0908010207060f0b061309050a02160311 81
    0x13a094440c04804d2220700740c100381c83d04d9104101c2d43c2c10a0500c2640c0301d45c00465030f000706001e000505600d608000e2180000391801d208070b44a12484075244211480340040381c3c4c0007404800300303901e4200c03501e030401000104058108001d58000408848048400c1c002590007041c83c1074540b40c100d012021202c00d90300c41141400d00d400c402d0a18440c0c1c54158500d200380d60070600304600d803406903550192202c60304040e2107003d0034054941c0c070300c0d40200580b6485201600035503114030000d500d5120700010307944d1860f16445c59500f0f80203908001c40f00d2080740075401e40616010050710185104501400c408034078901500d88041c00742c0380e503402c094100304507110500501a00007046607021042a03800141038403a0190407100c00440341c00290403540009100014006540c001036030420139114104101c040c51420400d0a218a100043c2c0c2c014101c0420000d011032580311940c0304040c0c0201515000b00c003000c82186400700d100c12408110000c4031032075034600c10480d880c010000c505 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 703414910 1250 703413660 703413673
    0xc061e0b0406050f040c17150102060a0504050309010e0a18020706051b0319020d050103122d11070b0f070507050103270201020c060409060315090206090d06020403021f11 75
    0x2000300d1113104107440c9140c020742d104d0070024000b0344076a441c1ea80018404040d20014100188400c2e180c00910f07002c0380c014031486d004900c8180091103400c3c043c55000740103620f4554400e0042d100040d03400c600c580d03c503040703010000b405803650125103d003040c450340050b03031225149840c1040f00c201030507074a00612500b10300c891386000d01088903001440c802e01803801c92800030300e50780a4820145420105414031000104100c0c0890f580f0710040216115980140c0c801000388070b4030481040224100f9428084450106029800301c034031040c1d40d4025580d4464840c00d200c0516885499580f08601d07000030b9140621100f40300540241400b440d040c007041c02c0d8001c540451006201c9401c8000358610036103401c683c0200000c46503043d01801241d1103942d00c8481c1801004a488240c0e03090404a200142e0710220b4454a8481c550080c40541000030b07803c00c2c410751140d000e01c1118910740c00c02010001d03a403003104000340c0c400340711503e84c6101c0074440c0003450350503603403501100f580c0080e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 703416160 1250 703414910 703414919
    0x90c03010e010e1b0904260a080106020c041b0c050715080106140a02060103030302090f0d03020c0102011d060c07170715060603090c051002010204030605130b011d0a0c0c061e0b0406 80
    0x78207500c0e8100b41c1001f2048814003040d600540b1141840d01002039010b8000340c1c0d040101d03007048041d412514184c007038851610b44042070100f40c94035036820b40d198914011754002014090380d451040c4074000d008507224203454003401345185802d03a8a0b4000b00740762500402082d41d012107600009645240010704000240802a6440340103002c010309042e004646407000d0713241c40c007031b20b681000003c0c03482c00e500fa42c42c01d01944500000f1103190040d403d004a519207900044804d1f0f4012842800411240e070750030103000c071140c015040888110703000300c20080800c032806014186143c0100d0310340301d62501d0140244122612944403106050a2064004c081203407104400100c5030151200003200700d040d0001c80c0281310701d42008216a04e4001400b00c0c0520603034442801740d03ca01c0e01950340f0390b05c4980c401c020b071010103050003542c0c8400d000a6a0050940c2140311840900d0030301c00c0c142d1100e41e80d8101642c00c040b21550440c0d84011b07848902d00c042d80a4905c0a01d0705031010424203090 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 703417266 1106 703416160 703416169
    0x905150c030a12110c0705100e10090e01140609040c0219060f0606050309120a0c080c0a0308060402131406072f15040e090c03010e010e1b 61
    0x50985106070401c0711022189500000c4c5d0003042001c0c0380c2810010f003115803000c84010441421158180c0792a8400c004d02260160341780c40780d13803600300034029840050585c000030260a500d00c040703201d034071032100300e03201310740c058902040039403030745006900c5c1ca00d80154001c80500310b50b46101c1801241e5028084101500300180075150369104104d070103000c21b50f07501d1403a8100c29404159800b44000404020480d400c05480f82c0d242034a0704003164110700b5805103650003004001c800c06503c4004a82e21440845085003004c2030040c001003c00c1d0140503004441c0c1c2c000380098ac44e80d40d044140da107150750220410640c04440c041c414540c004c41040014910b840b840c409840c1e203412404500c0d46401054654105454810310204054000d441d00036940950521010326480a00449001c090954004160641f844102c079180c50521440303040c01c02210211070721113a48 = true := by decide +kernel

theorem cover : BRFrame.Cov 703237410 703417266 := by
  have h0 := BRFrame.cov_init 703237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 703237410 ≤ n) (h2 : n < 703417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
