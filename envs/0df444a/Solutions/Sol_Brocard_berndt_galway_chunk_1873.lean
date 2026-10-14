-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1873
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:59:09.529993+00:00
-- url     : https://prove2.me/submissions/28031b65-36b3-4df0-86e6-2779298e0b3d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 336690647 ≤ n < 336870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 336691897 1250 336690647 336690701
    0x1a030105091c02071521090309030f0201020f0d020f01060b03040f060c1103070804050f180415020f04090b280608180a0c0303080a15030f020a0f0b09010201 69
    0x54050180c001200700e1a6000c00070b4020b100300030a8001e808003e081e001c0002400700042d10307000c0f102c14a11185007030220304149060170392150002040e09560f850346542c1c6543c640c00c81c840c80041c0140c0c1103014902e100342410004000d84285080d503a4014112035010340f40b1103085410a810a0440c0c074020010300c404980510940f01d030781a040003000901519000b8203448100b028082d4401c1800301141c3c100a00a045000d442107400982c2c06404003854a000c000316158900108249039078640c0c0460042205d5011010306408000e000510f0808032603820300581e00207500c40b18031b8540b81c2c48030b0181405d04000c5255243c0c0300f0060301074181e0340280c21001000140c0a01c80410000c80b00180d00360013614140d03402216140c1c1518614100f9040c600f40082403070001b500070402c1980850f8000c40c07107115441d485103401c510002d9980c15a0b8500384c50820982050740d104210650118054071122401c100a10504c070f006565811080006803e40c0d80c0000101c1292505039080c0b110 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 336693147 1250 336691897 336691903
    0x110a030203120310030b0c0406020105060906011d1504090209040612030813030e061c0c0509100305060609040c020a06050a0204120f020a030b0c0a0e0603011d09120a031a03010509 79
    0x25502d980900181c5a60351071160000580c900d40c8042c1c030740c0d0221803d000450007980000c1c015905d80d50b00034813031036540d02c01f405540780090314060f0014810200c41c224000440c0d415501891000b090100c5040750a19491002d0b0080d07007054a04560010b0a031005141c240b103514000c00c00c41e40c050030701c0030582d00e000e01000c000802e00042d8810200000c1c081600c1440b00320035020004080ca51210034040050031640300515500e20307220f01c2d00031011079450199040d1403c41c1c5006081410b01101c105045024100240143d1f0b0812014440080990381d00d004286080e00c01e0740c01040102541d040c10003d55101400320301c1142c1c81003200f80038005c000050400c1450700104880c05840407840400c04500866102502c658083d60a21031041074040c010443d400c400e40d01d000c440551401000340d20f01c0700384120704e00766a12440c0100c03180e1001c9101e9074090344100c1550200d01c110420210781d64000e903e0a000a80d40c0c900a01103030000c248090303c244010341c005c0089103460014280c0d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 336694397 1250 336693147 336693163
    0x1413090c030b04061107060507080601020a080a030b03070f080a0308100b040501050f1c06050a0b0c070e04080415030f1121130501230106020f0601050409030c050d0c110a030203 78
    0x3101d402d0090000301804020b8002c03844d00b420b00c1c20200d640c0c242d04d01f0100001c000a0300ca0b600060f4606000c9005503200050b00120141c0200b80d941c5420386002d0140e0081501c0111250107000d50390000030b02030740b50041400285003601c00340000103028540103000c10401000105001c1c8540c03003e2059107058400e6a054174401c0c24030390b94540001c0400d101a0007010041c40740740c504c10480c007401240642045040340e00a64034a245551603242000560185402c41e00650340041c208120101c1c42c0c100c3c6a4200380200c0b14946000d440e0380584004000392210f08011a8413911a02201503a038403900ea055800400c1031410038036402e59000040a11440d02800103e4030300100329400d00a01c003e900c11540f1078020130001800c5c17445000c800d007007420314590110101c800003400b00d00101c2c01c403c0d10032040d8040d11082e804c00003044014030441c1001d44c00c222074000c1c40740014008002c07010360410b0755140c40842e502103140c41000e001d51116040d000d0103c0200800045c1c40000c0e03819 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 336695647 1250 336694397 336694403
    0x1c0c090b07080f0403080304050f01050702030702030a0b0c040506070803060306060a05010f1202091009090507020a120c030c06111b011802040b040213120302010501120b040803150a1413090c03 85
    0xa035110071081003c8404e0085400162801000005202c100100000d8482600d000d0100034011503032441811381c0c5a00515034042c0d015040200c0301e20002d500503800b80d40c000211000941040d071a000442e943da0484401151520300000600c02d040c5001c01ca2a80d00c4002201c24103901030070078000801401003081410248421411002e0b00581300740c05a13001c02e100030f03116806820345814000e101600274400c10414a261401141c00c81e44040384040c031050701310f495034081d00b000300822240103910320810f84c1084421002d49001844138003901c040307410704c00c08264960010f401c401000c110000e4030450141e241444400704126000c140d806281c0e0100c034006445900007012801900c5280c0c6c100c04441d0611801081c41c80b0300c0344c580c002c4c050103a402008541c0e01c6031460a2403568400010340038640d0000005c0024159100842d8802c501126003201203417480081a807111550b0810920b03e01030401d1104a03040c601a8018032500c03041c414058510716840d42012005140405 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 336696897 1250 336695647 336695663
    0xa12050f01050f0a15180209150a02010f061703120408090d03200a12031d0709270206040b0a030b093d1e0e0a090c0e1b1e1c0c090b07 59
    0x26100c2c3d030b4a82030500155a0310a240e00c2c0cad68840c00c5002802400c000c1d10700c24849213802c20104201e94112600035003400b07240000e52919108440c0307170000b5500144111011501008940401e40303692440351846480b0740c50b01c002071100480888040c0c0300004202840364400e120100120f080c0031000c100d25155402c0c0014a2040d0810000710400f1402c1c2d140c001d446050000665802c0a40c0000041004580030418618840c0903410b00390740d19000107544600148028050500122b0040280d00e1842c200080c1e280450300c00300f8091002101d2031400900029511402c02f03c5c25400300c080da088284081c9841030441000913407c4803940298940d008048400340140301d02462180c01801c480038002c8014600905054007514031144d003180d40725400340001a01700441c1040740c0c02020312020f0381c1443c2c981c110389190316401c80c4044c50901415802120380c03040385440202a038151220180041c20400184901070321041003c550030000801c07000c0000c586060151103440340d1041c11 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 336698147 1250 336696897 336696907
    0xc071404151e2303010e03040308090f0a052d0a06081503010608030412110109030b0f0c0d020a0305040b01060809031207170118060608060a12050f01050f0a151802 72
    0x140310b068188035005101d05543c441400f144000c880f150016445200720f00a1240341c5601a034541c6074040c1e44130040490500f030043c20510300d049003061841d0030303014141c44034550f9075100040c04c10f5451000061a1401003041084880088200f140b4403802500c000e5140e603d4401c008051400081003024012a038002e82107090340c00703410490042c21440122a2200c0e1115050400c990b0051021036205610b0301ea0012a540103000c400212504200701c802c441d0741e16940b0b4400124010b01c8030b03000800400c2200f0700d010300c070300c09001c940500b0b9900192901d401d1800700e14251041e0088410300022108020400303500104680324260400da8900c0d180c0c50b000019034000e500240060511642a000481c01c100b00741c50030060300d19400002d0105541e95082500d4102c01a100c00c0d40081400b0000c2c01070b03103002905104840d00c10380403a20300c0081c3d00106400c4410664075011401c0a086c24010410824001c0d1407032458008007102203203250003178041000013820354036001e640d00030030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 336699397 1250 336698147 336698189
    0x6090f06070507031b050406150c0609150f0b04020c03032202091602060a2a0203040e0c0310140d02101e0306080f120a08040213020c07140415 63
    0x100740c886041d40300d82150f43d10b686a141503521903200c0082c1008101e01040001aa4a404d002d104204c40c07041002d06151041040200d421007210b00b01503d8035a103030400d000001d85116103521b56100c050340c0c0028102d1100c0340e60025a0b00240240e8800c0340180181440d00501008598000495404c04104c90b00e50208811040b442a81c000e1340c032100c000200b050345940c0c41d40060100750980d09491443c2c1d24400e680702100c0008242460300800301c0d2070728a048940d80041c803029205401101e0409a481e03c00d81c2c5082c4040701c00400102003c810303c113414035003086030350281101e000104032030078002c00800c0c2e0303070a030b110800382c440d00c1076403a180c00c010b01903024601c1c3d03102c0708a582c00104007503e8001d0040d1116105400f024410210700040b0030344080f03817290fa001040c2240500e4507a0403001102c1304103018009a9000960030603158003070b54071744000e0040041b400050702c000c0b031038010400000500d069080d03000b1030900911040c40403145440005544c1c1d40d030078804074282c2c59a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 336700647 1250 336699397 336699409
    0x907090803040308030f0603160302060a030f06090b150345060702070501020a0305030a0f02090d050a02040c051620060a050d0510060807030f1107120305011406090f 73
    0x140c0200c095000c00640071090100400c0114803c000080f203450311030700c03008140340e40c0317090440185800d40c010040500051420f00d00401600c03087d803402241c000040701c0081e045407041e0b84501c07601c45d510f00098950742403250410507a9101c08126500b149004028a209000c010130060304054101c0070901c081ca11145400c5d151100013049203440700c085280719a51785002390744078009441a00c4000440750300c000782414541764903070798003815525082c91500145c00c0c0d4840500172380343c092105090680300d08104c0300149010303100400310104180107000440da1404c1c00c02c02001000c00c03400000d1403620380e0399102070342e1058400310048001441d1a860640c0260f11a03130140d0001030808809034010f000c3c2000b094106410480b5072140c014041c4d19204901c960347c04180c1d100c000441080c0254085141000440c9000c585020008500c0160f50300c0845c0440d0820980d20383d0600340340d4503105107409446e0b8042804000b921040026955014a0f0010342c800c0100c40b171a00003d813141 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 336701897 1250 336700647 336700649
    0xb0c010204031703061305010f09020702130504030f030c020c0a17160902090901090c140a17070f0807020604110d05070e0c03160309030804120203120408030108010606030608060105090709 83
    0x101600c14030b885000c0d00b01d59a13482030700d01d50700c1424001612007018019206460482c0c04c0c9142c1000580e2600503803001030b404c080401e0341c0c01604840d4070704e0018628091203110768072a64400c1100701c01030304040c0496074240a060110760085100070050b80711901d0b407405036804d4100343c51903c0d804a044038589881480981a0b5418241c000504a0081e4028041c501c404550100d005e81c0c0794030081d41100d441290b590001800e014558111002c160028040c2c0502458005080c0903d000b40ca0b41b80030080da842000100d1740c422200c0190782c0b02c002686c0007602c1d0300c042c0c4407509094840c118101d6007464414402c21000c502c00c420002c007041450002c00854105001a260071030400c58940c00880380e1200010443e4007501110f4440d00c511a8003035899202c0f650b941c0c5964850700081005440d10009510040000d090719680350011b061040c1c0c803c107001c5c1e5880d8100122582034802c641c0c440030a242c1041402c5c4a0b19a0100702c0906441003626800415510300c03208031011304003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 336703147 1250 336701897 336701903
    0x90d0503072a121110020c03041707150f080a05060a15030e060112020f030a080d1a03010f09031107031a07050f0c0303040b1e1503100e011d0102040303090b0c01020403 74
    0xc61030783d48035030540000d00369500078035920956810110b0004600c040e48107891070480b10760020403041c80000f280f40035503c102d614140440d0400d40c3c03a410002c040c803403000c01f40f038003066840300090f541c564001409988070000d100184110300344003000c900c540000c0d00402e05956004100001c1031841b07030380120301c44100d00e000c680095a460340d800e590107540801c11b82c0180c517000000b60036420001009101c899100d003c4030b04e0103468000880041c90030100700d040c50030b002c221600980d40c0c02d024140308a01c803000c000800c0c240514001d0540400003148c02c3e01508411402c1003c2980510f4030068070b4202c4888041a540c0c00008494504c00c2c0c00702810a00800b0818115441000029502c160300c5446c0107545074507160005058400900000b0806416000c001104400c0c03131107841000c0e14010702201c103a0321007070341c81c481a118074115000d003da56030046601c199864180300380446070207400851600e406c0d9100241400031034041c40201141c00110706088000c254115002190 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 336704397 1250 336703147 336703163
    0x1a1002010f0c0801300305070f0804170105010608070507020f040e03030f071101110a03091a130b1b03070f050c010908030601121a0d0813060305090d0503072a 70
    0x400d200010300401070a00070f040e880740110360028601004850300f001c60301e05101c0c2c90100501703541d800300e800364406007044030007060000d40480002d000901030f00182c0000305945610210560f2000c1c00c6880591003001005402c509002601e5000000c40d2403c54041e1804458030b64184049006004411280800341c4400020040f030302d6164601e42c0d00650040c1e03500d03d210320052403031074280d45100a0342018410100305250710315000e540b1160705140700d421904d2aa01c40c55165002e1204100e61030f610300c1c03e900400404118030303400b0040d40002c01c0040000d0800e4030700c4150f00103010003412001440b0200031400c044c18014810303120030707601401c005d0040114510300590950015201e10b80803518041d9005000301c428000c1c0041c001810012110850080c02000020030b8061019211ba1404104c50400740d4510b02400c000b4144036240070501c0d0405c45242ca00e0052000540c0080045c144180a20070f030b0700c0441e5803080100c10310b110306498414140a822400c2000009191903 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 336705647 1250 336704397 336704411
    0x2091512030a051b1513050f010e0318030102030c030103020d030504170109020f030303190f0609150503060106090e0703020307140c0c011107260307140714041a1002010f 75
    0x3d610070014051030382c42c104a00003080099241c01d0740d90441d0003010b031410120b40c0000b82c0600300400300c43d0070b444c001c20032030b6803035400e00a581c0c1c01c50b80c0d1501a0350050f000010301d65003107455030038580c1802d030058000714507524040344414900c0c041800020b1288061000c0c0a0130300d44100c040c1c602804126840d000c000244059840c024405007004a0040145482400240c034001c81503c0c07181e49064000c103507032031601151500928024030440d40c0c40d0b81d6810089140c508030300c688d4041c42c00c0c0046070f0001e141000201460035905903c024200b00c5803520a01c0083c00c00308043d03401281509016882e9101c440341034404040c400798143da1346d2004950310806000004000781081000e072107200700912601d124070b40303c0106020301075100042c0144031900c6200e540503108010018001c0e00c1c10036041d0342d40c09655107100c03040800d141d405220188600102c40c0591f80b080c8100b03c80070401b59034500f10342e090f442a009246c520079507043c2c400342c81050007904844213601c52103800304242 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 336706897 1250 336705647 336705667
    0xc0f21230f070203032b060f05060d0c09080f0703050105010504050c0406030c141912150303081e090706020705010c020a060503070e0307170c0a0f1205160e09190209151203 76
    0x46c880003c180300390504000303002540950499001051f0f8001511940c6020003800c0c03114060152481c02030104201040005a0310109122800da5003000201070f1032024594200a070a480d07068006910861500050102844100f800c580803103185040104000500601c103803a07203500c0024000304554000b42e003c0ca07071210440702c40c0d019034030750311001c4584402003480c0e402c0300c018805160340c2c60b201050600209018503e4160700c00d403c641d01420607001c07800141303200a001e072601782c5076502c0050b091015030b40502c020005860286030842d10312800d5000a10f0500084c03080394140b003000404120428810100c5181d80710010307049501c0c031965010b02c8200f407848004100218015148824071603e0070328001070444a03044d0018003d18100410300c01183c2c64100100c0b0f040c424407a03401c248040c08003420005020f099103c3c6614584142a5428054800f407002d80c62001080b00c0001130703aa940c0f02c0754000a00c251044a40c0003e080803411154211505601e588000310b5122030b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 336708147 1250 336706897 336706957
    0x5012a080d1407080109020c010605060f2a12160f030206091e060f061305010e060f040c120c0509040603050c0114190c0f21230f07020303 61
    0x140c1c003607400821403400c182e00451100c0c0c0007910b8180c00160400e00412030300394183c000c1d24800252500000b0302513550000038401b60301260f201c0076a80004160708000038456011100440030003001416485152804141ca8486c100403008200f0004108650f22030b41605a400070258481070500d0580028240030355107181c00c4611a4041c400c01050318045c0c2c0440e0380c00b0007107000d0100202610380303c480042c860940005c08581e0060b907404804485150749024250003042048580070342c5090410074009440f007004078160003030742040419991650f001d10342190040c0444000074103420004d80480e1140b1a102e00d0a0303016040950200c1448008101c65010410036290840105c040b8203800d605405010024402103c0649900d0100341c0139006030745029100f450141d4288030141c0c5d455541d055103051a00303051580002c0300103403d80040745052188010b50904040350040003084965108240ca40141a000440c4041c11034804006540c45801410250380d2607000b01e101c0c42e45 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 336709397 1250 336708147 336708157
    0x60903170718060504080705130b0a0306020a230d111902010204050301050a0e060a0504030c0c0602060a0c03020313020d1a071206050d020a0501032c1e0f0705012a08 73
    0x2c100071500500059090082e000c650881e031450000c0c000080c6000308014000a1b415080000c4a03150f9906140701e541d01c0714250702542c4205801a120481900c0c0180b4950704110481c00c0e2803003980b14240c003002d914040d600d20100c5408041507500c190588600e2601403444411002401a841d094401e6019000303007040c1c4109400070803441e034829680030240c0d505410314001c1908030b180071610181c1d060300a564018082c0c00c0c5400503807259030740c0301e81c2c07820207500c1000141c00000074814101000d000b800408441f0707181c20350440c14804510b4200044488000b4400c02d03042c003120007005220603603150b81c0c202d607543c2d01000d03142c03c03000540f10320080c00030760740c0b100d01c1d01e0000304040c81c1405040841c150003030913007050b2a080070010b60042c11000c561321100441501e50718a52032003034070380742c080348a07020281110400c8165904000410342d21444070a4000202541c244040003944400301c8000b4a8013800c48842c201080940602100741c860007951310500f51003d001445004003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 336710647 1250 336709397 336709427
    0xc0b070312091403180414100b0f04030812010315090c06030f0b03010911130e07090908070506011e0f0e04033b10020c01140f0c010911090c04030f0609031707 70
    0x2002c807000d01c0d140101f1100c011103509040d0040c40b00107001c1b048008001d0040d180480c0c108528064803a240c010480d006056210210348a100c018130400005c141014040d8900903001d01041c0c10940d51254a0342c2da0340585801c040d0340c0e410030340c6e1030065604940c94491000c1d00801404081d803c100405800701c0034114000c410080035214400d4152084010031030b0f100001d800a14104029a00909100013064070062828401000414000d1084600030101c4080c80032412012440e0885c0d065034030b40c0030300c141c078064001c00c00820082811142c2d00c2035051400c100d180098003030350303c482e080114110504030380d400a001d00000348258040344910301102c2508851442c1c80c02265115100800140083e0407801d00c0c00382e441d00c01e8098a81c00500c50303201801c1c20300380d034015801c40300c07050400e07220103140050220742030030040b1f06550004400c144003440c00381940c4894400f0540c4010003003410780c3d101d0030401494400d80c0c3c03100310341407508598049030810140092902c039140b0030030b03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 336711897 1250 336710647 336710651
    0x130f050f061219061d03130f150815010507170901080a06050d0b06120d050d060e04170d020909071d0901150c080405030a0804030c0b0703120914031804 67
    0x18008000015014603a0909242c2c0c0c00c1a640c21540d810f000741c4108080c1750180c42480c845030001c03210070b1015199000f0111042d4040302d25020662900c22030360780c0040c8140343e45160381000154017840041d40006070f00c48400c0c402145c2c0e801210544649200906404402c036103c0f403600c0c0e030300001015503038800daa940a494542c90703406421034401d4401d895000a070041c0c201e000501c00d2002c10380c008002010508001b40a8030b1031070912180c08024000a0030014031550090424801c0700041c00e003e41000d036061809903585c0200e00803081c01400302002c08102e410b032203102c43c2c04403000518064240c031150f003044100a4401154584c0a00143c6005081c070025401d1103c6220704076031041111103081d0020000c250f61031803101c442032f1031040c0300f000041180d840400441d401c4034820410380365a10b295090004034540d5a801c020b8005400b000b420001c82c4c3c1c02440d84c01045801d10b030000300215107242400a24042405803d014000070071140c00c5160136030700c0e00200e55019101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 336713147 1250 336711897 336711919
    0xd1b1209080c0603160c06270201200c010815040230040320010b0307140a060203031902180a031514010302130b0a0b04030f060c020318130f050f06 65
    0x104040f5020440e00718802801c0356480c502ca80c0d218048040e030305401a840080c144800008180b041607400301080c145c81220701481045503071182c54000103882046030050a0710041e19541c1e00c0b07680303403100079040193312004a00c03851000300f0b5a076820840144115550100407504c1041c201c08815164421480b280841c080b407401c54895030300c01d69040e0383e8085d0030107200c8607400351401c0b00d06481000c0d40d82c5215a544680701001b40340042c0409074026107440400d282044007207001a0071410443d00280240564007042a00418511021820258075240d0306410340c038201c81840d40032036212066200000c21701c41800c540542010800a0500130304440f640302540f150800c3c40025080310401101c0f000c5040f1a07445a083c1c500c000b407200012a81d101944546030b000360308243d0300381c80091485400c1044511a1602d00403050000d03600b01601c1c4060240a8400e0000c01c6000794000c1c1d10400c0c07910303400d0307001000f5000940307400c005078141414090040c000841d4198014611416 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 336714397 1250 336713147 336713149
    0x501080307170d0603050601080c042a0c150c08150f09040b06030f0d0f020d090806060919090f120503061e060f07030309030306170d1b1209080c 64
    0x41200d5110b07030000541074509004040c05403540d8004680250500e5880c100070000171020312515000703090744801800758140210420040b910700040c59030450070a5154200c00c07010540c5003401009850810500c001c5281c2030908a400907540b042c074070725252460310f98545800824441c0075240380c1072885680c00700503041c00200340c601c0c030003680d01041600001c2c00082e0304c0d403101503201c040074040c5c034441e24828400900d801000e00000300071500390045040541d50401c2640c6610600e807800300c0c0c00034613056038143c44000140195010780e040000180c42c40c0010742d0240d0105240820400c5200c0f5030703042280001c40034400403541d04d07e4102c0c003079585500c00c0c0152805220010a8a56010728521700950200503942005801003000d00c20150300104180103131521074002c1e240411104190319004003150719035000200980407120401d410f0000001d08002c0b0b40117203080c01458407880800040d95036942e988010020300014521481c500e60150100b42110001030071074a0f0500d03440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 336715647 1250 336714397 336714403
    0x5040b070906050d020d060305010e030a08101202060703111227010905010c060e1005011d0f07050702030a080a03090b09010603080706020f16080301060207050402030c09010f050d1b03050108 84
    0x22142e10002082480004d400f004194000c0c42031012900000990310b680e40d40c2c1c0c50a5554007806541035030404650040150b0b000030100d40d014603800400ba960604000c10403d5032038030800082d010366004208442007500614100701740700c40480448028884203504080c080d844807810494504600841c8201c060140f0700c26014100140c5072035040305c2c00c01004447c0f0452041d0b0503039419440321250400d0320814042480490740761240440c685d8102200003101e100b940a85441049014003002401c64520801c55007185e018a0059900e0300c01e400003a141850300007014002000000b860007000b41c040d4000010f0510a03040c1c03549036030f01ca0801c20300702d071150f02c00500f41701410000b80d40091066401022009281403049007049019900100c0c0d4040024040b80c1180b030000c018050941c04115090007010b084900b1346c91450100c11442103401406a00c50602c640c03000c20102c0c00c1d000341c056840e07403540700070100500542d0031380b1140316804807050500481d10309000070a44c42c1c404 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 336716897 1250 336715647 336715649
    0x90f061008040f020108070c15060302011103070507032909060f060307120602030a0f050702010b040524130605100f0e0a0605031506041e090b011814130c0305040b0709 74
    0x121101c0d0f0040041d001034030311000041c5003034104040100b281002a4040d00c5401c54440c07102c0d0001030342403e6200140035408190700c00704044d4410711242d030020b10001914426207a00804e8580e8640103141c0b2620b80e0b11400c0088204001e00c4400c2001d8031400050046c86814144c05000098898400745030301d42206009070507004907203109000108580782c000b0b54005805150008040c41a9140f940440744282e82c02c0005075158a41c4221515260003a690000180300d2500d40c1012803202940d180d50010041c6e600510a41d00c000f081520981d01c040c005040243c410390b0b0080201000400003d6414010404514102a1042c85090203402081034450700d803146451a20746288042c01d000003084640d0b0700540811020981480310501401485071410040c11454100340380c00f4107031274200c141c044c100b0145416007000c01159001c035204441c900400000400491004a0340640d030100a03240d90909080040150607856844148928020a41c00c00561030305c410440c2c00c6501 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 336718147 1250 336716897 336716903
    0xa02150a051e0909090a020102060106020106051c17030c12090111030a020c0703170a03060b21041104050c04171609151701021306050c060705070809090f06100804 72
    0x8103000030050300c82001d10318200e155411104500341038003c40000c9000c0d100b2a50801c103504050008001c65804003c43c80c05080540001e200f450300348008903105101d101c10340000f0f43c403c90354900500c808480d00920802030545401e070741e494052030248060b4402303802d044032200c2c6240060800ca0061040110314110344141c46d00d1512200100806500058000101400396000010018080f00c1d46404089a040c1425466244441010b4201c909a030302c608076085c0e0070403920700c0c0d0f03884480701c0c5d5110004035008445961624141040d00040b2142c2540c0c0082c600303001c1c0710440c0c00b403501070000c80326400c400501e10410010b80c00c4d1601100052100300040304c22081c007401101e0f400c81d42c00d0440401e10300d0340c3ea5648400030000d8039184054883c4e03d03580069407000130030040d405400038100d142000340c50b0540309100d103031b540c22009000c078cc2004400320714402000307400c80403138540c6000140682014103088081c8883d0440c1074580901c00c4031012070000b030380e500540302030f481160 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 336719397 1250 336718147 336718157
    0x4050d05070f06050402190806100603060f0620071410020a0c0306020c120310140d0b0114010306120c23091501180603050609100b180604080109050a02150a 69
    0x942c3d5250030140c03d0180040743c6c01402c4d91a82c803400c00b002e100f580c0062254500900503070411003064020009950031202c205810050107010703044811800c942100d400f4a4021807600c2c12203d071070f1240201c048020003e014005001414494495840d95005400c5440c001c070207060308026682c50804e90801070080c01702d100c00b04042450b580c090440711144c081510681e070228031040c01180d0048071004807810007110207000c000040380d0350380090030098855151007899600d41c0c0054180500c241c0c60701d0484810542c0280c4d229410920040c0009401171103030900616010401c00124020b5101e070329100ca9803400b1a04141c40501c200110290410b66103480721004a1301e60030211002a06000602514480e080c4030202d009004211039030b03000a07a424103008000d02c02c00041c0c81005403900301c840030300605940c1d00460b04428081407480030010006004900d1364012903009846a51900c1e00050600c40003080e1034405038401c40300084c1c0120000c9010200340160305078500028 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 336720647 1250 336719397 336719423
    0x602121302102a030905030a0b01030c05010309022803021f12020910050c070b120420090f06011e2007060c020108130512040303120e0d0e1f020604050d0507 69
    0x150b11443c01c0d0203100d000c1d203441c1c2c18441d200c030007203490001c000b201299a8821507004105004c126a0b000b8064002440d0900c80d504090f00090301203108054820809641282c480028a42c0c0e4600c4000455001d85401101140030400b0020703000d00040d60008603030344136841e0301d0804051084900020b0010024803428010450484845d001550080a02e10500304041154001d400c090001085507044200c1985068940051600d400364030700d107145d1111040c201400e9560040a9070300040c03400c0320b401c13540d03500e0b801254560b00300010411461000364035040341c2e9522142c059000094000003c10715541c0d603402e03e5880d0200d108080005030304196100056200741c07019a0041610800c003403100400d501c8180c10299412110ba5056800003010806c05400920400c018000714508000001503800040d441740003c81d542000c10140510580c217550b00c8460360074485c040c0042004000a040ca4003954450381030350b041e42c80c0d07c6030800f1800041e00c036404903000380b03078016200180c034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 336721897 1250 336720647 336720707
    0x5040209010b070c05130b151e030910090c080f060f07030b03031c020301030308060108040210030c0507050f01060e100f060c080702120a02040b0a031a04060212130210 74
    0x1030700700d90011a2100b5504c40c00041d01c2d039032180940d0790780240ca4000140049101c0420110122a01011841460500031a003a220800401d8141760202d200c02e60342d642d55000b0440e040c09030010aa1901170700e004d4810741030254942412054030325550440c0e030b07000d1100c912940d0344c207400c941c4451280d87c00800900b80d0741c403030b81050b42004000340480c0e0030501c1c000080402840600d00420590342c0c00720040040c1584210510703040302080c207042041e81015004101521181400c080525454030222800c85114004503031816810006684080c840402c4580c080c24040c0700380064003801c00c000c070703482041540305a001c407035640014043c101e00d001c50030346500e041d90800782c0c0e0b1303601d043c00800c0240c0c03540b4113501001c0e40e85202800e4128400c2c8100400c440107001e41ca80215074128090002980004d41001507611001c50040595102c0c6021006441084890300c8184400307000d000941245081c0004003620031908013035903100c0c241c011901451002e140229685c0d1110401c160 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 336723147 1250 336721897 336721919
    0x3110c2e0c0506040303050a0b010306080a0b09030d060e06040e0309031c05041521110702090c070206120f0f04020f060a0315080f01060b04030209071809140a0e010504020901 77
    0x24460311420100c0d040036040e140c140c10048101d40c141c0100c1c1d268020041c0745410307407180085003182424100301260808242700d68941892000070443d045d010082103860000f0415150303e0084074100b8401c01340c4800307400c50001400d48819006508003250700f07418a0001c03003076405050707001d030050209a00075400b180c182c59003810301c0d0090010811000c9405540304460407400c0541742c4034500c1c0003070708007603400c400c403105048007010307901e40210f1030108102c41045464032307501180e09110a80740d0140400c1c46115048000390f204500091135076813500e42449151050300c4009200c0c1c413030f941d480c0b142007522200301c2e8002e6002c00d00200420140c50b16070080c1c540c1c01c032036107000200c202600c800c500348540030307402c81006a0702c803c41900b00c03880c0034040c51020704084000542454950790104401050189c0a80c090156032504081c20b4620804068000e1803010010300c400000c01c030045e040303400300342c481d00f04d0b850410703505600d9400c1c1409140d000710b502400001d2180c1c81c05501c400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 336724397 1250 336723147 336723229
    0x3070b090a020607021003090609230f060c090102030903030a111504020a0512151503070503030c19150c05070614040f03050306040f090503040608010f0b030408070809030a03110c 79
    0x241966100403030085275561245901c10340c821440c9808030070541c1004814119007000002495004900c4120752807404650b06401c5a03200c41d03565120400ca41c0140d00314041e142c59280c251101040c401040b95200001200c142c01541c10b036401c065640035070000c8690101c1c1c0c0030703400400f8503408001c641403800f5159108a040030a0300c00c05803844d04000780c001d900780c801210b40c0c05010000400b034a01405420f0050004500941c9040700342103060703451705884801c4800308200f0800c11410b104200f1480d281001d42d6a80c1081240302c0e407580684190403a10050718154503181003190090541c0c21424002c9400c02c5001c0071810311507030121065800142000c0c0c21640b0b4541d40070b0f03808040d018030440c3e6841000030399212414140b0040c0740202c16440420340f01b10414080020020650407690050340042c401a501c481604020740184a103000300c5e034040c0b040e03440040501d80c0c800c0780a660011404191502c2a4000c000c0040c3c8034058103d1200d000d100b070780a1810080c14100803a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 336725647 1250 336724397 336724429
    0x30f0c0c0e0406090c080312010504050417030103050d09050f06030a111b070305010e010912051324030e3702060f13050d03210b040c0203070b090a02060702 69
    0x11445840d2540c1007654203090341c0031126241c59504800400040d41d180d88050420400110f00701449901c81c4200d032141031003003501803a9120082801c0c8014104c0b400c04019501d0b41e099941c0d6500d00d0260703503510345200c00800040c1c11000114292500740120202c03034400070021070a50b16613116407402030640e00f0742c07185074807010007120343c2c0c2003a0701032100801c2880c40d002e08411071440c28074500703646014007031400a0340f400f801c40c4001880420101041c0b0b010780f84c107546840c1d0350030b50b0350680003c0b50001018400007020082c0c1c0ba4003010181c00ba407000f1036800f0b12042082c40001e0340d030b8444204902642c0540028882080e2040282c1a40810f5a040c907011106810340c0205525500640b50580890000202c1071088040420031000502d025038044c460101e0340c0e14020403603200084010440052260300c070181b0340c2c003904004c2c40c1d880024010040710740c801c20041c0d920b81c0840400c0b00e25248920001340b01c6a404100c5501c05500600f00d10301d82450317039007040321082401d8405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 336726897 1250 336725647 336725663
    0x1090303080603250602120c1905150a0903020d03050c3a06030b13050c09070302070614091b060a0c0507080109082812050711060c190c030f0c 63
    0x480840b00c00c0ea12420a13030000e401d03103002c50905158000f07007000320f1130005508124040007500c1c1c2d481c000003001c4c18150722503100701e00702141c903150082c1840750041c0021510400641404081e641d280d004004c0944250215402c87c406c41c682501580c1d02200d440085800074069450740d09003a01020f0b0700e5400c82180ba18000403d0341c1c201400c80b0b850000012403603524102030081000354070b081c6401c40804090105c1740c1005641380c0d9559080305221a0107600340c14003042c003060003038056580e090751100d0140101030802c110503407506400c545001c220310a92000b41c2d1820704019038207103922400f806075458444101415581d07a0a40103084801388905040010340c008203102d0a40c009114000c42d03981c1d621001c0452813800008511008a442c0301610001c805403c4812010400c501180200f5541c2ea07003c41075914840046002d01c0c1800b65104010071512144010440460341c88900c080b003000401007117070340e000c070604004c1c0400d0038401c140e42c9107400b40c4c40e280c0745030388200d101c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 336728147 1250 336726897 336726913
    0xf07050f0a0b12070807110307120c050a21111e0f030a111203070c0b04050102040b04121203060602070b0c120403050c040606081005062805070c0503030901090303080603 75
    0x207012016400803da091400d0b50040a01003030300d0740208800d401c40c08618008580501d071300140b0351030303100706d074001010012641c00e204c0070b56010300b00610540f070300301c02a68002c0100d4100600a170b2810100d071143d002d01c3c51005c1100c0780c0605001c005204a0000800a13611891040f40341c228441d014099284100c0d40055000001003004003200c2400340c0e80d240701d07400f004413240d2030841ca0100740640041c05104019103954007000301d001c0a074000d81c130744041e41c41d141885402849a031b00708501c400750004021401c50741d0450400f003160302c41c030313506035900107210313002c4044441c2400f40e0801070300500030070405203480c1000340022084000c240d813982d4000c030401e941150710560044910b600100744510032850144038a00041c862410000124900401541402c0d14031f405846e1289030041503080306c00c0d0b41c402c0b402d40c1030704248285c0c0302400e0340c1d1900a412178118130421140341c2d8401401081c9400c0120681d80b00742c0b01a115000205c5c21581c2c00c0d12998030060180ba014031a900c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 336729397 1250 336728147 336728159
    0x20a1106061516020d050d021608150f15100c150908040e0a021312020103150620030706020307050408060702012a030b0a030b0109060b0301080703110303040b0c0615030f07050f0a 79
    0x2203411f107040b83d40007080000040302c50b54841010755482030496030403421800c9020b542283c03a1580c02007284070140e0281e80c072840411071000c0240c2240c0e802509032610b4070768654001c42e260080901901d0740c0488105050000402d4400d0260000c00306901400104602440d410065030001141030000d820914400e44c244402c401c00da102010042c01128100c055503014454404000c07419130b0205030030350900350050a105c000190106950b80c001407282a111010301c240e4007210391000066540e428110340050154005009040e914011140450139490051180c200c0080c80010200c01026468040c4082c0b0001c00714000b0900d5101d0703440600c245d581c0622207002e18424035140c20740e0350502d04510308840f1150001e0320700d0001000140901000001d0900440398011903629054140d040400e04502540e400340780c09a03c085284080740c440852014451100300703142e140d0213202c5004140e51402c2401c0107800c9500000c03011f2080742414602c0e2641c62501600c0030303c903243d6540e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 336730647 1250 336729397 336729403
    0x3081c020703020c0906030303100b030a1508010b030d02030a0903030509060405030118060b0109080303241201090201020615010804120302040810291008100504020a1106061516020d05 81
    0x1c03004400581240442c21014603000813559007010301a001903043d4900421850003040b26809201c0c0141c00c0440091b400452980003811300b242044403002d011541c803803d5a004e402c5241880c4c1c80f0713002d80300c14003540600c0041641c0700414107648916880d4590388040d125a880064000e401200800002c110344e00d09001d01584006012001701c0d9100060070708100315a01e115900d410000444810002040000140c84d0002010004107201c0c007400000324000300c03000307030030701d034005026401302186c1d0001984103254282c001c0e000d42c0c020360b46000114520803d403072240d6001c23a4030b50012034089035032a052842e80844604005150079151015207141001030b0b0740c100083e80d00c03034102c1d0400c0310a4665003106c245a10b1048a10b100082e40010032811100e200c900400c0079aa0000d03581242c03100b54034000701000781c821980c03119103040c014142040388200034610320401010450380d0034020b10044000c14250100e43c2404100440008840d500c0300041e64041c008140d00b9012400074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 336731897 1250 336730647 336730657
    0x7120f14040605030a1b020d08180a0b01080706030506060a11100204171b0d0f030c0c1d180c0103020708090406090605011103030403020d08040311070f0816030c03081c02 75
    0xc3c0c94660304c0317141c0403c0e01c005941c02e46482c0400f030042000400301d80c5030001441b015100c02400c102000d82d90f40c00d891260300c02200703044945c0740715820ba0201440742c045103282c140c1d02114140c52010352980400d5003510800d5034980d41000042080d0084c20344680c0d42030302d0a58106040e5034440901020b0101a81c025820130a203511480c0c030340b1041e45500f088076030300044480503070080e0740501c4000a40000300988024010b0035003400301408051041c030076221065070242c1c4402001c0c0d240c5601070803102d0a601e01030400f030003000100703004c0c5041407410540ca00340c000c01059100150b500440107900300600c229090b00381030042594550700c1d400b4041c0603080c0d40000045882c1f401c80010040001c4500210050f0410418400440d0f40801c4e140902515418640d500e03403100d241c01c4031480c1500024100e617020f40384c80402d64240301410641180d869801b100c418280003101d19005800310300c8000c01d442d0079840100001071742c8401400c079148550280840d08055425000c0170303a03000d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 336733147 1250 336731897 336731909
    0x9050d0302040f0501080603030901030510030b0a0f05150f130f050a020901020d05180d1104050a1a0621070306051e04050c040305060a1d03070614070507120f1404 72
    0xc00c05000300c5541c3c00340900203000910b02100c4a05007107020907100d10a410001d410503072210000390000034150184002564030802c40040f40c40e10071140e0000705020b007141c030045814038000c03402c031100c608000c900c000350051101160140b4401000117003686e0b20312095029807603088810741100030344190b0384203014400001d41d81e41481d100082c10804161300c0c06003400024400c00030090100c2d004032041d4034007612281c01d60401800c0201e400c0508601c5950700500300010010752107a00d81110b2082d070b00d541c050101c0049007104206003030095001065045c4600b003940c0301d0b101c00d900d1816400030300c20b0500060143d2a02d000ca948148010150140c010452000132400c1c20907120316940000ba86044900301821580c80644960014001103481601c030940c0c090f840c1c400c2c03c03140b200a041c201c1265a40c0c0481e02e05031024003143e69403c611019550b00107000e030f90103031040b1800550b04c00c1c0854030f804c240351001d41c0c400501840d040c08100d05184081d0507103002c0801040a890 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 336734397 1250 336733147 336733151
    0x40905030304060507051314060d05240619270e1005010206010614090a0e01080f060603010e0604020d110a24020f0c010e0402190305010509070f0e1309050d03 70
    0x54281001c3e410740c0d001900c20410000100016850170104004907800d6809455107040c0c004414000600309004220854100318580000d10040c40e81c1440d0180c01071700220b00404402105d0320410605020760704c2d542400c54811000810458070904011500c01401d034140100c4200310700c91b082c0c4030a459000140c85100c2d000c1842519440151514000c06092000307009039070620f00000d1039101408892210580040b503544110390311589510068002c011070f201c0d45680d80c6c1c4002c0d589210052a0302c3e11070003040c0200350541810b01512049070034100050a407912981d082c0044090100026501604a80100c0d40196584c0b00038030002d00e03600b104c5c00c40040c0b044810800102c62059054107550000d0303002c1c6504600403a4a49030040c01b406c21201115940004c100130b446141d10398000c00c92146000d241858062340300505990055400c0405503848180c241ca003011040b40d64004201c9500000c4942c0c54801c40c641c084440c0c003000407615200c0f6558540c5043c0c49112074801181d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 336735647 1250 336734397 336734401
    0xd0309020a0806090a020109381207050d0c08040c120201140c03030106030b09060907080606090a09140c040803031b070803150906150301090c1403040f031202090315040c050409050303 81
    0x140c0c2c031625823806050741003920320b00f20207013261075070503803001c4039aa403a17003105d4604c80d101c40054a01a58094419140d00001c43d2401c0340e8000c00365070044030803045035440c0c0382240102520900510b48915071000ca840c030000e081c0f00d0b1400420f002140200d0400983d0340e06802d0361205400039090982d00c0e00000d5880c0d50400c038000d0180ca07003510400c0d00602c01301e010040150b5412000c141c102d0380702c1c00d000581d92184004518284248842d1b1b6401c03044d2908001180d2046500000300110341c40071000c52511192000c905074466885000031550040c0081011210b01c4030101320424001c142c041e242024959602845030001c0701c807001225143c00d0751f00010305085420303e602400071034010f0450000000342e034400c1e00040c0108402e03a556110821001c5018803000d808103420f81800c1c42d04c0386814944100107428081e000c0380020300340c1144441c02c01c0301c0c0c0203a030350803400100540301d9400c40098504007460000d1041e640300300c035100300052036202c1348100880c10f80030f0409560b9078 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 336736897 1250 336735647 336735649
    0x118020f1b0d0c03051215180901050f160f03090212010f05090303071710080106080d2a060b041104260a0209130305070506070903020415080d0309020a0806090a02 72
    0x8014021040c5051041407424103001a038007000703c07100c0c04182d90b05000e030f03070f01c1f00303d002034080301c059040d41c4d0408000054020011039031148244500407081c004e10490351620310240ca80348054030103100b505841845144800d01550061551915514000502041d0b64000400e007460310000265165035400e504d201c07a4002e8013881d40d01c000da18009600d1410325940c028102002c1020070f0300d071402c0c1f020110f100b0382a04000c0100401404009000490721100c0250b180d101c8041c28002190f18a4807030207026481081661401921718240d40008405803143c07005000520300c01c070350150f5901503c10040a560025002400403200c6600c44009060b0884282e04442981141ca40d80b202c0d00d090010b076140355000d45e00540d490310784001144540f6081c6d03454002d0140042c5640a00000c2000d107907800942e14089038000c403014411034441140d04141000d441c001c00d01d01750002d4a0304000d080c065044020100c0c8060b200c440ba0360703a14003065040c4082035502d181150064160754080d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 336738147 1250 336736897 336736903
    0x703020d020c0112020f04080a030201050906070905010f0f0509030106030602040f05060f0318030f210604090c170c0301090503030a0e071503091a1302010906020f060118020f1b 78
    0x20381034050006086280c000c0d8000b03400d00040c483c2d40c0340071030f4001900c0f041e502c04000039130300100341e0203085680603011860b01034064002142d040d03485128000004424900c03030340451044500613103410074913486076641100d01c3c8806000610511804100402e4a610f09200c0e10000394050100143c0341ea0420f2403800035941a5400a4811001400b15010105819041303d41005030310b000d0581c1d810394404440d080d80a030300c1600b01c045001007070100501003000b0001c0240085a030307803d5600d07500c401c20001101e03c0444c024104416030001070041c111981c004481f4a0b042d04200c444030300060001030b003502c02401044840c0c2c4c0001c414070100186900070100c0c0040c0010103400042e00f0072500c109840f1060f90140d040640b15440002840000302e6054103501000f0700d140d0329850000c032080b5500c0c050b02400c900190307907041d00160b464404110010242c20310b5025125603480e01c2c001d85100f48807141d40201d100e6003000450212000340c130082c4900c40344501c09603010700041c0c0e00141 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 336739397 1250 336738147 336738163
    0x30c03020c10142b061401050315040b150d0e0601050a0303021009022202070201020f012702130510030c0e190914030a0e0a1d0f0405030915070302 65
    0x4002c0d1440a886002c140d00f01d0208405001e12440d025116411030b400211403280c81c0d0a846040c08540c81080d0141005410400c2078898002c20040c40ca0201c40044910748000c49400001310f00455081c1c000b441d05411840d480308000b0150400009501050b2003503502c40040031203034656a90030f04402c0358082c00224010324044601c101c1d00c074503584001c1d440c0c40c102c03080f2041c0903a481351044110b58070303002803d04c40d030605008078180c10b03000e0320f50a009600124003607015128601849541c01c4050185072403851000c841e41c0c0f80040d0780481034101001908089034000240c0e00e0141c0755609921a1500c104203980355446041e00c0c1d402e009081952a80050b2000020142084a110358a5483c503040e4004120000358100032824942503000c058103000b0f8103400005a28800541c1c00303110681600807c0320041403555807440c0300800a5a4040094000ca00940010310b04580c12801564024003c0d01642d01d000f900d94000f40000c8544c6810a085070400301d404d005142d41004880 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 336740647 1250 336739397 336739399
    0x2409140c031e03071e06020708030603061b0405060901260115050a091505070c0b0d111608070302150405030304060c0201050708010b130e0c07260a0305070318030c03020c 75
    0x1c1c0b0412542c8865901c80c4100e41020741108400050642c0000c215800368040703c1c1c200c02d04649404651601151940c801c2d58030f20321900c1a40c001c80d0b07400760301c240c5443c0c0ea01d4214200924043c81e1800748400c60b080190720a041c00713420420701d03201c00080003102548180c3c0010b203070510343c1082105861040f02e01c52101c2008414051114181e800031000f5054581641d28640c000d13640c2d00d0112100d120b030150040500301c001c0c000250710741c01c617800713480c1441c81d0f01c3c5d003480720300c40807228041b503030040d0040300440264003050840400d40800041c82440d00910503518800e41140d949480e021f0103880483d030360b0344004208018081d80e8170500c16240d201d84020711450901d848003d000302010b019030145928000340c3c151300c6a091980d018014406c0360700d080700c0c41c80c1000340d0490b6500100419100d40f0888520001c0119031900d6080550480302501d074105480940f00300d004000c020446014180d0b2202741d00503503451500c0d030312106d520a644205160340c15140c020f052031219500b031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 336741897 1250 336740647 336740683
    0xa09020312070804050904150f15050d050a20030a05030a1e1d041d030306120c0616060204180905010b03062a2505010e07032409140c03 60
    0xc400014600804c0b02c2c11114111a10305c550b443d135051042d40900110440310340245003100c50132050580e50081c90b0031503040380341c8010444e529024400407443c8880001c251390062000c600c0026641c0942045818000c0201803c0c61200350110340f40c1481d4280503030b810360021a2045209501048915444150525400014080c910050403072701039110b00c0c81050203851030a200039102c5134824503c4804002a4900c000d806604803034803a4829618640544140e149100c40598002000400c150000d4401440c8c41004c1c00b6054812480c01c00403182175400b0440010300e401c8c201000d040b0a40090390029075100d5514056007103d0050300c0840c000c3c0c03c00303070400050300e54802c0041104440412441d60003004206200903500c1420b00c0000c890442142d506170780c0b002000c00d049081c0c4103000030080700c5c400600c030550700c500b940320003042c10b05444582e40c001904000305a5881402400100e132034020743c1d68115101e40340b102d429100e0303488042e196616243c1000039140020300020f80c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 336743147 1250 336741897 336741907
    0xc04050303070c4e05160315061d0702070f0902090424050103020a02030c0607110d080f0402010f0c05060708060301060b0c030706020a11030c03070b0a020a1707030902090a09020312 80
    0x441c070a4201e213401c8108560403d100904400701c0c80300350030301655000702501e103100207100300d202d500d4246001c103545400c0f1820009410414511852003690345032090301940c24001190404100030003840d26046028a010000d001c000111510000d0720301050050b845512441c2444221507105903002080d980c80c440c100c502031b00031050081a10003c1c0f90240c0d840450003002d0789903100da003a070389074a480303a034080001455000700d900c05201c8c2000305440c0140c900b000704407200c10040e034039554155895404a801580101c408562140715801c00d0b0307a00066985580e0300f072000441c1c0302c2020076506e0041085514080c0f141101504004608500704401d00000555901682030000c06003540000c10210550180b50790100f91000002201d54403426450361503221b81100c03204403900c89091022442d420700324026145160803660320904031150340c3e001c0c4c0440324005050342c014036954107405009600c5004489100302040b01e0702290031012481410b00e41408980700004c50707901400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 336744397 1250 336743147 336743219
    0x14160311131a010302090409080c010f0b0d17030a0f050f010312020d0e04090507170c13050105010206070f0e03030a020106051005071e0201090b031303020d0206010b040306050c04050303070c 84
    0x1ca0b1a40040038600140c40301403803808140102050300f0007604005000c20814624041504405a012001a0300780710103a020814045c80440028004006484d480d02891452000c000519070109803c5408215443c02e12680d4040364815103295040d00d82c4580107109001503000c1d1003d1003465840200b0b0701d240440c000810a40707030704190602c00d84e16440b4901c1800001c03ca104003900b6400102c1320701c0c8440d082c280366104014050240111003200142c04446001d103d0241201e03070680141c0303c0c503591901d08031008680021741200703200b901d003c1681d80341c5080014200c100c046400005031181000100100c00100d041d190017004000c0240301e00003402c4035841c0350060410300d44000107000520042e5420103694206002d891004000c000c0000c00840d4520b64840c002c0d009c1e141152a1914100d0725600c00f401204440d2100700b10800c005016a071049520040d41003402e03040581f11fa0010b815640203ca00b42d403004840d0405000441c001c00725050049030313000c90910609030001d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 336745647 1250 336744397 336744431
    0x120f0f0f020318040e03031f050405070e100216140108010b09010507080c0114040b060906010804020913050a0c0b04031a06130b0303070609081b01181416031113 71
    0x140c03100041d02c0f01e00b400c403283c41e26008640c80c049402d0969440340307407402503c15024015480004085450900028641800c0c400c40340902d034159034041d15040c1d0881400031011540050500f1442039490001c80100104034820140c500344800400b44070811000400082041e000425002400c0102608581e0001c5c211522103a1110300c0c60384411805183c0e03030041c110752011010100d802c104000c200070601f80448d00c40c00d002c54240e407941d21800e00444481703204a030005d411140d020080380052102c48100d00300103106004460500007990b5880304651a0b0b544019402d0b20041802d02c100b100c1100400002081c0c86811040343c070b4120001155903030b124031041219680c5a12124043d00c1c01c1c003c6802c40d90b0404c4c414000180e003854801b6243e4807900007480c0900b072000000000c0d40040c012400c0a40181102050700242511051000d11900e08001c4981c443c0550100280c42d001200500035070042200100c00d4124005110501d8002d0402440880c0741201005940c1d01c62 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 336746897 1250 336745647 336745657
    0xc0a1d0307030f1b09050403200619060f0e0402030613050a030f1b1104050106030606141308060a140c070b1603180803091204150516120f0f0f0203 65
    0x100d00d80001c043c03014240380e41c0e01d20704002124000481341e100800c1410b000d40286004d14480d0365a880c1c440722505a00d01c80304140c009001040d00144c011070600d15541558540020030310304002511981c03500042801d03c100d512071581840100e08000541c5000e114156000b1400103144440c82c2580e50340c0380d01d405110400074240721116602503a101d103c0c42d41c09000070f080c0215610808104e0401040004101382602d210b14140300c00440c2c01c0d84640030f40b00032229030352251802c85c40c221414800a8010b1828650708824016000505420400055009103025200002c180da1040e001a0012000800c100d034041010411600040c40b5003159583c070044d0003480550342442c4080031006810458000d0b6049682400c9890a01010b04011401040340c3c900702c400c10031081140b444140120f01c03c01c420300669044600c0594090f200402c0035501040182600d500e459a03880b001c02c1c507081c00c8000241c046001c0b204510340048611480c20344038205030605021142009680384a8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 336748147 1250 336746897 336746903
    0x22a0d120c050909010303110105090d020c150d09030518040b1008090106080d2a020619050d020711031009080301090b030307060f0c02060106050406020c1c02090c0a1d030703 77
    0x912a50a41001d101d1003d40c0c2c0106002007465a4550b96402d0042c900080d00135508032552914010400300080042d00b0398200b0b005402408190001104010a182900c120548640c40403c41110505803910403c60280e1290b00e4250f2240103030b148440540ca204505540114900101d4003801d580f5a00706039490071041ca444000c50303450303c1041d070140080b81e21249161042d00160203c05402620842c0c100228000d41c030040d4409450000e54646103441c06500702d04208a10f001c00900e04071050300020041c00c0281c54040101907050407a440b0030b005880088983c000d001586c80c09005180c41041c00f00418001c05800d522650740c907110601c034060046d642d9910a20036500c041c02a18440740c4c100030200210382221098402801d00301c034444006002d02e0001003102030081040e01c044c0c81441d8014804624200103110285400b03003c40802071118200e41001a40c8452189110381e40351110304e519603640110181c9000304200302d00100b443c4611854005841c000f5200c8100c03a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 336749397 1250 336748147 336748151
    0x203060d020d080c2a0103180b1b0406030c030507030519050601033201150507030806010306091e0c05071e0201030b1c0c0f03081c020904022a0d12 65
    0x1068a4011104c0c4038000c40749102e80035011100c3c2c03620188840031070f40004106406044215807000440454072401e566217944c1c45030b038881c0d10125120150040e8420f0424038400b1300c11901d0208520300c0e0b00107a020800080e1114903010781d19605008240d00f1208608081c0725600302215640c02120107801110b80c91595080050381c980e10036009050b0811700d0404003400c4144560210300000780d004203410305e030850407000181d070280f0046084019a0a595600d0901450b61340c22950003030098101e504054a80a01003900703400d6200f01680e80c40044d074166555550300420100f580c0800004105000060104101103200790082c1d07900d05031a0710074075290b0841440180d00504002e940207800030080c8588142003460109124075040c094010006020b5551684505042d040d00004029643c113000b048125107914051031802c404294015082c07500c000d000c2002c07600a45801e600917030f2088440f20f03042c013480e0704444074106440050070301e415000d00003412800c6400c3c1003243c265 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 336750647 1250 336749397 336749419
    0xb010f1401020d1d0402040e09060105010807050d050424050414010203011412011d06010305010e0d301a120102130317040806160810140d05071a0703020d02010203060d02 75
    0x2c20360341300f42200f500820854545482c0e20504203004801c4a949125109490001c20990f01175200c1910a250556855160506032018540604000340c000c4038601c401082803810b406003240d045440000305080011645882c2c1008180c031800404480d100c0e910410040c0b041c00340300224892103035819035402060b08100c012840c0188610380a050780e044101e5a01a030504000c607405040342c0c002c80090010440818940741c03102002c1c0350020205039100d003000407240c52140d8008400303031a010144d20701c84e0181100c80c1078070078210440f2031400603040c0c144d10b00d10b001e20513080380741c0000000314204a0005100c00c003429941c040613205201c110151030500c0600000c59000d09200015a000b81c10903500d0302c1031000d400c9a80c00f0100790400001540c0180c000c025104031900503586c16058207802c405e10144410070001500c9038004c0e420082a0000d0038006181d10181d035036031b519541d417641c0c10000e040440b01c3d1404405c59004100344a91941c50002c8028002d4045615401c51 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 336751897 1250 336750647 336750677
    0xc0a0b1e1911040513090327090c0c120503060117040c0603020f1303030807260a020f071a011401020703170a1704030e210304030f08090306040b010f1401020d 70
    0xb40c0110750099038041181d1201c10010107040c0c001208492094a622420115440800b803103003a00c18140c00c0005c0e01401c0070041e40f1580e801c8030480f0400c909190b40c4682c696203540740021078400402010079400001c2c030a280d60705c82e80010581e20000c180c508282455940c2c422b142c0d1040c07081d031003055004141c1c00400030b000002c45262080304440311900c6a075920380070345864022521440031a020a001240329044c00301100705465807034804002d05d554401007034000390080060030359403803420b01c0306400058045941561506000b14602d99940c9405041c0b00045420b00c9aa41150807070001040000c00280c2e440307030551201c207030650700c035040b000080340d8a1350a203003241c0702003075150148030900d60800510005940c095420016940c1da09440c0b03626200c2a2160700107130fa10801040021510003645d43e00303180c0c800c030300d0785290081c8900003038946075040d039007500c48070a48030041010300040540180200000802d840003680b2480001c2c0d01c54110301c58071400c1c84803040c071103694 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 336753147 1250 336751897 336751931
    0x30a020915090403030c090f03020f0907030617011506020c060a2706031b0203130501120213171c0c03050c0f070906090e0606030601050d06020c0a0b1e19 68
    0x20304407000e0300a000303500c3d00f0f0400030046c2c83c81c9403505003c06c440c1000030900c01c6885a0200590341c015100905005c10441070000700480141640105580c554001c0b64640540207011070320826400017090460b280d03e007010790010242e014030290340c04084584699144c4030250b0341c0c890307100c0c209590640c1c0341401c0c0c421411303890410883c09224420001c0f4210744c041c0c1c8040052581407400b00b844800d1a481641c3d24030034a0380d5a12503060307414007040258443d00030810041480711002d42858400204480c0c000a1501308025100e910180c07045a03450402880d00d020100c0280d07a0315580d180d00002d044a05001d00180410400040000d00000104400300c2820030300c1003218800c0d543c4140d6a00107000500030a07512034104800008654400181035001c0e80c8010040d02c41da034602000c2000140d20307000d003210101e800380305800d900308040c00300c600703100c1c00f640444143d40381c07250f14040701d42000d10f00000c2c1582d0600a01c80c1d040341070002e4400e04144130000085071000c4155080d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 336754397 1250 336753147 336753181
    0xa090f02150708032706010b040b090102010b12010516051c050a0b0a17150f0a020703090803040308040e0109021908091e07050a08060f04061a0315041b05030a0209 72
    0xb0030324000140013000b078110011704410001d05001c07040b014504040942c0340d980030300c0713004000c48d0140418007600d00c02400030100017205000000d048041c1e0404943c81141d00041641030b42d54610070060080e820203002c001c07030780451501c24604004181c0c0b004006181502c400406692000042c0344034240346d002400420004003403011856842020b68940d000704101072802e07014103002d400e489020b00701014002c007185046460030750780d180c850200a4110300c0d01542004200c040000304100c0c140000e101860145103490780d2030b030800f21003400c4203806a0201d01e186104011004030080c40d1003c2c91a6000c00d4600709001e9150003103054680a1b1a005e00e030b400b03c01040e1f8004d0340e924005002c0c41140c4e0190783d03109007240c1e20b10380c8a0b111002102d240043c0b0b07070907400060001f00c855000c602d035442c400341003080b0900102c0c0070910f0000c50190100c000321642d801d001c28000044030385100c0361200300e0071055281c101008680ca40086000082c041e40007d00801d2041140c00c0d4a60 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 336755647 1250 336754397 336754403
    0xb070c02090405010c260f040203071502030309011506020c100e030d120c05041d0a09061a01020f03040b0a14070503070503120a0903092c01090b04050a090f021507 72
    0xa401400c160034190300800208034a0303800f00b2a048600010400214002d946d10582c03a400c043c103590f94400504040c2d5002442244c1c140550040410320060084010b40109080c4d0300844e01d80c50124442070864451003c920310a0119010400890b82c0c009403280c0f540205032220540604051425954103903e030141c0c3ea8540030f880054038041c5d030700100041565150b141d0a102c4103a50038000c5d1100e03c11402503071106952044021802004942c402d500300c45090b01c0056210310a4a4240440d4011407100768440c81603445041e040d81d040200c00b0171100d4542c084c624107442c1070020111445030340038245c10f00c4002ca036000b5110200400359208960040d040e240c1d030302501d142c0543c50768400d0b80b1212520303007040c02082e45001144103000f60540c1c140c641c03845042c10001c0219040040380c481c104624494400110900440c221641c002c0105000203d01e00107082c040105444c40202100007452170b04020101017911045513600c03282d01503c8d698441ca404104031215440741032130103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 336756897 1250 336755647 336755659
    0x70e01082a0f1512010f030b041217040f050c18070e13020a0903140304060504090b0409051b041103060616020621042102100b0a0807090603111c0b070c02 68
    0x76080d03202450020b2000c2000401d18588176038a40210794400710041c007000e404442410009800162140c0003081090070a0801c030042502d5070114003188402140e0441e13451030341c5900b00c01002004c02030b0080d045811100c18038008090602e104e41e24100a0003030003003011204a0364990303220b00b10514800c2141c0c1c002075584410946020305a06070921003111068000c120302c1c80b200340c3c0401654161a003945e02c940c070306071402481c40702929510200302d034810f5a0316131711400100300700030183c4010f0000d2004080c0c0720b401c9080004135400300c13040c000003030810001c00645943d078000b258032003440d0010003c8000141d0001c940607009185a00107a4440a9841801c90051908180c8a288034144400b41801660040155000c02035584405640004c10a20f9101525041550080005005080c046548140d902e1400c074090b40204080790342e5000034402d21031003041d440301d94031060f00c845c5180c650031a001c882808182e41c001d014117000202244078184107401c201c0309a43c0050030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 336758147 1250 336756897 336756919
    0x141810090e07080c060f1818041112010603020a1e0305070603020304050c01030621140d0e04060501090b1b01020f0414010908011e090602040314070e01082a0f 70
    0x20700e594020314001d4500c0ca2007458103041540c41e1070b008503814443c108a050b41041a205d5181d0440020540210b85c03020f075288100758801522000b01d8070032401140552a518608030900800706150590700c103503070341041011b00141e101c200214040f58041000c110840c0c042c854180810b0407540c000030328601400c2c1d0001000f0368550080c500640c00358090712500b68154005404951082c440d2001000700c120310301710403000710902841c4103801011520890295015094140030404480801003400300c2080d0720541043c1c8200c4020701400e00346101c0d60790800b11854a64054a060198107c00420360300076008800c0d0150303015001c3c1094641c1d00c0d65100d0807900040380e407440100c1c1c00240c00c40700c0064840c10500401c03c01107010468460002c2c1521141005004180e0042d00c07526000c100000008080024401c2600141005040301d5414a01101108071060b0700c0040d00342d0149140302d00c11000306000c082c2d1042450300088800312440081540c0d002c84144243d40b010b0a491 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 336759397 1250 336758147 336758171
    0x1203081915060206070203040e0f06030109021210050906010302090f0a06050406030305090117070815120a0f0b0a0b060a030b0f09040605070e0102011803230d090c14181009 76
    0x72614160b482e10b03003d8a0656450240407640c0b401140303c0e1000b44400c081c0400c0c071074041e0084054020034054004510b04116801258040e926800c42043c00d0f40090128070010300035100c2c0c40d0704008118007400d004e500d10380000d05135410140c40c01080400b084089250303665150302000090801400600c81d80369241006011078203d02c94140c0400c900c902e00704407001c803491240c1d104408984580d1700c0380c1c841d00304001d00c00890740312960b0059209100c00300340c9101040901452803003000c061001c1206850074030218040913050400e1241001c480c002160b0300c078000c1e8ac0a0300018074001030b8082918000440c2840e509e915076030840007081c00c2c08140841504024400c400d243c4030785902010780d4004900300c446c400c5500003d12080b244032000a8030803101910500a10f1107001c81110460960451070751091403000c4249070340308050401c1180e1014004c0040c000c00d603200c05800501d50100b001b07204100b000ba00b041034541c2c00a001e210402c09104041c10468808210440c0091 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 336760647 1250 336759397 336759431
    0x60c1716080a050708041101050c01061712040303022a0d06050a18050c210f0d090f180504050106080f0115080c0102100218060706050406110412030819 67
    0x5215200011040e01c000790b601c0c40203004980c050145661102d40a40c0d4544501d0441c1541607440c2c0d041180c10880301c2c00c90320090103000041c2100300704143c005000054400e15140440e00301c000707024401c0c482000404e8010841c018002200058416401e14000141d0525555464020341c0f02c03900100310010700c40d0750341c07260344500340c0302ca0b0402551030002c07402c0da034505500c0c200810030b43c0000b007012030500304038200c0a030769085a8484039100c6896580c2902300541c6000c581900d6001403410045550b000301c10b00c00602100350816081410451080c281000c2001d5800d146512030011a0800c58250710580c01800030700c4c2554142682d0b1001503010708650a00c3c0c0c1c03000c82003181c010407407480104d80c108019030140c0041c940c000c14107801c41c01035003003000c80d2000c84861040408094503030704010034409200e201c00290524041c5000d00440e901d400b4501e1031490280030a100c8041c03911490017800344c2500700542256554100c055410b12a1403011450720700385140100c440c1641 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 336761897 1250 336760647 336760681
    0xc20070909030203120609060d030309060e1203090709150302120c1e13110a110109050307120f080103081c181b1d220b01063207060c17 60
    0x31170070903010b8940e00e00f0446240c0c41901c000d5400600e4204400003e40039602003100b2901c06c1c14045585541c5500e41414000010300141075a4400020014a00e07014800c0202800d01804100001006085198103000c1ea0740002130240c2d010130a400382c2040c0401884001500081140307004089140040200403520745069000301101000d412500045014441c0c2c0403c0c2d141c90b0b82d0500032407100c1160100e028040c90111035590b40310100c0800c20a00040948a010341c0c141e203040f10610345d0062a961003050080c040194180040c40080c411508075920119024400800504900c000400410000040d4101c90114501441c2001000d18100707002c3c0c1d0710206000c80580d0740c1d95035411180c001054103c03a40f120840041c0d4003910300c00300311812403a202d0700c2443d00340f150307904c1482c2014280c1002000c07560075a082645100c440b00300b2800d0110a5804100c2545101940310040c0107103a8000e0500d40c41c0d880e072202c241d11801001c00c02141c032040e003008600f000c2070003501c0124a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 336763147 1250 336761897 336761917
    0xd0804170c1c090603060b03061003090c0801020a0503040209130320030d060f140603040c030219090c0201060e070f12050711120403030f0e030c120c0402070b06030d030c20070909030203 82
    0x70b1060010700311a904041c0c9204001c040c004840cae0b540d46a200724010409101c0c2220a0422501c0104545d64244082c150314015500c503140e8030705041c0104003446000400d10174a2840740c001c0b640c0003d41c4003038200b441c022820364051018144540b00b9045000303108032801064900800020007c0b81c9001d81002c40e4940c8140e1105244072800f401220321003140c01924415400e01c3c01c0005051960f040d0444403c0c600f411020691902091426243c1140f05500182c1d10342d0404d0264105856600d070300815a401e041d00703481c480d01405003045a420b0407165220f0344d100001035160340031b070408461540c2c2c0e0b401518004c03150a00b0039000c0303800c5400142c0000c0d8194070000c03481070103000d0f40064000c0080090121a05280c02c11003000a40c40b001a024041c0c0b89041c0259226400503145881c49142c041243e07160042c1031602d001621a1800101418204200321590f0030402c0f0075103044600d0242003540f0104c01e20203180034000d41c00035001e1b074604000e110038076501201602915107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 336764397 1250 336763147 336763151
    0xa09150e0d1416052b15140a0b150301081e0109050d11010b010f171512010903031a10110c0d081c1521080a0f020d0804170c1c090603 59
    0x4408a4282c800317403200048100d40080c1280010701141e90510500007500c410400840c241e0145c060300041c1348019071380000e1142d103518001c0140e15040e240118102e110503680d0341158074040c0c81c02d6640c0060951404100038000000c1c0c0c0700341080d00940e0300d068221003280d00341c0c40c090b80010701c6d0050003215449554602286189158840e21319001c0f5031089940f10101504820f07205040298083e00b13460303000c12491342205560304c913074000c12103a10400c0000107665043e810f0250a8451004000803540001510b9044d1b035680c0800c4030010540e50b2030014000c0e20300780045440d0508003500f16a02200c0c001e600b104218103440280107400010705081e140e6001c2c01030103000c0c0c40c0c0c114618070f044070440c0360504c08499aa99000ba04000b1500e02238034085240e00c441c20b41358040420385000502c41c9611001d100c0d01041329800002c0035140845103441c240c2c440780b025800900c00e00c200c40800051b1740d080c07241c04100742804085250820b4010514100015002d98154401d280120b8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 336765647 1250 336764397 336764419
    0x207030519090f0302040e10060303031b0c1a19050a0501050406060507050703150b150904060608040803040f02010e0619080106030608030f070303020f040303050a09150e0d141605 79
    0x3030700ca9142c4004480140042000349400c41c3e0800000d440906243d903658800c000da00c40400c3c08078000c0800075400b9032000035040181e046070000d420700d05500313001401a04031070200050103610384807001810642e0400e800352182c0c0e445060311072508045c841d84e54201070038441280241e502c058101c0e02d040300e0801449030740e044260340724003031941c019055410402d001c002055150380f9514200407146400129800850001280c40350381008a0441540c0407800e07520350f0900e44507800c007412490070722003c07a103815590b180303d034840140700801e003c1912015008590007802c1ca80d2030098018107054840003005081480c41c80e81c011020002580c6d5400080d04034000d1281e1000e568848015501c1c01c40300814003012075000140032400c0540c04c104901d003922004003d40059840380d514036585412000c40107190003955003025248001d0b103030455040e50340103401c100c85010242c4d2002c400440c45c0c00c02d4122151011100c0c8218050412031104400003042208140c9400b00c656151388 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 336766897 1250 336765647 336765697
    0x302030a0c1809050618120409020d0b040501030c0314010216150524011d1020190b0613020c031b01061d04050304180209010e0f1318020402070305 65
    0x95040c8100c0139140d50445000303c0d01003c08100640d100400340e400b110800740002c0c5105489030f01c26440030440703680c0415121800c940d28090080f51860482c1c040c4125411a1103082c1c000c0080e1000821407840c00c42041610300c004c0d0180c0c0c03402a22030030800307000292414407088054440c404046010715120002d000e41503140080c0500c1c4450111284500c3da0400041d628155a1010020b14041b6218045101d64422410641c3c82c1c84030340c2e40780026151803500c001803a081c140908040d4002a000088141240c1b11402009800211003029070300c0b00c02c08134070b040c0301b6541e5412601c1e0002074070040206000000f0706501920040400805000050719822070f0210300540403145024107501c03a080c1180782c1c120b40c001e802603003581d2a1564a401000801c40603d4441801e2a004100c4240c250703000316041000034800c1da590702c5207100e000006a04004182c2d4040c8800741e6a002440404007240b2600308a280d0244c0110350340c140c60f050241181d0840c10b95045c0480b902c0007a9160 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 336768147 1250 336766897 336766901
    0x240102070e060d03030b0405040c06080f04031403060d0c0b0301050a170304050609030f010c030603120f02100c0903081206040b0a0810050601030e16080d0e0307030f0602040302030a0c18 82
    0x4881480881c01542d4075010308200040e81024000c0e010107865941c040519950f0784541805588505080c0808518000010b0710843c802802e01000c105035030100400b2035000344000007401001c01c4080c2c0d40f0742ea0140012071450181d400900b252103603040200d1070030b26280045040e540e081380c44d5900290340b003039003d240700000d6940032400d0f0000d0104100909142c0d0180004038030050036940f01c040440141400c6602c04035a542c0041e8131050200b040c02155803400101003190700e080700c410400d55002a503a041002c680781c444655441602410034407503103030040959400151701c0ea60b81101c401c6030030000710a40d001440f41345415003d564600c0c140d0040022543d401c0302a000803802180380500421005081070305158480d80c1101d203010040c00003c070403465003048040e940341060812403401d80c0e10300840062043e1650056841e6400051400441e80d21241c800c1c1030140c1850510081e020340ea00c002d4162144200741420040a003080c039041d00c00d100360f0603103100d8201001d002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 336769397 1250 336768147 336768149
    0x9080f03040f05130902060c01090b0106030b01020607230f1321030c030e120f0c0f01020a0b0901110301240801030f0206030603070305060c0c100504051c1724010207 73
    0x40302900c448000c200e1401c0c41801304580300400d40001505001c0c0350003046907540041a280310b240d40da4412002080840740d11075014048a10303013080010f0903240080c0d0307180b00c0a400d5005114030300c42c28000403e034054169806507280000c45485140c56125001c113900040d8003c041d440d917134070000c170314072105440d180c041101e000851400244241c60540b003108100100380c1c108000758082054a86941048040a46107540107002110811010034145104a01a05e02c9662580f495a0300c41c2c1e800114500303000c2c2c01440403101c0f0703260180320358014440540302c021180c401000000c0c101640c481014086a940d80380c61403181c02d0450200c2c2c210209000c01011100d02e0010f107805410f101000c1e43c0c0c050310180481f8551926a01c072903141c0002180c184032403d0f0005800c0310069070600250284d5200507130103100038100f9548151704c603a03000c100f92030349841c40341383c1c880b03041d11802d041000707008141180c803030505000351500c180c3c86008950510604c03003030b98416950751000030a00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 336770647 1250 336769397 336769409
    0x20c060f031b0c070f0603051e06210a0f0203070902030910020a0e0d0c140d0c050402160b04030206040204050f0f0103030e01030204050312070c0807061d180709080f0304 75
    0x6461951030400034000d900c802c0d20305046080003445540c01c0e0400070450355000e0710800c40c044411034a40a4002c056481c0144002c0c3d030504025002185514071a290030341084040b2802c64071121605110f2000f480e1041001a441c400e032a162414000c0d0a020584114000d600ba100780a807200310344800c3c0e10003070341c542019911000000d100e202c0154082e09010580e440c041001304400e10008641c0254a0001c3c1c55011400408000d41040c0c0c44405605d42010707103000003210401c0c2c45400c000030b401d03c1880d00503170b00094400d900c070010481c001c8810361301000b50007403400c060400039901e460440d400c9015038984004164601c01d50404184074845a81605031076a0940e038085416035140780b5003d0516800f8007022038240e0341484401400001c507155a0344072403080c1031882c0d180d141c680c00704046400c4401c052202c2c1364000003a0000d11a50182220b14200c100d0200c1d01c03d444a103483d0b100d074000d01d010f104556902c109410700b11030300e01d801c03030b1009104413802075200d2241c1c1c4204 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 336771897 1250 336770647 336770677
    0x20d0203030403080f04020d0b0a0b040f150909140609150f0103050a140106090218150f030a110904020a02030d0b04051005010c0507051519023f0d020703020c06 71
    0x45c1c00120b030008500d0b40a03101400d4804d03020382e01d0b0313600004c0710f00c1914075034900c1c0d0701c50011075103506052182c2c03089240f1464050103240220201c1801e605c0c02802a4280305440d01e613000180010800545070440420b800c40d503081c606036002988810f010307413142c0540c1c4848404101196030000c800e034107890304400504040082992007070040000d00b44041205c1d500d030440021004a03a2002e031141149011000c2c645400b100200b00b00d0068000f1071a025843c00e006001d107a88240098940c41094180f000901c0407003000075483e14000c0160342c0ba402400003c219a101d03a0101c06080403114649003071004072502c40410007503c070100d40207880409180b408000b00d44c496500d00304428014010b07603041c03d8450002c116001c068400009200c3d100040d042d04c480350100781c0d1600040d851010300a024801d007414020f01103190100100000c1150034200e0f00046401401c028103409042c165030380e500580c00c10041c0d0000d200c00c6d0054080c0320074124013410801d040317400000b116002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 336773147 1250 336771897 336771901
    0xe0f250b1c0218032410080705010c0c0b0423040606080703020a0309061109100912020d11030d030f111903021b0a05061909231002040b0a020d020303040308 69
    0x70344000c1d0021000e07840d043e540300102c410252018440700300c10310100e1500c03041c0743c0d13406000d034003200101500c4070303c00940811042103440e40c04108101034a0b002d10740b8110340151410301003000802c84d0005030881c2d07070001d000662034030b00c0d50140115035441091120788200b102d0410040319207a01c26032021905841c0040d01c054440d50060140c15901e0a00040c41a84d030384400048480542400e5403003600061a800c1c603203000f070700c90741c2812114034000245500301010000c0110440c0c070028040c0e075201d8081c10401031490f4410745550005000c83c2e00a000100008000e0207504030b41769215850401070200c019601000c8500e20520030039130300d40d1254064000c030000c2d4841c00c4d8840c00c0f2048000c80501e19070007400800c0b04980103500414180c2000c0b00c1c03011410380328007640080d20349800140300014002202c1040183c0c1c03000000e0b8a035a840a02d10790a0194012030085d060b03200242c0441d800004c6000340c80c2c0354060754225042050100c0050780d0f40c0c0310540740540403c1c40360780 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 336774397 1250 336773147 336773197
    0x3020702130506061b010b1206160f050417010510080a08121003050a0b0a0513020f01032013031b120f02042901031116060e0f250b 58
    0x40b03500840050002ca1804400300c511829004008440041c02d94540d420b0000c2880c0c1a1200d000c6884d107030014041d281064000340d604000074807030100611840d030a00c20f2080703000f03400703031401040c011005506c00c5070b40d98101402405d04464034802011000310108100304005040e84090390f10844039450480031034580c030b14000300284000d0959403c000040009201480361a900b00d204001d05413203030400219440a40cac1000300340322a41c5001c90640c00140c1e841c0c500782074440c8420308000808560310400d45031280413905944412000010340340079031881088810040768010000400003000c5284811003c1e6240d1180c1c60005118550b100302040c1186802c0324901c2c4010300000e034540d140c400c0344801e4901e003015015070100c07107900c041d00d13940c060107030f6060321110664044c601108010080c80014246601500203952844000d5801008020b00040d64842808917001682251892881c01d00941002d111202d014a0001585981d00c1d0540e100d80154040215001104030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 336775647 1250 336774397 336774401
    0x307031e05070f1d1c030305010e0408090f040906050112021305060906060c1617061e07050a0201110f041e0501020d031e060803030114030a020f010f020715020601060306060302070213 81
    0x15080481d0300d003141d03d0321340b07555203110b000e006600003c000d041e82c0503e820301604442c0305034810318400002404000014030000304860080100301d480d24105881c8a0105009162240f4024402441c013000400c1c1d003100c10084003401c0f84221758000508124001e00d4080e038406440303040e0800b440d640403c5417450550090301c24443d05804071501d0050700440c812020bc100d030300079050091081110000d440c0c050143c903070702c000c0c0311110f0140c00c02030001d50040030f80010211010407201081a0000c240700327401c2001040609580b1589900401401045a0340107214034940c5aa0402d101031101c0491040e1070100d40c01600039001c00a841d440070b0340a04a54242c1109000386003004000d02180f41c8161030150031040c0c011174607903062040061280d0045102c1d00e100742c1c40402c1c48001a900d8001035102202c081c6061200c0204d850402d82c0b5010542c1c1102a06500d030250ba6007901c3d900141c3c403030407244503035828080709645120a070100c2c4201000650071210141b007103031180d020f03a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 336776897 1250 336775647 336775667
    0x1803040e010308160515190e0c041e050a0506090907120f0c150917011104050f03070e09010506011d1f020c060c150f010b0301060809010207080307031e05070f 70
    0x1801d4440f030000383c558403103040004190941c1841d00b9404180580010103098032082e21491100c02c00c48041c0c8c0803502d1f60f48084040c000d511444e241e00304403414407141c1f5400c00d00c6521118042c044d07410641c40c803a000d007804594060191065030006004682c0007d000c41c101c801402c150724400340c00c1e407a0b140030411403001c1610440c449480004003070001c407a07010a150502c0d070700c1e14202e9041ca5401910100f00902c44038150381825500700c80c00038020b040f101224030403140740c981842c01d48007003400c2450a52000340c402031070408205044a0641013a84246d0007640d40b81c1c0e1114550800108000b100c450440d003051201c3c0d0f145c84cd00d84e00c8032076071044d001140121022200380c1000038041d603014a86e141041e81041d154100d136001c0f004904c40d0404003140415215604000b02c604150105100b068204107030f036004159441029411903a0180d0060701065a07458000c0d809800b81080c00c02030300e1425880b98094480300a81e114440c0134101568540c490105d510130304865001c08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 336778147 1250 336776897 336776917
    0xe010201060e0903191817150c07060b0303040b070803040c03140a050c030d0e22150608150a060309140303090c0a08030a080a321803040e010308 64
    0x1e200d401007400088801902d1040c0010340086a40708564030b02d4084050401d0004410320140807110301208040c2105941541d420b54900662032280c114102c0c9444813080d00205490240c5003030006c407a00c544010490503015007014420524403205040e038902c00c5110b01003064030240402c00c00034000000640d0894040d902d4021101d440e9110804448451800c144030390703200d40000c0080000c18443c0c40300c500c90441c090f000040e54601d0203030a00c2960307843e0b1441260220702e00c08140c03040500b01e482141900a040011010380262001240c0c400c0c060700c0d011624030400920550134420b604141000058516925039140c540c094015042222048030607089100c911100307810200050351088828100412500c4180c805004540b06160000303d000d4104004200340f0303a030440070715034001e50307440000038407001d20340d01c1c3c030b03820040f2560b00310315400030160707d5040700d01c40c0f80515001c1d07030a0200759807581000141056a0744240d11519168070b0602004101040c0c642010748981d081e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 336779397 1250 336778147 336778151
    0xe0f07120e07060e030714090606031b0d1509090c0302090a110d09120c05210c01021c0b0402070f020f03010212040f111519030204090f050f09010501060801060e010201 74
    0xc1e0306800d4200a090342100c0d00195140003090301e98039040000300000e10024080029404840d40802c40198004102c2e81c00342d100000422034100702d118040524080101c50310f03403101200d04514010b03001c0e0566040b4400c0e40e80c5000320703119503d886510402644901880301551a590900c0203040004150701e03169a907801d80e06100540718801404800c6179451300082e8410301d0b05e01560300c000400f051604110001c0b460701d002880000d02c40b005500500041522442c20509242d031511498070000a03650001c5148640060002d49811020352180018000940110103100803800398003c0030344008030707950088025082c40d90340182c0c1c212002c0e001601d8030301c4d84940c84c424a1026079040303800307034141112081401000d8030051101c41085580c0b1503440b41100b11803850740914003041100101c80200c0210b8140244d040302d00a119500b803d01904c2022500300c401045d04541c6031248290784000140580011700c206411388680307894900c420f90800b04110341d01d0b804100440d041d99 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 336780647 1250 336779397 336779411
    0x5090712110406030608060903030705030c0313240b01110a030e061224010512010512071a0c281b0801050a05060112050601020606010c03020a1403130e0f0712 70
    0x181840051010f40059100480c03010324202c01c203440c02e00001c1007060b440c1c00900071301c008940d11a003140d400502000c6030303e49985031000000c01e007105c40e0034000d003154492245400d24800f6100351f4004c145404604001202000d8010b5031401c40708824504140c00c014002d50020703000350b0304c6d000300c1040680401d00b0031009105265a2604c03e0362902c0700e0300e84d882355501280498540c81150390b6420b290050805000410840c1d0207001806001e00c070b4450b2441c1c562501000b0030120000700304d01025078504041072207000300e10742d01103281308585010354081078014440b041c000304000091001e1009000b40152201194100c0d0850404c480c4c009206001a03030940900420340203400c915800034090410380000340c5503120100c541d00031282040304008450ba0045142940700c482030a00700d01040407440d0803820201e1000000f400c131800040044850350340000034002e503105142d18502ca45071610070318840c810b002c440207810062460000b6020521a01d41d0242404100308080380388 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 336781897 1250 336780647 336780671
    0x3050408070b1c0b011d0402070203060c03060109120b0a1107080a090e0106031404031409090115080c130501030908040503150a060909020616021801080706090f05090712 75
    0x4295070300040d01d04501043c503c40d0215035038120b030b07048031901104000700c0c444c010000c1d1150801c034000045011540017942400e4455070101d9101c1640141940c0262600d00c0d002900d617041612100e001400c00400403e4418500702e03401409900001e00c101140c1d01d01c85540c0207000d1040d0b51f243c40340340600400c00010f103008050f05041c2c82a4030f4846a490400c0c10340034203000164029010982030060b800d1164103c80030490708941c240c5420280345200000c1070a26100f8800e150382c0142c070a2000158004102c1400904040c003546e8801c03803a29289001d8106000d00030ba01070a2404000f41045950300a41c0704850461140e41202d00f8a6944c2c2e002900b4101075807000840c00c41d4000410880320414803c50018012072001009025021780120b441802200c2c1701c0040c0d28642c9248505654034402005200820303d00b01c3c0c05d01e50384542019840e200c2600c41c41000c03401c2c0705000f00c0d044021410000035200003400460040c0e0f203c07001102d401700c1e0030700c555102613507a000603240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 336783147 1250 336781897 336781903
    0x10201060b0a020f1209010f0e0102011e0e0601090b21070e071710140d0c090203100303030b0402182e090315050105031e0312010e07120903020705060703050408 71
    0x2582c005401600d8401191400d05043c107981005154482e54200100407031a038005d450301c8503016041c40c040300c080201c0300050b4010600c00e0a00b01c0c4181e19642100a111115006000c84005120030b503280d6903038600300b00040c1c5400c0e00b01982e000705441d140480640b18031001070480700f4143c040750a540d0b910481c03040450000e6401e040014100911408402c3c3c00301c4055800550185d01c41d40f403107240540c81c0882011242c0924884d42e02c402082e400e104134206008041c05001e101199241820601014540e41500c8101d000c2801c0c026035440e00d2030988256000b00e11086803024922402d001004a9620034180d400003403d40c100185440c40b0501c2c61944a10101e91203a070203280c01c5007480b6805061b0813034100d0603141880018816914042001c40ac6465882103401042e0700e114446030840c0034141117060001c0c501c20001401c203503200c9046000d84030070703100d000c40e000a04540c0401e481a400c009005680404c408000c42d00300302c0c0041101a01a01d04141000e4450401032b007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 336784397 1250 336783147 336783157
    0x6050702100905220b09070207090c180e060112060e0609040f1a09150103050d0503040804030b070306051314450111040e010306110d0c110c0f130902010201060b 71
    0x8164107022400304d62180c0d1203000300d91034045030080c0d43e0345003084e8004d641e04104d02a9003e09601e54007031554560154110a894502203407032140903641b03032100c40c4026a401c80f429800241c5150780c1050340f903124030845099403d540c00402040d07644a080c4500080c000c0c0040311140d100502100c0851441c10301c044d160705c9036036000c81c2541041c0700713200e10344075040ba000f049001c3c81200400c006203000403250003542941c10810313181d90751401c1c6000c031030040f603001402c0a0f000c00104034105a05511610659104a608030f0440352181c101e10304540b20541c0700403a001011020440544940300c0101ca0000c218104c0007011200c4520011020340041c8101c0310403503c01521140c00b2070070f010f140050868050a1030809140c0003d102c11a40e0610003d841160b8505000034205140710450f540350043d61010720800340802401040c00704017915090150082015445992030811340a801000740200f000c044003035408031030401440240d00481c1559070752280050f0820030b81000d00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 336785647 1250 336784397 336784429
    0x50409090b0103170909040f0c08070801020c070605040305150c09030f01020d0e01090f0b09070b0f07050c01080c0f030a090b010618060c0f0803040c051e0f090106050702100905 78
    0x400700394998a049000414041e020080c00c14082c0240080c03916200d4900344e20581000085e604a0b01c0c0c0d0038605d242e00866080440d20b401600004113100c0d0341500180108004442201c2105070740d81011034450045000003000341d00071203000614a4180e4070741680043d1212240b40ca00054040000c0c50f10707141d030502d460b50341d4020486c020b1010040c400c2032403240d8500000d20208240f943c48000000c44550010300100b08039022400c02c1341d00700321010140625161141c0c6c0c42e02400401c0809800075501180c5500c180c8400070960352148264502803446403900c241032608680380001180c10080c1580440c55030784d00c0d2140841c000510807402441183c07a0305a601a20810b00c12080f04150000300601071718241480004202d10200001140c200c10a51b0302c0e40c5a91401c1601000705501c15a406140e0480202e169032007511200140d0408584541108003000c0034001080c50034400e820129005001d80d070b001d0304080d025029450114900300307280c0ba0311807001500c1010250045 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 336786897 1250 336785647 336785663
    0x1060906030b0f0c030c030c070203010204031a280e030c03070b1b12070c110904050d020708070b0301210803041115090907050d062402010507080103111005040909 72
    0x410034000b4041950741c01a030380c844180b602c0c0c6001c0082d910a03100207007030107004800000009903410710410580300f5082e1f008000350360b00c0d40d0301c1c01c28403045482d02c6481206e207659040880d00c03c0c0c100c2900d070313681c42290903000601c0c103075080b40c240e0041003030410303071104c50008001192038200184001d00103140300e1200b000d51820684010703c01e40074200c00c3c0d1941154200890480341c031411ba080b660002032450b00c0545118140360040310f400000c2d111070f40088086041c04100400801c1d51f03420040140c0c02c48052654a05101d0707600c003860f2040e135100075410801400702038a6100e020034003810107180c0010328010760b0389412081d0700844095986243c4001280002c0c80c1ca000c603c0b0b030f41059010000c1c01c1162042c009070340103a000c1c0c100003d000c800151207550a036507030001c034000c00203843d10b001d11040203c83c000d212024000740700b0040d460b08000030005030242000c0c1d4180d84c1c01110b080701150b0b00384248402007501c000c0150600c03078180400a0144503900034507400522952003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 336788147 1250 336786897 336786899
    0x240306180209040b01080606101b0804270c09050a0e0c07081204021f050306010806041803030b09070c05030703030e100504030507060c080615091c12020607090e01030b060102010e01060906 83
    0x5040c418040c12289c0f04846046d144034101d07074841040940300e00341150200e03040b442885c3c000381c02c0c443d540c41440c141c3c880740c034140d20f020b1f6441c489030b4104140c2c480130700500c80000f004488040090007101e500103241d8405000c41481c49500c10780c4a07010010a40c5840141e4a484055410880c910042c1180d402c04100450410014010809856200a500c0d290115034050410300009240904001e4544009029035540f5001903e030140c0d0682d0360581072032903042c0100a0f00009079400e0090007024041a106845010b43d100303606d41010296003040b61503a0210301502c5014a11200c0b8450200e6042c41030740700d8400c56004502c01e48030140e8038407051a200d01a1803110313014006201c2c15504018050702c409a0b400200403410701070a41e141101c00000764010b6080c201c41800e881b5442c00c04040280d031105450540141d5022658241d842020403a9420a2400342660fa107e03a140100b00140ca9152800d0f080401400041281d0a0268009003181c0703107070b0300407502c00740c44100c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 336789397 1250 336788147 336788159
    0xf0515160f0c140103050c1b0c0418141b1e1504060809010e070504151a0405090a05011a07210201020a030b0301110412050a140a06240306180209040b01 67
    0x10740f044468800782418441441c200740e035100b541c0110f54580040c0e9425610f0720507074407024440002024030040081040d20b044900d0420001d6000b44101d55000d109180403801100014030510305c0e0240c3e5990040990100e02071041d0940f644401003a0900c0c0610420010750310111640425807107a039519032950718009006080210103003c0da14942d14100c10031000f5080030541005548060398086201c00302059441d1000c100c0c0d07400604414800c840030342102140000138401c030b901c102c0d04124991102000a802c44800388541c42091102d10b40040303a0003e18000b0f400c605010300d51240d07110f103090480b1402c1d45504504100180d41c0021946030032038151203230714251801500200700c040444641560a0b100c0d5003e4141c00081c00c80d240010080304020010405600c20b801140d46400021001e65903c00000708076a954140a000c0e1074003072a41400c0040031071140c03c047c1189145d501c840b4001c1a40c5d0103100d006082c094400d00140e15044040c501440c030501c1e2034000c43d8134100c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 336790647 1250 336789397 336789419
    0x60a0b182815260f0313080d050304110409050114100614075c1e0307091406090108030304020607170702280f0515160f0c 54
    0x2201c110314840c50310440b140303041c0c01c494194058640b10001c800702c5800c21128403070000149441000c01e442075105840e038940c000301c040d00e290700120082101081e1100c6030a07845541c800c00c1c90b00022000d02c00240803400c101da4584001c60040c0001805810076151386081d154505180002c1c0c1c0781090500114103442e25840300101070900c0c0c101c0c0c10320710741d0b6560740c940d2188038000740501085107292a2001c0720803c882d401c40041071070199003081c106070100300000d030401c04041c0359007a034071f0740c820b0010301280a4076250a00601c1078801c500700902080b201d8081c114020740511039550003290b980842d106001d00707169442c4694a075854143d0030400329180580042c2c41e503401c00d20078003005072586c000361580240c1c00207007090f14511008401d00640105031000e540440b503800d0780a600861540d020a6100f26580303040001a11074444266400c51072180a42245000c001c004441c040d01c4098807000c071017407408000501d0552111902042005001d5600d000b02e50000c000e42e40e010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 336791897 1250 336790647 336790711
    0x306051008031e030907260d02031303121e030b090c07020d03052203080714070315391b0308070f050d0c050406030b04020903060a0b18 60
    0x12000442c50b0031018031200f04254541e0043c250303d00300102c00305407120030500030f6101908100074004000c096a4452030743d003d01026500400d401044c1c13a0b402040e1004c012100f807800c0d281070144085103180c0c0c52a41002414011104104940004011200c4c40b28101c681440f5941d0700401d010541004101403a00054070024009504200341030041e100d4413005403101c0d4040c14026100d0800802407290b1040801a03070141040c2c1c010044204841d1001a00c0302d54001d440d06041e25103800c002c144d4526076408040c00080d51448220303017510141e000009602c40b100740c1800103018942e002180e403640d4090300c410041040450f804010b80c4901101050f013040069034030300302056200a480810050318800c20880b0010300740381c80a0095089a542d0014004100241280c4000040c00d54001e80504000a410401811650302e4107000740c48004c10010060140c0c1e843d0392110000070807804c0c039800d800103002040c000c03000c6400e02c0c10a1040c0e80351f11614034901a1003190398120198 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 336793147 1250 336791897 336791909
    0x6070615050f040915050c1917070305060d060203070302040b03010f05120a1104020f04030803090706110708031c060b0d020702091320040f0614030d0201020a0f1211030103060510 79
    0x1800c1c4100022486840212030840c440c4100002d158480c13901419403813060204941000303040304843c0d05030b2640710b140270004200c2d40ca4005e05548400d00b0890503100d054481560090303400f114000400e00a50041d6007107070280c1001413034169600800032568100340e0240c21450801e40c4101f0440c2404000420000c859202409001c20349907981302840c0500c001003802298045035a44425040c40202d90295402c0446161a45407e00a81c1d64a0701d0034042d502c0004e140810407000d110001802c0c40594100e1405582030006d1148026025510000d4580240d5255070000426901140050803404030070500960340318854018032000c00c0c07005c1d000d0300035a00e02c6040c12000c60340c41c0c004c0340130500850700300c1002040c3d0600054090404056015561071a190340040c034010708404c3e40e61710180076825140f552035503440503400c0340204403904001ca48104108411584940e4580c440d2040c1d8500001d001c00302c1103000c0000f904241c004540d02641c91051019621220441100400c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 336794397 1250 336793147 336793151
    0x121e0114060a0306020f0403020904140714030c01030b0301150b07030e0a05060a2f01020702090c1305120304080109030305010501200322030b07031e0209180606070615050f04 77
    0x1001d102084490202e0f11028103115804a40c0c569403003400000c07500215002070541ca014200741c100044810783c6520401801d104804001035030301304602c000c1da200d0500501a10400f0101c0c001035001c0c2400d0341d02181e242d580e0b8260031b400c0680002440c4007418000d80c07056210b080e14580a020320422100303151180408803000c111b82c0d07503035404489030403002c0c0c0f420340c500b401c11000303000d00c600014642c04400541c8a4072480d110005502402042d4001c486d00c1800c1c2d1a07130319144d10a8441c0318462001c5e0640b00a0a114030305000b0482031104100c1d4080b00d20306640c86032902c2c210780c0b04850440c0080d07110030041003252383c08651050340c2e0096000501c10b9a80d07080d000f03a0389210706034110b068100f0602d40c5042c2c003000d03080c0d01c00c0190b4012548040ca4030f40703218001d0042c1049015811480880c008110000c0c17007e100b6218401e034041c22540101500d4156204c8203640101050740c0040101304100000c0c00340d00441c400210241400c003016820700c0200510a0b1100c2036450040d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 336795647 1250 336794397 336794401
    0xd020d0e03030307030905011d0c030c09150405130f030e0103110a02150601020c1302040e0106090305070506030c1c06030308061519141201031112030a0e121e0114 72
    0x80c0d004803ca07600316600e81400500b031101841c02074058851035030450404c0400e243c94041c0310b070003ca041580c8010840548001c400080e0030010211019075050a102c51221120086410030358402070f00700e049410b080d5000071b1156034008030002111422400140406002c0b5942d58241c0203c224410540c4c0c4154141001007800942d100405204a40562001e90118500b640203115040c200080a410303800d03024001d00b04040650311611400c091402c0301e1000040300c91140011900381c0f6071000143c60440d10708010480150030140c001038000a08101e084402980f41e003020074051400e00300410190b145040207442182c00a0115008516105441d4071550380d64084400d00350700d4a1490303400c0d5502d14022a07101d51385001502403140d00290301c030b091420503850307541220b1007100e203110072156807030501400d110823a2101d64240c0c001c0c002411154040e10600704d03103280c0540039401100003800890300c1c068803810002c1c0340006030040c5200c0c0e0705080c040c2c01601c080e140300306c0c1c42c00c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 336796897 1250 336795647 336795649
    0xc0506070311030402130e0d0305041101080108030f03070504091a01230a11030705070308031b07034506020f0307050d0807140a120c0207050f010c020406050607050d020d0e 76
    0x103403200420080c41b44040030080c0400c400c0300d0303000054128044c000c403040d1a0700203002600403d4151000c4c1c60541e8202490b000642c840c41e0118180c80410003d5420084001e00d0441c543c1c0005e0002024003e0620000c1401032240c452006c15203091001c0d0000442300c00e0001d0981003d41c0312880d0a09810407841e90388041c05400ca80021520b0b2800401d00350741c0d40401c900310b000702c100042141c0201480001030024081c090741c01052428281d0211507000503103440c40e4400c0041c010003040914030001310241c5070b103400510407540c007052005ca030402d584540700700c540e07400d480e500d0412202d82c0c1801510b504005140440450000845c60440130b501d4050f62041c00032400f008101308500025080c0c0c0c41440800580a071302040c0985401c80b1500241c1145600300304605c4491500d00d83c030400c24400034481040703800103001005014142401119901340c122070507604542c8034640020a900d03180b00030100280600050164140e400f0340082c10000c0180b8a02c1c00c000c165441417500d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 336798147 1250 336796897 336796931
    0x906130306182006040e0a06030b1302130209030a0c0306020c070504020403080d0b01212315040509030403050f03070218090715032301090c0f09052b030c05060703 72
    0x3c541d40c8102040a2410100022490710450304800a05607102052100e0768109400000540e4440c0ca20155039585003a02421380845202011350b000007107281f00b800f00304041d80280620b4802030290f5202c405552110a8010296842101d020742c0c0040c01c0300812506000500c054141185d040d45440d141d40c951070310a000f109000d95400d80d65446000e826805a030005010407100c2051101c44643c01c00c003a001003494a0a82c1e40708449600c0c10084842015401c40c441c3c44515400354216a20006100003001c00520311072691004000c00b201161041040400b0103800500a5030f480032148140039150310080610807201c445002400038600000c00c09001340d4040740c01d0491030001408086011b412410000341e0f00320000e03040085071000010686040c1e50140754207000e010a902000c0701c0c81451034200000043c0b8440c810b0200d4a020b41c58600c201b840c540314441140e841200d111120038144200318003181d10645a00100074040c40402da1103820f608040218003105201000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 336799397 1250 336798147 336798173
    0x611121506090f0906011b050c030c01050c030d05040305390316060b011b080703020c060a0f0c05150702030c0f0304030f0f060e0d0e010215060105120408090613030618 74
    0x122441100e13000580c9a4450032070300c101643e1709000440b1a280070b042603501c1c0c508000310075000e030045004070216940a0b03822104d0011020380114030306103001d9000001409e01a008900300402008078440c44044802032682c0c0b80310048040100c000b09400d580842258100150300c40d03001403215044658402c00b03072408044e0007010200e0080b104400496459905070081c030101034440210105100844024044542c82a001c99030100744c48010481607010741c08040c40081e100c0e40301010003512034250040b03098812401c0b0b0304034502d00c295611000d201100c9020060340045002d14903100d04000003d1282d4262001d54900303070440d207601c0074014140d00003400030200e01000108100302c40d4814502f07003850000340d41000c5400d2100030490074080398401d0061103514111108240d20108240c0511416110546040b80c0003503904a00c960080003540c140d5402d2140c11050b48032180100400e1604a46d03116a241c11841d1610403038001101030041d0301440c8006100182000d400c0350 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 336800647 1250 336799397 336799399
    0xe0a0e06012010060308030601020c0103062301050c031b100603030f050309190b1b04180b03030c010603080d0606050a0917120d06030c0602030a080a090611121506090f 74
    0x40c00000c0070344400f4506020781c50f2609580f0300c1c203600001030020000140d40101c07026825641203803a40c03001141a0340c0c3c82d00071b40046007107100c000d000211000303c1c05100031106040076424070b40b50800490a541004c4010054100190840400042c0c14042000680c60744c603c1041901d086840050482288400e21420312900001281000c08100507000c2c20b41e21b03414100002962a20b030408050000f40e40c80c140c5180c0b110380884252881d00181d8050f20003030100342110a201100c51006840c0030340500ba0540010054414001c80030f00030310002d540074407070081d99049401200f01c12583c05078025010000103110500d91158012140c90071241002d81e01d8850000782155a410107024480301c00300420009040c1a803511030380c200d101185c0c0280c0c0b003405400d0740c0b041d060340c50744039071001c9400051035000000d1011815602c540701841c001d003400154251409140322482e84544074040d00c4004440410446141da0111200d00c01016a9030368140070924000c50100c0034001211 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 336801897 1250 336800647 336800687
    0xe01090615080f10090903030c020c0a031115090a030605010e130f0b09010f0612060b1504091e020a0215061c030c05031608190503010b0301330e0a0e0601 68
    0xc82c94120284c1044009000c41c8001000005110b103030180040c4032801005025005e504044030417460800c0d11082100d401c1410051452014030401070310751000881c00c070415006000241003500c400300d012020714460724000a1950500080c000340035001040814115a0024110700044400d0503615840f075100079526201d4607020009409050b15000d4414901d1800c50002003100c1107411070902d40b401900300304003880401003400301a80159451043c0144100310400c080140b81c1d1102c020989109910310310000f4074011441070360f200450b4400140d104c0030182d030000c030482002c581c00460841e030408107001101003041072804140c00107000e10000145030818800180300711243d42d82d5803000c0c907811540318941103206070020700d402d060284107900200465402402144e040e15892000b281c1140c2c41c107090720900c1ca14007080c95012240c400011007105401c5003248892703025a44404030401e1402d000e120840046a01071440625100140300840c0d0f080300c1c030b20040061403822 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 336803147 1250 336801897 336801901
    0x40f020d2102160503030309070b0706060f030303020403020f040c12020a05040e0702071a030c0409021b0601061d0301020702060702010c021c0302030409291014040e01090615080f 79
    0x1240d690800e105041100300201d266031446500e0b4041803258001d40c544030b800703050b60346440030306560340811102030390302d503106003000d211b01c1c40400054400c0504c1408042020743c1c480d40f0018a20903203a2044000c070750085420b1045191040003202a0034058504000214254100030040000700040e000e14a500017086000d00e8420300841d4040c0040044444090410240081d624480c0f441050544000b08a503003e5142d010702c122401100601d18181c241401c2c6400c40c07000307500005442c012502180c46030000801e040c00b01c1402800c450319090081804800c03c4a5074810082242d0300c6070b44104030950050340d41c60180c40a194081c608140504054800718440f6414101c0b40400818281c8042c01016030020041086d103500c0d000030b11070f141c01402d1034004804040180044004503484c0c201141c20f22150030840302519140202c00111600110142031380541c10020902000c034005012241c280d0180d132006200c40d501d054118510f0080040c02410080c01c101e80b030f8515080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 336804397 1250 336803147 336803153
    0x2013050105030a06030b041a09030304051506011205070201050405010c050a1205061212030907050922060f02070c03060e030405011e0e060309060f061002070b0f1306080405010f05040f020d 83
    0x2008801569001b802c4070740c1c0781414140000d030000207038100f5181c22a80c2000454a04010096900482e4404000c0c0302c03d0100c8044c1924014000303080b103040210019258413419031034000c40340144940d40001a890906092550075219054800c0c8207014041107625101e982c48800b6519200b06204005080e8441d40000381401c9803004006445114440f4044e0540700c4d548000c6000e00c4100302110081540d0380c05000c04444104e070135440b0300c5030300740d101c0e1001e080e00d07000d403100c2602c24440018420300704003044c004c98100d02001c0d02c445640c000140200801840382074100c3c100d220085050030b2070400000d00111300180445207030401000b207084102d024802c0020308080c000d00c442d86038501402404c0d501d42c4115000c13003030701000c50082201414400b100d208094203d6001e80405401c00e00040790582c0245001911950b0402c07002c007000002501482c0a0240c66560342c095040c00e050890940d40050341d00b000c46d5283c40144800100032180704541039078103541c40007503500c4c181 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 336805647 1250 336804397 336804401
    0x90b18060d0231050d03090306020304140f030403030216080d0f12110315120c011805060a05040806010b0c1506010c1401020a0f020105040f03030e1c032013050105030a 74
    0x4060462020904148501070300004005400301240310690b6120184d8400411030080e00c1d0503030107404a4244c100900200302c440d0010365100740213601202a9110503214507240051102801c07031a9040840c00348200341c2d040c081a41e12800c0c0b40b03220f000550400c0086911010041d45000601485649402c8024040c100351042212000400c100c588401d40e03000c0700b59801100c80e200701140d21101c42e013141c503048540340034411010000b4071070841e20000560f44080700c28079030010b81ca0740032000a074590343c4c00006c02e00c03041c03142c0d81d0135101e504c2d01603414600001030300031035440e68090010b88000b510014111181c1c2c000e00c0800c2e00540c03116001039503140da1481018000102944400301c00c00015002842e08000c15542d506aa04010f0f400300d0880b2002e43d1300078001c640c025195004a8829008801c041c0c0c0c51900740c07140d9810350407000315038107415000780f00840c1d181c550051803016216041144110703d900b036103283c41d8884150b19000d40303840c0552418000c010000c606a200c081d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 336806897 1250 336805647 336805657
    0x60515070c0506071b06030903120c080f090705030a061d1b04111b010b0f030c06030c03070e030d02010c03050705120a1104050402040b0301030209060607170d0b0d12090b18060d02 79
    0x68405e1401c81521040024060081081d0590101700002030440d14800c55100f2450a0541c65a540d4404d898041c0d49201c0c00c403002d803002c1071a01c5000e1000c20365603400d11044075102e104100005203240c0c1405c504182503c44001c059482c0c010b0840002004860341000240d45030132100040c0c021032103208030002c1d000340d00d80c022400e5481901002a01c0c815030080d005a00c044443c0300c41203c0c43d0b01050f503034156084440d0780000c4240701080b00d050664000c0e64015405003400e9011003802c4c4003003458942c01c81810070042c0c3d1214481c170316468140c0b09168100641e07250991408001000d41c00e65110040e182c5c000c0305944404a1140c3c004281c2070f5805480000e00c00d5503125a240b0b5500c046410078003080e4425091030000c142d032881c1642c21155016400140c1c80542401e21071214050340003a83d941480da5180c41e81107026079145e485055550744615141c00300440100c500801d0710f0080c0d00070a00b40c13036041241c2041c00042c0042d44044501c120340041c0c2d40c00036000300303030041e001da = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 336808147 1250 336806897 336806933
    0x70b07090e07020a0b150a0b0904091b0905010b0f030402010f0908060a0e010b100e0d030c0f060218101218050d0801050310091a0601051c060515070c050607 69
    0x80d1410b1181c4642d0200e00343d081280281e0340c0c10045d40300e216200c02c500880c07040c0341da440f4840103420090054918083c2c101c15a00800019a581d400c0d120311500c00c400558119510001190920552006114007400f40001c0700c10a0b090030092903200382c1c180320250000c0c1c18041010b55012005228074052009400c004040d0703042c909003c10808060b0821080750b00c0340c5d50800d44011414203050305484e000d98000c7c2d66106444a814081c0280c00c2104072050301040460f055134404a2545500083d500f071142c000103a43d108004001340ea80340c010040140300391001354075141d815900444444101980300b400107240020440850122000941c0080c0369004038001c0c0d224071303034012030601d040f01c100741d094840680d60081800111103051400920085107100d04006201c1c00e4803105e85e05c1001030600510b020305204588101c00c01100c40c400d0749640310f510601031403c000001c01d404003d814a140e0130038140f075541f00f86204442c002c00d401207a011994000f40715000d2038410032502 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 336809397 1250 336808147 336808169
    0x40215190c020f0a0b09120c090714160302070e0f060901030206030702240a060f0f0303140903010f27080318190309060207060504030506060108091e010204180908070b0709 76
    0x141e201c00b5009175401012400f403080300c645030510755200002c5110011a50001c2c144500c95803038440544080c104400e03004c0d015a024420074090703820000344058200d020b50000d103265840c151600f8007981c0c0040020300d14079244001d008182c2ca034030703001c03d043d01e90458603191280da030302c40704914088000d84010b05094040703c10000e00200450000e010340b20380b240620503aa140c902c21050004144a000b4a0f0509007404001207841003402c0003001000007840e600e0b140442c00000c0c00d45882410420702c455880c3d08040300b003034480a80b8080c01000c0a5099900b404079103822549004c01402602803143c07032141d221102c030003840718680d80011a5049840a07031350b4280148011128058480588560303a400714503103009030142c1b0112644503004101c00e030f68401c01101c09403000351958000d445100c400503400d0070b9140070250303140316030000103840d80d1415104104003103078012591070f000d180084007030115075040200c459242d00840c00c0402a16850000c81e000e4540f64001c140480c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 336810647 1250 336809397 336809399
    0xb011b080c0a0f0c0b09010507060e2d011b050412080d1d010c0203070f0f03121b0806040608030f07030c0506070c060e0c1e010c050312040215190c020f0a 68
    0x108504120f60129030066600d181d0842d181c07142c6040c94822040741c0c40c0401c405205800009406803c91546081d83c14107941408007090411744184602c003101080d49031480c80404078546c000d20a0368070581c41c8500d082040000c07404050f083e44513602650100640c0c000c0224188103820045846040601d41d0402268000075003980701003044140d29603207035090079a10a4010300c00001d507052150000c038158403000c0e8507515040442240300048081c05000d0701c81c15828900352140d4003c1c5c031851070001c400c643c0b480b0401815800010700706480b9078a030120903c000e11001040e5036041403504107942c1e48451508094a00000144009040b41f003030178200017800d507225014001c41c62041c4024850f8003441c2c600961980c000b440400d40141c42c8420b44111102d940d41560840301040c100b04102303500310b88a05046500ca0091814070801040500046042c45200c000e04031013540901d40c184030841d4a00d1141030349a085031000c1040017204a01135603076400c0c1049140b040245040c450b2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 336811897 1250 336810647 336810653
    0xc0406060504260601092a08060409140d02030c0705011e050c120a02073210141902060609040c0b0d0b13050a06050303070b0c0304030203070b0c0304060c030b011b080c0a 75
    0x60003804030705002c4910440d16400002c007d42c4a005040000f6848514666039180103000c02086201000d803000c03d134551410004160900007038081c1e00165020715a074038010b0000354540500c0d54803044c10060010150040c0055100b146a0b040c6c0da01c1c58440daa805500040528020103e03410030034080000401c84061034000440108803259408054644d501c8041c038541081115501c4460b072800e902c144892074500500003040e6400302e82458040d1485030f0107d6682e94010742a051200c0c41c00018080c01070707030104071050f4829400c0724001c0f0545000c0d40c94520100b401d101e64a80c41001254082c0d0f101c0d8070350412000914058002c0705140c440c0481200904070668072920388034904440440c56040102c2205d0070f16030042d0f03070001151a82505201e00d03500050040d0708501007071049800190300c40a80c940109030b8641c1c282c2d100d0034a814680201c078155000340c0223043c1f03003401e1841a039802c0034082150300318404a01a1901150402c810300e48119003801c9501d00a0082c01c1c810 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 336813147 1250 336811897 336811901
    0x61a09120a080f070c060302030114090907120c0e091603030807050706050a2a0f0c080706090c0e09060f0c07051c020318030105100b0c07180903020c040606050426060109 75
    0x41e07030f00070048040d05c00d503543d100742c0c00ca1200b8058044e02203400d00445400d4142489100e03041240c540c201c072000342d5210b0b84115001541e1000719518002810b082101c0c601c908ad125170410070140283c48451003016205101100c1840300505010b0450700185065000f007003981c1c03602c4e401400504c0a0310741156603a0081285000000313060912403ca20021061059802c003811426114103209501d100c10954248851071400c0b0342e000c00800007200018018002e0380c02e014072400341803448500340303014a021400c0041c0850280e41c012030402c000c00102c40d09d600d030441c010152165581c004d9092890031306400d01485485096000e101030030066000000b08800b054000d881988603412408049c01d8a00640305540081faa90780148114014000100100080310040381e081696400340500d0700d000401250540a6403800500c0c01d1540600c10b1320101e0000f00c504000040c00c0100191050085000e440c020140c1c4101030100068900a0034441c5414002111001d680da1190940 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 336814397 1250 336813147 336813157
    0xe1b100e031c1b0201080712060b0c0106030b0c070c03110301150e10061103030109150306110a120506130b03010b03010633020a031b02100e04061a09120a080f 70
    0x4009543c1c540e041d000002da85260740c140c107605035111802da803a0001b0031a000d1107001d5982401c0e81e9580e20008105101c00c00410320351207d0000851080c0c51410002005000108400403010003003043d4070005180b4a000d4083d01d601450b44070f4440600e501190041c4038400d041c4801d458003403c00300d04681d1000c0464480e64040c0504010140c4592049440d01505414620264002d2005000e40b514030b812513000c49842110100304260340e5240c0304145e40b0303000c07040c8124003000102207080b25031240002001c510000018041400c0901c0070420086400401480b00f550350130005019036801c0d0400d8543ca80002c00a2000644502041c0300035115059144922081f48010456080d490028101c07000115005042003503417684081c0e030514400440e4000010326484208016513411703900c0d00c041e00c030300d90f9028030221102e424841201c000e50040300303104603180684103509500c001144d0709803005490b0101d586c01040d900c249480f2207460018030490010500002c0324840b00040d00c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 336815647 1250 336814397 336814453
    0x1030507050111060103060c170f060102070501090303020334050f190b040b0a0f0606030e0f06010f062102030103080a08011203140a17090708010e1b100e03 69
    0x419059607900151040d0555815072549034102c94010004034401d82c0c04101c0702c090034240303000d00301906845000341c10002ca90010b0b00d07031141000d128055a0400002000c1c00e002e0070428111425520041d64a00403240045000340e10749131600c400e4203402c1081501c04240c41d05120301040c061600586404042c001003105110f4180c0b510221101600306c0000d5540010f00c600c0a5101d9480c1c01c090300b01c00802c0b19809644030300d6031100f110420312640004041a9400142808510740114146010001d406101d90300100c010301078800303482d9400301180d210f4103081c900d8810020204105007054116084030701c4c030101c00001031100d5440200440ea42c0d941e0b600750543c2c1c9983c9050905104040054005040142d107070303564020010081050800c01d08041d89055a2007540e002e00d000308954444940e0042007080150a601b40641540300300780f04007800c180402e0741d4100052412441d101486840301c0074004041a000d42ca0821402c00061309507140c10030522086561800603030001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 336816897 1250 336815647 336815653
    0x50631080a030201270b0c07080d0e0c10050d0905100203040b01050a0e01030f080d020c0601030c0512010614060f040801020d050115082e18050106020c060403032106030b0f010305 79
    0xf44841c3c9426038000c9905e00074060910042d140c0c17501d407480d0209000f0324420141c0d504104d0a804210040003401501003d4140807403041598071115051045c0500c0d02e030f0250510620f1492034a07080f10541d101c1d40032003100040c410f9800e0400318034180e0484210320034030348000103004c1407010b1703801980d05a80007075815100e0555142c0043c400213100f4440507000c0c0c0541400f03480020a258007c05032842c01203400f40c1070000342c403801400d060003a4801c944184c1d0040c000c00140c140b02c0b0341c10000544a200030800c040c50f06c035201c03800d01c6800a0061207040300180550050311300d40190f134060407480d00215260346840040600130131082c02980300c0f8085a0300700b40034452044c1d049501c1001125060140c0a615500b400a03003421241c9581c01e250380800003003080640545030f0080000d0202012856506d03010000e0704050200c0c4203240160001c00c41031001c26041000c000251080324411401c030070403403c0450060030241c00081907199102d0a03c0019803105038018141c0740038800b5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 336818147 1250 336816897 336816911
    0x201180b010501050703091d04050c0d050606060a03140a0903030f06050d17040504140f01060c0b0f0915040302031c0510050f0f030a0f060b0109050631080a030201 72
    0x205001002514600510410419005000340c0d4030541c041c01c04a8421304164080c140c803545985081d0408240031031380125400100b0081c41010400c5502a020544030821040207980f280e43e140e410081c0300901540d400950200e590380320b44e001c0105c6944c0c00c00ca0303e8a500b005c03840503000e40052681980001d060007050110f20005118400840c0c070020b000c803a42d020780d40c1e00d08540400140b1105504202800001050f845a020320320105000c20407030003a51901c6081003801e54811b030415010040400070381e0b400509008007440c0c2000c14509048955070780c03000380c180703842c81c4100d020802c689075006010402d600003002d40483c10041b10400c55a030101a000b004440b070440d80503001d082c108804121609291809806444002d440d4510440300240420f00d4050010001c95010356100890803e0202a00c1488030450342447e01101c801c7c40c0000261880c0a44070401103502c0441c01d001c49100303201d00700d0082141c4c03000103c8050603507400314503807200d9603401c080c0c015500b0005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 336819397 1250 336818147 336818171
    0xb090a0b0c0315010305040203100c0903440d0914060f090d03020903011128050702030a0b18070801020c070915121a01080102031005030a050a06110d06030b070201 72
    0x5492180c9043c111996030526a940110090308005d0001d0340c0500650210101c404010300500d40d0381380c10368803051001c0b840d5180c44000c3c445910300c1d84480340710001e0518180c2403000402281c218029910a040c0c9048040c1480544a200394003000740d8a402880410082902c0c00e4091509005040d2072880c0d440074800c9543c024200d87c482c481c3d420084072a40068040d50242500000180000504600c070b00902e1025500c401428040c2c0040d5200c00d01e00b02c05012a90b6080110a141041c02c00303c01e40c0c046a07a0f42c80c0c1003001001c03100460001008820003441c2010148000c0302111101a954844c090003036010080900b01801124400300c4d090000d07000d80c400c07810300105010300d858500762551a40032920201124100c85401900c9070707056540e01c2c6540603007a030388001a0b03070341040965a01010110341c8124029004028200089400418000407180e080103022401480310b4211514030b114034004100741f81c3c6810f20100a001e0f01110b9103100300c1e401d400801062078009 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 336820647 1250 336819397 336819421
    0x306150d06090f1b180b030901060f120302030405060f0f180a0f0609031514010f06170613110d0f050a06050a0302090109021602060408010f110c03070b040f0b090a0b 73
    0x74403840c10700c0ba00c1e00ca041e20304c14452100214030314803149840d0a00380d203038140d00340707a94015515006036a45401051186845208804000340250501d12240d280c0030f6034065100d019610541d0710401001c1443c4c0c2c02c0300e65140454400c01c4182011540e00c1c41481104910481c66403916402940a5400440c994170f00b41c10071f1045d20340d140c41d0b45100750302e9a642e8600c50441400c40f00e100caa1a00d180000e80312461000502034020403950440190038804002d2100141188413554401c00c507003400300c40c1d02e44111005410303c04c3d901c0810703641200320f5246250322400c404100c05d0342c5400c40140980d16a2350107140164403024040c44215a034608000c2000c400c0e003c042d501c80c1c03280d0010011100298014040c00725054084c054007800754000030b21542095001c0b40899440318110842a1443d101d07031a40c00320400c910341c4c2044032000f821952030017a05c03801800d0310740010208041c804441c0310400700681c02421490700c0d1500c020141c0c2c0714240b1285c00c03545c028601c2c01095aa11000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 336821897 1250 336820647 336820661
    0xc0b04060905040902060415020a050f0102030f06060a140f0c06060d0b071b02060301090911120d0e030a02040f150e07081b0712020304080f01020705030706020306150d06090f 77
    0x9a41e80100140c1042d0802c0010245080101c1c2d1000b01048001400781c00c0b407001c2440e420079900588002001c03070400c241414450f8110070503591041040000c8114104142500302c10155191512010021811354105113a0800c210b4154004250f0140e2a074000c0b0003440c00c490b8010a42e161a101c0005020b004400c1c540d00900415505d000102e12500c80d105a009442030082c20401000050b000300e00542d0081e00194103003071b218090042404070880c0c0900c01014180d403c45c251901c5118003548440c0e40d1002c0c6000c2021701e4800d00c80720340d010400c2104e03454004204000c0301002417a507400510640d02ea14204140030340e80080c91004010385184141e100307031a44001da64441c85203160080303080701d02401c5586d0900801020403007850312101c089004c3c1d0000c6584070700b0050514580b1102034480105680100004c03400110041f09943d440e640c400c10140e141d84507000091001e150f03c1c0b611002020b03002c180c402c00b08005401000072501ca907170040240d504006110002d650803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 336823147 1250 336821897 336821909
    0x1090f0908030414030d0906020a1b0302060a0e1005270d2f06040606030b090c13150b0a08011a09090f0a0b181b0703021510030f0f0c0b04 61
    0x5000103000703d441c951320b00300070784c148400381e902d0080380c1c0928400b1030b2120398042d14120f5020414195854000c0d081d68003001182001c61480036a980c1d009560b054001c003e140015250f08c005c040705042008002402c01407400c0600a43c600070001801d0101510b02400c1080c1d482908901400c501094001c0c100529070b03914080c8041c64801c8580e5818080120703c0c080b60100d0194203503c905109039401184141d00104080d45103040c401c011a0026110001503040f09114031202d0b07843c441c94100200c081c81021882000354400c90f49a540150b1005a45620010750400117540c0a044241600c0100100314054428007100c1c1a0901800d00141d401009100110b0354403408003030240d90240781d4590103c2e00120040202e1600000b4480c1050307500b00b03040503c03000300c01382c40f001e518000b00007120a041500130b1311f00075600d03940c2030100540150250049160701d240900184099608000c4014102600346840c040508011006884601004801080d0306081d03504960072102 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 336824397 1250 336823147 336823163
    0x209182e0b09030718020711030601180f0b031c080906130219090f09060501080f0c122d010c0e130228030501030524070f0201022101090f09 62
    0x3060042441d2207620040400343d05206418002810200c20000a0f42040c2511800758071402d035481d19140340610346035124030030341084005100e02e41190340c8169840844500202d9545d10744400031004069a01406402d030250242c43d44c1542900032030f000d4155003c1c3e990420039920703484401e84a840650b58004000701110080b00545010ba0341d1022160501c05143c41e040e580d500d4040c111410224040c040c59201e004c6501882418841d0301d005045580c0500381804100c02c0250710f8842c801d80c00e074404c0c4004111402081020008200b018020442549a81a2101e4004070b06100b0b00c040d201290b0a010b0325500580c880c1ca10090110005020a4000c901400c0c82c600a5001700c45400329030b0101d0392030400250314410881e84200c0507502e00150035415418040d042107a445200700745c00c00c98100600011500050349070380704100303291180c90240082d0f4200c3c0680310f28400b252217030445424112182134a6026a4100e4921980c00c201c1455000c1900c000d948100d200508004c3d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 336825647 1250 336824397 336824399
    0x1050a0b01080717011203030b0406031101180b030417070803041b06022b0c06090b040b180319140d06050f0a030c050d0501020702120a11040e0a0609060209182e 71
    0x44c80c0040c06c026400c2c8030f0304011495901d8480410100c6034141c0c4241d801000c0002d00d0f580c80d50b044000004000594209840d8850a11382030290920002d0001844541c135600050700c00c1c80c0c88010b032001c1c103510840c800c1d52414181480d001401e5084116000d0008400c0e0001c0c03414000201d0076203c5420540c0319151303a44c0c41c14054140c84030408a2401d00285162140000d01d061080c5110144140c06460345410700d0f04045694000003454100030b040c8455010b0001040001078420b1803500100405580740810411a10240c00e00d000c941410360200e40240320140b40d8203d1001e646054800136600c1141c042005000c00080c0b00240841000400502c210b0030b0100d40c1e090080c1c00350002601e080c02d282c1c0403c03d4800b0400c03480181e0307000b60702102c0402a52194a490040307088800380120050020015100c2c0000036000300f00540d190904000c21086406454800000420000821011010000c2e05103411a003408040d417014108441e2200e41e40035800d50301140b940489481d03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 336826897 1250 336825647 336825659
    0xb030f010509040b07030c0306080d080f09010c09030f05030403020d0809040b0301020901051e0f0301031a070201020909070e0a091107140f120703020102040305031303210e0103020d09020301050a0b0108071701 92
    0x21f00c4030010a07010075490711000b2800d0001000051446409951900e81a140080c0d48034046a0042d045003202c0e410a00704c80c0105610100400544ea009081f2540410081c500b940c910703c0303907500094110020b103c074407092100100c041e0202d0340c0241c80900143c41c004003003608071b1181c42141d602042050052000c03c1081c64a905000d050204006203031100e000c0d0344075904e0b04241c0c4121500a41a01c082c440032207000e418a0300004103000030342c20148001e00040b0002c0300100311004210130043d0011643e44d030b41d40010b0013070401900810a070b81501403001c0c50756001c548140c1c4c49000d003980e2400c51010001d040075950380a500507256a240403440b0003180e074040002681199000d01c00400424418001400000e1910032078084582c07440c5860500f620846a00b02551400034a140d4807494000ca00d0f42809142443c0043c0e407500540c000e100108090a0301a406618100c1000003010296120800454090300c80b107402d0b50780c642046480741550a20743d014030800700010404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 336828147 1250 336826897 336826901
    0x6050f0105061815160203150408030c09030109060e0304140108100e0403210b1305160509010201110711011707120903050c0d0807090f050108011a130b030f010509040b0703 76
    0x2401000305002c0c140c503070740c40c0c0c13040c002d03000b0415000d00740320354807a040c00314074003045010b00e00040f44843c04050714003920341c90450f000c0180804c0c0020700000d5080c615507429071082c1c5c2d15640c0300804022220750314140c540d44e80c0060050107024500e06213841110360003000450310601c00c42c10403050040c14020b85983c0b03402d0290044007407100500e0030b4003a4582c51840c50100250b07035500040c0541c08141006110a2240d8441c0b0000d841d003818000c40031041801105811458289155a1465000105e0041c01c40004480704482c011582e141089140400144100803d230f8404104038011701c2c1d101807500e01500c4842c080303030820280302c0900503150009484580603080441c02c005180c884941400400005e10000817440e0041005803900540c414015011104c145502d450406001903c520010701a401d1001001424624010031040c21a2000310310361406903080307940c0d00e20720450703a0404c1e211000444901ca00203e0f0b1418040c01180c0f180303030046404840e9032601036060700 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 336829397 1250 336828147 336828187
    0x1107050609030c06030405011e02251b06080604060b09060313030306050d0b06030f0105100b03040c0f0807030302071a030c090a05040204140f0a030f12120c030906050f010506 77
    0x41c160007082543c207060754981c00550b01c140d009070004108031100200450101c034004003064a5035105100c0070607900d13031024804400b00324111010301c540c0b5550a201c01d101e603900d0258400100b030b030317100443c000c0d03402144640984015581440b4041d1102c04290300d83c010004030540015091001071703662401501c1c0034030624081d050018510307031a94040b0b0740c60f0b14101c1c019140c04034500140206030500b04101c008040c10742008201504020003d807044000d40d11600038000c201101103014004400e0b090401402ca090480da030941e0344001c901d4513000b0920042d405401980000203800744444051240611420840f900e1643c1b58000d0050315080094400d822500355400851385440d81e02c01000078025041003030084000c07103030403c2000d401c1c0410700d0340114041031040000904604003100c1160b481050b6500241911000b114441035460060f10954280724280b00c445415034005a0f4244c040c8406105d581e95007100d1413900b83d400c1c8189038125004002c1c0209108407070080030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 336830647 1250 336829397 336829399
    0x10e090a080315060a03050f0f06100e04020c010603060603030f020a03080a050403410c030414060706061508010b0c07140315010b030906010501170c07030e0306070305040507061107050609 83
    0x30040b0704443e00400c0700758110b401d0303040220f6560018401c46801150b821030f48601d1414401c9181e14221010500d0015590702c84010b010361403410000300c1d615601510002e0740c1f4480200185556810700c07070082d00d01403006034041480b03070b89a403042d1807006c1414050245c154440b4866519042802c40c01401d00400076001c102d030415030100d02600c0c01c807014510303a001c0c4a0703c1e4411807241841c0c625203e100103241c4201c4c0410032881e91800c8010007502d0449520820b890004171070304000c21941d1044000007091035107041d2020501c00488110300703c25400554618150342c0c1c0b103008583d0f2902c181c03490002280d0114804004000105000c3c0305240000341c02e42d12440403407880c4100b6540c003a089020042d101004002601108100e0a4014071007460510805151009143d2400704041e0041c0c00c001070001c0c1010030302d4001c5001c1c2c1035942c000360844200c5c1c5495a0020700808064408991500a4410000b441881020094205841e44001d000d4461500003000180c0e80203200d91 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 336831897 1250 336830647 336830671
    0x31602010c08120f0112050a0b070302122a030915090f030a0e0f06130b030615070506091c0905040e19080d1104140d051c1106010e090a0803 62
    0x3920008901c2d002a08005039040340d658858280110800f900080507084150f80c0b0711030b084000d01083c400228410702581185c04040d0356210158124040e124464140507031101150070300c181c1e11414540d0200100365100d1000030402003d0580c450303032009446c000b0841c1e002048205801e244a004a40c101c1c40010844500000c00303513001f41140c214282d42400b00e454809012018104001407000c00c240440d60302d442c0904031032903200ba5454074000c001024002000191082d264503055440f94100003000380c0d2112100e1074119500c10f41215a1044d03400350223a40e900400c65101c1810b440c2c01d1039200c800d1f1607410701c0c040c00f0061060042c51003503445106c00410740c0360703481500d001950340a034611558413803400d83d6442c142e8010420180d115a0108410000720b00044005201a08201c898114101300307410840d10b406100691840000c200c0140c0c14111030700200c2c5e000500701e03010103465240eaaa0440ca4244850484d90135040e500609c04c868000b4054500440d8446d000c8264 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 336833147 1250 336831897 336831917
    0x81302040507090f0902040f06050d020c1524150d06150c1406070e061602220f0e0d1803080310092706050c090d060504110108040503160201 62
    0x581512070540301c00e00030510400341404511207840041015040b8140107500c1d140c03034958103170140f103018450310003000703008900003140c1e03403890b0111901044072030225803408401004546079000305580703846140c041e908241910340103035105000382c041c1c002c04440b003e160180ca03c801d154400300082140651b00c010100b2420142e10780142900c0c1207545401411115180482c0d40c0d41400c1130b10180d5134021010000c2c5607034031903150307140e40000b0366000d516045910060010504070182c0258009030303c02800b08440b0704050740844520a1800c00c0c000301400a0f44413040707a90803c0d03524510341000300ca11003254058140d10388520340401403200110368940700c044a5800980d4498510041d11104102e01d840d0f5000b8018101041d1540e04220785800c8143c1c0c42810a5500041100fa1200c2c005032191807640305481c07000030050440d000c1e10205103401001000c080b0340450b08000500088a80f551080703c3c0503200d00e034040001c600d0480150780031525603040f420120b04022980007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 336834397 1250 336833147 336833149
    0x9011e06031d010204090626060112030c05030c01050615070c090e0c0a09020909070f080f0709090f0f0e121803100f020702030f030915090604080109080a121506081302 74
    0x100500046c030b040c010002c0d4090a00444c140319074892200c92811502d0380c0540c105030b960102e03a043c1107981a00c820034031000e0324901070f42c1804a10101038000e000120380120740b011b041d004107114002c1140c4820607203070101c02442245c0684a03000c0d0003503202220074407002030b1035400480ca00b1080000c840b0401d00940000d0007510a5811950503e5004a2012204d040a600064111499003000000620081001007600d41d008140c5c00d030210000c7d01103030410f40211500006080068001d12010510300301200142c0350751149100c41514100a0780c04805003c100320140304200e640d2107180c0340c00441c0401011421000c1c4031b0781406015200c181000395446200c04c2c0c405160303005600d51240e030040600b401350210416016800c1000b510585640d401c1c103d402c009103120030070352140751000c080344182c040d03038008207071961a1010000a01c6002800340c10321402c15528110338100c201c460b01d0943c1c100444c81110080c00c01c1c018064076000d10101613200345210110301e10104c441d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 336835647 1250 336834397 336834401
    0xb0912010908040807060e0915010f120c0c05070f050619140307170a0501030b19090c080102131410050901052803111204060c1b080909011e06031d01 66
    0x15100840f9031748030a40400c0540e80083c40100100021034000c5a03914200004440440740ba40f88581000120540b00340e01034000c0e03c8042503600c07206400c00520014800140c100c1d031003600c05407030600c0361140000b154a0224240f40685101030712aa05209000da02070420045100b142c20a2020381c000b00380c0c52612607409103218070400c0c2d90b03254085d03600c03000c0e011841170003418a50032241410300520103e4101c981c8243c012110316040e0000714222701d46c0100070301d10303140018556451701400048820054010342411061800346103086907039580c14587c151107081400b40c018a000c5078400c901406080504002d880c10b04040e0714107400700c509000e41c15982c40782e2425035296201c03d00c0d4416410b2160301814480c42075010701d0516007440f80340c081a802003008040725101c3e4891889907200c1c0c1c8100c100040429408a034600315407a28401540280e4409402400000c00004031151743c4d010391003000c212551800b1980f41400ca04401528210240c05094541d441981e20251024 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 336836897 1250 336835647 336835649
    0x90702150c0304020a240503090102091c21020c0409110909070f0b0a1403040c18020d143d060905100c1505070c02120a030e0a0b091201090804 63
    0x8240140d9034075280c410891a2201c3e9040400e40310354906d003024140c1c0841d0136010f9581d5040c2400c6450303a5a40160901903c141d84030f40e030b00b000452032048203144400d140c1340d4101d48215095009200c1210058440700b100d24107881c01607000c03c0400f1b0480c1030584c44a12064020404a641c0c28441c4c030214403d244152810002a0301805040202200c50300081000e0720000e07042d10b141c03060404000b001c94400d40d102800158000020604008101118400a01c41c0c0410300d0030398003d100d44a8025041000d08200190401c4d030050b80318104140a030380324100c0c441110b40c904401212051141111050b103070000d1031010455901c9240e40c0a42c3d03401008503a403601b5409042c07030140010701d0f0411180d0800c0c040540d02113400a490417194540380420320781c00082942d1815011500c01c0021140a50851200450714400e00804150307191020700030b4071411408202d210070301c0080c00c0390740b01d408030400c01444190711074178110700041c8180e070700000003040b02000c940340c0950903482 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 336838147 1250 336836897 336836911
    0x3120e09010b0a02060703020c030703030209030304050a0308030a0507020703032028060f06060906050313150203041a0f060d050f070603140a02040e01090b131415030304050f09070215 81
    0x41052083d0990400110350f22840c640340c1035042c080340e00d031900e550303010300c41c8001c05160300826001d4284c1c404000350b40c01824001c14140b030940d80c0b41403140303040e4000d554011742581010009200c0a000046480450345e240c0d85a0040c4141c007244600000c00c1c08540b0301c5a40200310745600440c0c225901c0c2c1d4102142c1005008444940c0e10b8201c0450300c001909058503814000300f0400300ba00440040304890f07880c1401a07880d41d0b4034030034141c0403061039002440305d03005640340080c00b111035002e18801d03841459010319030002e2450440e050407044030000440640311000903640e040c4404841c0490348510100c401c42c04680080c03078100042a0800f40010740e455070303c04084100421600e4000c4101c0d44110f00c0c150600b080c0d007030005414000d03650ba40b40c07038200c03560341620307800c450303145100f0540c20421000300b003c00c1406c2e05040c25604c480390211124a0b21116113408811030342203c1008282c2d258960302c00c0705116078104018802810340c06100d5818003480080081544507403c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 336839397 1250 336838147 336838169
    0xa05060604060608130605071803081b2d010b131410030b1b040b071101030f11041a090a030c0503100c081302041514090a02031003120e0901 62
    0x94100d081c40100d5400d540000e040150020170311581c400301040544071560401ca0100303ea030b0b07810105440d00c410f074903180501801419030010501c082d41c4041c0c8100307950780800e40e100404045849543c0c643c610061030150b80d80860728075000e0201c0142020561020700003251745604400015064910b00160915641d100c0101184c040d840140090380f100d0038801540099003144c40c0c00000b0000100310a00c3c3e118641c40200703102c05880e040c2c0700100250300055540e403c040c903000e1289c0703c52001d65408039003850724107402d607802c034007400c401001211030660400d032824050204200d240c00c1169052841000052810f840342c1054401640c00751040701401c61410060514000300200b136652241d140070301c40c482d800c2d44003003c40e401c80e81a840f4905c0c410b61750700001c0d0040180c862600700164140c04c00050940130070799492000c10003110400c05541c0c2d00d29071401640b108440041000001a00500001d41c09000f6104825440d140010385a0b9458000c80c020035400c2c0c0010f15512 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 336840647 1250 336839397 336839401
    0xa0309020906030a05060f070201060b070f1101020f03090603060a030c0b030412081005010f090902040603061a0a020a03270605030a2412020619090f0602030307020c010518030a0506 80
    0x81440340381c07541c20070307070507402002c4690aa45495442c1c44c4068440c0120003139040100b91654806d4202101808810401c01c0c2d030b03101949407207000d9483d0040c0032034055401e8454003070349600208001c01588452005185001c002200300102030344003d1003242d01012560303012011901001041025110500e0311682d01d0905080c4184c95900c06c0080c2c0f401c21001d02c0812401300d00300700c1904e08492080c2403040383c1481b040310685c6e0040c9642c1140c0a000d01c00b0800040642c0c1c1508880c044492130381600c0481480305040005e980b051036640000741c1d0203c3d0703c0d00d002a1146640a054140c0d1800118001c0d105201020381001958001000200007000340122592940b086800a000c1d144140168020202c100e43c034280440c450010103000c1040da5006540343c64080311500340c0382d202c210958499951001d4502c600038050104031030b003650408124a0700000403240184415001044041c90141c0112015803101480402c00310f07400390608015101040515419803040003d4002c038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 336841897 1250 336840647 336840649
    0x2003040e16140a140304060209040c0f0e0105030412050306010915030204030b15030615120a1b1d15120d0f0e04021201030b100302090112060f0b030303070c170a030902 74
    0x9405580c2c02d040403001c1100e4407803190424a03540b0069003d041d40d070740740d036030f54144040240200c444850b0002d00b009400e01070303d58810903090801590351214511603003d080111810301084030014040c0601404042c072260090010315407008051504046164881400d440b000d01ca0708803c80c0820307004107081c0100001c294080741d0103001681f40e00b614001003c0025a940350240a02004140402e450761240c1c45030340c0f25080c031203800c0c0e048481c10402854240c04e41c540051004c01c1100c040840491007400c1c2d09026501d00c10341d492520420780361031007480a00c2c0b1002031243e07400300c00c0e01c6005002020501031044417481540f01c41508042460018000d01c0c007803101140f06500c1003000b20300300f00703c440155040d681c000e908030390f050b078404c085d03410300d000180c2010b0f6110300180d000280300101c1400a08016110700014441c1103458032100d01500d401c010002c1d41900148001501107100d50b980f038483e6405915144100e280b40f0103072000c00c0d8402564540025112646c00c025 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 336843147 1250 336841897 336841907
    0xf050318010e1c05011d060f010608090a14031e1b0106060507030c0c0f0806041b050a050d150e010c090e0c07030c1b06030902041b2003040e16 63
    0x8508080c00c2c8690860388003000215007407045001c900d0007030307480d6101d0030501000b54450b00c40a450110032a034a14030490045a5036a81207807820084122a000442e90b00c0c41252064002c0000341d0007000c8034446036880c0b507840d49068251281c4d034481401030b07495a03d0700e0310b91810080059841180d4070b1062020401814031110401c50a51b0304001040207120f80c054103d0382c440750149000000c4950502d01002d940000b940800b090001c102c10125099a010407058040c07486a4049584e644100b0140400c142441c0303e03c1c0e6002010407400c2220303081c05284146001c0c843c2d03412032542000044408211070311903041c02c020769559040036110a410a6650740030b8981340c018039410f8544210680001d2082d01c0c0000d0400200450120800000e00720903500024804d0305a03d1107034845900400800381c04805034400e81c248030f0440b034082603e1100f0300d654816580d0707a840881070070f5508651070b4401c000d50f011622003000000303200000388801c2401113000b1071100680d036811a0000b49 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 336844397 1250 336843147 336843187
    0xc090904030309062417030405060c0c0306070309050d120f0507020606010e0a0b03060f0a0909151d0c040b010c02030a08030106020d0504060c020d0f0b0f060901060504060e0f0406030f0503 83
    0x1281e1702020710542d1007040d4082c03107481150303c040711120011500d0110b50b81140034950000390400d03004038209900f02e030080b48000310210154202c80480c0e59120049055903103581010706590001801080c0c9280301b5805034840345003c41020804142e401d4100044460481d014001038200d0b034140021585e10040701904c0c80800c0341d04440e1241809a941d9840c40b0160529129684c410001c41e03172034541d610708a00810322010200400039440c10140441400c0411046842d4500485c860620303802003100c4040d030b03a140c0018050040300c1c005110007040c2ca00d150ba030610440085240050b5402c00c808400310b845102d079191031303500d0804007924048800c0f24000c03d00506100900c006a03000c59047c0d11681c04032142e10600c211800d1404080100c100041c122510400400c00c4403d4244007240c0a080107131403a215680c0c0c1c0d403600322218012409180000348502450000b1480c080c1643c003d203240050000502c00e94a603102c08200d101c1c007204076069000407658040c008000c1041803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 336845647 1250 336844397 336844421
    0x90405011b020c0936011406040c0509010c060e010911041a180c370801081e010b0d1506090b0a180605030123090109080f030c09090403030906 63
    0x1002a03d0480050740d8100002d2845d031030114038183e40904241c5000b8030422036507001e84151000400303c5400c1307010307100440f050a00f180400f80031800c18203191254148201c1660b6549080c0885a00111035a41011009a950b203440c1e03005400c0d110020320a844516100d0000945540030b000148070955981c02821400450305454681c81510743c0c4281140c00200304002209507910024030780041c1c01108140002c0c0c0e07941c0c41c12021903c0000d007030f40851150401130082c00300b513110f038100c0340500240250101d98115480462669000800d000045c00144c0008682070803031402040181040e0300703059855800505083c505541184507001c0500300042090054109480204590411920404003001200c40000303074458200c0d48540c0140000800a00c9110011560b42083c100d03044a201c81156042003c079500100501c11482201da10104050502890701c0d00c1c04290340005014030a07401080083d2016640c6000e003840c1b01d0382c400d840014400d005030a00e0012641c03000b09003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 336846897 1250 336845647 336845653
    0x30d0209031e0c1011030d05010501120e073506010e0c07112b08040f1e12020d060203010612050702061302040c0c050f01060305160b1c0209090405011b02 68
    0x407140102d404a46030140c240152111101c2e160011030481e45044124025640d600001c40c0401c040d44007034201f24104c903026a280035903100c0705e03000b10007141d4051400015940c0540c00401405040c120030528074240c1c0e440ca04403016100b076400d030002c0381e1aa540e0300c3c0340d0400401801003c0d0100e00582d0800d039034041d12803d1040b19514500704078100840e0305d04c5098140c4408125070f800280004c0e084454000340d20326409145000030076900705024800c0d00980b41100892414107000f40e10310080629a0140c1c11a40b40284103400110590801c0c0c2e00800e25103986030201c1ca00e40000c0d8000d060b20b649503c014a841e4412030b0440300b010700100700710f400440600080c1c11903069040282ea80403a400116100304407010b45909941c508000c03c41c0c080c000c15141c425806601420440b8041c0c401c0c0c0b099001650042c0080d500603008102c440c22081c020000301920808240c0090301e0011070061800c0f15140001c1c586001c1110111016034540c200c5c0151381d1804800d21002060747c1c001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 336848147 1250 336846897 336846943
    0x809030d0f0903020f0d14060406050a020748060f05070807060b060c0a05010218041e0f060e090a1b231804080c070f05060f0a03090203030d020903 65
    0x34609901c2d07101c0a441010501001c254950704c4c2c606041010380d004a0000749442542d103002e482d140220f4043c1d030300c140740c540020303100c46041c0201c411031540141210041986030f0440c80d90460020003130740e840308440541584103511a000c100b02c18510784880802d5602d040301c020451038090f80e6600411000344450b80000b0b5005098600181c0e20032404035800e104140810181c1c081c040c50a0054402e02001c582405410b5008044500c528a031200c04031002d0307414402038813024035400e241c0700e414010000e0100314691017241c16200c1d03004080743c155500c010340c02c607048003500c099440703400c4840e03401304000035100c2e0240d240e00c441000c01c08507494084035140030144030f0807103040c1c0e80500111007020744e0b8201c521200c192114007080c44505103070401130250341048900311000e20804202041d0050341d240c054003141e10051069180c090042138046e4582c000402e61802d150300c1cac00e00480143d40030300150042860310880141c65501034400c04d45061100c1d03403092000c0565442c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 336849397 1250 336848147 336848177
    0x71b140a0e0c070f24141e2d01090e06071e02070f03081b01060b0f1b2505120c04050702150a02030103060509030316110c04090809030d 60
    0x74a0560000c0c01111032620b41c64941000214071005450080522130013000c45a001360002055520060f8004400c014800d24101c03000b000d04c0058800038190a0006400e80b0480403545140d5440b84403a5143c150810186084052880c40303040c039589a44c98400c018003000f03031140b0501c141004440020052030a1460340a41824000e00c1c4201c0d1078080b5280782c0381c005008028100040641507400c0c503102340da0f400c041d070194101104010f041d68030740c41d04801c01081409240161140100c0203850040c0300103000c4402c3d404170000340305408455985012400c400c0c80b44c201003801200340110505052841c244503002135800840c894030039058040c80d2104e0005003180e22101c15200003070184c84440040c2d2400b48808103400b10032445404009d03007030b50380d60040d5048900c43c036070500690300da2075141622400105d0b07070302c4040c0c0c2c680d9a0440f01a84a4095455141e0f003550a40d4080351031a40813900b07482403404266030042c40002d50b241e00b030404100707103184180e4516040d03140001480b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 336850647 1250 336849397 336849419
    0x1140a0f180b0d0e07050604033c03020f0d180b07060608031b0106120b04060b01050d09050106050f03070302150f040f15030c0302040f09050c071b140a 67
    0x220000c4204042000400003224020003400c02400b0b1801d105611500780d061580d018046150600d20343d03005039203000805081c0380c0c042c1c17002d80754444200da45c01c00d2026102d03915070b0002118151400700d0301200b0b000c540304410f2507009640c0a58003511b0600340c111802c9140c42d204e80e00d404108981c1380d41861401191041e1001554420900e042d0b0b602903d050101c003803c0c2030b400c07400d11350000060018000f83c441c6604141c1440c50760003400007a6503040c071044030801038500944004100c10014001408a60041c000083c05041590030301444c0c82060080710804003003190702d0ba41d598000d205501c0d110185942100b022801844c0d03890455021640406182010010541d808038a1600f17a88505003a81c1c054100341401c0110a5550021078503030b03040e4010800e0100f480d20007440c404510a000b120207803020003c0050f2094504a01d00f0700030031006040180c83d11007030000e82c001580040c81902540300c0403000100050a1a0588846c0042500618411225071000304490000c00b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 336851897 1250 336850647 336850667
    0x110d090e0402040b03010c122304120207031b1e081203040f08030403032a23070602070809130e0703110d020d14010606090e0a050705040e0a0b01140a 66
    0x4614080da00d80300e600c0400d016024042c0f9040d419401c0021101b00141e000d490b020700d540700d6000510110f0910105041e005c6101801600c2101140e400180480e410390075841100e002e520460b21203d65030303141e1600019102000410301500c154041140001440004070100491b010b042102850702040d0303655103c00b04d50702102d00c040032000606002e1b034a82400b003c183c00c6040c442e928940303441d00400902c42400c3d5a07406103a03000060412000e46420200321250f51b450f400c42c0d8500c01c000c070001d10342220000c0c0c0c03600b61003000400c2c0003e4007400600003552041c140985c07103030030000c00c0142405d00500d24107016440c0c6120800c1d11035001480c60308903900014015010041080894414080c141c0c0181d040744061219038100410b520700c4c4604040e88000030001c80d42c0740e5604035a01001da1184402c041502408a10340007600e0b8400c540050583c10103030320382591500d80400382e003822a4003501c800e5036145810069600241c541c2c680010010500746415500c40000d4203840301 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 336853147 1250 336851897 336851909
    0x5010f050d05030714100e0c09010303140c07080708120310140103020f0a02100b0f010c06020309010b0d0c030b0c1603080603030c010207050610060f17070c0206030702010b01110d09 80
    0x45110000203026061007159185600105c410800b82c42c3c0e1401c003a0b9900000a16000c080d1404001000310080807441c0920420000d140326556461130300c0468041e0a8003c1a0b0b51080c001c0290041d21030041002900030b00520b0003801125141442d00d90a00c0060b00d03101805410400411001481a00508042e1254403003003410002e00a00124000c0c080c80b80c40d04000c00c800900203000300d40008688002034181030050050b00348604c144015402035080c464082441d03080000001365241c4c020f158450048030001031950010702c00541003040782c000903512120150340a0091162005209038071030400e5041c0b511307103c0100590902c001e0825000342c100104503000c21076a0b6420300c2120028402c040c000c0d5103034034031810613130303290a400c0d903860502c2185030308000340c0b2a0090075503c805440688806001c070249460760b0780392000041c4030a0030001003c146500696814019500803880c40d40009050001240013410000041001d203003030303078000360340115030691101c0000d041e01c1d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 336854397 1250 336853147 336853159
    0xb0604060e060a1a0d0f140106050c2a03030a051909140f0d0204110d23012303010504201e010309030c0602030406230f01050d08070611130905010f05 66
    0x315041c2688031900a120030b80300c0f40c6061414001c0703284525040302e2180b021101f5900d0440e6a1004155424030030119200165000030020ba42c800e5000d001d00302041c540010341400c11520540007d0030f5a0003c803c5c0004694045200031120f580303000608000c82007810055941800c01229034040074071300309540c0c80b030851280074480316258002c40701000c0da4041d0090000700a6031210811a8000349000e04600340b0300031f41c242d044581000c0e4a0084102940b50705040d0342455030521000d400404540c10341904207040c24900c1e1400d103c0c061041d07008561241205030b00d48444054990b66400003031203083c80804200c040014000f107080400b0003400d000440d209a4603044e650b20802c45805401c041c404020001408440d4200303034140c0038405200c0d00310211244120360002030581781d000260341410010302413030800d558440d90f0503004d10a401e09140d443e0782c607403050b0345070070092440808002c18500304141904070701c000902011081030116604200048481080c0c9200b040c1c4506 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 336855647 1250 336854397 336854429
    0xe0708101a0a020f010507050406030b0301060b070602031008100902010f0c052509090f030e120a060207080f0a02150a02121f0f06030506011227110d0b0604060e060a 73
    0x41c020885060390518130802488030341b5114001800a4020344240008a8284084022940790602c280010b0302d08071295141491113a44540d8005c0d00024078110b04100c42d650081460f200400200780303201e0348104085030070711140c800113200c0c14628060300300b40607a4410b1140042c0010030b24080e1101c1c40d170003000c80580d00c0c040e440030300465640142d480358a00107951003401030101d50090710502a44404055030130032000c0c03060b184950000c10405801442071240090425002841e51a00520710981030100c14914075990b07500c0b40400c600964003080181e8801041c111945500403110740c011400c140c040100d8400c9000024684903103441d200c0c0d00c0412080003000c40602a00032205079246454035200060010942543c0030b501141e0a0618104c07443c1c028091540042c03010418440c0c1e40e00c001034100c541c51075a1070b00300c0d4002e070840b400c00b40070303102c0c901840c02c0369020742918525402c0c0744090000301d4545401c03241050401c24100106c54031036803155401c403900e41c5101c60210b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 336856897 1250 336855647 336855667
    0x15070c0605120a09051204170705010e0a06120209150a03050f1512030712120509070f030b060d02131a0607170a03060305010c090501030b040506010f0e12070e0708101a 74
    0x40601c50f401b40301c2100c3d0100d07010030030f0b16a107180d032080342115400702c500a0780c170b810064801035440c500351035000104460034003c90b441082c4100d40901040405810070400d5000240d040841d80c0314212315601c041050507040d585801840e4012541a0789000c4900349000e441d01800c0f80701082070f01811585054018000003001250001030b008070b010480002d803080002e02ca1404107a446a0003410100841d0100c2000301d8040c045820065804c0740340da180d652030002070312005100a0b40001c0090010016031503218040c0c100c4401184001840702e00340116901c400c4c1150303112406803106204400000d241601d00b403050301514040c0980b911007100041f07024050f2600009c0440d401c0142e1050031a4001640b04107030707003090300c05210880180c0306200c1220f01c101c901c03500041c104200c0340391060040d6198450000042c00003e00100340300803c0d80ba1842e6030f4050000040b2120404c012700d5480220190401e42c640381c504000ea10b041013180c687c501504440750300510008842445c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 336858147 1250 336856897 336856903
    0x80a0b010e060a020c090c03072a15020d0606050405030d05071b031b090507090b0906040803040f1d090d211b030501140919090215070c0605120a0905 66
    0x200100102203c0d41c2c0c10325008000d4440e80602c20391402122920086000f0303c5546c0b0a41c2c1c422aa90f50350110610403126a0b003540f080051180c050351004c4100705004105450701e040d034441c50000008d81e0312451000400e003150002da0124040010600080c01309680100701640d9141a500d003460700c0e14002e082403078294218034100604e1103000d10300002005000b0402c2405d410a41e0110310f81c01c0e565100100c1034860440d02e2070005841c02c40e00b031009142d070358042c040c05000541083d0401c0d4039605443d203154080d03000f0750461201008108000402a05a2071603075580f4481162a400d007900c8070b42c0d031003904e100d0741403d014071100280162000c030755142c0c40000110b10300b408000315080241d42290b100d04081c1b0006030034000041408a141d003154003450307030701408007031380b40d6100310b08a206070503450110b007066a00c40381d201c0c002d6a00c440c039a0072040703050f2000c0c81c1d592100749040c10080c5e01560101042c041c00303105e85405461828080340c1d0003585600f01203038844061034003a007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 336859397 1250 336858147 336858167
    0x30c01020705130b0d0b090c0607020d03112a040e0307031704030513030b09060702010c0f0e030a06060b03090f060105060403110a091e06120209180102040807171507080a0b01 77
    0x30304000b92052100038801c0d40001c160152640c0b005441c5050781c0790341070202270320ac1c9030000b03500302c01024000000a44103101c0c034819589040b06039003160048003142400895801d001d0051260764442005040c41c242c0b054049000080d4021861300722a95406850440c1d0001048103005c4208009400d0601510807604600c92640f590b0310000d403030345000115000c0589403240c0600c80c0030009440540144611a03202c1c0103a00c130002e902680000c22034488007284145900b6004400c41180000c0250040c10094000301d8801138591a00fa100e25141c028040e410003c0c560196004120545920080300c041d2500712090079075000c2c0302004604001c6142e40040b1050b8034094140301610b489041e0040b04611900c07042c0802c913070380d41c95a00c0c0c500c04000040e50102e20300707001c98034445d100035800d240010402c0025007059590400b00b0700749402a13001c0e060030b800c200d03580340c42071030709118050201000d1441442107040c4204014405100101000c0d60715941cbc1188040c141e02400b0b03440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 336860647 1250 336859397 336859399
    0x601051f11100f0b0103140a0b18070201091208040c1202061908011a040b19020709090f12031503110301060e011e08190b0601030908070308040c05030c01020705130b 73
    0x25041a00c2282c58001005101c1c4a0042d191903d00c101d0750380c0d1320034081c5074030030b00840600c05d039552240e258001c000d1030f840c2c440c554090340e2440300c480030002d19410188030300c010340c0000130981c48500b40f00d113010180f03000342c07420031420360304000018050f0048132040c2c0e00054895900d40340540301040720380c4515400c000302130104c01c4208a00540c042c3da00f40c140e136200121001c003c006082c50085500641c041c1038809035040c06143c0188003441940b040c00b01d140d1045502d4640e458926108450001c00244c510749050b4400200344000e440760180c00d034403c0e141c10000341d00c46d402d032040070903498003004211100f65296042a5502500b2420150010441150403541e4500f500b94064000904554404804240010740f8000100340d0b095810142c4e0301c8424044002d99500116000080803241071590b1040c0d800301203048000507201d90391182e100c060540c105030820001411195121034441d6000d500380e0140350742c4c045101e0040b0380c420f071a01155440941248005807054412803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 336861897 1250 336860647 336860653
    0xe100909060b031c14030406060e040302010203060f0901050913050319110f07030201020312040501060e040303020702030c0f060723030a090f140a2606070e120601051f11 75
    0x100501c0070541c48140c030008201c04944203900707000c0b454581580344a18660214648158601e0010b140200460340944969000030300e041c2c43d030144101c01030058030203900503940801001001c2c1030010351500c01200c110307000c42c0698913040c001001d82c0d600420181c10b0074284c01c00017040007810401d0303031400220740200720b180480c4014024600c0041421390368851013401c0280c030b80c03c00c0c00306031031003501e406a004d14a4080140c4180c3e48100014200721034a6680703003030009010004400003409103119550140e07a45500307004151800007440c0c03003940315001c81507100407155101d0301114070240e4405190b111144600340722a2400d4441038840010b0700000848130031036503200006100781d54084000c0c5004603107413501e040450041ca0107440c0c0090000703000340b0609450910030402d02415620300301410030600e03161400c2c010207464040114001e8a6902c00d01d02d070201090038100c000000a104541c9060b000600040c008601414040c0d000507034950254405c00e00e11002d02d24002c11 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 336863147 1250 336861897 336861911
    0xd060207020d06181707111005090a030b0708061207050d03030b0406030305070302060f01050a0614090a0609090e06090a06090302151e06030309011d06040905040b010f06020a0b010e1009 82
    0x814500000308103001c03105d44103100b119002a031090000e03502182e030402003461046415000348101207035480e5018007031010500c12500c150362058041c10141d4425510300555007011035000d400c1d140c000d484a8403078400703044180c02c9403100140507009c4480443d240080c0a40c0742c203080e0003e16182a07a550890300f400004020b05400000408402f80719600301e42540d611074400035240842805055404100c144040012900c1031213102c070848111b0b910945000101e20006034041c18541c44140402d00b00700b010000080e03544644d60101030154007404c003030306e4428112030700c074204032a00500c86584e0b0120103080c5882084405007510701c1a026a01034103020312084062801003e09104140b00d400008070f190401000741d40d01040107845105219102c210210308400d10214003c1e08200309110004140103540941da014038012144185103506042d40c80f0480d000703a40001c2c00b598402c142c09400203208032026030444000c0261182036071144001e0f5902c40d41c0f142c0c0b04003412410300329 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 336864397 1250 336863147 336863171
    0xa0507050d0e150c1615140a060f0f05030c1509030613050613030807030e030c100f0b0a0e010b03060406050607030e190501020304090525020d020c01030b0d060207020d06 75
    0x201940e00422070f1900200540c0c45001c00c07190b91146010440030700408000301c00000e00c46e00e40e4502c2c00c0051410103d16410700d58140c0403941d06c11241a00c1c1561240c000f0400360401d803224a020300b45110041c0b501da4186008203075140c20b8103825501540401109049280200b0103070b801d8104020292205400c040d5603072414600703944020394990240001084189503c1400e1140344d0390301d6120582c2a541b00402580100000d1515200b40e002c1017010b942500303000d104a80c100c0120403000103010150320744c0b480072551325000c0b56014030402d10040c44110380b03d1010074111092a000650f40c0d55078071011034081c0c08035600c082d400c28030100c0e8080815802001550400c1c0083d100c00005595904481b42d981d0014410140035810400080c012120b90350400e070b80c08419680c9060084d510460346403071076840c481300c42c401a04081c011240c150b6044c046091030301c0302441c00744034440000c000283e07241d00140c0010580c43d0b00003044402c54454075841800580c01000801038100e801c0c07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 336865647 1250 336864397 336864403
    0x39010e03092205010303050d0506060405100305060d1226010e01170114010b070b130b150315070906080708010302030705310e010e060408030a0b0a0b04060e01110d02060a0507050d0e 80
    0x1c0341300c2361400d040c41c0004445046ca00700365412030b0001040c0c4005605411001d0b002040040c02054100410705444070105540d00c002ea400c4a1041d6100384840c00c101060b203181440b07402041c0c3c0311640c0f14004102510403521814103465010f0f22800c046208120902d00618403505600c00d8114a0702c00002d0040f01c01c406400c4240c0502c1c0040c50b556903140c1ca0312494000d03290020714946280020425100c10700d89071030840c0b50058212100f014000b0500605040c0840302500060074540003030161652200c000341d008084c508140384503504550010780c90705012700403a4061410188840c0013800080740154182d641d0900d140780745200d07420428007501c882d98800c0425824010405814500042c03001c0c4156000a403803030850700d43c491004050721000e5041c55200080d00300101301d03100c40c88000c1005114944072100d52500610025244000c4414803001da500510300c880d078055008901581d100a4403680010b003595440020382d22401500480e01c0a0b0b445c00d072840100d04400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 336866897 1250 336865647 336865657
    0x828050d090609090b151e04090b100804030f03020a141303060b1c150b10050702030c0d120807030204080d030e1005091b0639010e0309220501030305 66
    0x6640c864440a413190308520548a035144480e0f00184a2038207110740c4410440039140040f811150304030005440b0305080b400d07400c6900b02d841150703520080c03840710b03103809094002030f1101810a4242032620362405455808900c008a0a240d00000d401148078818140301c605207540d402c5450711010b00f81d2102c904040940801c4074030700d191040400a51030003001420b44210030faa850482c0403500d0f0344c0c0c0e6150415520100014a03143c0416200381c1d5201b80d9044408080d65690507100c5495004143c6005001d05400f4040c0740c5203410300020404107000c0c03165190302414480083e03168030784c01310000e04c101e92040d40340d030203004040f400ca1039040d000001401414412901c0400c2d116401c0c008440041c1d50a659590002e607124040c030b40b1030044051010340c010466030030884840c0103642007081d0600705c1343c0c0026151107000c00d000c11513032100d56802040d03002001255840c5107003d40c2c0c0c2c450180c0782849000004a56841d030b0204500180307100509100a01c900d5030f480c0b8006d802038001c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 336868147 1250 336866897 336866909
    0x918041407080705061308010207200405070e040b01021e010603140601062106050a0e070f020606030304090b0d021009080d03110307030209040e0a051b03070828050d09 74
    0x1001103281001000488805a40644014150280c13401c01042003a130301410518282848441c0000740100c0c0a2002d448001e00403100006480c5401d00048402d41084201601c6a45400240700641e44c2c000e171010319520040e02c0c00a04a90300d140142d1070a002043d400d40c4042001c4101c115840c0706400c8441200d20401c0c004886265200305140c07202000d00881001955001042d28000c4d11901c00100101a0160000384c480e110000700302d03250126000f810208001105000c071b1903a1000702200c00010a1002d003009007480c000207a2a0b2140e80704000c041c82e216800741c00e40380e41c1c2e611322030301040d4020840c055012504001510154651003600b00707a01800b407003251100c1c02401144200008400c02c607207995035425003600290061907030f2a40156868089103240a4100070442030b0a006600a011525500c243c4a0310044040c8e551402030304440e0041184180018819500b6894000a0240b1b441540062401c20503040c0e0054120300c21014006074154010f21075409543c9 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 336869397 1250 336868147 336868163
    0x3050301170a02030106081e1c14042102010e01030209090103060b0312030f0f070216030b10030f15180c05060c0c060409050919200301060b0a0201050a1508030711010302091804 78
    0xc500b800c0140c58004100442c102996410600c200c0d152080d030000e02b014500c40c1015051586400300ba40c0c6240a0301e034241568914100a8000c1d580c2216010001309000d02e81546403c1001020a024400611000381015280c0c4114001644c0c2404000c0e800d50f8120b8a0320380700d14205a8038011400241d40b08401d50000c803005c95036461000c04c40d003d001ca11030f000200024a1a5611140a00010003081c0e0281c1d80c041c002c0009504920f20b82d6405004440f80c2d11140940600c540c119255446600c400040b4203403890002030302c5ca111031003141c000301c0320143c40e801c0c2e1891242c1000d03414295030f68412000030700855451143ea0299004044040481e038460058543c601c4042420010242c1001c40c80c1c946d201000b22009071404510102400102d84a55908228035090304042081070250f512407040186d180494850100300034140c1c41c1a61400e4540492a82c89204240d07001d080040061012451079001c0c1d0100c8502e00809024006803848404c080c003041801a942260401 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 336870503 1106 336869397 336869443
    0xd030806150408061008010e070302010509030102121e0108032502152a030711010f031503080408010b041b0528050307110a03050301170a0203010608 66
    0x101e2420700a103c2410040c0905204080c182c010146c40c0c1c0c940648180140c400182c0402140e4080c01c00c940d80300c0001012a000e84034003140d600c40100f002c42485152007120f00d2501024407401c24031803559032188010f1b52030344a104492014251203051440c0060007000e41d00074564802040340016100041d100c5103c3d80007266200c0d08103007071080c03101c0004217500d00e26140460040c05949001d03496a10384801c0019124680d04024110880400060199002c40e800b100034203074100f40c407980e0f07140c6024154024090b0707a090b94241400000d00342461702400c01800440c17440c24203805c241500440b250b42181c00002c9038580c8a44c4609001e881ca050520b031140d406685059403880d003100040c0868a0900f1002281d078003041003100401d60000c00c1c1da041d5581c0b82c01113407600341c050022929182e007145c0040e506500e48800082c2c1101d000503061131550184803841c0c811 = true := by decide +kernel

theorem cover : BRFrame.Cov 336690647 336870503 := by
  have h0 := BRFrame.cov_init 336690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 336690647 ≤ n) (h2 : n < 336870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
