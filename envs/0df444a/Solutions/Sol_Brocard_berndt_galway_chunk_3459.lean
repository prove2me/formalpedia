-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3459
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:43:17.382357+00:00
-- url     : https://prove2.me/submissions/b9186101-b87d-4daa-930b-22783b9945a1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 621942446 ≤ n < 622122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 621943696 1250 621942446 621942487
    0xe151324080a09050316021e06031302040e03071b06050a0806090a0b04061409100e0f0403020c0d050c0a06030e0d0c050709051e010f051e01140a0f080c 67
    0x916001241c1d0711141c541e1001000c40340001070442c030000814032080c0708607038410000d9038000c5a52415541c1140280d03280d541e201d14149502400800000c0c10b107103032441201031064005800007858041c03080006144d40d1085c03800fa12010082514000c16041851242020b00070900d041c5091294503600502018005085903100341d001c0c131f00040850103940d111111000d00204240080f66403261400c00146074100f08600801030704c0000f9403403080c2480c08000325213420402c152250303209110000c0e0700380b02030b0044045006001045034640c0c2c0d100c008290b02ea000d400500302084180041010141c200d40c8100c05040c00c08025010204010486111045a5042c118000703092850020b0900031320f5002a18100c7c980401d00001d40c0d12010006a210700d81d00b0020000d13602c0300000c004801c0c1901ca041c1d401401156003801095400c003240e00720600c1030400007900240d8004d0b2075819080702001400044403006d030400c4080c0d000c10308030380040041d0b03421450031001c010a052680c889 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 621944946 1250 621943696 621943769
    0x12d030b06010c051b1906020d08132118052404180203060a08151b0c1b1003090510020705190c031a06010905040c0e1513 54
    0x100d6000030401d03405480c10046003540102600c0b101881028400501031a5103002800b03101604807281c1c039407904103002410f40302d0740d800a04409121000480c1c072820000c01012613403401c412a8000541d4404201d00013120b003441540403140c0c1801d0050407041ca444040465800da07000800850310341000c4080c00ca00c113400020404140c66941000e1442a5800415035612400707816102c0520395000c4c60040000b112480c0e22540d4580f02e02e6036600b0520700d034646225480c0041041b010f00c2100180640c0103035080e40e8200b4400082e61400c140b600031610101c2c0310010034000451526074214035000382e80b410100145103164440903540c50b62500b41d542d640d940001c03c007050150030800400c0d9070705145e6101007420f020380b80421920f2151320046031a51050380c841a415035100070400c0c4114010303510400b0181c942401c100191103010040e10034084007031820034441c0c484800c045803044000b40341660710a21301c11510040b2105034001441c00341421101d052141e070750b00d0b0340c000c140d55 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 621946196 1250 621944946 621944963
    0x40305150f0a15060e0409050316020a06140901030213091a040b0315160201020705060106120507031a040c03060b131509081b0103060b04080a05120315010c0501020d1103012d03 78
    0x104d2401b0800420440002038410b120100c1c1d81180c2c140d00d4925451a14800c0d5214903c181d505e4605840e0003121110041e078900c0c0902c1660000c0d4840e501604e5020400010030f003015035101624400c9502c05000c911075649134484030991410315000d4150508801c4d0010301a4110054031a5620035024000b04190f00040f0f0708500302c0c0c0d100350155043c554004081d0740312541d465002070104003481c0400000c060801c2c0004803014060300c1689241201200342809041e148801c00005061004468050560740d11010034500324101c046c001841480c41901e076071504062540382c2148940003e80100701c0d42d49801d00c030410010603103000042203140003c03600d013030349030069020301040e82043c014054003140c0041c98880c00a520301d40c0368004c03c00c0c3c03800d51750000403141440c4022140310400380121300941e40c8952040c040c140842d8010b0000505200725141110241e8180d030419010b401400701c014800144e03080800040c1044a20b0103404a40c568541c88016500e6441b000d0401d01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 621947446 1250 621946196 621946217
    0x30705010e0d020405090d112406031c020a03140a092108070807140705030c06070606080a0f14030306180403031d031e03010b07080f040305150f0a1506 67
    0x890b120090003900d54020014429450510007031a0ba8224041c0303000300150142c0301c0303500421004a41c00140d10b1599024070240c158160300002100303000340009805100381c041074184810308409101560309646d029042c802c605050013850a58040000b034046642000705061440d04550380d68125920784640c5600003040c00b201d01081c030941c0c003001d851501c00044540410546400030444148140901215100344c080001c2d074030803070f500940390140c1c4114070032002890520050000540700b4000441c07510384070520f080c280820f0110494507a00c41045070341c02c10441c0300480f0848103491004500313510b0700c00001848240d6050100c0111100d400116003490b1207500800030007200c040b0a9004012003038000781e0350344c3c80704c0460386005080b4507901042484003002c40c1e048039040f800305801d004003a01c804110b64851fa0503100d214074200000800224144030a51059a64000002c0c40746010441102d459100402202c1014a000000c13143c00170081210002e90784c0c01d142819141 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 621948696 1250 621947446 621947449
    0x141c0b0111010c0513080a0f0b090304091b0212120121240f060501050714190302151302061902030f180a14090f0c0d02030a0203091b030705010e 64
    0x6055640c841d400079401c01c086001d540f9000340060041c02c1c401d442004034240c0c0e5400031511040e04810040000803050030200120381c4001c64aa048410001680c5c81c00d0b5a81e2004011140c0e40700d001244240000d0302804800c2e0180300001ca84421001d12500d0230040c0751010600a0301401400210540500382e204103003075000385a03981c154132019215030b13000e03c2a9898820040071545442a5042152101d80d40d04540100412104103071103150510785107555000c8010840d03105100180b194102d0710300d4000c00da080441440b4080d40280c58503920a64141e080d00100815102268031540ca0310380060f12502e045a1030682e05103100742401405070022400d6200720114a02d8030b0101240070015a40c00407410740d104c10045a1100602c1d42d9a035034044098403442450b54008c4c040720000305000d8040100c1c903030003410400502c5c900b2102d40d400078200d0304181d501441c026404810021511010017800951042185070311407480d0890000941d6000c0600429041001d19014070103103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 621949946 1250 621948696 621948707
    0x904080c031b0105090c0303040602071809022106010515090118050a0f0e0f0c0313050c030d03060303030c0c02090c0d0f021801180f12110405070f141c0b01 69
    0x6a48a6030034070300d048008682864040c1c44196105c40c131a0280072030101141c81c00000b00c4048440d250080c000451609040300d4440e09498200c880103a251409840180e07242030305a00000c0381410141c000c0001c1c22045d902d8030714143c000b180204190148003071507030b01c4242600d050079024a0300d41a4480078070f07060140e0410070303403040d904444a0000890310460b01121913064070804d140140681d5034106104cc80c00c181500d560441c0001017021440b000401c221090f4164001e104803130000b40d00101191501038070401110021b0740e2074000717104055140c003540308050f5846c94403881045080d00020346503031340039101c00102c02001070038844800941e0001918484608411901c50580d51100e4280b81c695210590000c0c4104584030b11501000c1c17912026102840100c085540c200685040c906c5142d2509407403184504080241075512070040503c00d40c480d03a00c0d074042c406014030250412740a00851030011105114580612541c5400485040c000c0c00020600c0d5810300c0040c1c89 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 621951196 1250 621949946 621949957
    0xe030306040b01020f0f1f051911041d010f0801050f07050c1f200a020c0d0602090409050705101706091f0b0a080c0427110d0b1e0904080c03 62
    0x6d00075005240d400302c50200b0880500f1a24202614a00b60190401021503204482e40011405403038000c040d050000d074003001011202c0c9504929107501c45400750144151602c20b15900c01c24003005005a1281820000081c0301140003480385043c00400368451200042c03c10f41081030124000742881010007900d14500c0110100344994640c150812000e0300000c0c0005203541e200c4400c0c10288034102003100c51019095024007002c503910410025411410f600507070b011038003440320784c00d9580c0b0761080100f4079101e0002025458500303c140860706400e50040014040d014200910111030b010045500030805c031000b201e1684e94080e20304800e20041298641ca03030555001003091071070480103081a4400d42c40d015442d40da0010110300600c41c6010300c05400360142d00907084041100000c0e90542c0d008180400c00c4c8880301014296034100d2500304da80c054460148000340d0408010b80303055949146400b00c0c500e0140350100b214080040c000803d505d00c00100a07041c020148162003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 621952446 1250 621951196 621951223
    0xe090603030d0608010b03071707031713090c0809072126030103050705030604170901110d0504030204110f03130f0b041101080a090320190c0303080a0e030306040b0102 74
    0x340700c0d120000517001300180d4208501034400e545c0045011071412805502c0c00ca0700c0da009200082c1140ea03840011607280c0302110900300700f4000c010403803081e084100047c2440d11030001e28500010b20080c0789110240100d240b81e04900400c1c40b80707100500300d80050300c0381344040a040190500c0e0180e003402580000c140d0703500b0003030b00702c08145900c0e400543c1240c3c0108100da01058440c820562515800d64004100e040c00b44c0d002d00703004036440017901c5420814101452054001c001c4941001c0100e0310441c00203100203414021417500c0d100c2d140c62003c108004a0811945032003210803440007034811401d491448040a0401180d40c0c0c1c02441035074040c00028203414549025502d61084070a0b160205040c14006000c407003191040000d040c1d05540d548100040101c000419210341c803a1107211406003004035030051401e016010500743c8641c030f00540c02840c5003001800100040d0007550128140003100b0024030001040ea0380102d42100c0008031403035084c0060b40b5002020751700c00c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 621953696 1250 621952446 621952451
    0x80c060a0e040204320102030d18021234050f03070909062009030703030e0f0303030408090f0a0602150a0e06180d11060c03040501230103020f09070e090603030d 71
    0x1045c44c02ca43d00007940b18000e051020a02d090454183d00340c404144690140143d00901119903031945a41000250424401d007140c2104400e0300802c0c403a00c81c0d5220600d840d809094007101d0580a810541c0241d010041040092003161445110b010001c1c810140306241c0680100041d03070f81440350100034040311100b0030043d00940740400c09001660520200c0080003000c200d0400c0c02c2c01d0071140000380c000e010342025800d541d0300352140000c0709030300754010006414070368007034804100650085000b0401d26890392852030400c5042c580707110006000311000681000380e1500011642c46140400300012901d685092041008000c00c02d10550584100d0040c03042d402c500110b000b145221003420f640e10541405001e58a01000c071015a200e42d01c4900020100126000074580151140001045110b4800c0c51f500d000d24402e8140101d101e80a0010011071815100c0008400c40a44540c070030340c0b5081c0310140001303601852080c016509100080d007035540910071a201c03150b0341c4104 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 621954946 1250 621953696 621953699
    0x714040f02040e091614060d050a06151107053c040f05060405100f050d060e0616090603060e060904020f121f0e120c0109020d1a10080c060a0e040204 66
    0x5107684c0720303110301c1031034044c110811020841b0720a9004104908401900180c40d003064601c4046c000c14001f410b24800c0da40c0c0b40d0b004103801c040001c403002044101d44d10f45a8010130300d140f41c0d003481b03d254002c0c3c0c452000000a441d1200c81150704d09a9030701104140c003034130103102c410801c0e080d05141c40c1c01c1c0d105281c8110110014040c2c0d04c0700e0300030001540c08000a03520360561510070310142c050402c800e002803904014510704000e03507041c2c440c400c002c08611b0541e00d09005d40b4246041d107000300030602000342c03400b9850340070815000401c2c031864184086450b00c0c502c1c1c550b4182c06001d046c080e05960000400350340b24501e02c1c1c85c070010064401413001242c4120140c888049102a03c0310341d15019084030402454010b85800d4106540588100441300c0c80d030060307560150348450410754880d042c0c2000740c1d843c8404468642e001e8040000401c012907503078010f859005140c030b035800940840034068401d00003000d600b1618241c1c3c88582e05c112605040c0c440a440d045051360040c0000340 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 621956196 1250 621954946 621954961
    0x1e1f0c1b0803031e0a060605040b07020102070902040905040201021c0815010e1513140a06271202040c0503070c08090a0f0b0405030c010c1a04020d060c02010b0906030714040f02040e 80
    0x80082880c040085414480d182c5d2141072055a4852042c0070028009200500403040c0e503a00070180c10340b0500490300035030340d46c0c581c0000347d8003d0340c0540d0074140c2c0c4004210035560103100e422642e01081d845103103103500e21800075040500241044000c840381070b0394010030340d00030040d001c10340200a02d21409201d0545107581035a201245082d9469000c4100260200b040000d0042011004002c0818641040340c2207444c104048808040000c2c1e0003a40420070b403000008001500380d00c61030250101e1203005001c2510582421003041200030420004055070151018078410352160000c0c0da50840d0900044006440340c226024000e0301030350018448907403070010012900c0c29820354202e860080010755040f503400001a01010340c3c0c016000e008051990795543c0b29100824086120055844100894440404180c0546e5640d5100840352810411542c0d200707604400600b2003908040710780100d01348a01400d4050380c2c0b00e401c1c11440010503016907010b44503c2200c02400c1c5071502 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 621957446 1250 621956196 621956221
    0x1203280e0a052104062012130905010f0509070f1808010911010203120f0402040908030702061e100314071703070c08010203130f0c051e1f0c1b080303 66
    0x1003c840b9001601a0b07042c0140750b884013500d0071984691a802d400008210200d040c250960030142d65500410442960b1010190090b2901089a8108007501414030031901c0441d241a0002050010040c400300956515118895030091b0540b0b000409500003c5040e02c100500c04e5020410039219040802c24180540c00807a540d80642c40000c241d80402c001641c5911580c5404203440e004e4a000401c52076180400c0d80d0810b20282c000141c001840c0c40c0c403181c9400c2074450300c0068016a046c04940e002c00030780601b0486d01c41060741041d0a190500401d4a030145c80000c204603640d284000c0c1c400403d1091360007c040960500203a4a0240d000d16102d503c00c20b0111104111903201003200c0d18144240da2080d03107101c01400d119415601c5000e0000003001c001c885188004401240c0b644541c50f0245849900700201d0220b15884070400083e0304450505402264186030807002e803690011f80c501c070040c0c00c04c091007013840540901c0c0d15001e10700e402583d51480000140314104001c2d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 621958696 1250 621957446 621957463
    0x105190f06180e0105060f030c010f0c0f030e0f1002032508070b0f100302030703020d260a030f1a0d021c08030f060409050601031712040807051203280e0a05 69
    0x10020441070ba40d0b1b0040060490310181480d8065002c984008110f500a800780b15079002d05003408030142100c3daa0b0542c8a0510200c11030020310f50040c070340c105040c10050105009001c44201e0740c0d102d0b10b6200256070340580441c03c2e50b0070708108d02103001031220350382c461001500007410300da480e400384c100343c0d000705425100a00d82c04107010019002c8821039814900b52580100a0b002c03c03451130f02081041d110300b090035604448886412400d010300b451030310b010b0f003c546c02c0254440403003440150848698404640b80e40d4148145190300042002a408249100b15000f0302c1d0521140042a2103010418603160b11000841e60101030041c1c01010718451070340d1051490181d6114420b03c000d85142c240024100d0303001c40014000203050308840702202d850110154200b000321702c809c20710b45509039000d40b640d0500280b8801801030a1000401110240803034a02d18144048403c40030424603400510b4201c1d0741c4000060001190494030f421100402240c01c031100074140300d0307280e4412 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 621959946 1250 621958696 621958721
    0x60c02070b03040c060f11010f0b030609030c1203040c0e01060503060901210b06040e070f03020411121602070306111201082a030f120403140105190f0618 68
    0x460300c0001d400155101140c2c07040b40c2c0b21401c28041c501e0001d003030310311402154007038003804012880c0452202c000d1082e400110f52904c808203481c0681800d050030004054821801e0780c1081100075860100001c010031502c1f0607010155482d60703181001c1252300b0a90304a0042609110000074180e0351040c051801102c08440ca580c01d43daa0b100e40070302004511013a02013910005c2c141c900419400c00380e4540c404009400480c041c4201c086c001d0400006400c0031300c180c01040413303c1582094800d90018140b0341c106180703807101d1806240e9520100070700c940c85800345085144500b51081c00070320000c55028005001d42c3c250f020070300c1865045010b0740090310519900009042d54001800013803001c1819250b002c603020040e03074850700b641801e0b9882d0944a00e08452103d10340400c9118560380d14203104949136130451411501084040c000010f10fa030401050054488202000e00c44a03a10504001030742d0740450001000b41c210b07039109650807003202c1c11008002546170009980c5402 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 621961196 1250 621959946 621959953
    0x4050f1204030b0703021c050c040303021507210603050102030a2a081815010b1c060602031902010e0a05070503240604020a090312030903080105032109150403060c02 73
    0x4116020038264000d610000d031040c0e42d0b10021405a501a50090a0300316401c000465089840138001c001d41d40d05454a0b042000001003c00500d42e060114440070f40e0204100c1401d810180e02c024590407041c0200ca1080155010120340f4549940c0210003c55001e07000b951285801d0a00384000c02814040080752140c6042219280d4040701d00c4100f0300a460700d0300321040c0c4455100c50720000c8010550030483c0700d103415010b800342996550341c0c0285400040300c7da80ba49000c030b01212141c40c1e01031916000303040c280f05020720303030f0040103580349034420281c4041c01d582068801ca026000851058110b130180815040901034041214010384c5e206408851074411000c0100840d801041c0d012107006070100c000c1003051a25030010600c0c052180707820314006449071545000400205a81404255104c03c1601019044038000d801003508501514002c042c032a445070403203903050210504140001900c01c00c3d507880004600c000c14000200b40d45840d10b0785080c030018007050460070050710 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 621962446 1250 621961196 621961213
    0x80606010f02010905070b030c0f071b050a080c06090126160905090a330302031e06130201020708030a02102004031221050411030d0203070b150904050f 67
    0x5005009130642035501100030212140fa19000d41e0319a04041c054951650041002ca240100d0200c040c1c81064060b03242002810400c0a40c400c1285499200e6400740d08503000821048030b022a001d6945503054941640c1c5881040c0122648000041c030f41d110314040000c02c4e10b080d105030b110039108600800a0103142646510292031040b080d101c0c055200e0700140c000f41c2d54a845070040d00420355071200340c102c0c45041005c2c51071484144a103a000082841e801001545000c12180400c02e540d1310111484081102590b1340340d031002020044c000c68158603800c11640b08101d40d40040120109403034a808010300e00a480d85c000b0100f405a86040000c400321030f40d0501ca00c1c0805c0700f40814090301d014a1607070790b040181d00c00b2401038180407942100300b074803440040641c8000d40b91408001060328292410400392406000c40c0c5000760701c004100c0c5500f9030000112004d4070303000003402545907500141520780d1861a1001e941000c5980244410414001290404021410140d03078050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 621963696 1250 621962446 621962477
    0x41806050f101a07240c0e0f0906030c03031c0605030d02030a1d030a120216050f12010902060a0e1e09071413030c08070609030807030305060105070c08060601 70
    0x50500b80c84101e0b056481c03110030002001d01c04090f1061002081074076081c550651916116109003c00407600340c03480303550781e2100d044d20744a5606504040c5c02d004241501d0741003c135683e405400320700340c060703401440401c070996001c202e26017004200404403680ea146c01501000003011426850191504200d030114282c50b0105e00f010041c00e0507802503060403802e0208941c42d100c40f807180341110510103d59900c43d141803044a50003401a0030001009070f807081c00901d890803641c080da03515120762000b401150740c2c18103442d02d84001112650303070211020601900420321410001d500100001d074107003a19402c0700065804403001c03100d80d16410810100035102541c1030380c00d43d80c007500744030001e03c0c0140141410000c1007440c2003642c1c00c1440b0100c42c1034811030300750019a4515110002000451020410740c0301414240c94200b034002c1c51650ae408a50003440f40c02801c2c5034a503800924180d102e00b05035182e1940028500001c1130b0f90303030303a03403034a601c01600e15500048007110180804c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 621964946 1250 621963696 621963721
    0x1150f050609040209180f0714091315080106140a050a03080706050a09020316171f0b032107060501090509030d0b011101090305090420030c07080904180605 69
    0x84610181c54a0b15062000c02000000e6018807082a401130149800440c00d0741005080d52185050241640103030030410406007101030120240180031390100403004194983d00b03da841c0c00a0445000310306003400000301101d080d0f5540000c64658a417010004104804441c0c813070780141c090b11498031103500c4105100041c0410702024080c018204105400220194442c0f5889440c4501c00034440c4407a900003420500c10020242c44640c0040c0188641201482600321540e2003000400842042e090002c0d000458030000300d9480d655140701c0c4201c0c1d10b0174001c020f61800a035030a00009607001c0c10314882504000d10039514603280800100f4001801c0c442d4500070b5a05d032000314105100c0e01c24201c05022400245810000500300240403600c00740034110306d8500c02d0322176540b00c881040910045500340c0050f4001d903026250030b04000d0302440100c03900214800f0f0003550f5040c0718149070159202ea00b100035001882c07c1c4411085000c040380710300200344070741001d11580e12048041c0c140d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 621966196 1250 621964946 621964949
    0x1e140a030f110c0a1118010801020702090f090c042007080c10060e0621030d14090706050406080703020720040506090408040603020703020f030424080c1b1c0201150f 73
    0x543ea07200c0c0040e240418000300f4240e600000c0104103510b022421607103114500d40a90180e452a0b401140e28030461804d024a41d0348862a809640c03841c1c94018a52681c6000c0113441c03600840d80d91038010140202ca200c101c110700c0060244654600242c83c203c03003d94817038003840206015144031b0078403105040c0140c6048601c1a010110a9110101000381d10700440019650112619543c4070401400f400984039100d8001400194500300703c003a00a40d00d030041142ca4182c21400c4c0500c45079800006075416a46070b0700c5c00030302c160394450003940240719840018000445002c2151044c5c2801200c90940c10405d03a400c3c449038988800780700000200303541c020904001444284400c034400c5c0c0c042e001580c0648110b4503040203422402d0309503400b517004000d0502e03030020380c00c55007041141000380014080c1340c070b0001c601d09201840c1c003a010744007152580780c840c014807282a100070031403400101107000c0c43c0024221403a01c068020030001c0342c44804420a40340000b02154540100f90 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 621967446 1250 621966196 621966217
    0x4090c121110081609150e121e010c050910031d19060b010e0a05040b0f040f0203010e010806190902150309010e060c160b04061d03180a03031e140a030f11 68
    0x14106d0002450564200b08800c0400350402600c1001c2e0522a00400c6441241120f21000d141c0310341d08401c07001e0945941d45402428814108040440c40c4c64111400c004c401440c0303000070b150900c400340e4941741c0e220703500741070020300c102044403d012021a01d401234881c401e850801a14000f0b00c0192942803e5402159010520305802c1000381850340000c2c40c0d01c41c004006000c901c95000c0010100e03203c580b8080860b41c2d01000500990001054a0b4090440701004001c145080752810980186031032510314070356100c0910a04544650890b80d5145080091546d264500078103080e00900364012043c0c0c00d442513a01103065104e44a00301c400078501c00409243c000f070284c440102c000c20291046546658a009041550040501140347c1105c02c0000d190789280f400c14000b04040c800f80490700c150302c0780c00c003040000c1e0804640d00502c600b014160f00100340c580015111010116560031040c0c40c0044c4030034078550b16500c5101c980864080401840c40d50a03c0d5411a004012020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 621968696 1250 621967446 621967469
    0xa090e0408090d0501060803040b0c070608010302131e090602090102070501080618131a0a05060402030606070b040f0506010f0608010b070b0705070c0b0a0503041104090c121110081609 81
    0xe07102d41007039030965114500803c000b003059030341c41520526690240e8030058611501050340414000c05100c2107000b004146894103140d415600094680c13443c041200c02c081d075440c0e406d4118000e0b2556004050100c444041003020102d0500001961240001c40d0050003104c0d0045115806030000300d02400000c0c0820b01c1307881001804401d46e030b074050840c030840c0284001210014058403440384441c1e1a41040c0286400c1c211409000d451010f071401b44110300500400c0b000b51501e5058a8085810070508041074a940c108551584840540984140500400424180f699202c07200848001e5954051103030f03039866510245006d001001010413070034501240380c441c4104003414070580601900d0040326506e480b001c48550204050f400851004410001804122a201102c3c04c2065030700340111035066981e85020700701400b0380701e41c034544407404d41c0520000060712002d00c0c0c6c002e0030741e04e0506000000030f07019080442e2400b90a810710301d455009244101c1c101411100c609094 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 621969946 1250 621968696 621968707
    0xe01030218070e0f0307150306150206070e1c0615050f1f03150b0a02010507030b101e110102161e03080c0918150a0501030b0303041701090b0c0a090e0408 68
    0x4c2000100c0e224050365450310401501203011038580c00e000701d0b42d02036924001021850303c0a010130b00d4100c4004030f4159000101005100740d0062030f003000c1100121207041c50380c142d4403046854085050400b800151a0010901d0f84580f8500c1500555204849141c4021491000c0184203060501d16200265100006110041c066003140c0c892000302d400c0413038025200c0c6401045034002c040d2110060f919007090100240e01413080c0b100c094002c1d114100035403940400945020740180c12020308901e0300114240052044943c01000b045c5a0000c1d95601003d02142d0004004a0001d49000c030036000e0001c090314000880c0b446103035160b00e52074000c0c0d80f0001c203809103402c0031030965044100c060010a899107000d00107072207a5860b8100085502c039a07800d1040040081e0020313814549440b0444155075000803c6e1011608113001c404d00d120140c0b000280334000c4298001d05c44c0310500244500c2110b000f004d000348550b281d64201e45159150168840b401c001e07030b009003004004126 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 621971196 1250 621969946 621969949
    0x908040905040204090519030f05040b120601051b03070203100501230607152307021005060f1918020702150304141b03070b0315010c0303150e01030218070e 69
    0x100d03802400140b0015407170004d07445160400e640d00b45c81c0704000c0e101000000800d43c108000302110315680c40c080b400c00d03040c030300702c0c1c2c0440c46881c2040c0d00000e006e40010321181c0c4140121902580429502c82c51801c07509062a5a03800880e0228400c2c01181520201542144a864122039240d042080f10b0107400c203440700b4000001700d00e00e8100004000030700100e21841c0c00d6040001c80c2ca540003628100000d8400c41d4001c8214a01940c06440010720110070360010724100f20380c03003010001425440301000210440d0b400c8084540000d05072035086103500c9020030702c800b100c4001221180182c0c0d404503180491081000c002d5011070070303401d80070220b150940910340c007522a003c200201400f401545141c507044049900c0e1065003040700315403071b0a040c440c0c0303001060290941811410040c90600385a1030040c8940d04109000340c0900515209421441d14483d094109501090b21040441c1001400340020382c091140720070600c44040078200ea09210b00325640d10035240d80706080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 621972446 1250 621971196 621971201
    0x531060f020703211104171b37090203070206070905060403170d0608030417060423100513021f1211041805060406060906050d021e03160e0409080409 66
    0x6a80b00d58150350305e940d000c4680120740204041d0144100301c0031400200c500c1c491070a24a00710000860000032408800398a804a150b58006012594140c51f003a4010011104a1806c0007414014890b404005100d041c9640114024403455090311174565907601e0945111115210381c54100c0380400080000c152101524103401818080c52441d2129613198601595501d810030b03c526080010200001ca01017001e0003180c502810140500d440c0070f0b01e0303130b000350704000c00b035107400c0318008420800480042c00141b526080c00070082140303040101e80f0a0041c880b00208030300850010312060205408100f4003083c40700c0943e54552600001c40c540300103043c5141a514040030182300124160743c3d00303403003000d844190810000355031030081d04000946600764000c00a119011a0601c00c0c02d40c00804c40e0a0322a00100c0941e03aa22800950700042510781e02d4121030140102c1440405070b202d080d002400c241a680d100344180c52803080004540500c40001e140003010402084001d103241c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 621973696 1250 621972446 621972497
    0x7050d0509150c06010504050a2d0213080114061203090409020a051003051f03052e0c08040204060b09060409180506040803010e100e07030531060f020703 68
    0x6001c81d816901c1890602c459038114400d810700343d0300041c0060141e81024404c4031f80c045584a0b0601071103590700b1b003000541c680488000340d4654121042720049206404890f179140501841520302d5603141c03031060003005160743c2c2070b03080c9201c50085403d07860100420400000402d01842c5042d060f1020040200440103040345c1041d5420000600750b40c0700901424090b45980380401c262401941ca0045030030007203001c00141c05084014008200000b4442580900035040900c1c010030002640761144440051000003074100914202c43d80c0d0f0200072280641c0c0b085d5030a001d07050303e48108440600810b17109540004043c001040220155000000841c201281c808a4401680c942c0e5050a004540680e08520000010041d8110480c0a943c0c00001d85a504c1e03c4a401c0207c1c803581400040e003213000701500c40c170118003d641018a1519002c00c1b030088204a07020307201207403c404008420a581c00f40c034104008090341002e0003240c41c0703a54181d940c0345818811380510050100403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 621974946 1250 621973696 621973699
    0xe010c0b06121c02010e2503031805040f020d14010302030607120e160612020f03010303111606020d020c010206060d02010513090c090906150e10030b060d020304020a0501020307050d0509 82
    0x103001001e00c2c00380f440883c07400381d074666500116006c0303002c3c4001844c0400d5800300001041809403003500400241c1e54290030340c0c0d810318140904d12032090050a951440b500a60b6001d880c15210700042c0d045039006061126006100b440750700d00102c007440803614240b102039016000440003940b003e204214402014803001c000240c20550442100c0c40c051141111151401d0f0091041c00602e80000350312004100303068040d45401d003469441c2c880f5002c10701c4000c05001e100c40f60f01111417018091000c210011401100b004d81d07483c0c500030b40e030314480c01f8900054040c1c0241c41d803542d4404a0104c0c803805c0c02911031042600e055004545660010100151070406083c02080c0c5940e1802020102c01c03060780c2d96940c540c02c0c201d83d0000c07640c19621440c4803002e641c0f81e080440d50050304105c9820310448060752043c01a0400380c2c00390030f41e000b990382d01c18000215040e02a80c40e6001d0341c01240282d88a0b007400f07413a20016642c1e440352400203001035009807031000c021440b800080030700100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 621976196 1250 621974946 621974953
    0x82401030c0c0503210f040503041406040503030c0705010801090e0712061508030702040f0218151905041e0303050d02130e0108030c0c040218010c060212040f030e010c0b0612 77
    0x40b15200c1d94195042214065442d8001109505100b004615071039001025202e0120390b5084c81e5882030303030340d200b144107401000d2409681e40203507503a18426100103250242c2a640d0b03c0709030300001c03501c50b580b80c012540130504510022a03008941d11400c100642004010301a06040c002e403000c4072010700b001100c48a843e1f9040582c801014403074840100080c9000307648401c41441000b040d9107003403210302043c0303106105805180d001e41e100600d802c0d005590b211112402d40100032281c0c4030312844220440140c1940c5210701c0d80c8034000308100d4404c284034800700c4416141e10000d00c07140e844040c00142c400d01c01e00a04103403a070b0040c040c5c4404030000c26003095136070380d00383c1622409a2101c0d0158001050f00f0603072a405000307402000000f19001c6160601c505a2504a00045000f041c100501c1c0c3e00b20030301700718090381103400350b141403104108145840d162072081a004100700302c00207560005810318a50040c01c0400410764004107500442c0d49100034428203c0d4440b652030080d11 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 621977446 1250 621976196 621976217
    0x30c0c07060f0201050c030f0105100309060e0f070807050a0e150301110d0c030c020d1805031b03150606030402060c030717030718030b040b06060c010c02010507082401030c 76
    0x10010000d5000518039610760b48542c440010380682100c600501e808000c04007001008404035102ea41035054810071a068026004081c0c81103004007049070303009004514051480105074400500c411400d4001d8049620145c1c40b150a5600e4080511900c1d4100e80908003d000801201d0b09156210034030017000d4540c400050002420f4035a0000c0e00020314200048403c00b0403042c1c041c105400e5100e0500340f00040144c039000b5511000304108030100080b00c0441c03c0c1071880e1003085001040000c08480090844940180702c680f59044994440d1203800000720855040d5104a17105540003484141159216028401c0540c4440561a507600080040c00c00050a80c0d62900c41070080403d2181c407440d18610142014490780c15001d20021060002c10014a64088660780590702c58082611a01c0306004113019000340011806c055081c81e00e0352004a6055125038032a02c0c003503807410100e46a200301d51240c0c20800241c01da1540041c020023030a940260000d660040c6070389000b99512 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 621978696 1250 621977446 621977467
    0x81209061e04031a090d030b040b1216081c0f0311160203010b010c05060c1e0c01090c05010e060a0309110a080a0203100c0c0b0402180705030604050108010b0607020402030c 76
    0x4541d0910942040c4004101442403000d5040c80708003044207001d60f4903142c2402040075640d042e1003002c003c1090340301d1300e80c02d0058603160044100307000054410740285903070307803e1162070b000b2004007071000c041000000107500348000741640c80410322504402602d100f5550480b03000c00c541260509041d2549224040319110304006c20300070041200380034086480784101802c2d0740c1c1944184d810452080d4115000c684082002a040841894026900c2001c074104000c5188150324080001f0303c00325880c080410306400c401e646910600c0110b03481921280156180d0700300b00e210301c3e0030100c01d00ca003031860fa0182e40310b8401c003400759240b40400c0400314005100400302d50460b60796a0005410002142010844084440300c0900140160301c1998001824042c0d031030740140c48031000740086029900c42c6003103a020340841c07046940316490004070240c00d55005a54036400303a0303c0d0100001c2d051006120705050311700010042840c00c25a230302000003a41000c1c0208039148003c0007014080d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 621979946 1250 621978696 621978727
    0xa050f040905040203070e3c01060c0c09110405040507030b03010213061107140607030e030a140606030d080a0b0f1c0201120213090e0c0325060908120906 68
    0x10000c0041c049500c0c9400c1c410726040c240701c1d41c8440d02503c07c04040c85005d04684811032600c11207084c2240500c4003d00345003e54102111288609660310b9002181c86648180003450b2140030b55101160070740d0394405502160146c400018a6050a101c2480300740b0341600090380102c0c5030326021a251600301c000a003241e0100e000100c044055120800010741c02000c4488625070380000751010702d03c0c0505d009581d40102550a1041d03000043c0c50b010180148444145c02c60082c0032909605218500b15030310810802400304107124041c001403030707442d0002e560030800c07903640e0303503458261100b0b0b007071801403d14000307050f50000c043c2030640ca943c0c5607840c060700714464401e42c2c4d2420500c01c1c000940013140c0c030b00700f203041180100329a0040c10080030500040b51302c0008001400940f1301c117080d040c101a1540d503641401800300e1501da0514030841000b200302e80c010525000c99681809450300161f51040910a4010141d500e54070001503024121220016216610b40380c4da003141c5000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 621981196 1250 621979946 621979949
    0x30703021e0c070806101a0d020451030b06031608010b0406050f090a09090b061f0207050910050307060518060406020a020d06060b120108120a08010b0a050f04 70
    0x3040000b0619000b20a000c1001038003c01403000a00040e0030700040201c04503106000b84241d51044038a054000c3c1e02000848404540d20002103440719201c4480d00450000400e0b454509510303508145812410038803076480c0d408035000b110a00782544e80040c02c400300a40965410f056640e0031180141c1c80d410001c62281c3d020340086c5c2114403041101600c2140d06800c80c4c00c1104041c0001d10405800c0000c65840b003205424140c0c58403040c10002d8100100740d007098040e00d040003070340010400b80c800460b0203a1001c8405a1200d08283d400c5168806030082060050780314032820052810600036480e08a0807030b0310300303150103500c3d44082032400c5029480304000400c000341710201c0600d00c0480d1400728008440e02c43c601868044000d5580e40c0c10b11000c0d104d40c03c06c03102a405c1080541c00703540101140400a61101490030f00050005024130490500c0c6c0101804074403a1501d00d4111190108251070301d009a0f400c0600c0303506d41d90800d203480070034030000b0007144000d214207802410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 621982446 1250 621981196 621981247
    0x10b030f15060f03061806102f0d0807020c0f12030408010c08070201060e010501120c0e12030c0709110f0705030903010203012d060207090b010306030b04030206060909030a0e0603070302 82
    0x1d03a02d08045d03044c0040560340c11501007101415070144002a036540c0949503405946107406043c840c1d244083c103d440c03001c104651008000c1d00e0b00b4505082e001305080c911480c82e80c41b00c100c0f694400b80140c0c1c0b51540c0c03822081c3e100322810070800c164500082c800342066440c6003141e0400c0d4a4490070350850303c00108030360104101d4802c01401d02d60900a19014000c4451407560303d524090005c0c0640c60161280e400f00d40d240c02448515030b100704000302001200405402e800000081c0c0181c483c0d101c110f43c1c903001d00403942e011404001c1c5000e031001ca101c2a40c1d40b0741ca0003200f4200d08010785c00080044030380303000c104a070040035a824009907001c1c0c8407150621000312030a0041283e03000e20b490710700400313402c8888104220741e000f1929404480203e6008030749070710fa80004034010191604010300c1d17400d4200900c03080c11760000300c00d44210002d4400d1002e5440382e6591668134001e0000c582c00103015640055103a06090000d140c00c074816040160801c5210101d150740b0401c03406141 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 621983696 1250 621982446 621982477
    0x3040209150f460609031e0f150506130c0e040c0507060e0102030615040f030305070221012a0804020607080c0319090905010b030f1506 60
    0x951400910a5030001c0c04000344006080c0c159010a01d07541104100c14407503480d43d4040300020f0015503481074a0040300d010400014041002c0c110001404103201200490100300851031901070b590348002d41c1e8100d0b000b48410750314440190700c0c0d84064042100c1c011404510700d0002007801c82c4040c21847c03002c00105261901c0d405212a401800b400c251a8600f01010456002d03001061821016001d45001c03994051070f031010b03206440f0ba548000c01c0ac51900ca4000480803065020303500600081300c180000b4400d01c00f607029a40030741d000c0c4000a80070081708000103402040180300d42840031b030810754a04d6048858462000c80403089000603516500003c22940107150901a000310720700c0080c0303a05c040d10307100508040c80100000c1c011140052600140480c1400b624a215810002ca81d601c905156084203c207005001c1900800c0d104000840c128100f0f000d071a050b5a00d140e40c180c151b03940e01921100025002d1320700c1c10441e5054440281c00d45400000f0b04850b290101c49 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 621984946 1250 621983696 621983701
    0x40302010e120f0304120212270f01020d081b22050a0f03170d06080718020301270605061815070503040b0309030d090f061505010e01050d0b040204090203 68
    0xc03506003440c201940b05069400c100120708684a841941c2c2c005800c500303425421075600e50140e140414100c038081004001040c00101d410750f0362507030181d0004508000026924000500c00014040c41b5500d0240e0000241320216603c42c0002d181d002100050f200c40c807610804589016500840d8075000c00d06614255100d5090210f0b8100002e01040d5000f4000603d01003040403d5085130000804005040321a92440b60004c800da03200b2200302c0f9801c1004a41d607641c0305965500d288621005800e80c50b11202d1000240e00c2541c0c101d4107500c0d1441c801d050b0103100100d134a6003940c40c0f10046c2c0d03643c2a0100d10f139180c920240c0b0400c030400d0030089541c1010420464411909107050114407820402c0100254004c030a440440e074200f04180c0d12030321144542825400b8140500400c54034180e556014030000c081c080a056000b0b000402c044000d0004140701c092060280e01d01041c00501c588805511842c01040030103040030001408192070f50001e002e991055000525181c0c02005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 621986196 1250 621984946 621984971
    0x6030708160c020f0d03120510050a080a150b010c141b03120405012f01020d0b04020a02070e090304031509030e01170106050d0204030b0a090b09150415060e04030201 73
    0x1841c00c8215894104550011801c0c0e00180000d4104d9030080c1c0100848102d184c01c00d4010000440c0a0003080400d01607031070503034031208560780a80b00701445012011302c0080e8910011640000164210021201c540070602c027800181401d140d80c681000405807020000c68443d4500c0b81c845541c00b40a07203200a035621800c042c42c00d01e00da180380703e5040b000c0d81503503100b1120210380c02c96100782010000d000104258001d040300304601c03100c1c1540203840303d00d500407040d0300600c03000880c40307000c0098001c0e950a02040380a00956003000d6409030303200340a002c804000c2d50b03911600c841c00f140d162a8030b9030340f012040802094840c104607115001c1200f0580c1050419603c84000e18221011407520100031080500601c51001030180000784200500020740443e0050350f0042c042d102c2c0e070b0034108101c07001040031010031740350400e2041c0800e0040750040303480d101c0c682e009189140386403160b03281d958049809000515049940310000640d181d5813100300e2303201e00d000c0c3c2c0000440404580 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 621987446 1250 621986196 621986221
    0xb150d050d0807110c061c020403080c010c02060a090b0601031e0606111516120f02040803130b1809060a091d060108030a0801031103010e0304120611072406030206030708 75
    0x13140c1c669541180b0302c0c016150300c692003030b0b8251b058100f59250600d070b40c8140b928000c0c4500e4102621203280020204020b0905401820320050590308075051903a44117200c030f04646c801c034002411400c01c0004984190304c290040051098000d1848a0018000351410220350070780e4461800309004c0012084880000d010080c800d0701c00c40c02c0a403040c60207464041d1858010b610541c103014000381d4146010b4560b5000612410480c94110b60f199110000d00da070301e0704481081c1585072141c10012640c91181f50030b0300d80c0768951483c0c3c507089800500070400750300c00041c82c494102d02d06010000b401070b050b004007208080c903030f000c400c040750702030303040e10700300b000c140c11003009603101b00140101194840ca48504694020017030019514804000a02600f103455203499180b05c0441c0214030407940494144035a40300d007200300000c0c01c1c00d1400400380c1c051710340c020701090707007140060305150f544000201a8103050b00300001e09585a9000441e80e03001560200c0020303c03944100820800c500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 621988696 1250 621987446 621987467
    0x618060e0105060a270f0608060405090f070b0f0904090c081e0712021f0905010906020c030604031b050111090f090f06040c120608030c060f040b150d050d0807 70
    0x80c0e8459160110b00781001c2d014601140c1850b014928800900d5005c99904902e0005002c60a4465070460f6544070010403070341c0180c42907403180f4a0240071a000f950700190504009a00350b002e464540e19007041002da80c4c00000c41e09400d2078082048c2550342e40c0e68881d00600c60b00c0f80c070a000e040750070070250038508000d08952909108042243d10a4500005201400c0300d04040480700180524804900008124000f01881d000d0408258079004e4101c030b005019078400303a8521a40c140d481d0001c03030340d60100701340d1160542c0101010030003013446011601c11121841842c424448075076079446085034001da04c240c05684000c51a24007518120300d20060358a8200c603c17410a050106004d0903d01c1c0240429105682c3e80c850002c140340503d81480c1030b00301e0355400300040c40e40c0304000ca413a070b80509840300e01c1d4011540094150400384106500850b008000303410355503280e03051200013480040c00b8650100e0001c0940f000a081040301000c902c0d003954510b4141c4c1088e64001d01342c807140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 621989946 1250 621988696 621988699
    0x20091e1801200a031808070b150d0606061b030503010512120a091a07030518031e060610031e02070302100203130b06030714012f0f0c03070f0b03040302010618060e0105 74
    0x18072090313101086c40501520215600300c1465502501c50302e1010030110305011550350000d03a006001ca05001c0b01da80030000b25102d0b03446d4000803e1030a8012001601d000c0740c01004076006100510140c18034140c00030340308803c00121422848030180e21500b50b08035484000000362014400d1140d2101c21303060705684007015142e941000b040e42d8000d0210b010300a550114603035051140030f40e990f001c107c4403a80d001e0414804650010078404144c0b1a80c0440d0081d0081001d40e05a0313506603c20700c14000903a080d00500e0181c5151880c44801a40c0040c01c00e4045110310942d41c014400507200550252105540c50204081240f502c4e60b01c61000828003880380d044150704004406c141c09881c070480c1006d207460084036580303c0b0660780114091005218000c0030780d21240c00d8100000f2404048040241100c14000c0c0d036508040c0c0c0d40c2601e0094515070b0f00300820401416440304007454016200c1d0000ac02c016460f440c0251040d084015070440c0d8607141c11081007008100300740766024010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 621991196 1250 621989946 621989981
    0x50d021221040c030b07030212090a030f12201c0b01020c01030e0f01060602160927060209090420090402280320091e1801200a03 57
    0x90341d8207404020070015400031408040c0c40081d0810000c04040c0c0065544252080c0450410542c010000d4101040300d4007828101004200d00900002d02e200d28142d259513100c249600d4001c04442c0001526818440035031100000012041c100300d04822142c64105110f440d4074400301c441054240802c100c4209514000c0c0e00941c5982c04500051602020308012940c03104070000689090842260070000e5440d0240109805034045480811090700c1e004511003e511040300d10111502c148108110480e111480003d400a164500031210701840005051082100104140c440200c1e4215518180c1450340e4422040801c0b4440b4101000d80f1303544402d14150740402d0004ca11806440f02e9440e0768003004641ca49101d00ca140659401440d0640b0440c020072543c1117500b80c000306da4402d00071040012080043c40304500f184c0410614402c02d1500c80c110005080811030428014070354856220400c0d060b0310161940030754401e40300c26550303a80da0480090444000d24024000c3c00f0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 621992446 1250 621991196 621991207
    0x30c010e0310140403080f090714011202070c050117090a1b210507080d0801090207020a08030a1d0f010e0d020120030409141b0a0c02120d09090b0a1202060f0403050d0212 75
    0x80000f491902b41c8010700c2c81464459030340401a130b40f1f04140141e0403245400090b030313402081000107103003048881c00e1b02c0310440285400009107903a030013110605159801041c003d0041442d071b203040b02c08200800024504035807034002003203103068440d4903000c840310002c03850410842e04015001c0204400d00140100450300400241030700010b118a6141580100c3c481c0159a40c085d05680180a140f04a03a5039020010b0b0180498800c84213402c0c68141070b480f90b5400d030a102c0034085545005940f0100400580d1007001a18401520700703a04000e481544115101104d04240314601d451000941d141c41c0703030030642e4064441c0100495019541401400003480b8000d103075045004201400944903c00c0400880e000800403001a40c00b50010b9200d10308188081750011301d403540707a40c5261006450346512030954182528030354006100076010031004155420410410344010155464000c2c0788001e0043c50300303e5001134a407600801c50803e612034040000d01f0031030015000702030506 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 621993696 1250 621992446 621992461
    0x203120a050114091f17010b0306040807230106080a060e0a1a04051005011715010501140c0f01110306180f010b1810020f07060c02030c010e0310140403080f 69
    0x3940f0541280039040020124900010401d403a0707500d800003d4a0140581c1c2c2c99200c42e0841c00da4143c802002c1d4078203908101c4609002c1403882c8619000110b80b45410840d41d200740c140c000c000320a40104890340040e000c18030003805a0300c028070f44c0301c0090a501d800d60034000708456201c100c001e88c40d4041074140700001c5000303820f10280d00c0245c481817102d6545080c012b00300b0440b50503001d2a94588030011404461451184000011305001c4544244c0104040100d82c0340c03e0080301e0200e0b161001c0245015040e0004068030741800003540d044500880510742550740c001c14415070a0b2001c41006028204036581c541c1c00390038070903e8401e500382140000c460382018016038502d0780e00022154a003140e1542e038148040340140125500c0c50b1209002034454194460b5800d0501590100141c150302c603840407220190000d02a101c01c3d81001c8c01542c2c00c01c000d82d105905806400541c182844940c400e410481d00b004803040c84620b4280381c010080d490041c514121140880c0a01298 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 621994946 1250 621993696 621993719
    0x3080601032a1413030506010e07020105100b1804050a0209120a080a0e0d0212010501031202030a09181503110f0d0515041110051306030b011d01030b0a060203120a0501 74
    0x1405010300300f594103036188140d90b48940c46407000900d040c1424080000070440c0c000751240c100c40184107000d225031030f050000c900742da9050f03a001c51440c880c41d009001c0281c07007000030000d108204c080301e6240d0b07480b2400700b019204101da00c10070903607003c00c449041e824030096030a108911070003d880d40b403045954101190207500c3c4840108415400507003280d46400b8045801c00e90010a03003034200c21001a0b80d4003800007400308448641808485512035070002050390101052034840c0c1e1484d078101500c0d00b4102000000850046868441448014800f041194003450084409a4000f100718083c0000e00d40d1152415002d115000116070101710041603101d48202c0c01c16644500351181e0a00640070f901011202c1e40c0a4280e081010b040d0750410700406c2c2201d00c0602d698040c3e0b9440e034095040340d01300e0381180d0200305852070030300141e00441c0d006000340005040001c1c1c0c001800b404900041c4054009102507400090540c1503c40400c0220742c1c00380c0c1c101c5003403241d0341c1005c403100300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 621996196 1250 621994946 621995021
    0x6091503060e070c0c09020f0712020f0304090504080f030106090e060a0513230a0c1709070b1e0a0c061410090e03090405040609021f0905101b0308060103 68
    0x804c240b05005204000801d181c21008005400c41035403035000000e6101d05c1980310800407140368145601c450101c500205440905054242c0918101032910780c0c283c000d840c1c014011508624100801c40c060711901c40510301070040d82c0d44022085041c03601941a0b10b034060070444c4210000002041540c1e50045a030300440e844410106200c9030080d42070607d400304684200c812101c000401c001410340ea400352140d40d099a48001940009105103200e04105561303c0c4c070950456038080c0074a000840c0107040a50003101c0c04803107039508141d401c955070494220742c00001c0d05415540300748007280c0903000c83c0b404800b03590011030a1000351058843e00c2c071b108121010303403a6100464050001d03c10f889a800000d0414451841e2034a00503000304401c0c1070407072045019008140442d100c0d04480b600d551140d4882e00d0046040208200782041d801809004210168250061044440c003e2218a61003920344d0150b0303041c0f10001505440e110420b90a08000c8242e4841043c000800d2604 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 621997446 1250 621996196 621996211
    0x606040302060a0c1a0a201207090e0109020a17251403040c06140307020309240a2a02010206040b07090b070804061205251806091503060e 61
    0x581c2d801c2c0006098540440044001d00801810a51040c0c0884495102807080c1443e881c01c01c426210005046000900d059204450a04c00c0c421400c2d15507a174601c0039006016414400c0b0f100b40c3d6100310340c01510bc00d801450380c0342c0c3c02080840c640c82c0c2003086040c10014034400510b461070410400c4004661014940ca40c03050301000181585000f078030300f00d40c00003207000c200d5900d1030107080c402c089500500c02d4200090b01007a501848207002c0056034002c1c50940d01a620b4640c40310b040158543c04210f04a4650440d80d05040481109200402d03501d8182e40f1514000da000c3c43ca00c051000c081031528480f842e05440180040c1e9020070b9950b0300c1903026009006070303162140f04235040082c0f6044005015000a0075106000d5000d010b401215400d503103800c0c4c0985c2c030030700300300540302e0a031174000850403c684d003a0304050081e0620030003074003680b03031904000501240c13103040b1060592092001c034045120510114401000305500071065040c03d200840c80c24040f040b1140700100801c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 621998696 1250 621997446 621997459
    0x150a1706040609080c030a0c020310020406093b0f010509070c03050c0f0a030203030406051b07080319020a0c020f04110915120a02091c031e02030c06040b0f0705030606040302 77
    0x4102902007502c0c2c1700700c0070504503a260440d5201c040c0516901840582c40b82c0301ba0144007001c980903000b19019a950799942c0100d06251030300c82c001300c0360144055080014000340780003107018414101074032800761f0075415426040400e40a2510351068002d140100000010091110340104480303903030a9151810a960b49181c1c0e51b21401c100341c0184160403805941201c000340b50380007000c5c1d8080d5020341e500700441d0301c68000d00300d000305414210003444c180600c58030000c20000b502a580c00b0054405118103400120000f80480e4001841c030004192141c04100035414025414070725203c090f6020000301801c0b4108607000e0150940c0c15109503038424144a00b0b4001c00c0640e5a118040c2d0303100300c1c00b800e10301790450107500850007940c0102c500c0c3d42c0d5421540460345491950300c1d050380712040c2020294003180000d00400c12050b041d4801007108090412041100601c6280545070307000705820301c0032040b91003540103007908041100620034005255281011101104d0741221034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 621999946 1250 621998696 621998711
    0x510030b06121b120607050301030302070e070e1509040509100605060c06061c060213061e092309090615060a270305011a041b09030818030303150a17060406 69
    0x280412400744e9a10b030b240c010700080c070020503007000186068a200b90255144284ca901d004007c00608a0310080010a034410001450130f2500c0781c00d070751650558980c3d01d000c66100106040d00e50980394040d5075841140440e1441e0840d11601c005081e08961031032810700c40d926160382d901d01c05002c1c603210319400360051240354000c4440c04c000a0b41310340b040d51940d003800c213403c021910740e00c21040881c3c00c8254002e104090341e0003074a5801816140c1d0401282807941c59114000d40d10242c002040d02a01d991030240d41e40c045003441440320030005d001c1c610f42a141c4260007070324240346078018034081c03142a405540090161080100c1c40201d490380c02c241d030002040c451842d91002d00301e94071b05a00c21080010007201c1e0704c10258180c0701805a103018484164080c40c0c1503074a600001c0d440b010034400070300068001d00500a07600d420002d010306000001f804c5600690b95655001c10000000045d410501c040d00d00a0900561a60036525400d1845445140081c001400903551300d16 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 622001196 1250 621999946 621999949
    0x190b070320012016120302040311090603150c160c181103040b0402180a0c02060609190906140106020303010303031107030909020703020703061e110313020d0311010510030b06121b 79
    0x41340000581050303c0d00d1142c401c0d0030020300254002d0209440703410070003003410103504004130440c4c01800e0180080109003070341400300d80851000f030300e0002c01040821000b0550000c880b005241e00e0b01a481510155103010b0035000d5030413a040554400034240307031462181d116401306a07a4440d130041c41c101010341c0d903031001031203001098510248505201c4248640009139071702490110005400302d44594030340c1d4042106902080b11003d44662000202c2601c0c0c1c540c0350000829280709a1f008503101e070b001d800180340c0c0e1a0981041c001a0300102c010003c0c1603150160380006c0c03030180c010a2078007526031001000881d00f4001c5510550f0002441b10400d4400c108581c0116040181003101c0f924603001070107002c400300480b8102d24100801c40c00c44c0c001d500c0c00c43e4018030001110802500e06a4217000320b1080c1814254140030090001036024502030151901c20041d501000f10344600b5444c0004c0c464030058143c2c1d000e0307402886003100c1070308005081038201c0d504524000f03180c0c10303420 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 622002446 1250 622001196 622001227
    0x1b0f0703120f0311040b0a08150f0411090d05010b01021623061902010c0e040e0a020d080d050f0412031404080f161a01060f0509190b0703200120 64
    0x81044184d200005800941042c0d884041d10100da09580e9140c8140c860b104940c881d1000443d006071701080c1000c4401403442c1ca6801559041c0e0036003c1241010a132800203507010f090240b0076601a512a8501740f25507a0500c81034001d0340c88040b40302995801c04050002c120780030303000010580070b5807180d40e40c81d070755000542d0b054041c0c0100680600e0303061800280030b083d4407502c8401095010041050070b00d401d0203091510b220707070001006d105807641c081214640348102e040e240a1010054566102e050340a620310812a5000c01d000505142c9001201c1030300004400c1c0c1058903001e41c101c52440c81152a036045078210b00915194111800b0285807403150a2500c2070a060400e2100108920002e01003c410480d40c401e150382c0c0e130f940e0b00540790103c1080c0791500151040140010030310700304d043c481a038401c510070f010070161035183e030300d01e43e610100c81a0081002900065140c40c6000c5039881558080310092100b924251000c0c0e80060050082106200c804181d811003c02400e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 622003696 1250 622002446 622002461
    0xa0303080a110c16060305010b0f0702061602030304060306180204081506010e04020c06010f09090b0c0c190827060a03020c0f0a0308010806071b1b05061b0f0703120f03 74
    0x40a035030404080d40044e00c00c0450070320a100109007007400014001c208041644c1c0440300e20416280f8110090b0300b0480d899001c0c0c11410520550b20708110090384040000e0f04c0a0075094900142190a0070006418400d400103034a40980c01000305001558000c03601c020074034024100e040c0561039143c01a0b8040b4407403000756801c070b071001c42c4070f402d00000024154102d80086041e0801d65885200100c03d445413000301a10703c1d43c064021403034205143c0e00401010b884681901c20842c040081303009414844c11301507400700743c01328448001700269003c02a000800c84106560003100c94040b0b03040b4010a0059800c0c190b0102d40282a1401405282404079030b1006a071007541030ba1501901c040e000b0300408046119450001e00c20b103002d1090140640d2400011003104030981e51342e01028010500c01304002810400d00140c107880d0003000d4842c81c0c0b2882610440c180e000c0b41c02e00c1c500040d6000059142e4010482000030079401d501e4090501e10501d0070060076030801c14198040c0010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 622004946 1250 622003696 622003717
    0x3110a08010507020d0e1507030804030c08120105041a090c0913020f04080f0c030604020d050f010e010509100501030b0a021e04140f040c09090203070c1b05030106050a0303080a11 79
    0x1c11040000d140d44c0892a02c144c10460f4948401503030309075080c4000b0004600c0b6074840d80004102100109014068a0364003901ca8a40b8101140d107640e1105a41d4125420040001000b4801404a89094000d00403850040d1844030088100180043d01001c005050789041480000b44810740b602c03000d2122186040b10081556118041130301038002c1c0d03010340300d100e20901440c1e446200110001c00d210b0710fa214001c0c01080107071074135000c00001c1d0441e144c00320340d170348660f40310002203003002c0c0103042170b07000094000620391609544aa04002407104040c00b8149400c00500004000c1a01250015810500145c884090031010300c0c452014240e07503c0302d02d01c04500012010544205007628250503141c5080c00040042403000343ca008501110200e00c12007401e2014104a40c051a404540b515080309503000d6602ea00c0c4a070070985070110240aa01501400141024015031004000a440603644070b49035403002400000c0184c000c1a001d030300d0300c03a0062001244401d407144040e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 622006196 1250 622004946 622004951
    0x40311010b030601030f020307050a270605030607030504061a0102060f06040914060601090e071b03142802120a18170105041a1e1e0c1b0307030903110a0801 69
    0x2100d0410306d07040d80139208200d1007803261450103e2181001e01e0001e044680071515138017502c5501c6401c401c00c0c0d66100580d40130130740d56000056241d9082080340e00030380468400250506050030110162400c0b01030005188035080904c00d07a50340c3c0010580d13403200c412440d031019a240c480c0040c000d0400c200000d013203104041091005950b010480500031142600d401040b1540c030010500304a00850f0700f54007150540443c103040501c1c000300e43c1004d0384245014070300d03481c1d0800e00da100b94100810300e01600300c5000b0000004020340d41200d088407050b000800803281d0a800c60752681c4036442541c0700700705000c48081c114010b10071240002d40303040301b5909042640031611074020542118142c0e0400000f001c055240030945080c2c07400703004400640c00040180c1c81c5251070802004d041c00303243c201007040c549001904c030340e803c1d40684501340b4695982c2010090508031500102c100d851075410801c1900d0000740c0282509040b01e40c404082e209605c008800240b120010303900c1401d0b50f50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 622007446 1250 622006196 622006199
    0x270306040507092901050d090b090307060e01060803040513150b071505390d0c12110301050f030c21014a0a0308040606090203040506040311010b030601 67
    0x404030b5440142e0b0600c0d1000c00c0400c419242e0f106800507056049101075503683c2011044e035111b003000303000010740794101007440401035841c241c40030b0742102d041617560004202d103070070890720340240140e44802070000d12a1500300a11203403a0f12a620070588070700039031007403508601a01e8110702d0550054040c03042d01c1740c0c0d0b502c0245070568041002281c2c1211600c200795240b410038071695000e110001c500e10300031002c001030143c8200c200d00302881c800796207004d2040c80c400144010700202041400c00b088498800700050046001e60303c185501e41d060011841014220800f07603411200200c4040c3e500702c05070390100c2d0500384000f040c10307080b410700b0000200100c880090b6500100184008000c0e81c06118042c841c11101034420403880c81c1d03902c0700e0029501540c040f0040d140380054401b102d1101c82501f96292628079201280402c002d00204814069a13100d98070080c12204000e5145151603640c0035154500144002c082c040c46803003180c02500f00750320240450001a04840255 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 622008696 1250 622007446 622007453
    0x70c0e090307020901120c050105030c040f12050d08090a12030b1e090606270102070e04030305070f0f1b150f14060303131a1603050d1a010527030604 66
    0x1c0d807100b601a405040c8207000001c045602040b0700d95039903000707000640f26a0401e00110790561029207070400c0c8081c00e00c808511b041000405600400465110350907890b00361401600f80341004400400f80705c000c000700702d0419004640990850b034840e01c44244821500c1c0268018001e006e080c54004002620020725964010050104507004803076a41407076903980204503091103680050080055041842c904d80703c1c1914011461005c140145c48180751103d0a228182ea8121000d40c0041d0301c40c0103000f0b001340c01c004515040c0b80030b840d000b01e030f000685078080c260f510640c1d80700d601c0744015100b100500ca4030710062100d0a10980c4148601045541204003901c0c11010480b03c3d030f100b55010904034500001152060340106141041070741c504006000003414030303030105c12001c0c410004070002d008844803d4048074400d4076aa91660584583c060490305040f518144055071240001d8080e03800405603011049202d86d88a0900ca00492020f010300220814503054030071300d410300c02003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 622009946 1250 622008696 622008703
    0x60912030a1d0f010e0c06070602030606090409030c03030e0111120411090a090b01140a030803090a060c11010b0a050108011a0c0f0a030f08010e0a0c020f06040302071a1905070c0e09 80
    0xc00142c00081c010b40c0c0c040342c17010780c4a000111005601000c00c101d1500041c41580103154407400040c00c19050850071404502964030600c0c080700000c10090380c01e410107405100e1110500030500007000841d210619211103072085c86c21100400011000041c20483c08510160381d034000501900c2641c14002600009401c0340c2c64211030416540d00003145200d442c49020580000040c260032445185440d102203070b600140458815000b0540c510011540c1402a00c0081d0780725a15585282d40a03454182141c24281c030031441a074410b581089141e03804901241505c0d52241d03481c0401000074143c4441c0c0c42007070007401c04c60040308005c14401ca4042a80c0c6607090091b01c5082c01011490342c115a403180034014800544400d601050300041c150380000b007507496900480e007a503146526094944201243c089006a11401060208518000c04501c20340e50b84082142081c030b4100c115840078801d06540d01c2003110200b8100140802580d8410040c910980641d00d10304046011588 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 622011196 1250 622009946 622009963
    0x807080d0b031b0a0b18121501031a01090504020904060b040612060c080714070602090a180e010b0102030a0504050904030c080a0504140a0b03271f0c02060912030a1d 73
    0x2141c054030a0010f07545c5009011140b903059901600e80820300f640302001003485c503c204166180c810000d1450102c21501001360285000b0700900c0301d030188254044e140b14105802010540341440c0034000103864410f11250060760129000c1351448212021038002d102642c460070410400260b0302c0c052101c1940802e00941d1265a044042d5842d584142d03415034030702c284003465440400066001c60001c3c1d01803c1410001440d0000540e91541d08c900c035481c01c000304203201c6030384000c00138100100744110900b02e8401e001a50a000042002034000c0c0114416140502031010000d010035206010910b00300d03900586c02078136090391640027001900700303000b201883d0001c0d80a000482c9042c0782c4e0a01210485003c0038510741d15940c2c84c50b1908240029110000b810114101d000001071103402e00341800507808451000702c0b401002c05490a10340c0b00410b6410460038402d403604041000d240c90310b503844c07080d5a280c441c0d03140e0b00010320921800b142c0e4064999900c185408000c070f50034a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 622012446 1250 622011196 622011199
    0xc0203031608070218010e0a20040303020c01080a15030605090a0525050906130e0f0d030b090a1b1d03160528050f0d051b01080a020301030807080d0b031b 68
    0x6419041005c3c0c0400c24880038020800f401c003501d4006803d0050075040100404c207400000c50b905009a80e0008460300283c0003107002da08041c645440950740510140c1c0c2c000d0080805100e00101c0302c030007000903450742c0400780849440c2c40001d0382000c020000c07400038070780c080201ca0b003d0b0105c440700c4d594180c40400b20708450219050000d2a442c28000241c01844018418601c000c04041110014110000902e0041c081c44411591003c402d01901450074403c0e1008100f00c00c1c3c5074200903104d0b030003e1503e4403241c03400c4001480d10003240000030000718a4140a47d0205498041104040d1410007580e81485401403503a41c000c3c00c00c414100b140e03802d031400041ca08081d0080604030f4001298140d8a28800108000c1803904486400202d2000b03440040c400c4081d44409052100742c08246c4808074449100094550380281e41d0b680c0161118030443c115411603a9201c101c1c481c2150140190318085200d0708140c801da4003239907070410004c080310640c0d11034141d840070080c00051443e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 622013696 1250 622012446 622012459
    0x1b0304030f23070b0f030a140f01080c040207050d030b2803030f0f0c02040c050c03030108012a0807201515040605010816091503021903020a0206070c02030316080702 73
    0x4141e100340001e031030f000f0341c4c895004403400c14040036280065071300b00030403030103030b090300d40807864000802e18200c140201641c031a02d400560411a00754900324080e03c03901d0040f0f00c10801200840e002180540040c8040c1c41c4c0807e50f040c4190001c3d1b80c030f005194121851a0000f09105e0f1200040c83d0f0481c00c80741702c0d4030794409003903145006840e4417820b4200d030310109469200349001441c050b440110b00b049a810403030b050401403015035180d50400d8002c0103417695aa40741402003035980d04003203a034000c00403100d0580c030320b9400001c0ca0300ca005404541888a20070200c80145d0070240d002c0d19002c921070031102813491080888410600a030ba140c0280881070000801a042074068013007942c4040e10b80b491a510ba40b10341419003e4401d101b001002540c000c003080440050004103620710144c3c4d00942c66201c480b0600344a80710124041051510402691510503000301300d0b680e11140c10300703003103c59080b540042410340c03084c009510300c48803144d00142c0401a50340c1c05800070a0098402 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 622014946 1250 622013696 622013753
    0xf0c051e161706060a0509040209100b07050a05070b0405060d0e0703021005070201080106090b1615020301030b040c050301091e17031303090b030105030a23010516180b1b0304030f 79
    0x5d100001c201344c045c80c1c0d082103582c0001409428444440d81d00000350701e1110142e96034640f030250280c0c000d45003c0f04c0310b82040441100b445010031250000d098040040c0f0715003403034040000c0a40c4500300b4114107207034455407011034000003800380400450f00600300c01c100c87d03101c1d4402000ca5100c9a800ca000ca40070030000301e141c5202d0000c44c41902c8504000c903140c024402440c24240d85e0460003100d440220200c60498200540080d5000b144601d104a0071402c00e443c00700a20205600a0b501aa243c1041a0041440081038801045e502e000542c02a20035091482c0000301501c2100c8400b100002031009a0036000a4803144500030f030341d00c68645444034006c4403540300038404d040d0f0680c042c078003820110b6200c0c02d80d410407405000c0e400000d0b050000500382540d008840d40721824400d40304804e65071380c020114a040c1000d0303002c000c28850610401300094010820107400500c4c0310000428560000c200729030107960440380b0030014284901e000c40b2004803071034401c82109808501c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 622016196 1250 622014946 622014949
    0x201050a0c0912080d09060212070e0603040f022701090608010b06070210090807060e01200d080601050c06090102310b0d06090e0105070f0c051e16170606 68
    0x1e58501c070009a0ba900300b03040d00d01500505030f02000c00c401e07203902204021a0052103610b10400703480034072551000d80c8440f4041c80e080c01491006201d103042c0700390641c401d003141d0b0740d00c0100e80c0c0c4150321400d410400381c002d001044650208a4002088400c00381441e4080c61951070001d0484003410014013a040d15803103071609031b4105005060308110300b1f005400c011b103001c3e9245100700b81186040b400c150391310035003076152180552202000c601210702e82c1c5c0c45540c0c0010300c10300003514451180308603401414900c3c1d64603800d41c080c1c41002801030200b070030740c3c0c4610304803440006100c2c216051403c224a541c0c0c000d41c440801406000150a64001c45070564241d1050180581c940e40840c140741c148130f54804c0d40443c002e055810340e940804140e24400e0702c41c114800b607011000290a250000000d800c000940040900340041c42ca03005000810005034042c000500640294595007804000c81c60850343d01c00c4200d400755622b0000c00d21010314000310403c1c040340f000f1901551184070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 622017446 1250 622016196 622016201
    0x301090309080708160e0601022a0310020306060a080901020c0a21020616050306060d1802042004061d0306071710060e0f010c080310170303012607150503070201050a 73
    0x1403056034541d05203500b00201b8044009143d071180041c0190b814605121822147c060440e01c009591041c4042402500d4241040315480e020b1103140c00f1807035800c0410000d015806a1485402040b540d200011200e4400f90141c4131000d41c0711048079507140092401c0030b03408450700e00681c200d00b00c0d800686090303031000503070500500010340c100e020040c81950403a200d500c002c001036003102c4108601100c1001501c14800007400040540e0220081c40c81003109481c1d035011000711500310140b40400701c05a032011034017100c1082c2400180c0300080c0105c10100d40c1405130a079414051541086001900030314044031440728400301c0e0400d50307101c0404e85a00d0400c1e02481000403403024038118507040607610010407081c1410611000c003510780e920740e2680c0c002c45021400c00f200034001c208280300c4440000c1c01c2c102000145065606085400f07e02890102000e48804840002c021104034207002503006030043d0382c207200709034500c00760103891540261010001981f0303250000b0144291071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 622018696 1250 622017446 622017463
    0xc02190308130f0c0b0c060901091104230412270501140c0708030a030c090308030402040b270708073006050909010e1606050304120903020301090309080708 69
    0x180c40310440d94542e10800b81203010b09031000c8030014401500100420084074a0303030001c0c407154104550b81c40307452902e5403c0000192540055a0402d40310100240a56003c080f41ca1070541c0c00103003001d82808001e17404c0c4c050303081c90f45152008a05110522800c3c10000001d00b4032622080c1007414199100c030010345a8001d240440a0800740a108942c41780041841180d03d1511300c600748442d5040c1a403c0c03c1c020751024600c0d50000a01c00f1034243c0500071110740702e400c0d0030107201c00340c55610303540168400200024400c036940c1400413215661a01d880c005410340104449800c1d5102031880040e91081e03500a01080704240041c0c021481684410720043c507411000a68500c0b9910800c1d40000c443d01041e0965140d190100d00d42d25101d16040c840d0b180e160011800d24400a442801d0504070707188000307010700c0e400003071112941190459411640c01034924400540440c4111006000354000940c95402c01c00c540007030552003ca1001682c4a40007aa43d54075560000d03e507452106 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 622019946 1250 622018696 622018703
    0x1f0606090e040b0f1305010c0c030908030a0509152205130507021911040c200c0618010201090b04200f01020d030b03071203020a050c10090918020402030a0c0219 71
    0x800008060745032204e0380b00d82001007030012002c000c0c540e544650039101940c0c0020006148403800c58149540492031400521185000e1850540c01170344c02030541c451207510500903070a5428080004040350b044850741a200741c2e1030103142841e0180c5d0400a4410700c0b80c103124a03c80e0101c001000460b10500c0d00524481d00285660007002860281c844e090000c2a640302500503079025458541e40110303550040c0b21354906240d0204880d601440c0301a000c1d50100503485502e1021454070b60380d003160b40807052040f030030743e04169510040303024120360080182240c4c034100070301c010040c0c8032007039008407131000c80d0b00300da400122414841c000c1c40c0c0e051014010380c41801440c460600a901410764040064141c0d60320f02c5e183d129106080740d001e10206c0041e48551080b01c203211050043d1480340008842e40b01180c60740440c020803116a07402400d40700c560741da400d036102862060a003a2342c69400342007591603180c001c3e946001800701d4600f2201601a0440c03201c002c40b410071a29962960 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 622021196 1250 622019946 622019963
    0x180501050301030204091505090f190218040501021315110114190921020706080c040512160605180103091e052109010f0503100e07021f0606090e04 65
    0x80d613001c00010707000d02c032819103c8410786d0034a81d81c003141501a0300d21600004009207080f568071311800385010210710661907401c110001d41d400580d40d13281d42c99076411842c807081841c3e417a1410200e00911a001c1d00c0d68152440220008004031000c0c91406000041d8482d1461000814075a500341c0c1d41d0940d00e02c0c00b460704480000e140c250f11107288039a0903d9010009801c40c626640c440110001d02410040200488031264045034100000f4006c1c012074500714001e428030075202c14aa00032405642e2241d4001400b1072410107042002268900e03a118514a03029070b24407019045a101d4621003c400c031b01c07580240e0495020307008800003641c1c0300c410030011405008448600c03d00c6014100e03083d010300c0ca1410b04070329031220f43d0400c3c1407049031060740d51081c02001425640c507000303021003488418000c01c5100000d12042504442140d5802050742da506803040341441e1204080e0741c0104000c1545190010f2542c1c0100c3c15a0001d40310030070400e40f6850138084046080350000c1c003071307107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 622022446 1250 622021196 622021199
    0x60c230607080903090a0806010504050903040305190f0f11151201090f0209092e0303020d030906201201050405040807030c0302010603142103270304081606180501050301 75
    0x10700c542d980743c1d40580b80380150780c205090b55002881d250200d0340b0620031580440d005201d1460075208250b0007220b404011840d152031076440648440c1748212211061345100d01140a0140140807008426400200c05001c40140d00d40701444031f6000c0661030043d0f403080c0081081600745421207518045c1442180c0391a80b8000120001e040c000240c02201c80e004c0c000b064241c1c440041050250ba109452419010200050710341e1803241c5142d101d02ca0031049004101098010030f410548400a15001c140c1c0c92060030300384064020750028100c0c1080e0081022201212080500302c0f00141050754903d42c3da0740ca04100070344006540180c0141410054440002c6c011419040d80c54801d000103d0401d64a485a010782c0700e1003050309142d07400c0520341d2180c000d01d04007940341810b181a4100d00754100319907052011440c200150344400e400c18020030249a0410036600200030751421945c941541010510481140e44964400b180b00c41c1e1401d080f000e840000c41080d0740c0180c0d61305080d03a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 622023696 1250 622022446 622022461
    0xa0305150121110406080114030316020d020d020a12050601080703050607080414100218010201090c0909060219020c0307060207060f0e01120905011b0905061209030c0106060c2306 79
    0x800c00308003090030b1651180d82c0700003601c80e072000e04010f000300d8407601800e40c50014500005c0c003821035158070175002008102240d0b43d182188900c15134040d20082071400e01d0b44085000c4112004010307501031801400043c20021094040000e64401c009640441e42ea0786401c1c1d60340e0303515000061a50704040000f80e4214400c0c0c5000b40e1050080f510320200382d2650141c14100440c1c186095541c5400003809071100c030207034901c8500d6000c20700c02005070558503280e551905401e80159111940c9407241e00091020a0b016a0007a14a0031b26000d06504078241c003035516000d032544540240070f04c9500140b680e0001c241d20040340c541c1e882c0d07007041d111540320454041ca907045002d414031038140b060505801e01880b41e6151076103c1c00c00041c160124081290744ca400d082c142c2030070880d0307038042800551203040c1503d021508250907941d550315041c0c240350a50041e00c610b00f078158030701940020302c1540005109180c2c0c1c000c0705000718407003038240e5490300100340c0c04c5450030ba54449008203042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 622024946 1250 622023696 622023737
    0x5010c05031905041719030f030b03031b060601110607081015210608071502070b07060c030507050a0f0f021f0605030c0f130b1909020a03051501 64
    0x14400c8003900e00d401c03560310560401c00c0802000c0400258081414880015181100814600e03902c005085c25103414003003094103504400010104101c00d81900c40c01802504001c03080070f030080513a502d40b40ca10f12043c0c60240100010402e07031140c44003148981d4007034801d0501100c44000a441243d81d840000ea403d003a0181442e1144405440001a910082d000d00c0c1c1d01490599645124548a00c024014824944483e191003078a491400c00c15024001450030448060124482e044240001c0503814000350303034000c00f414407002403850200700c07581d401b03200440c0090310100320946454504640f00c1c02a1010303200411903d010808131a8006e00300300301042110b10403602e100d801401d4445210f8407456103092041c0c0c5810042c4214902031120015001d000e542d00c61545420500242501070b001d4104108035035560700d564141e440e8000401c005040210201c2c2c401e85d6a2030400000790f00c004c80c0c0c000000d18000100f103070740700c08808000e1344c4481652640c0040d4482c0109854 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 622026196 1250 622024946 622024967
    0x20d03050f07080301090902030c12030d0510080102040f06091a0f07020d060e03070b09160b0f0f040605030a1409031b0c180105010f02010608030d230108160b03040203070501 77
    0x10980c00d010002c009810300c00194081d08840d03c0125983e0381c3c1d44103242c81c1016a0070030030311407004601e17156002d001c00016103944502e800408507a41c0c4468a9082c01544107410188155000060106e02ca28480c28960704545065a4031072007140e584641e010990713403505e00c60409010800158184081c00406040a20300040601c102000c40e5541c00007103400c09401c1c06482d810100e06074091000d1501c5240c5d205503420040c0030010740303078480040300b620b0713034068868842c201060121041980a05559040c0c45a0009035952515410050403540085a14103800c50401e0f2006001c101000445806925144015820101c140c0c0c1d030700c141e40001802c640020300c5059010740b60303035541d0000d0705600300300400c98607555414000014604108040444103581c14004104080c2c07800001326a11401a00720004040c030303d103542d032044504880c43d149603100c0c244002003500f81c00032500c200303502e0300840d2061070702d956460601194042140c01030b5054004000030006540284a80318 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 622027446 1250 622026196 622026217
    0x90b031209180a050a1415040207050f063111100e0411191d040c0905040903020c19030201020307060b0a18020d05180d0e150c031306030603020d0305 66
    0x803400010070300c1d210b0000c01c12201c110940c0d40b56400d0156002c22481180103e0100b04100345072842e0104100b68030403c00a9001e0289030700040000620106205144000540070182c5040d8281070414a00315107440f54101104400038003070184a0001c0380106083e141d0240c02900e407140d00301c0c100715002c0a449240024012083c40070b0a1555a40c0b00303d0099070294420140c8503001005d24400c80c40400410b6000c0c000380c4903c002142303030002c1c80150074100444011944030b518200032a610091036204680060a207a2402c041680100c0e50740c1a1502c15504640d01c105c610030207101142c1c040c40060f015800420912000c0360306034004089038040548a4100c01c0e40e1b03410301005006810380782d10f07240707079002c6003194081142d07024440c1c00c41500030200c4100d04011155540746c1600c94000320038000f41c41049c10443d1520301d0703400d450702c0320f003135803e91a0b28960102586030740c09440800c014068400000c64200c0c004c1c81500c0070750350054207500d6041503a03941a1f8281d8132040707190 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 622028696 1250 622027446 622027459
    0x2a060e10030b0d05030d050a0203010303080103110d0b0f09150112060e010216050706020d0e0918011b0f12022d040b19030506030a0b0a0903030605090718090b031209 73
    0xb20302d40318600f00c158400c1c801d10046a950007110601000c5401c040d01040c2c04900400c01003000c2075014104a05407900070140b0424421044c00103146150203120080c2465000410080c404e0507035000d2038858004a01510300d1900c0c060b034240d125103000d028403000c10a5003403841022403400c1e80102d2885000c00001450070200c0d10808000f55a80e0030221510b40c000d000c10702201d54184454003214009003841d0000c901803000055400300e0003800f00d01c80c00c800e21010703103201c6001d4000b018a603850140d05040502107200007042d900300005a400031922550594300800924821180004c0001054081400001e103105039840c03140f07448400010414480811021030710001415255072045001c69013110500d40982650401003400748207800101410300440c01030213550b03a1040144400184005092070b05400070101d581005070481c07050002c00200036008082d0034907032550f100810904655034541c4000762291b014000b03425800902d90300750000c2100700940303103070b12008004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 622029946 1250 622028696 622028711
    0x5040b030a080d200f0a02070f06050702040504030e0a0e09070506181002030f030f0a0606030219080a15030f1406012d081006031e0503160f0803042a060e1003 70
    0x5030601364001e01d6114401c1100000d90a034a1901004100c0003012040c0b0700d80e00c001d1400201070424050b801d00a4003c80d02e6500140400d44600c5160040f2003000380640c0200b41c5a1140d41a0504210313030b000c40030310030f200d00450f4500e007100985030703141c2e1007001c0481043c1c92503062001041c15404d4600a610040c00a0103609408501952290001c503000c0905850070820a030191186948035109043c410000c0c0c02800c110401c130f4110710030803410700403c25100c49007003038000c2080c16002e02c905d0407048808410004010141c0d02614041c82c0510603003805a0318540d2141d00030301c40d603056010080e003081c0740e021080c03040070844100900140c182641e43d101842c18030141c60a0340c18100d50b900e806104010b4079504910460908900440080c9403c2d59403a0303403813060180d00f40400180e26503290800c00300d004025046548000d9668480c14186000304200c1040d092500030031750f11051002c0185003000d00201202c09a503034807060040880c0500c08118003a90b000380c10540c40322030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 622031196 1250 622029946 622030001
    0x1d040e011404060c02070b0c25050307030503120f0f2e03060506030601080106230402041707060305010e15011b050619050a02092b0b1005040b030a080d 67
    0x1040703403181d4002c44000c51a2424404000e04140c060f40041c4000c501c24400d5140e802d00c0000c090004104060284210344500c5e0315102402c4500d0344001c0c2e0510880101208100002c809412149440c8980030115251b100c0d0003090780008507802ca454100020005d001d0f0300c9004004010313500302ea18901c00c1091b550303010780301c1c11078aa00162113407600c1390103001681c2020807000d40105184802000342604100c45a46100704034156494142c004540d141c003240d0300c950440c0d000f420381c0c0500c541d10107040c0a09a844108920480300401e26000001a0038040c41684621548071034903520025a000401910700d400019a200d20441100e5a500b0004004200141c0100c0c000410040c0c0080d0761340b020b50a440700184440050790050201c5003007500ca070215501d19000b0a049070580c85218191000c007a040550040c0200900105000c1c00303840d00076601003610070503141409a09000d030141650b40903642002401d040b000c010b000100d00155100d8411203010394210f81012982d5134 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 622032446 1250 622031196 622031231
    0x30e010804032d0e010228020f0402070b0f010602010b01020718150e2e1a120708040311030304020d02040e0114190b19150519031b1d040e01 62
    0x400144150040c0f00301040342540000c102c5000500900c01400804103903903010b00f60540403600d48600c00a51a801030440d941d200c0d8400140101038011500d54030507081103652a00b0030356108032000c0114002150062040c0070340040301300180c0041c400f40f89001003018180c1c04100c807a40540341d4901107080703001e03110b2460310010144800f0030b1040341000861006104005003e42c145038558506191800b41d88050410884151000f04042c0030001c121030703c00ca00c070704400058051180400c0041207500304003102c0c0039174041d0340d41c548003d02100b407841d0381e403000ba80c01a5004140e01d45d208018075041d00a0b0440360010070004c10001c0c40411500203136001592030b0b5483d08102484c00c107007400184290740780d039201140c045001e1445080700c0504000c0038000d0215803015075500400b054001d06c1100c48004120a14400440c05000010014030041e401900c80d1500c40100030000340c843c00300c51004102030f00000459410900400c0010701c0c005035011110b5480710040c509040a05 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 622033696 1250 622032446 622032497
    0x6030b150f090d02040f0b09060a03261207020109051c020c1203040513090b0c09010504030f08071202030c010e0601052209231002041a03040f050303090d0318030e01080403 76
    0x106c0c021031849000030811242c128000c149030302a413101201000492145110403501108450a02c4001195a00300520038032910301020300140c1a08180540b00341d05500c003c25490040082e0b802d00011a0000809800d1590004005a0251401d404946804d1174021440920641100e00d4569100f01184500c0504120f14202c296900241c1040c072581c903000b2a4081c0c0301c0920645010700030000a41540a680005801c0041b400036040c10030695000b1250041d0700046084c523040d88400000390b5a40c0a1652520b01b5401e20003814822840001c032141a05d0004088010030842082140c1c0341c040100c0031a0801c1c0c0c1c13038000c80800b290811954404c07030422041c031581c071482171500451908000320360f030031400c40c41080b082181c0c40c0407038810306201c0a00c020710366507a215420200070000c02007a025205020000038414890800900500000c14645090103000c0284200701c162a401030b9026000c41c2111200107203d40c8100001c42c0c0c4a8428104822401003e580c440e6451812 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 622034946 1250 622033696 622033721
    0x1205072d030501050315040f1104060e040210020105091b03070b0f130e01120b040f02030106140103060f1202010804081b011505040515060a051c050106030b150f090d0204 75
    0xe100d103140409906005160240030280d006103d5120380a50050804000500c0502001190044a810440c10307003030121510a00a00902840b61510300750071b062030095404a200e2680c03007655800359030041c0203952280c03d41e00058644854040751a50910012000c0780b03605000e1940c001c600361400c0406032400e510700da103a241e15003c085006000151a079005520a840c000004100d800b03800c1044600030ba5000c0e90105580c0c45038030381040b0403090904025419401e264003c1140a42405075403500303003090381c00b4443c240d0b941200000b0306415018040042c1086903010000d9401800c405421510462030503183c1811002154240c849948100e03010f07945030300c0070040081e500610f003005480708a900b0080b1b410040c00c00e082044160595900441000c6445d884070f0b0b0188050302d1400320360441c916a072800e03503008003004140074014140030910f4800b1081040c104846007400d0a0701c03200110349007245030310040451703400804c11103034001813201300b51006850720700601142201 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 622036196 1250 622034946 622035017
    0x2c061005030615040c0c2f04020a020618151006120b0609040b0a0f09090c090203040305030a050406110c011b1404060302031506040305150610120507 66
    0x18408125205100194002072003588410184004085011800b032034460341298000f4545140302400c0d10700390760342c8030b000c1c041c4005100d22440075581140301541403a40c0555190204011108101c00c178002d0315a503d0059014400180c03003000c2001aaa2100b14900708984003101441c1010000c1601100c0407100380f0001c1c5820030400c2e81081070000c00c020880c00900c4041250030100c0e400e0b004140020b031145071031700300444141e1903000b001c170007414040c0e500001080c2c40d0780c060001742c03490200403544100183d00011740c60300a4030942340070710761582d965803654075002d805201604001c0c1c0b080e101e483d621140d00c281c00341b91100510b003c041e40c00011900c5082c50b5008078100b1181c0341310340f06200c0e00900501000380c881044030151829400d00584070f0316690491890b10302074501d9560408400100403050180000d4415034840501024408950b6410f040c40f0b0514554242c120100c0c4a40030f200b402c0c0b80103500310b59400083c5242c040038400c0000c0110614100b05071700c0444504 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 622037446 1250 622036196 622036201
    0x20906211b0604032415090605030c04020408070b0d11190e010c0210050a031d0f2509021b0114011d01030209072003040617060103090b0a2c06 63
    0x200054860980c41408031500b034240351035522a2041c00d1501d042424902e03034201e4000c005108070b41d006840922149886200c00d5440315007040051141d030280c18403910410600001c540381c94000c0794181c1d030307998000d0010103140956404841e00540c441c0401591207540e0000400e09030340240c03004444c803c0c0d007c1800c0201010142c51504d14000290401140003a0817016894504030030784d4920940c60503079a41c05103000304400600c0d6501d82103aa415400d04100d038a0080050202e0a001d001016101c05030300c841429425140640141641c81b444070742e003000118034680c050500d251200c940340d14094516861107007101c440b4070481d040c1c240000c00600020700c000c868030450882c0100c4811155045800040c0980d00080c81da03c2080404a0060350684244000d00f400c0c40c50007084030340b142d0721114050703c4140c0c014000880c4c181e8141c000f8000d58404c1c01800380090700031180c41c0c005c0d202c0103119009000600700030071460070040260f10741260b81c540b0b00100c6180c091301620050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 622038696 1250 622037446 622037473
    0x4110118211a07200c0d1103070f08070807080313061412130c0b0708070212070803040303020304030605060108160c2d0b0a110a0e030c040f0c0201050117070302090621 74
    0x44d04d608020f12564004200e0b00e096880c0c03607090001071901719600c00c0b00d1080c9140024a061859006210b9540801d200005c50b10000109402512021800c0d03c0c0b4844c2c4a40f1656a40c1c0110340002806200c142000c00c0894060341c0381304a9a0110040b8528029100c840d510328150203450708613600c0e01c1c50343d050051004c1040200c0103480d5070b03071803030b440c0400725110800c20340114580a481101d24045454071568100100700040c2030103020380c0c0e190b0b580c074100030303440b41c0161000352070140c107000c00618551302c1003020760300c1500c0e4621084441004100c00701c42d41a100c08088585500c1e003d44c0c210b4100c0802d4840c501c2040d103294046009519181845490340701034002d1303010038100303da80c0d80000345032400c0e9002e55100d482e1008bc0403001e400064501243c40031300607041f902d004030340044d03602160800307805546241c0091149903a11848900362024520000495130420340d014001860000d0505030001da00801588800640da41081041400303204401c0d11030b802071440300c000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 622039946 1250 622038696 622038737
    0x20423090c03070f2601090b0a0b0405040201450501030b0d021f0302070204090609021c0314130b0d0204210b011203030207060504110118211a07 64
    0x40010340c0500300c4036140842021362000d19002e0100b00c0a40800e045c0003280600880351440c280500003442589840c1c1842c0030440c0050b40c1440c016400c048561110381003038014903025030383c181d54034042040c45e0300301d8460804201e64000036564107a90b040480d0f01d401c00c0c1a44c50024010700604070700f80707031400240884000480850140d400349800380050782d0f400e03100130914411f4120703603000c81041d42c40c02c800a108500c4001c1d8002d2038a40308006008181d0f010305882482901d403441e50b011165500707400341440c104000c0c0061200000016502c0700c0c8006841103d000f4120703045220707280e83c0e058180d84c210440c00030311154041410800581180c04c10014402c0c09445882508519241c6074010041401100c001200241d04801058402e504888c8070756040300b403c024a080901c0c2c44140c1140c6070801da0700140c107580e98040700000e061200c40858035a0070108141c039070310364402642440d1140c0280c82c240d284d01e40202d100308110810364444c4409907507880d45c03144552042c002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 622041196 1250 622039946 622039963
    0x3030819061502011518020a0c0c0906150e090c0c120705010207050106450219091a0d3329030a15090903081e0f0403050702042309 58
    0x1001c1145001c10000c031b9851070400c03a60801c0d04a40580e5507150240700383c0352100c81100050801d0403c031000290340c402580b00d6420303510500340600d8034180c9000300702d80c100b90b03e040c5160301c0b00a10001c622451303121001000c0308514034058500852929141c4007254104c2007003503410740d40004507801001020712680011740003410066010043c001d0310001c0750075010f91840108024178800240424041001005c11b2002000c10340d591000d0441b202c16009034040c3c54004039140c030001041c1810b04204c0e403004c40c0c0302c06104034101081a02008041c19900280580a0f400209039901c0700c01307030180c2c0c8911001c07070003c01d05005140c040e20486014000c1021240d405480500303180441002c4100ca400c0744213568041030416003034211121044595004003245450070302c0d8030f01095004120203108039100709141001c080b201103030090300101165800c540d101404001000030b406440070300095400540f0020f058001003094214104520440f000034000e400c0422a200070200312840c1d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 622042446 1250 622041196 622041221
    0x13090312060602011404060f020d020409021306030507141e030f0f0f04080301060f0306090c0f02100b18191503050f07030b070507051014060a09060f0303081906150201 74
    0xe0440350014041220001b8000401e440d888010760b1341d50707030074a8041c6c90355019060821599036640c0d0241c04025400303020810544a419000002c4181c042d00c1060310904150700d440401c4080c0390003c1c0640c0d8811000c0e0082d1550740700c0d03900b41c0040c40d40c025500c0b40201102d89078a90401c00241468040d0007800241c1c1e0f0300c00350b01003000140c00704d81600e04590300e40c1000c41254400c40b0050703020b8201d54203c1d10b40c41d031403c5031680c0b00d5907020307012031203040302a001d03140d500800407042020744040081d10b0760413102c50010320105214072000386a0180c04001e0040d07003c005082d05109582041000641c60201a5001d1007404414010540d03040203180007481d11901d107030b41314210f04000038401002c0c08008982c10050202c244030400100006038030801c40200c0c240000c405104098420600801c60810f010481090511546040d40e00c1d010300111403600d141d904131007640005280d48102e0801d01d1601051101074040c40003c0e010b9507226012140d00f2040007400c407141c006010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 622043696 1250 622042446 622042451
    0x90f0604030c080d1404080d0b010806030a110a090608060a06121104050c040812031006021513030c0203010513030807020c011b08071208041502030618061309031206060201 76
    0x40002c0d080992400e64540c00700400340c54442980a000040c40305004101d83c02820a041000b00018200107290302d688000d8100500c40700c5000440707409000b107030f6043e0590303c0a1410f20115100c541000c5007070200034a40340f101501c42203264255001c590012071140d20100c00d01c0f203400300318028900500790318a603001801025840e4007005503503041d1a80e008640d5480070500d03600700c0c03004640240c9004401c862258040440110003544200c800c426034110002c0042145440801c20380a4603000030a4100c06454001d040c854480c880b000072014040313410b40d42e03030060320280941c503c03901003500360484002581c01c000d0507201c802844201150072511081185a8010320500d84040f00d2008041c107840c000c1c9081d01251041403130103000713204128424440c842d0708c4214070b40b065100300034940d0550f1241c0706400603400240c071903941c03260300d80070b030100c42048d644251a44058001c10f2000c165101003036070b80448101c07400a80c0059580d00a2200c580c1eaa8003883d001412548000c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 622044946 1250 622043696 622043701
    0x170c0a060e12090f09040201021e06091204060503010306020a020c040c080601030b0901080a06180816120203070308060910090c03022101080a020607060605180609070f02190201020304120308090f06 87
    0x40c0c003c51940c03110351045d240900032a043d64403c000000c802c001a0407e0411043c00302c1c483c0f13603900011034001610788509840018801040010740d000c990050722fa031130071079003503565480c0030307420600301c0c0c100f144900f54880e162983d1718000c11541e80c0207515200030345e00b0040e0004042c0d1300c0c0c41901c18081c0310440010842d20100045410790340d50000400180c0300300d0b07030845110000c0301e210007038100307640426005466034480b2200e0000390310035081c4404868000c08160388a00030355070042d02050304500003039000d0604004441d8007807100886400787c0e680382c070351400803078400090703038000a80c0c0441c00c5070509036108800303c0d00021666110b049513151019503a0746200b4070034028007030800840d040f020001c95404c6040a010010401051800020440401c1c580101e850a1050503100c000c5440d0300d004016100d08085903501804205100f48086202861854001ca046200c100130000740d03001e214201294491180d6106009824020000d0b41b03402d5a400306249150042c0b400d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 622046196 1250 622044946 622044949
    0x509010506010504060c030e090c0405031e0d0e030307060c0e1023160b090c0103180506012d14040c02030406020309270a051807050a03170c0a060e1209 67
    0x180d0b1304071516840c0400b0707114540d20f0101c8001c030070004490b070071070401c00a20040c0340c3c01c2c4001d042540c600360110f4400820fa400c2ca003401c18140d00d42d4410507040000716078001c500c0359150b03860154010b411607142810b01e030344140840c0c0c100b0659000080c0d82c00c05002c2680b800d030406032125042450a401c16128142e0000691540d00c01100d0304640c3c00580e0704481c50f07290b50311140b05a0132038854074040c0740164030b454331036400c000d041c0c1c002850070b502c5811450b400e102840300542c108008000d50303800d092070500388032003800049400441c940c8480300b11807040304440001e0031513082c4d04a400c08141040c0300c20745002192000954205000a01100d540001510f0540c5001c0b150300c200e0104001e040d000e00307000301d540b0700000844c0000300040700115422a5005500719852841032190385480d282c2c07210003034041c04e41d04c0700210b407081000c107800e6070403461038035816403144ac644250b01452a2a00d29513440c11980e00da00c0f98a150008a814007400304080d001f010643d282914400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 622047446 1250 622046196 622046207
    0x60801050105060a1e21060513090506070e010201110d0e06130512160b01030813090522050c09180d051c020711270c0703020a1509020a0e0406050901050601 69
    0x80400382005c01c1c02c044c203819114003401e4550700071099040403101090070b090307000703031100e4000c10340250345107900552000c40901c5552004e44c0c004001c1d106644884038100e4032001c44400703050440d0340301c0b0206440600d1a0340103118080070800002071403080c03145190f00f048030040000d41910322070300086005c98400f0500902580c5001005030356180024014140e51820400280c0b000700d20500200c00c0002510003000b00228004c889000282d46040750b02c150340301112070f011030302081506209a180550704e16800b03075120f44141d903014043d0b40c000c202204c0c42103410108072813500040216014090140c94460b43d15468000c2c9055928030701c401c000c08030841a070600342d0780019403509000d0000094402c801c0010702c11000c1c40c0428443c4040404051035502484100d1404600098094822a032285ea40340d0098a4001719507103a000104015042c0450000d480740030040041e6202811400907040c0310b1701100007402c1c05d08080703046131002040804542c0c507042c01d0241c10303030f04803 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 622048696 1250 622047446 622047467
    0x80c01140c0721050a2a03020a05130e010e0606130612080a050721020d0203070c0302040b1f0f0e01020c0108010e10080609032d071106040e0a060801050105060a 71
    0x40d40c260803000b10904882000d0fa040c0c42020b005401030045441c00c00c9045400c801200290004043c4541541c684502c110076880c07100a521440801041007141000304413912288a0074000141c0f0540d1a0382d00c41c01c2d100514101030b456003000d400c01c1810716105008050500302c09004000d11428454100b209814401016002d49000b1484080c09485981121b0340c4070f40c006200943c5243d4411035540c80903504002c0381c09401a0041e000c01e041c070020548003080d40201034030041524580900c002001c141006940150030300414000c1e0316580e40030491602d4190340d504216400ca07141c002c0c130b5800c013107001c9811900801001141603038070000c03250644060702048511612071403100d5095809550021480e03010f65010401100e10100182c00150010444110340c100384805003200d82c6052180f8030701c04003003400701001042a2315640c0000300c8000c3c011625240c1c4440d2075485c40102184e000140300c1e10352005005680d001c0c01000c1c01001e003030b690682811009072024084000c0d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 622049946 1250 622048696 622048709
    0x1103040909080702060d09030f0f050904090f0b0c040509010f08031c0209040905031903060506250b04060b040b030303160309050a170301030c0e04030f0f020115080c01140c07 77
    0x11000c01c001444a03040845014643c01024143c0d40c0c500701080001900c000c46065003c5054250151f03550350103072880600740d0810740c1c1e8581c40c0038240c008110040c41c101001b40c030407107545507400000884003104540120000d03002652600e00d0324040000e60081600710078208410200700b00703c041000402e450280c541800081d110090300720303611000b03000d0022860740c03007820580218103211001c0b00405d6490440400040c0481c65698103800b503a02c248070722500f04000f04040c403881a44844091214103105520401c010314549600701d891005075801e44110790b1340c544003070b09450107104000c2c10100c190050740c15440c05905c28840d00420b10411001d0680b65101310040007810302c9051603caa00c000410701402e20b0070400401c0d42c0090008a40112248001041903003884458503c5568190b699a0114400c1c5404030303115940001c1e40815036494210b8086034400038240c0744003a00003c0e0007014100b441e000014601645c25a94481e400713020403940c0c1335040040340785c0c42a03520 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 622051196 1250 622049946 622049951
    0x3080d0c03090501150905100323010204090c11010e010603031d13020a020c0a0e090c1513090b130504081e0f070807060b0108060907110a0c0b1911030409 68
    0x9220394150301601546000400729480c1003908141a0131407000c1400b42e51040800300015602e00e06201702d03080c1d89000c06018401e88884045255031440781019150390344600140c20305684880039401e5408000c01c5201144403040008808002403285a10041049000b841240d00e181c402402ca02c070050740241c0001135550105045856941000c2c03072070010100b0842d9110342642009480b112551005031184540d034200213504a225540e00340030b11000c0300a05000c1e0b401c1000c110740c00c410f258580c82c544d8030902c0000c0316144502c2189004050000002c00c400d0680c1c800c0000d03900d5a040701e050901e103048280404104900c00f40d520b540b8002c0b465003034a40122884ac0100c4c00f0b80854950660340c0010400f0400040304041d290b043e20600f42409040d01403401907034801022610190425460400206d005109100340404c2240000c00e8640d80c43c580c0c0c50b00c42000700543c214010000e030025205c54241034041c4003e01506440c40c1410f00d01d021184010340341d100d00c4c40381040c0280c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 622052446 1250 622051196 622051211
    0x20a08030a061a0310090c020312040f060e0d090506310801060801060f090f020903030706020418050c160201110a060e0c0306010b04060c061509140109020a0c0b0c0d0509151003080d 80
    0x14020011243d0680800a2b0305440d4074103880c014000d03401b4814101e60590507c00044051000003070310040a120b692101e83d00305084c10248042600140a0140d800c40001150340556064079180700010692048441d4041e042140c00b50944407540d1000e41c4c160724005003085102c06220718182034400d550b4010a41c0981c2c2505a000382c050100004c2c1d040c0000201603042240d980c0c000d0044545840c100e0a9085a94241030100c0340111990510444d0410141d034905101010700f240103441410805540c03c10aa111864003a6250044a8981d80c50700e640500740710410a03e803258108a006011940c140140001c00340580e104500912040c0d40d040c008002c5550061003483e1030342524101c90903515a214400350072212555030300445031074004103281c00b050085480d201c005440c3c900d02161155134030641d16100800401000030180000070202109000300c90042095100034550148007021602c01ea25002c1d04103120302c0107801040001a4241c01039400d68284500f0000709007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 622053696 1250 622052446 622052471
    0x60c0803100b0c071404090803060f04060315020c0601081606120608011a0f0a0b030115030204080a0606080616080c03062101330506030601020a08030a061a031009 72
    0x3082d040042001004920481e451030000780807421140342d115003100c3c1c3c1003c542440101c4000403c080c00d1075400f08009841c80c2481c62010384010030241001036100daa0392030b01c0110380c55100c42010001d0b0001a0480007034020000079025010810107000500049901c076000600320b885480203020406400d5585010300790701083c0208000c40c020322030141d41d902d08078503c070394030841c8900c15051102e011042d8140781500e174003600c000c03414840c59a401c1001d601d20215680f085030003055001c2102140240c8180100030303146100d40c8011600c1400c000400d820075100510500c03c071540004104496a801100c15030840d00030300300300c2d50320780700c100c0031540101c444808220940805803c500b80403005510103484040c806003c89000640008400d4481c411103211041c00f0f065440144501d10b000c2c0300440c0c1103081401140e02802d0903958203a001d8004550340390f40980c1d40d2408000c52120f484d11042c44d50007820f009440c6140c500180d508454080c01070304038140d130f00c0f10010f052 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 622054946 1250 622053696 622053721
    0xf040b010210050702060f070806150c0718021806070506060405180307030f0801060201061d090c1203030a05060d0201120c0e060403140d0c0b0106050a0e0901120b10060c0803 77
    0x4542e240e80b02802545030000020750303510303c20b60b109103269960000180465105510850141c20b00401c030854600c0c16290740e52280c1c221590812903401381410019050040c103254280c840d01d600d0700580c0303440703000b488002e460b20000d030001d0240d40c00f0130400000400102d069584105c0071200002c2079200e00000840c0300d030417400c9000c1c00d440f000076007806140d004000c41002d0605a038030454240c3c2c0781c4108900f40c4031603100b000080800c0e550b0102c445900644410343c07202c1010304507940004684001074007499103844195007600300000340617840b80c03a40140d590250060799103103580310143d40020600302c02802c0810050350f40e0307a01048010b1041c44d5040030b04400401c080c0c0c550743c8030f0902c422106030040e4100500c1c8599200380040b0b6010300d10441101b41c2090410341789a20b0504181d9141c3d000c481d01070700f00b00409000c0d400a41d200340d0124060f100e0080d0405070301d80c043c503046600b000c01074603050304074828500c2005100d500001000c01c0310344c441071040d120384450703103090701c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 622056196 1250 622054946 622054963
    0x10311040e0c0f0409020d050709140409081201060c0506010617150111030a18120f03050c0c0a0306020403051908030106140706060305150c0c0c04020f090901091a040b0f040b0102 79
    0x3d40c44400140080c80001030b4002c1d0140004c00c81080003e521000001e66900c4003a105608c400d01078000c100400d1315041d03101c44102c50086011620304218981c4a00c4159401d030428008a00031032039100c240305040101c14094001420401401207072001009090b0000130106901c074103010a40110907449203075007000c240701013000c898840c0c000000203002180c3c05220070701454102d44002941c403140810311850503811846401c1680b5a94400302d44641c80101440e17100d100300d003c4560305403540c20081380118002c1ca001a29a419482e05a040403c3e140806580036442075043d40881ca0384000c480c1104c00c42c0c24505451010001402e115021324200a40490710b44040041800000700e8280c0c1603034804542404a40d51707403045502d0501030080c540d15a13900080f03038440c3e542010703401086030341b8135082d20300e0410f29814001884040240c00c0324112070346440103c034484440c8000c21101410454060210700769000101d141c030003803420b140b0b11483c0c0712590540d140e40203109000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 622057446 1250 622056196 622056217
    0x80708161a07171b060c07120908060a0c030b040207030212090f060309030c07150905010e1503040c0501030e0705150304020a03080d0c26130201090b13030c05010311040e0c 76
    0x1907000300042400f07510b8002e151107503c190320700074a042140c0c002007020b03481603414070510740c01c0000603200d20b0b103001070010001c405d1119104000c01e1810742003080350b00c00e11100174041a102c215000050a44201440aa005900501020707000a07008144000d02040c00400c0c181ca4807400e50000d980883d030760380002e4100c000001400484200800200030082601045615035551000210200c07c1390000450006650090030300c8103620615040f00c59410040961020102c810f030091301c16442030310102c902e0890203070104001e581501501c5061400c0c14080c00146c0d1801010500c0c106c9100d10000e2841000400602103584059540c009550030940107529200c1ea06001c4006014002140d030124041074180f0140c00d9125240c1d11882c0c200f144440300035101c1c55010301a103554503008a0612100d01c40205282c902d0034060216041e109000301d5859285003015006c1401700d4022138101800e110003010342040301c0e411a03040b184c00924299655445a41c1014980614841507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 622058696 1250 622057446 622057463
    0x42613060905090105010c081206030a0b0a0b120d051c02190507300c1703070e0a0b031e070201090204020a030b0f18061c020a0807080708161a07 64
    0x309000380c0c003407210000d50740c040d601800240d8a400055800301d0300850003c22042e02000100100d07112040380b00d412000240403616440081d954407101d0b2681141c0504046079115101007007803600c610294882107440c009044a001e007400010500d1048919081110011003c0f80c80e0f0112a54101d501030b1401c042c41103040d0f507800c4801000c1c2e901c07104003030f5902440081360034110321001c03105c07181c010318250302031080138030000003510a009014415a0400611038008156865090007107106030640c0e504c401010a5200c1040014001e5403c40c1d40c8108080c020030043d00c203000b0341480c040400040c0ba424076030b15881e049024000c0504020b400c036001241c580011909600941400c80d4125080902040c404090240b000d103004486c0995055000c0828800d09210340d0640c2043c149610b49291001c0039000300700c90020a44c00020703980d0040008011200e400d201d80d4014101201c05000310401e83c002c5450024840d000b0004003000e07812080498a520004513414168040480b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 622059946 1250 622058696 622058699
    0x207050d06050118020f0a030509031e0405121216050f2b110a020609010e0303030c0703140403030c1209170a1403070c0911041706040515042613 64
    0x800040d0100b8801c913503110013600d210810b80780050003918111100c0c06822810095410422005804060301030802400204000307551004404584110601050001551249008140285c1a030034201c034240c2908001d44283c1891103590480f0f1611303a4103500000bc291060801e41d0510581c515800c080781706a10081d0103400801b001122546510310944400c40400e1805541311120702d130504410746c100304841d01c01460684060000c0d81d4040c9072040c1007807804008079143d60703c05d82c0d102c42c91f0040030610808060f03006a05103410b9000608550805241da50060070b620001e40d4000d00c08050300014500386485a60010700900300c5c10301d003080307000b60022400c0d10762402e09001e0307483c070280d0701c20b00b9140c003c00421910f2060b0f02244168605141019080040407104049404444100700018030f02c01880700d1150140c1d07241d005000541010b00d81186460003110425180100e010100004201640983c15028665000c207c607541c1c4800d07101121445001d40507002008034460 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 622061196 1250 622059946 622059953
    0x90609030f1b060403020907080a0b030106060512010b070f030c0f06020301241d12120a020303190501140904141b03100b090412020106050607062307080c09010207050d 74
    0x425280b020074400100a0100c42801480749902c00d80c00069000485c0d400410020362042c01c040341c0c80328810900059403406103000034250344060780294000b50012910b203001c3c068540c100c03030051030300000c828501a650741d0346030f695007940c0001900380040400c02105004d032080340c24007800d500840c110741d2580c60300c581c850000070f88040e241c048050314184140c0c01c0d00410091922070801c09107100031605000801010402441c3c80d02d80038043c100309000c032003900c000030301800a03403a0040d540b41d2514001484103520101058044a41044010030007405200c2d10240c901100366a031070342550319400e080031420b071591000640d900c9614002102c0c0b104641540038017500c201e060f108a820b00345005020303504005141a031000c580c1d070229000441702c00342422001514000420406d0340c440c0060b100747c00c031000540720f05d03441b00b0707408044081c403649444120320100c080b6440c1d41000a0000c00c10072008080a41400e0005040038003a80200416002004000c000c055010598078 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 622062446 1250 622061196 622061203
    0x30c05150706110415020c0a050f0d020405070201020901120204270e07060305090c1f0e030f030a020109120f08061909020705160e070509010c11060705010e07050103090215090609030f 81
    0x32510301d4000c1049806440b9030f1022950404444004125234031071420441008180d0044411581e4090070506880c1e00586583c0621841040076400060721440150009041e2000c20390f01420980d00c104400d1118030080681500d00041000c443c00042000322110402000346519002c894070418000003411031303041d0013041c490102042641da4082a0300305002131039140c59000c16180d54940d01d103030780940c400c00c940c00d1010802811a010152080102402c41d07110b600842c00503516465200140301e039807004100b0095052511000200000c90014017111000d0149442502020702d05c3c0313118908407a0200150003e000115980c0c01c6d80c6c0741c099038032890141d01d00080b4140304800100018100a420300c00c2e0403c0d2541c4c0d02d420034131001100c4071a040427003102d82a4541d480401c050700d07000c0292046c240700748000201c1c002d20b022030600d8401c46a01460416080015200060f10b843c0b44030040d034a00140c0c0307903844103a84d02c00580c0e02e0082c83c001c02d815102d540941d40d00f442001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 622063696 1250 622062446 622062449
    0x50315041a01091a18270601020d17070807030e011410080a020102030418061710061509050103020c0f010903080a0513080a0516080a030204031704030c051507061104 73
    0x7600d88100c0c2a030b880c6410701c00300040701c0401020003824005ea10904401a01c9001407580040c07810220505a5001140070784984e80b00d050440d0800007000034a50301045450441070450606a610001c00d0f000340c03400590042c4108100440714010030102c40c0260403411000503080c00911200258580c1682121303012108154096400304c4001030924000c0703103241144da010303800344d4649420982d080d68100b0165004a5006030703141c00c0054182c00c41c501c01001144a0740141103240309450708282030311036540085c2070381290081444582504aa03805040791001c2c24003580f01c0000307407000b60404d40d090707240146070f50070000380804041e4402c40240c4078044a030801c0000fa142c013480300403499807909009040440c100180708440d40a02d003d8515039002c840b1000e00703000150b8036112560000c0c1010004330342c01040034420055249441100f030714100e1000c078100b07891038a906000324414410a401440e20b06040d540c140b031120100d84003150848014807200184081c000b0055125 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 622064946 1250 622063696 622063699
    0x3010509010c03060f050d0803041104050a0204030201020f014107050a021006150525080901091406030408070302070807060f0f0203070c03021323040515010e0403050315041a 77
    0x20100c4c04988250712003040c0c1d080d0780003e0b2102c0000d04141d07441c500f42d68006402616018482c2c85c1c40b415590307035401080c2c4079003c0e6482c0075848600d144006441c4c84803c0d40344c940e0507410b1214180b4400608103111103803145004042403030030b03981c43c0000e00c0140075030303d40441003420b801004010b50300321004024518042e403c48464046110881049800c1e600410080d54802e400120744d56124031b0184c00d06240f500108840501d50060f003072891280d0540c1280d5648000c80d440c450340d13801001c80e000130107402c089242e481c403401d0001074003480300500040240c50f0114000050601c03c01180020344504011284000d45840000c0c0130f940c1605090b4000a5400e1b50b1805d80f10b10101c10f039580140d01c481010b0860741107a00f006001601d40180a41c529911070400d40b103280101c8440940d05004550001982041c2c14042d08041445542e035142c401d446004101903c02030b8001c660082d05850106c2d22030305e800009462012584041941c0182009803055200d088901500e900520 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 622066196 1250 622064946 622064951
    0x50108010b04060504090c1704061e02040e180102042c010f140f060d02040e040c0905040302030304080a0212040801020d060e10060e03070e280513110f03010509010c03 74
    0x3a500d0501070a84650f02400b00003030707001c0c0310402510480da003040c84444064180307404400b1041d048040780c803c003190241e03140c5485d90b0b00d0456130360014035200e0310f03000c1922080d441c180c14a1005540c001000c2d00749044500300c44410700d184102903066030041c000d409003d64001c100f4080c5000b004500c1d24003091113500c40000021861040402001142c16403285614280300600030028514500800e81d90010010040c0c1110125144020005440210341200030341c00c00b0300702034851015a030007800d1500d103041d05010220760004140c0383d01640c48036031035a540001000c100d0501c04694402c2424210102d00400d1100c419009407103130500d5860100041555856451500ca0f0151920708111304085018044580b00d42901000280040c00f1030380681da840d044900c103c0001c0b00d109096001030130f45034290100c1509001660031401c2000d100d641090300c84075800e010032680c0202424241c101d10b0340b007511248015404a43c0081c001c22a03403070300da00305034064201c10310b13000000385c1f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 622067446 1250 622066196 622066199
    0x281e080c0303031005010f0306030b0c130807060912060e03041203020d0c1101031a10032a1d12010905010e0c0d1203180f0f0303060b09090406051b040e0105010801 72
    0x7000415a1320030030b1301c40418210310303180000658025800c00041403c06480e4107001c0b02080c1100d455600072003020201940d107100ba60200b10b4031489e00d820180c0310350864031040199591004c90041901c032217801d0b11880170f40c00c1c40c092000300b000250300d410501010600040b1100c030034283c60800c501035000e6031002c1c21806030440d00c12449020081480000e440d01103205d52181d4808690300c407002d0041400d0004480002c2c40218120303010100080d01c81440c10002c4903034101700f04100300000e0881100300c544d15401360154a034540c0089491002c103058181a81c1c941020b0381442d18a1002040b4019060800724064075800c3d9845042d4070078200882201d007400c0301c400c0764482d0418201e0001d8118454200c014222841011402400c8400c0800110340f524030005141880341200c100386d01120315003e000d46590758041c81c090030041c03000e04225100c15115aa1199000c1800100c690300c860750066840e0b52029903601d214030108001c107284124035030703c905172102601d4409080e07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 622068696 1250 622067446 622067449
    0x30309061106251205040506040614070206060613120308091903200a080a0f120501031a0703021c0b090603010902100309050309220b0a05281e080c 65
    0x1101e003070720410100d032500182c103c1075031003400d0000c1c090503162524040b903001c03540e00079082d550700f954140e4060f00701e0024817040200500c51308090751030305180d46071107180956010b919075400500c254007a0340c00141d880c00c060b401c40c02440203411400044d0030712405608000b44111412501c0f00101d02c2864101d0111540c4180c245980d154559210180c00c0303c0b813a40d40180a00e110b20209442c85074019003000540d00302c010b07100c04801c664420002408200c001042d002d0560b24200b422460240140f02155000c00c2080e40c855000f50664419101c003d0210000c4c07050700641e00035940b2010f400c1c9004035150704040b8065008a42c0287c07035490300f0007003500700c0c7c1c61403030029800303501d02141c850103500070b0300610496401042681c1c2085401408034850039036030141c4010a402404510101c070586208a00000f14151646001d9504140c040745c1401c1080640750501c050301d0300740f100f04c00034909040b00036000700c523401c840e0040840005080c170001030090101900a860f5115000d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 622069946 1250 622068696 622068703
    0xc010b0405060a140409140a0302010b100f0c051e01020a1202130e1b0f03040203010e0708070b09031212041e02030a060209040b0405090f12040803091512010303090611 74
    0x4202c0102004a11882e20903003800e0400101d0015810a03102e2008001040307101d60545d546c9802c84014184440561500a0031202010103440c8900304402034001f015a20030306402001c0e034103017040318844d0b0880c280305152800034984440000c903000d902c26221601900a015815026110b0006110700b000c0710500364026540301d0a00c0c54580042085410961000701e9000024948000381303007507002900c0615a4448068004182c0d000810f000840c1001d1184286090300800640710103420904025126002c3c0d12a0340d865502c08250f2001c50f030340c22b0002d0341d081840c9100080c2d030f0700034580220742d803418100c8054810000c5258050f0741801e101e103203e001700303600a000e1300244841e82c0d2110001d4001182e03040d00160703550313460000b81c0c0710f5108041c0208a00d00c014503094220764180b529090313000110710404c0d06e0900003003012070b4002007a5110080d040300c08440003090403044910741c1c0140b0315040d0056200400000134141c0011400081d03410301d0352407003641916503112658 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 622071196 1250 622069946 622069951
    0x6010b1e0f030402010f11010f0501050a1d06090a141303080f070c15091401150b0a020703060b1503070e01180302010519030b0d0b060405070c030c08030c120c0c010b0405 75
    0xe070260108005001076106028510360700303040c0d050492907050900c800e40c0c00c41e90201d45409417240d84200500461400208401c01000480b44003440342d20150301d11154040041c0000e40a4500c61011920f40e0400b50030168a000d0001c08006103882c103c444181c03a00600c0805401140d01c001c00300b03075440590007003503104c0d14164031091b500000640c1c645624200c1c3d882c035100c0c0c640e81d4110440000300580b446070407031283c030000451810100e251001d810303074085d84086081001080030710107003034011400104903074002c01e001800200304030105141c14012100802c08030400400c1248040d0048003d00c01080f0a03030300c1c02030150b0001c0070324182101c5400041e010400c18403407404080300d01c40b9854246203151401103104c100c4240400ca8450322800100ca0a8214104100942c00d0912036550720105900d080e000b00c0040340c4000d0031030402420080c2490380000000340c3c0050380b200445050442c446d40c1c10b4180e00c0d043d803c41405806c210124012035091000f0704802c0d1410b030080300e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 622072446 1250 622071196 622071217
    0x30f1b040b1008010e040317041a0c040f0b07060b060c030c0f030703120b010e04020a0509031213121118180616030b0406121101090b0c0a06091406010b1e 68
    0x43e10f64244506500c005000034001c42c100714041803401503c0180f0000741c0c2c00745224103a000403602c0c2500300741c4191000100b0403800031170309020421212180040100c2112a0300da17207180c0c2c503819420082d014282c41d014182e002030303000800b03414101e0000020032401c807002056400007c0302c0d00c025a164400c0b000041d000a80007034002120720b080b54801c00741400c0504000740074442403008030b005da81021989901241010a683c0c0c1107003030501c40e070501c2000c00c028071450591540d034074214005460040040700300c2c500f082c1004020120380365100b401300081c840100c031052502000e0304840c04403030a40d1000c4168038940b080c0ca40005540c0c2c02523600042d031413803001144900710300401c00c10058907130041d25180c00003041106c2c076804418190003070340c0c1d0500300c080301e40c00035202d01d40da03038441c401c0031000700004100c0c04004a00306034100d50015020610449030305151040c0c940400742908240190070001400303038520001406026007100c1c28000c0116490880e40240c0105c0c503528 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 622073696 1250 622072446 622072457
    0x50a0b061b3408060412050a021507051b01021e090604180f0b010302160b15120c010f0504060212030604020403020603070207080c01020a02220e07090203040201180b0d0506030f1b040b10 82
    0x100440d0003000507141102c03044c41114000b800b02c8ad1130240c080c0c0255407000200f80c00080b80c681841460404e01c1c811281600290318140346c0100148619900ca4149840400041941d21460ba58502102d00818403505400b89002d050701c042001030094143c00c051052030b107181c84d4815400b03802540c00010090548034900c0c000c6440f810103040c1d00402c002a0741a840008400d6580c502681c00341561404c00104441c4080d9000500400e500d4612441440014130081000c2d542c0080e90800600c20000255101d4480c540031038040d000c0c0d500000d40c0b03c007000c01048481907001980b0021030b0380c0c44007111500e2624000680c4c0301c0c040440c0203034128501c0500480350361000000070024a1760356200007180b0001c41805420300011381c00840211703400209100540d80e0016410f40c460807581070181d0054504250800c0a06c80c846009050a4494000807420b0786d092218018142021050725070603540341d5988400c1a154a40303170b5101e5850234500a5560604c040c0034020685e960300c40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 622074946 1250 622073696 622073723
    0x60507082124011718030c1212090307020604270903020312060103050105060403030c080d0c0c050f030415081512010f0f052205010603050a15050a0b061b34080604 72
    0x10101007200ea0340d05e01160b1320080000100e04102041803641c4d04601403034041d01e0b46e6880342d42500494014041259a501c10300105016075a400215011901c0c2c60b0b00881c0c1d090b4081040d40c4503909030159a40343e4601d00b81c501400c0c1600070004110b40c807601e1466589a40d206030040d01100c500b070240380c0d08100144030501c00a80141c208880c41e42c025003180b42402c144210050030313240c0b1f030b5003d003001420000b102d40800104001542c104a00c0300017035818541000c410051070b11800c500f0a04202000c00403c469006050b491500500058022140101d60b000c60074046e10440007200c58562a0100c070100c148030520509004103804407940860001ca0a15201c0f030071300c40e00050b20203544c0e0362000800600c04006140318903220b07008800c072804019144008680000313049400041c1400045c00d440d50b07400d800c48071034180c060700084000000354011444e290802d45084151154401e094005800643d5100c0d80c2c0c1c101002504481a103034034000fa00c03910705070707002811440d58400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 622076196 1250 622074946 622074961
    0x1f030309081915020901031811150705060a0c050c1608210711130c0c0209091603120504080102120a110a1b1502160b010603060605070821240117 64
    0x403e021a0140340201d003040c02d030303042840c072005004012100032102c0d801d502744a0410001340c99000112803445070820b00789480e441d84840000300f030303811981e507a0301410511074010001d56003190440411140361400700400c08003039402600422030350748140c00b0300d1207520002c1012410401c6120380494201449541c480701c992083c80b03112680a2526420402c4040d89441008044030541d41d501c003014006e801031107107869010b411901c20760000980900301c0243c90b080030007140d600c5411582000e0700f11400f00c5a40c0159040421706500000c1c0f0058252071510342680500307040c0c90104842d4011080f0325809215440e6120003003420300b504072203503000110813500c5650050401e202d05415454002e0200e0b44964006120402c1101002c0113000798506541e0141c482c900f0100023042c223041014090303010705480200781010008455101101036603080c0f12041700f05407081c0242c200b0501000c10902c05400480d003600000e0ba901d10341c0d40c491001c141c0c000640c040c6000c0c840c0c44014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 622077446 1250 622076196 622076201
    0x60a030c1502070b0c03120c03091507020f0114041103210706091e03081006090506090a0e010f06030e03041404090c0b0f040e010f0308121f030309081915 68
    0x450341c030254041c40c9000500c088030000100013840c0c0280140d641e03821907400d145c4120402138a00c2080d000c0a10402649080000c1c410140001030f5030900021340e01c10384124507166546100050550802d96061280b080c6004041d01079845a07003a04154141e0308141551502c10710340c01d00e01071100f076506d18424004800244100750040f030011449000c180c49035000b80603425502c8090081907900803050546c0128200d0b003011800080000d039914106c0002c3c502420b9000d414415000000c8805e00c5555400981b001080446c2880000d580c1d210964201c0c40900d10030000820709001d17144060107004400c0b0b60503030750000070400c070542d0302c4002e010003802d01d50801c0300c40c4d034400440071400c101b00b103010300402d000d0341c0d41c81d0750344505100c0d030b0300c41b11241039201c8006140f14400600000702d940060754008410040c01541e2035440d500d00320f90351120302620915040c0c04100100600d94032840440c1518a0f080864406d20f4040d60420a0340f00b03840c602415031440d001c0c00f004181d034543c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 622078696 1250 622077446 622077479
    0xd0b30030c011401170a0c060e040e07121b03020d0f05030c060a0f0c08010f0605210a090201030b220c180909030806010206220213020d0e0105060a030c 67
    0x800c69040110080301d560031a03c02c030345500d11034405900104842c0b4043c8400360245c84045029020520300e6907103407110001d00c1d010300404c0c0300611444203250f40301c90740700d116481c070180c0440b00e1f81c2d0f903558441c5401d40500402510700c01102ca481c90503030f02d803c4072160212a405484c1915030707130147e226480c0307952110304101c500340001c11203481034500420041e03006507090300c00002d2007500100c8000841e4000e40d03508003441382c100010040d4107800c400b8141160411300700701d41c0e542800355901052039218070842001034400b80034000c0381c64556009054103072003a24200a0507101d50200f241c1d810360b40100c05400305d447d40e00e610f050035558000300c0750489070b03007030803042d1030314084907440ca0400302d07044010503d555181c00002c2c1540300700020b4002800b0300103420f1904010b21480b80c10080035880131400e10766040900110344808035504e00c54220a00b0031515a1500351048020304669115418950700b0003010801d680f03400c0c4c018504503a40039004c0468907103040741c4e01e01202c030030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 622079946 1250 622078696 622078789
    0x14130501052104030e030d020d1e0203090d0b010e060916030c23030a1d071e0504020a050309060f1e0402041d030a1101091703130c0b0d0b 61
    0x406910660b40c500307103800c0c1c0780154807030b4880003400c0501d4000c3c50710700680c6100704421944070702e0340144456081000001004003044030001c20b800b82100036459440380d90146034003c20b01c040010180100281c001b41a40d0380d40c118201c07183c5481c810042c2a01d01540c0181c1301c10f811250301440c090113a0b00c030f41684011360401024842a002d082582031a900b00481c032039074000010000020359906c1109603004072210b010071001c028690003603641020340289000318407228031801c400c0d103810301d04200403d0b0040080d5030b03d02d0140002041c58000380c50300c18046c42104081549502640a281c1c8100540500d101504030031802c0c40b02c83c1c0c04080c0003680c102d80d8030200300c41c55181502c07240300591501002150313107001d0030070003d0400c0100b4008640030b901d01499140050042c074060049240c681261903201d803901c901140a44400d00002400b00e050300600040340d55901d80074040d40b82c070100c2d00f0403d60f03041c14103126445e0320b01d01001803007408440d441c060728549200c041507115003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 622081196 1250 622079946 622079977
    0x60a0503030a0c1505070e0d050f070609170d02120f1303050309031506060d020c010e0a060f0c05040315090507210209060d031218150605011413050105 67
    0x1a1040840d0940c0d202c410900c000030a1072030640180710354081c400701c2c60800b66104205602d8045001040070002e0042d6600c55181c500600d0117005040004280c120111001d85646543d1000090580107880c81221984d440903d00103001ca000400c4048281010380c016084400314074803401d100c2e81c400703100764850f10001d00c281004400303515400409184107000543ea680c0064040510303013070f840d5054004052404040100c143c5800c41658502808001c0c0543c03210498550740d4054450003501034903a00c01c036001c040600096410002c1441140c41c801c000a640782d006c12112480b6a02000e00075802840a042c002c0741c41d82e224a6410740aa41034555190307c8500c52400601c04c0c510400c4042085059001980b400b0300105820082c111039410401c1304039a40544010100747c0d10220301d50761080341040301040c0b1512009501d42c031401d0004803a1031031000c000102254010785000032520021590281c00800848409141600798002980d00e00801199240e2004040fa2980300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 622082446 1250 622081196 622081199
    0x109020f0d05090717030a0f08073f0e03250b070908010605040522020f18010e0106080105030a08030a02120115021216031116031b06050918060a 64
    0x980d588216401141c0303070b5001c4c20343c50b860040341e010fa62024038000746250300704000c6120342d280c00c045039036202412818580c9659981c0002920038a40385620714480c040c11000d90140d0594540180e0351488004190760040f1f501d0100c0f81040f500c06007150f111ba603004000507000c074864000300c00a0008817690095204406640e02040d80009a980c4004101041420701c1800710070700450010b4801500c0410041c075000804141810750090040300e42d1214140303480554481800902c200040540740d082d011140304200c0c10001d10074031411210325403900020070168802c2014604131903009006000e004000d454640c03c42e40040d03d194055039007008400e04a80e40c3c4d00d2028000c00c41180081124404001c0c0681881c1140c000c5482401c400c01500c03080e041d00a00c06100c0a41500d000c2d104580c18208040c0b400c81064400c003540101a41e00004000000d400c519284ca2080b01d03441c1003e944000907035250180208070b0780d10011010480040100740c11149138088401481080440d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 622083696 1250 622082446 622082467
    0x22030c1203020903121e0f0a020705030a08030403050d0609020a170a0c0806060a03060509010b1c060b16050307050a12020d09080d050306040b1210060605090f0402070201200106170a0b0109020f 85
    0x1940844603010b080b25001c00d08c07403031650b0144003000080c1000c3d406001720b48200e03950040c032844020001000e0103408900c185a84181da0302400c003401400d0b4045542d816818405000900c051000d07900441440d80010240032140c01000903e20386511100c2640d2202c1c010000541c100740c49010806a41d2030340010b40d607a0303180307810b8000d0a80c045030503500d07141059a614001c852441603540c640c285001006034440c0b160880c0c0704040c1c0e203400740e404500f061520710700790720580b80c0182140c030400d60200d01307101c014104185003103081c1d000c4500080d075803e01654601c0e501c2c42001c1154010300c2c00221428000d000859104000820004000c4015400180c080c200e41c0c003800002d070720103004868072400a01c506805060b0a040103030074401c0f403000203414040c819182c0c50050b07030049010000c59004520508a1080c400320100b003401111291a0090a5a00c503550050300c0e29016130100000229650f00d1803608800b400902d80e080001c1e2101951003c0c01d64446070f4130821040c2c006 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 622084946 1250 622083696 622083757
    0x40b061b0312010f09110a0c02060c07030c030606050a060807021b01090803070f0c0f26031e0307030f020a0e120f031c05010906060807030522030c120302090312 71
    0x81e155005240b0b020904250359401201c1c0e0000c0ca102007075104207e03030600140c10411641200d5411619545d44003401c085140c10401d0580c4010300e041d0b0606000300401031607070805015218241c0740e440c50141c0e51413003120502030940d070400140c1c001151903400080302c00d114020b200c406040041000c0d83e02c980c038a2456100d10380c1034821a4402101c1030402c04801b0000004140140800c400c0b20706180c200c21380341d0950300032210000003003e90000d44d14414003d035007004200481e1200111900c0c4494440d5078000c030307000c00000b40b034500c0c1030700e00104910a03035840ca6466500d00070700c240078009000072810849081202e910a4000203101c02034104014582280055102003031052412001006c1c0c401c180c04c00b2900e9030030b0102c1409115440100039510150314a0085203686515074002907644911544a00724085270a1103428103810035100c0b04ea440c8a81174100d01c08140708421000c9018103c00700360b06400c1154122038021040c0048c00303805171ba4040f1805060554850880f4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 622086196 1250 622084946 622084949
    0xc0301141308130816080c0145080105010602031c0b0a0302030102030c1308120f0f04150c050c0901080606010f02030c032d1801030c030902220b040b061b031201 71
    0x10341c01080c01e84040c45c010600040200510f5000b0b0030785a50202c0064070807940284011054084141191000300845a10700120000403070110740c2c15482c071802d041d100c002402840d80c0380d2b003032100005525100204880f01d511140182c0502503015811000203828a07c40e200c0c1e20542408002c005030f6000c1c40214010f50301503645503541d07000d810b01c00d00d102c00c0643c020311050704004e04c51038504488504031840608515402c940d152001c0301044145e01864110105004d03800d006a101603801c40140c0405c280240103e48481c80303c0c4040201601090045c0d48030364103c074003c100030b5401a01e05c500c1c0c4205038019a4100511002002d255801c10610390180c842014100400c09800e00b11007500d44c1505840700380792107160680514403841ca040064101035540b400d00c84541c1c8203500455180380d00800c10113800c00d4045200407417140380c0c0410030f120751900010001c0c0746040d11504480680203040a810001032101907508403881904c5404680002c1003181c844404042c1c64a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 622087446 1250 622086196 622086209
    0xb040f09090503480d0e0a0312080106080903070302070b0a091211010801330c050619060b040513020a091205032101030f2a14030c030114130813 64
    0x109080c10720789922403628681c01521120708862003040b021520003056130031403017201c1d040c80ba60035222480850301e035103401c1d40702401116184210000c100e6002142e14101e0b1241c0c1d9842c1e000d6110200f0711512032003000d6005002d640902c40401c45500e401e009403580c1c00c15824809034656480320120302c480307080542180c0c10703014045044a0340d03030482c6440e409840e003140740960b003440640b100708040600c4540c2c4004000030602c0b03e58081d204080f160300c4664040d05454643c2004614080000c109a107000c02240c24581c02048400c0900191021544001c101907008a05826200000d42c405100380081180d05403000c51305003608000c8084562207a0015582e130a240c01140c001e0500740c04c03401401341c141000400204590300072144100d6006041d40784149092141c0394004034400210031800792401100140c041346c1070001400f8503078181c084c0c0e00e403920100c2c201400ca8ac07107043e034403034102091008500035180494000f00001d114202051511664840c01402d5401039400300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 622088696 1250 622087446 622087507
    0x240a020307020a090204060912231501060e0d0b10030501180c0902030103230f0d0f08130b1b090d0b06040f050c0f07081303050c01090b040f09090503 66
    0x1400c50800d8102c0f44010300d5075060850905050410041c03c100191090b01c3c40d015481c0d01c1401840070080f04060302946120340300382d0190400da10340703803110a048081c10b4a07884032000021620f0203402860310030000144183d4009074242d40d440c009902c0600384002d4601c107030b400800010403d120b401c0c04054040c0c41d0003010001441c1500a90a41e6000303806100e00510040001484c02c0214403c11241c0210309159040703100020b500e000103c80402c20350303108000310080001e4004010806502c40350750b070080b45a6501e50303040402d40403003500030450400d4070300080f85000010080c407c3c840d04c0781c05941c60f0001202c00074a034030001c22019928042d40c035091144c1483c051150880303413502e000d8144960310b0f1494010b40280030345081e500c22444001200c004000000c0c04440f204500100c02c031024a403071381026581c0f150200e00c928041800040302040402c1c071300c0e0a450844900a0462440f45c0c20f00301454058814901c04032240e220500200103492410141d90400c2c240c1c1a120 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 622089946 1250 622088696 622088707
    0x303060506120f01090207150207020f0915121212040f141f1b1b02090a050604050601110c100c1e201c020a031203020309071a0306240a0203 62
    0x445202d002c0c180c0c0100c144601c1000240c0001e00c1010744004615a40702e130068450b44ac034004a5001001000746542c0000c031f8008100e050340407511800a0000240d89503102e0040204d2850340e80c40b41c2c0303c444209101c00b0700000d0303180c0001090b1964850f100300c400007034051580e9103400c03111001c40014159034200c080d802c40260310008202809401d00391081c00317003495641c0b440464541d21b031614001c2107410540c1200b502c43cac0d00042c100d516405800348002d460000d00100040209881ca50320817801c0c1004a80e05610908003004c94589800c050b01614000c40104411036000400a00c14000080f8003c00460030407444101240807090075051080400d16001c15440c10340144000b2000c480da40b6a0341e40e0303c0d9001c07401c0302c5502800b50211600310794000240b02036682e42c4001c1004400c0c41c040c0c441298942c01a50043c0d01000c21155625120040001c40b4101201c0000c401d1106000040c8945800a07001c1d40c078030907408401c1103001c0221030b40250b5034040c8170701c0710141e400041c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 622091196 1250 622089946 622089961
    0xc080708071a160f02031c1a061207031a0a06030b090108011b030b1908250b0a031e06080304030c0b030f06130b0409030918050405030a0c030306050612 67
    0xd0602c101020392000040d1420360060310407805107505031001c1191804424000e203000700304484585c003112001030408113104041101030020300c10010003048829a50041d98201841611000130080a818245a548103c201c0003040304089444400b56002410384d06900c50511020151210b0381c0d010940420141c140010380d601a885001c0503890070070220b05c1c2d0111f82c405a0780325280da02c1d000c5503001c0700c01d0000700b2401018114200c86a5900710000316494001051070102c02142500c0309480100c40d062807020059124403114040104280c4501a229900c0110068884004280b030501c0c04001c0c3e030101d600301c0d0841c078416880050207006201c182e0401130002c0c690700d14440d18600d01090307040032061019040c180500490110340e01603149030780180900600c00f40007080641c180c0d0900809548a600c20284405a500c1031031100400d070b030040034401d030341100044d45040d82070001240c10300088030060702016690f070000b095940c5c54074001c0160124980817040d15041a00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 622092446 1250 622091196 622091213
    0x40c0305060f0c0301090c0212130509010f05010503010909081c0f0b091e090703060f020904060602030c0a14070f0801090201090f030c03080a030209060c0d02011b0503040803070c08070807 83
    0x1032200a200700e1480400a116003181c0403681926120503022a1010031144240c9ca02820210700e282420800702c0e4112030003c001b00c5a4084510884044138940d80c2d6028a1002006500801740020802c00050200b01c0c4160041202c00344034050071803400e006c3c07002d901a04054580a04015500e8018a500002440c01800c07400041111041214280089207001072064401f070401c11800d0000002c06009007031088900a5400580900222010b1035184000350701c02c0d003a6500c5036152120120340540b001095811035400718004203412145600e80804030040c900e03050460f0322139424003007400c0540b15010b1000b8546400040303504200d034400507100d11515048038028010007039042012480b103e03441c1c01240d8102c001940d5610340a0800c41c041d21a00707500a800c22030015070070040500002e80b132454801990300804c101c80d51808495070111400f8a40c02c0020010701c04240404c000200450700000941042104005a613031010019000503405403481c0c080030940310107110404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 622093696 1250 622092446 622092451
    0x40c030f15050f0f030a02270a02310f090614040509070e070e0a030b09010e07080a021c0501061d06150316020a170703030b100203040509040614040c030506 69
    0x710750000722035003040301141445140301d100303034450102e490040c0b94548041c00340040300780e00a8041204030b003078a42415090002c0d0050154990340e01c0c4005904076201d482a5941c1844030340114107210040049948144094003290340c0700e01c501400003919542c542c105038002c1c80c03803110100380e03185410624000301265600b0ba42c0501d082130100305a005000c5076482c20790b05640c2e9a08015213603200c045a144001c02c10042c0c200070003003004000c1c00b1580000900c2891036500a0084c2c2c0401801c1e540c4400750b0344560981c5a10081c03c050062620008041501001141c4850703440c0e0252682401e554040d40320b0301c608484150f0420301d9210300d200207584200c05903a44599480c0a940702011440f00401e0392600c1448007010100c980d01c00e101151103540c000d04008810404061841d01540c00000304601027842c1501415140c10a030089000c6225a500554206840d040503c869031800600845045685071a06007030034a00b0030042d4015405510b247d8259800c502d001407038a40f02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 622094946 1250 622093696 622093721
    0xf1002040e0105090a020705070311040b04091e03210e0d02030901090612020702040e1c02240714160210020a0b0417041706060a0b0c07030602031302040c030f 70
    0x4000502038041e00d080741904455041d202181959615801d8000a002e6030000074103a010342c20001042c000d44280f550345c10a02140e00704000e900c08002c02048469060000344040820404107590000c140d500703010030760107400c205082c1c00d040000251003140d100350181040e9541d00c07441541580402c0241603900e0f10380002c6240031072580000c1c05101641c8540030401400b80da10122024058059903c02540508180000c9543c04002c50700d60221101c1003200051090403111100c0c0300080391484032040d50b03148214202c02c00b80000c803a46000740707a80140681c080c1d44c0940480c41c60010032100103400094403042c400751041150074220403902000310360040302500085054501d0480e04154048064800ca01c40e003c28403003a80200c1d40201014520040c0005c149200440c0140c401c0078100c50b068149522440036204a001d10340103000550301c100000d1000894075070041d6000740024000040110300d650010342034544d00292035000985603000c281ca031741c201e07001d80070680c44d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 622096196 1250 622094946 622094951
    0x1050901030c141512010e150915010908190308072c030c03030703170a0903050d02090a0e0118050106050c1002031b04080f0706050304020a052205090f10 68
    0x95502c915501009074040d50480c2e200c0d00e210881d4942d12148040030450300921500d499007400b042010403640c092049005100d100c100040030540e004202c00d008800082080d4242d85640038550404800d00d00400d060012003000400e40e8003081000300414200b2280540881c00d03036140007441e500000d8901402d100600f41c4000602b441c894080c1d0124140c1030b84003482d140440c4c0081d1a042c0021800d41e094000000c0481c1031583c40008000d40c0c449a4100541a8403108400300450f40240000750003d90144800c150050310780e001041d03802002002e0008045d03e032203003080307007500aa101c00c6584100020700602d05485018150040c100780c1000c5d800e1040c1e606d00940c0707440c0740c1c411040119500000003030f02c690307145c3d58103503580c0e5601100544031030f00d031110903559881d691903143c101e124804000803080c1c891800c603486940c0c05004a1003207441c210600c178a0110581d9401c1e074007100504021500704d142d00c2030303038401c8158100515210b840d071034400f8208044190448001d50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 622097446 1250 622096196 622096199
    0x15040f03050d031803080406110408010608120f0703050d0902030601090c080a09050303060d06060e0103030306170303150d0609170406170c180a0b072108060a03080d020c03040e07020601050901 85
    0x13403003100f51815035007504000358585c1d1145000c00007081c00d0020201c1492000c240498040015031082d010b40f141c840031214201e24050b0700585a0080c0110303007142417001c20501c2c00103449000078000e4041c1400005c40d0b1240154000b0f130404900760400d2184694038805900a203070b202000c0c58008480310410031120740961551a1a4800101600d00440e400c001d481d0070170070168402c00040c04a1007503858196100d203801000b42c4101e10404060f1160a10405850040401124010f070b042d90401088014548284110b01c0804007058840607544e10100e000301d40320b800584804d518413030307030103170b503a800c0c0000078000044802040a0384c40100342003109100851088803408034170304080c0341010b01e040340028060340e803d400c0206400030102d8582c1c10000c502d11030800c481145d10340006140b2144204468002049071201d5000711544020004211101d0060003051b01c080c1000d8a0000c99a103154510340c01680124402c1100c01d08001c1d07050740c18822103014020444044c0103d5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 622098696 1250 622097446 622097471
    0x8060d03090603020a0e04090b0f0907060f0c0f0203240c0421110a09140c0703050d09052e0f110307032d05060306180d08040215040f03050d03 63
    0x204060b0051005044e80040c40c1d5522038099041105c00e944020820303c0054400c1c580813036548810b641c072654419011000c2031440c1e102154a10503a05503a0769801c206500103030848030b10b84540c0b0140c901c10060307026900540c5090041c20414401000d52010180400051384003815004140490218083c003051008103200f42c904c10000416240000380700205041035041c0120b0f1034a95544204002c0c07000031964943d40106c0750007612800c8502241d60b42d046100107502c68210004c0008008200701d0468200710380c4518650341c040c604984010109c0490b413501914480e060050705110041c1d42041000c460280641700c1c4113600c1305010724100b030f40f40c0036400c0c00040e007180f040c1915802c41ea200d103141c0000700000310115400300c1c212000c0381d00b5071100800c003e40d0824000c0c00340d0030000b0128440120700d1525101c000d070003440765150400088884200c050402c0741d0203122000d116415074201c80140010700502952030044c1c0345140303407191500160344a20802d0508040205004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 622099946 1250 622098696 622098707
    0x1b030405130905100204150806010c0812070207050312070510061a07080c0105070509030c010f1d12070e09100902031c020328020c041505060c03040806041208060d03 73
    0x310501c10002054420903441d0140c18100310542000f4020b20210700000c5118001c0000d048015060303c54101d03c1e15160011141106481030190205c60104001920580024103040c2d00064900c141c4014544400029040c103652020214040d03d02003010404c1c00340900410f0100101d14034100b05542c60070101c421781c0c4402c2e9880381c1c850f0f580802da00c6c044c00040b0301148c4030801490300800c6546007020000e0529045480c82c54007a10030712450020381e5000e070300140ca410f1066100d01420a4108444040e00d0390766180b5544c106500140304150725074200302d004050811a07907414031a06d06280307081d24190400c00071010703042c14602420050f840200d502140201101c5283c030801d0f510340016851032007408144040f0764034a08072843d00c000c1c200040e55100d40d01e030707090303034007224064007004250f9158840f010b08c10391480d40c0c03c0001d440d0900c001c0094210901c03e40381495507407081903081c51000c680907640628980300028036980d100c58190351100c01103d90698070302154800406 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 622101196 1250 622099946 622099969
    0xd0e0a0603020906070f030327241404050304210305070b100b0c011506030c0801050f21100b01051207080a0f020c070504180308040f03091a1b030405 66
    0x74154000350410f15903e4400c11581c410f03402c0700ca4032070500c0583c900140140011a041700082c030b550545440443d420689002080d500b01910200d10a21007410003034429040f48012070300da5032a807803003080c140510491841540290007075900d4a2503c030103402410012a5915108504110306000080d0441e00742c07005950030184010541d9036074aa0025081c045030042d00c2c07134104c04141c0c0032041c00e0542100140c1c0f1402030703111026540c0d4441c2907068031945209000805c0b4800010b00860030641c840051001d002010342c00007005ca42900d15442026005000c3e417500414280d6042d0819402061385052007840d01d18984100031545030004c0f0000380005041041100104070042d125802000c500444281c0455481c814180643d5072004140301b218021800c200031504000d500b1001c010030b2035010f403154490307542c50f5540c40c0c1c280ca0303110104500f0301c2003442000c01d05e40b18440c030901c40d0039030051125645250503032a0291610038440c4c0100c01d92720410003841030b500c440c0e80420 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 622102446 1250 622101196 622101209
    0x606040e04110904060207060b0f0a12020f10050d06050f180a061a0d0b06030c0f210a05090f07060e010c1112070609080307030816030f0515030d0e0a 66
    0x8168a5a1409030319180d00460320b281c0c8031000d40e042c4400e010071640202036081c8590f4081010602803000e20038010700b0001207543c440140103040044032413002c0c810450910081459440d4625000010b1101d81c1906055001030004500c805902c00c90780300340e08c00b0b02400c6810342072841c40d55002560805641c580e026041b190080400c0786840c0a4004002a000b2410700100880028080300710700c1c0c11501c10b00020170304101c02c0e20002c0c103200301180c1c0225015003040b490b124010705240c0165020041e01a404071034030381c0c4003400c14500c0300858025034002e5400b0509042007203d49107012040c81c84a1700c6c0c0d42121508102040d003141000d20791400a0034140c24050007402c006185182c0e19640d2600f0030b85441303160018500129002040d940d0b00c2d15503c100b2a11008400c0d507a000c0c803200180030480c00c80100c2c00030059051140c10b880c0c0c0038078000c41c11401034108003041c1e40d415185030800006190404d02c1c54581401704480c140c03500d1410318128008032001500c491903911848 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 622103696 1250 622102446 622102469
    0xe0f04030c020315011e14100c02030312010803070309050306130b1b0c030d1d0607300f0f0209011d0109080f0607020d030c2001020408151905060604 66
    0x1ea007151410300c0785202036081c030f1103922007039a590f8040a01d83c80f90707484420641d1a642c80003044c001e000d00e05007174140744007400015458040701402d651003902c81d0b03809d917071510080c003c10b68a8207d07006900d0190080c1c201442c1c0314682d5103009080003000c0e802031071007134000108004041030a13000182620f80c0001c600541900da41145130080e505c29842c0c6000480d0024001c80320700c01c00801880c03001070750842013281610101a56849100e804900031302d940003480810703003061280c09100b2000303804904d004400d00244d80000040746030440c40050650322070810070748101c2e031440f070f800d012442d00c90258581094400020040c1000510803426a03090b602d00d0941c69114103c00c0000d8442d0b08225407004801d2052295a8070084078404010f20801c07009070b8000e0300c42d005031000e403282a190003842c149100886102c0803000000180259030a00c40040d080030308000322000040d4641483c0c00d2801c0200700d103500c107840c440301001d00d24184800e0003a81c0d1500801c40e0300302c5803950f810 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 622104946 1250 622103696 622103717
    0x2011b081611030a02010e0c01020705060706050a060f1e2c150d0506010f0902041a1b0111070c15050405060f0c0109210e01021c050705030301060e0a0e0f0403 70
    0x10307622494001080490340c403000c00d484c0f541c0713501540064010440d1038102c41100d42d105004990b103c00c1d40c00b0342a04020248986400a15944c00054102c03d00c0314012038035a0300c5880d2030030a510075521801c80701c500c000c1c110780c1c0f82d070301d401c42d03140680701c0701c454000703072045005080b0001d0802c09070350500c0844080002c0c00d404408070440c80280c1c0000d0944d190341045081c0300380e5074002800fa03c83c08408650000038a40c1e035901c2100c04441541c124602030300b4140d03440300380940101c070140b200e0f04c0c500c0101a10000b000e104103038640148080c680d4485486041c8003003850101d4101b21b5a158240c5944008107400500340c504481c0100c85640c0d03924443d140008030740c080d0401c403008540c240000d4038100b00484106082d000b582048174103d8684481003120840700482d0b0250241c0c01c02c6924034100c520780000c0314045211400c1042c074015503541c400707156602c243d001d00000f986400180c0e00600e0080c0310b20009010300000c5042c5401d00b054800806180a4170040034420544517 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 622106196 1250 622104946 622104991
    0x20a2304142b0c121505070e030d12090c0308041703160204090809090108011a0613030206031b03011805090a2103060b0412050705090f07051b0a03080f060a060c02042309010c02011b08 81
    0x20f3380031944002900c00d81c640c0c0345014101d540281c09440001c840d41c071a07c3c4a844000001e039208403000e030b55090180500f83d002d00005104130350041d0f030355002c100036041640c1ca4038402c1e14001d10b5054000075a1a9070956001d041107601c4a10310f01c40c02d420480502d042171001185025260100c840b00d0f500c0e02c52a061000d000c60780104075803120004000021040c0d148040319051451203070040c0a20303a2050007060b280c40c0104001400740004550400141a0618490040c00124100010030710f8443c51602005d4225611100c0d544100c000100c040000c2442400000c10054451a19601700a40c2d0341030050070040125017041000b082800c40f00740d6041e070700c1e0308d11000380b0b080ea040034030325080c010008142256a1030100c3c1000340072031140d0070700002e2441120082d654009202c042942008081c10708002038424040e80d044410740070503200407115004003c01b000014103140c80c03070400390030b50b030510321088002c00c010390901c882035030401c03070495100b0240c9941480e02c191608 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 622107446 1250 622106196 622106201
    0x1090f0209030d02070e180a0605070e04060f05120106060801090b010c020616032d080a0204091121010f09020a2304142b0c121505070e030d12 63
    0x81c0c5055152051801d2448440c3c0c000c0358140660300c404071030b01303071075554892080c0d5001600354000e030035a401142e001e404112994005908000103103040034003a0a03141c002002e890a580000c80c42c041c002000f00200e02d064a05080b90041080c0207005013450f05034050032014051246810301501d0740c540b0182e50780301e91403140c1400c2e4004c0c1340540b500100c407244011a601d0380b001b180410059044843c10b9240c9010740c0341a012181b400d05480105030000301d40e103050103001002201c6e024040418030b05854018045101503103207100ea11402044845550301d00c034002e10944145000c4014000d54490790401004c0c3d50018034056640d0300740d000102c07484d182080c0f4400b020303030240c40003082c908542002003007162079084040c5214083c02003004150110a0141844c002e0311000c51002c00c042c413040760f01118020380f00e19014a5442ca0200382180ca00442142e6825100210031011310980c82002e400140c03500d0456001303d80d20022958480301d1100e80d50920a2800340002e50f225245c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 622108696 1250 622107446 622107457
    0x80405030d020301090c020d18050625061b0807080106050f0c07060203031504050c040e0613020705060601202d0307080c061b0d0203040f050115050f150301090f02 72
    0xc0855496035102c05640040c40d1800d070030b00042c01280b580f005258800d002c4904900c00d127440d2007440b0f030720300405c111300c07030384407449441e6582844002103001e8088400303040f01503402040c0c00702c1c001c60709501125020898000000034026501c0174080340f5940460034905503600d40c10202d5951010b030030307107903076034010f0290b40c0707509102e00200413840303035404005940900c540d9034180c03505004100800090320422030703084d2100d103000c1c0f10802c0500c43c402c03041a007064019206100036a04580030200fa80c1c4914001d4507564007200501c078007964840850341000c1010000c2415143e5821001030b200c10414040b17440c801122490302000e41000c1d10510b8404000380c1c1120b68804552408000076000401030316081e021b80000142c1011907025041c400c032100e00001031500344c884402c88000d40003d4000e8941081e0780c040100014024031a02d280e88560000002c80a803805d410841d4001c0c80400040c007544111282c40030583c0c089040c3c9065600040002c148040500e089600a001d81c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 622109946 1250 622108696 622108717
    0x211201090906020910090f080a0b06040f0e0303130b0112050a141e060f010f151101110307030f11040621090c030c03051c1b02034e040608040503 64
    0x60004411141b50401c4d00b400498115442da2202c00f036440741d44a489402c0f4540151000c00000000707402441c03e0f42c841450b035032550000044144145074181c0c03135600201c0b00c0400361304581100343c0071300c44540880d42c010140b100100e02c0c411819a645c0e030325001030840041c2080e024100660a0840c144044403000c82c0c21004e040c4142c0120300c1d01030b40c440082d510282c0d0541e2400c00401c200f2100170b4280c0c152440c08040c0040e0074822b10313049070540726aa110344501d540c2d41c0784480c40d1b401d9220042d40079100595000c143c0a00030051003003150780a4982c0650380404000c10400c0e00d4100c040284040002c0f0458008411981912006000c1450000b40a4410355401104100388055144d06403070186040380c17501c000c4160320408a218071081c1c080032490381410503010980c240310401c0e0507403025060340d4801182480c8070100c5034000032000134007200c0d03821382401503068010b550312140d400000d40240960182c3c0c000c0003842a13000d03003410880403a00003000d000e0100f080f944120391 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 622111196 1250 622109946 622109959
    0xb19050703061a0c0d0c0501200c0f010605010f0e032b0809070302060702042d1b0306030209040212030f1309231909050a052112010909060209 63
    0x4094600500034407481c041c0c0804400e400940c3c00460703008005449210342d40300000c0c851503d01005c1940e1202c60207208480c07564903a9000d480303c2034141c4000ca852004861b8aa481c2c001110b8028142807028080c014140e01d4524104102e0381c1c4501007083e414405d00b45842c80a8250010078208003a1071018804520003105e202c0f088506184007071060400c81c1d0f60b000e040e448401440e0307120605844040d50105040c0880805480c140d4010401000540a070300d00c41034030303039052042280045c00090440d070b958040440f990688885280b900d000e55203020800f19095030300044c40c11002800180c0110320017840425044010411034a10382c01443c01d09454103640615005101060f00914500605202c2440340d1144000300260030304541521143d80340da2400030070380844c2c5c062030703501001d0354540780c05a01182083c0480300915000300060031005038081c859400703480441000c40c0d0072000411018a94203101d116941c1943c07071400e4082210b040ca402c1c2070010b4002e94807200d0b030009 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 622112446 1250 622111196 622111201
    0xc14091309050d0305060a12021519020a02130e07090c0507051e1603022107051309060605011e050a20100f33080102120901180f0b1905 60
    0x4001820303d1400c0140d50240310030358840040c446c0d0301040c1c2c400c013802c500048101c0c41c0186845820f03405003159166946007410306449461044003587c01c03520f409604000c2c408419400c00d150508164202e40e00140300011104550b01ea444105c3d00c114000d41e60341c4d000d440321040c030441c11100c030540c02c40304942000403512500340f8400b100e62581c00c1540f10b10b801110301441d51130840740c12aa00105803481c0100320a81440c915000641140300c140668100440c85948400d03540200c030386403110000e01c49140d032910804440480d0003541c144603c00f100c00340104640941c0034824451864119200d58402d1802c1d500f10100640240c442c5001c4c2c4101c024000c0d00140c8140c0e08210840140080640504120700b2200b01c03440010805181081000703c8014003c0c00c0c2d5003c00740119588071259130303559910308981082d40d8180010b03141005110010500740610504110350225615440b030559035510010b500e10100107220b81880000182d03c100d510140360405020703d071080c000c91 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 622113696 1250 622112446 622112453
    0x3040312050a090e3d0603091e050601120503040f1710060b04140a09090c06110601081509011509050106091406030c07140a0516090c14091309 63
    0x2a040300218000150001c0000507a20031403801c01e034050a1000c80e140140001780c012840307207020402008500f414000f540307406041d42c0c0c12052004260503500040d115010303143c0314100d106121592406020840c18030404600003180b410b04452440340309900c59001e91908900b1360080381c1c003003040c24130407050024038800740a0028100103180d03021fa5884040a134804821120680150340c803010040c0802d021200c441d200300d010740f074030081444c1c0c20a40d841800000381c4011040c12030310080c40100c10842e0300d42102e12403000e140c1d80c101800ba2581000070321a5519451101e550307100c01e40701d0110350300040a502200042100c1c0017230f20303401a01e0740c0011010b060b0a210381c800040c0420000190114841500c01c0030103802051240f0350303103030484d01c2c080c240c00410080d03420800d04044009168820816145610702c50009021a58120ba03100890f480250740b240e140741c0d007802d4851408540c0500192001489021503603103070f11820000c1188001448402e1034038a1170b0a1902c07007803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 622114946 1250 622113696 622113707
    0x3230c15191103251d01051303060b030f0a08090105070606081501030b0105040b010c0609050304050d050d0801090e030702041e021309050c090d0303050a091208090609010204080a02090903040312 86
    0x290042842c13400c11111400d55a403014010440c0010014803454965200380c03005220348003c1d11814903059041048040d2812062001d907030089861680d12035980d1441d040600400c00c801e80c84001801300754901c0e0b12a4495445203004c01d03410450006040400c00c1b217182c0c081d2001d418100215284014092a101402d010a01050318584070200c00010340b842c19014403890a0300695030b902030702c211903a4840160007d07003001c42e0680028003003c1402d403a42c052081109018178001c2120b030041020203004100d040e009120350070304010b843d80c2810000011140140d40c19940000c119020091414000c100342200302c08040c0005003039071071268050a28000da8003030300b80c10001074542620108603481103511f07441d00006480200310210b4000d601240d032046a104004c40c01030760725680c450300180303c1003a40c03000c00c032500709010764148100281e662010f40d52001718681801d20716410354030180a040288690f4412000400d20001842554000d40c0e0082c000c8818801d0094003814 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 622116196 1250 622114946 622114951
    0x3030506030d0203091e030a240203010501090308131e05030105220308090712030c030e0d0b06060f0c030301060224040809010c02010e0a0303230c15191103 69
    0x2420100811000e1901046500240442d900114609219402481140340c44aa5007040c04260410300d0141524140841c1268902c6000d9244544c01012004c02c1c44002082804207a00e106000600c1540d0f0061545400d4a07041411141c5540c1008555252004240c02818543d4880300140404c00040d018400070394404800a011a548040701e000306082c0c0110844403100b40c00e1400340100f0f00480900f40c102110704142d4036180d40342c40300c80142144505088000602c0e1620400a059100d444000d10034011200b0071180c0200b07840c0c40007481000740c0044e2081600098000381b0700000401c907940ba11800050b640c03290380d60400030f0b4669080703640d44450f00e0410000288400590503240348220f43c0814814109940c0000443d002160703950f089051000900380000390703649819042c0e0086210f03030b0310030344140076203c4005615012958843c038204010302400c1c800c16808034058000285600a0080694070482402003044101d00d484101d41e1400e00b038005011a150300551 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 622117446 1250 622116196 622116203
    0xf030801050a121a04140a05070f0602011e0203100302090109061401110307030c0c080636120a2309150c0604020d02210105190605060a1206030f030804 67
    0x8014582d41c1e942a044031507103da000789402082c00344400c14510596109401600403211482d40c969001900b0f86040c00108080d10a640440f40401c80c40d0b0b104070b02c0700040c01e800e10003807015030740c2e4100c03051407034001400400d0066000703c0051058524114040002c5800404002665a50310046802000780307004042c2d495a09214500041d4090060511302d019010700039454100540c50490301c40c90705003000ca403040f00c1400c001071010405c0208501410700728221100388580241d107030001805088448003031020084040007281c0380820342d54030015000c40740782c0c0d465103600300444200c240d00f8501e460030049036214098000c0c00e5409800c00800568000b504103991003480309150050030949903056104400080041c2080d0102011152001e08554008482d10a0f24440a041000c860189079521020000040ba400300c60704110550501c040010b10b0500000c204548200d8900c042032107501a00f00c130700b016a99201c0002950840c00c2030054030154500107150103402c1d81d050303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 622118696 1250 622117446 622117459
    0x30b13020c0f0105010b1b010605060d1d070f1e2d0b031005040e010902030712020108011a0f070305040b071101030b0406050307090c0e100215180303070c08070f03080105 75
    0x2840414052207258140d1303842d90049807e04520030314540c40c0c42d030307004050031807552514000243c03510340c03030040d040318180c0900208410900d6801d0602c2d0707000004400c14164001c4c0300400c207890040c05440d0642d584c0c51140c100d5424150005a11928036601c807550b640054840d00e40904d44c0404100b0420340105203580f91207685584050040c001520406400300d08940108500d140c654085221080100c00101e403d102c250002070a01c0c0e0150b00480700340820b8600c0f00b00310740e4824261800352074800300d020040c000e41458004540212900c00c04121340001c1c40303138140b500030005d0320001d00b600c400103a0349032810300d4040e801003012842180407034200101500280780034001d64055031009401081a14a403000f280058088908494288540c60fa10314200f500d659006151180d02600140900e01e00d075464075001400c010050300b6621804d0720560b03a007950201c11a0342100c25451300542c01c581503701840140300f1040003c10b20310206c01e4041c02c040d0132042d524102d8004642d032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 622119946 1250 622118696 622118713
    0x60f121e0f071e05040902030a0c0e0610030207050304060f1803060b010e04090f0303020d150b03060108070f02060f101809030216030b0a020c030c1e160810050403030b13020c 77
    0x3148403c2d02190b036400140f02403541d0078015400c10368400c824250000f03003201c0b403420302900c614252412641010881c107403110200482420131007541c070002200c6280840c6082c0954556544900a602682c0d04001081e0310b1a0f03c01c0e48944013004182494250007500c4913a24501b0328020b01020100364085100c160800d54585454854803041e1600039005082c2e84045550850007035100c6041d4400c0d090307403400181e0303201d1480e61202c1c0151080a103055500c3c00c140001500c000c40083c0b0a03001c0028448480c1080c550109801c0c0e040a04042d41c00101c0d19003c1a07605201079070703049076904142d4107800c10141c20b801e0b00132107400d44c002c0c0c09940e00d04007081c2c1000007004039404041c120405050204044003d00d03402486003c0d00c41d0162414412001c030f4032410001c9001d81241c0300203100a200300303409400d228100ca8010000011036170341e4a03002e241510740e000781d0240d001c0b9680c1c40000a0038180290000c0340c289030020122980c50b10304084640094000c290380740ca491203803102 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 622121196 1250 622119946 622119959
    0xb09403c1e020102100c120e07080625030c03020f07060c0f050c07061101230a0608010203070c0b0601090312090306140c07230714090f060f121e0f07 66
    0x80c1101c1040d01a07020745030221031806041c000c2c046107408241040316030541d044500d2040e10403071b44002d0380b200160030214a480e007481d1510002500c0404424001c0e13560400c0100886417007040700410341008641400c500c078055009000d5044070075100c0000061040400100341d1240214044640b1a000300c0404200c084495005c0c1d002c17a0b070420303881b0710810320180d03018070801500038030024004140303900480d00000740210f1a4000d003c0b500b03203200a00024156500800c000340c046d100003182545810300c4c1c02844128150400740c250502500400c0702039106201c00c070045c0d50000c0940c0e001c4040c80070000c0403940035100964519140c4402d8504881311554040c1c0a450040710080c2080043d450301c1c440150080d4050305050708860007842072140a020302002000302d00050743d02d100c42c8409201b002c4000034024016903402c401000502d0f501d0f60910f07002621305640712881030340c1100a240c41d00b12745811102c120303900ba807543d0030740900004560043c072074071400b43d401e80c070740c3d40a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 622122302 1106 622121196 622121243
    0x19260f1902120f160224090f010503131e2a0b0309121602040e030d06060f0507030807030b09403c 44
    0x428400c0050380500c01d0031000b00546100710f01e001803481e05540c05105141d41040d090914419120942d222818034000324001c014100d0f88012850f00185103541104d11181c0c89091080c4420409512171380590b4002c61007d0b400e000080601e40e6038007002a20840c503002001c03d043c07548804031307040f03140b01d550201d616607502c21000c06910301000802c02c1600040000c50b0100144035410740001160800348042d00b41c0544c59610000c0f800c0c032044e100b40e4001c0d501500b0a800b4106170b030000300041c590111321844c1003110540c0c4210968080074034026000c0403410522851303001c81d0054070201e600c10300500d80002c0000c807031030010301485401d8030003d40d01304400705104100e4080030240c148145088095584000c451001c94008011a25004002c0c1c003800c080c0003003c1c12010a07a07500f502004e92100c0941803001c40708076004100c21800c0d181c2d018901e01e48404940e002 = true := by decide +kernel

theorem cover : BRFrame.Cov 621942446 622122302 := by
  have h0 := BRFrame.cov_init 621942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 621942446 ≤ n) (h2 : n < 622122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
