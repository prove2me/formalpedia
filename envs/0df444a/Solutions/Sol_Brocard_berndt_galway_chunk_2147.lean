-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2147
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:47:22.505622+00:00
-- url     : https://prove2.me/submissions/99e281b7-8111-433d-b8fe-a5bdac9e9be2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 385971223 ≤ n < 386151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 385972473 1250 385971223 385971283
    0x5040507031d010b060f0d09140604150c0c0b0a2316050a050d0b0a050604061d0a061704020d05030703050c010b0f090f042402040302031005090307020d05 68
    0x8150b04140d0104032100100503203000d1400c0380c040c003409580100782080340d801c00d42d05220190029540642c400b054480c3c0e19580e80f010001e00000c00002c9a20000a002c20004e80000c1e50b11884681d100030419155800d0005111004a00015114000701d10100307a202c01203800003082c0200f141601c02c200c00400149000f24001280c1c3c0244100700c851039248000e10910803a0302d200425078070135007040b05245c901c400074607218010300d41c00303070007440005610f44034000504001c11454440f404180d00c0761164004000c48504442d1141c2a103600c20700c800342e00050050004054200c0d0051190340c0c61000c00c56545890780003034400c1c0300101e6000200f41c1e200c8020200105020002e1000c441100701b48141003540c8000300d03a2261610740081c2410742074405841c2c4c400d000e8200440c00711244060122000098402d01c0706c411340000c2d0a20642c02c080040306040d4060040410a43c074242040c1602c900130a20000d1240140d05441c5051080c02c02000000303100201c0076282e640150840 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 385973723 1250 385972473 385972481
    0x5070311120d06080c2d03010f050406150302030d051303020402071101090b0412110609190f05090c220b030a1a09040201080f060a031e03090b160201180504050703 72
    0x1104144074107254022034551404960302070888030140c803403821607241800d01c9821b5004141010a8480300034041c261a95007409019041200c8160020312400c0908000050754a8600e44d0401c90700a4001040161400100e22010304503a00d807203030f145c15901c014441217804039070000c1d50190000c903500050080261110f42c5042c0c0176203485103102e6440a00c915140940e00c00d8003200000e140c9000045480d1069107800f483c4014081850134482900107110009170f000950305035004850300744400305011030394602520040783c2c1c40c001c1d4503020345084840c0c070915003c801c86c03c1c0c9250a40043c16222944480a010440c401c04d07100c0c50710f03114078802404002c032506401380c04005003440700c3c03c100c2c42542c059601a0b440182c0c680d140301c501402c0306006410540c001100e03410000c04680038a0340030702c00c644079480300340d001202410010b10070807aa0f00300c5a0780203410045001d0311901c00720624001a0f0a081002584c3c2d0240c89035901040340e980019001414402006070081d410380c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 385974973 1250 385973723 385973737
    0x6010903020a0b220b04090b210604171c0e0a020d0605090c0a03020d2312190e0d031112040b0c1002040b12150324160f0507031112 58
    0x2106040ca1070116240c022580050305c0b58403c5000100020301000209802006001502808000c00c0f00440794241c0038010611601c0d001a4100d182444204120038420b044540c101e001c40320b0034030f4503804041d0304140e0034a281c0300640e6070300c00208800b070200b4051130704800c0e00100f20b8844501182018405010225603950a078040d4010049540c50901000010390740c003d00801803001455458088024803480916013403059448050070f5103408101d103e40341c10031000e019844845d00040d0000300040d00c07124406004281400e92155218040b088400d00d0701468203011100185d44c5403414202c0c4402041510400024080740c81c4059400821034004000102d88035641e000c10307040c08a00850003141a81001000003c000202c503c41090300001d100b84408011400b41c0c0c0024a131240780f4142c100154010105404807a040c1010542c3c010360b901e401e08004084594010080c040c18015601030150100b9100285440340301d4142000f51520101e503c01485071580b0b0407240c111351 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 385976223 1250 385974973 385974997
    0xc0303030b010c0b0403030c020115121a0c12040f020a09051608070806040e010b13091403030601050730021e03040e0a0b220212090102090112020306010903020a0b 72
    0x240100302d500c11840c000c4a107401840010b00b0392181d0b038044000d0909101120110f640300d80d070500b1072281407020000280142043c1c10200d9500d03181078503240000307100d115483c3d5001d004110305020080c0c1280d040e03001c003d08200090740c442c41c0c99044480c5408001c0d4214503039100c00b0900090300c1c1d01c030710301440e14107034002c07042d06110b801141e54140407500d2100003402038012802030304060b000707080c0300707145100042100040b101c086042400754041200c02c0a4403103a000e011304c4100f18075003401d1005003001d1455850300d017002a14500c41c2c6200204003402d2a41e9010703c6200c00b06541c0510707503080c4d81401d89204c850f54000d582e0b001e10341c88401c002c103080303100780b0740e0540000884040f55489000c1d14019510345040b030005055400c26560024003e2080099a1280c41661f04001c03509150060319080104e40030a0201001800d0308800d03841004190b9240c1c0e00a109050b008085c200b0240c0d032a03940c800100d980b40e219a100071340100030b0700d102040580c0080c1c00751119103e00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 385977473 1250 385976223 385976231
    0x206031b0c0313080d020a0209151f030518070e060a03050d0306180603171b0d0804030f0518121906090b0708190c03111612020105060f04090c0905040c030303 70
    0x36501d803e482c0c81c5c0e000e243c0401340c0d100004040047c1840c44800398050041d41a0030520840314011070000d080544294030002d0040c03036220301664140c820243c00040710950100310a80d24011107035900c0b441c0c022000002c0050001500d00e41c2c4803502040910b07400800c0c0d40000f101d0140281c00341000307000d43c0c0b000c80c0c02c540c141d03541a502d51180c44101e0390400c0d150f000141c200c00e406049580869018048055120103d050080040041031058141551040070600c0c041c00d0040c4482501140041042010003880010080f040e2a40c0703d01181216000001450103104138500341102120a01c0030309640c802405200d00c56128088940c000c100c040902c0d030b81c9500c00c8903940c008485824101c040941801e050642d95440300a00c08403904000980080c56120703015076400c4a101003d08504000f2010108050400d001d800500240000d1005080c0000040c0d10256500304050050780d42d06003138424001140e00200c002c0601807070400083c2000d0902e440c1c50781c1d442c04180e0109081c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 385978723 1250 385977473 385977479
    0x13020f071e032c0d080d0608300d020310050306010f03110402040e01170304030c42110111130302090708130b1e190f06120206031b0c0313 61
    0x600d202000e1039010307480358400d00401d0310081020054410b002076171303480f2062007607206c141e11034810034002c3c10003500180544644542441a034a0390f0f004c0840c900540c220a5021100c880000d07101010301c000030140c0c0300c0d643c00c4510940d99202e40d00c00c43e0301d0b10078000006402d0b503011011303006a9005103109009085180103202c1070340f0072841207100d040401c0004101c20b2903032200501c502141c0d001560301c0c1668075254444d0450141d00080300600c0c580b000500401c1c101000140d5111524098070565652485194440b42c200000d140c184140018000c3c200c48003035104000f001c0b01e0780c800c0d64840400c4903400020b4002804120300400c008800b1949840c0100b524502c11002d00c141880c01c035141c1d683e80380d00c40d64050316518802078240e0700d200d025001030861603c02d80382074011294421035030624205580f250000f0101151030898140140820646024421601500c0d016035a03116a1140082c101c1c4044903820000c0000c40c1c40391440b0740101c01408100d06201a500f100c41d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 385979973 1250 385978723 385978757
    0x1701060f050a14060f07030e01030c0e0d3309061d03160827040f0b030a0611040e0109020406090905070522091404020a0e0613020f071e03 61
    0xe500d018141c0d02200c85a420440d210075009510341d2003601800c104d05042118040b80c4054000640480100d020748288120303659044c800c05900440c0b500d4002040c155050208580316002c01c0003910310b002423001d00a91001c04114200c507800b902001184000b4002ea01e0002841084001c44a2a04016142c4101c10b0210071151202e8190380255241c600d042c0c1400e01203201c41441181e0148091001c1e0070030b8840d000d0145d2100400000030041c0c0c016203000c00080364000c14121805034039240b003104aa880000f655000603a004100081c440b001d112000c99901460340100c41e040300c0c0000115510181790041e02c02c5881545400540648a000040a4543c01c441a000041c01804051400213550703200400701d142041c182c0741003a0310741c2c0085082d125680d8002a040b0690410300045003020103d51005201c2c82728442e91703e0130080700240a000d4080040683e280c0c000c1000f80d0001400030440b00f9a5038880400303603145500d4620858011201c000c1540410821680049040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 385981223 1250 385979973 385979999
    0x50f210703021314010e0a09050619061d1305250f120b010306030501020406030e0c0d02210f0304180b0f01020d0c030210020f090a060c211701170106 66
    0x19500314121600c1c00e10290009400d021144c04c1c0c10402c403140c82c80c4681e11400b20100161032541004103080c0750030b034107020510315950304800900303c01d88010001d03154086070b070600c0310010b02402c48a402c007020004030000b4003c5d000030281d62604e000d002400d8401024100c148602c09040501e801c00d282c400d4452245480c66600800c0204032a90b6011007154045880a001410000780464407030700c4260032078025401080110b40d407542291040c503c108aa403500d8a0101d810010713072402940401e5211007100b100d00455034602e14400c0343e0100070301c00300002940c58002c40e6101c558801d8241c00300040c0d6aa140482e600c1d240408980d0b04100b8850410300c0d01c180c0040c80500c100400840d0707150701d0480180c0071800341074400c950400540c001048185454405261038520380e508009191100b036000c2020305c8031002100000030401d82c20441c0790708007074900d4415024540e40036641c2d1039690306d103820055120b200201f944009941d984102e82150b5000b00b006a4179240d000c9121 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 385982473 1250 385981223 385981237
    0x70e061e100f0c14070f05040501050a0605070f050a0503120106170610020f070b04090c0503070e06030a0603080c06040b010b0403021e060f0c0d1209120f050f21070302 74
    0xc040300e049240903860003182240a80e040341e14000b11401600d0b11902d5400300940c480c00e082c5e401041d01084001c104401090103080101c40401107545400c0000d03411032a64070440c818042c1c0800d82000b40201d0300c0503c3c00c055000b105681483c0403500e006074032607000c105031a42c81107002001040051041c0c00780d500039107044601194907101c0c0c000304240005498103400443c419081c00180b08681401400020520301c020940c80f68144295042a601c2010709207003041000c0c410400c03517607400b1681014140080c0d52541d41ca46034a1150310241048c1c4d08007900d40b803c0000c4140000c00005003043c822400703400036854590b02d80c0341e103038880d10842c440a540900c001c01c00e9081c2c0d10000e02d4003050640000c020a00e40314554050410399008498010b1860b00080704040150303400031082d402e40d0f4003880e8100261a903a958405210040c10520703001c001031a05c40a500d24001ca044642da035012095290f214030820080c88e000368140c0303034608552007080011802482c0280240d07a04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 385983723 1250 385982473 385982479
    0x30a140105010c060e070801060e0a060b090d0f050a0b0c0304020f0618062116030507030b060409020706150906030309140603041407050607060e0c0307050604120303020c070e061e 79
    0xe4400c8580303868028005800c040305c400d00690800007000f0b10309104a800501091807005a540b4000e540d600844030507910030888100c0421664503655120181880703255403062010391032a0050401c145011100300c0c008281c0520342040c08032010307800700a584110301c01c0b2440c1d11094160800d1000382e01441620b480748650058040b2210f1038481c1c0a0200c16544400d031404035440ea58000d00040c005a84c4100400001e20480040c075526014069001c5010304007407028003650030200d481c0740b2807440340560441e4080b81c0390007004125000f91101041210345400042d448600290051440744030403404107681c2d800c00146200c902003040d5140780001d100d07030b045660315159404001107201120b02d00b40107124002c034544c0e4130703800a031060741d0080c20b00188141d03181080c1032500c0c016400c0607120b03074400c1d00c04020740c0d9541403c030342c02c1c0d50303c0c146031400407440c0f483d080d00030b0301802041300744a002d05000407a5464400035020300c100c031304841010303000f407179190b6125038100d80707814050f0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 385984973 1250 385983723 385983737
    0x140c060c2d0409020f09090a14070305040309030b0a021b1c140301030f0c0803070305071a1015090810051b0f0d11070605040c030b06040e15040809060f030a14010501 73
    0x1043c0d909a40c081c264210b0880e2241e840d091840c000280350043c111001c06410380d07200d81c29417001c0c02540e81c05a00c00d6403410204090b003001e480152403205e0300d1000030220344076040020100ba080d5010350b80c240c031911224881910070030500b01c3e140d100b14040425076a11400400403030700d11030240d0341400032884540602e16425503d0324074480e940c16900340c0f0381000c0b20f04005030302c0100b08010102c86021b03658075600c0303901626104d05800d18031184521410781c1d1209100b00000e04015401c00c4070316120580000f079400303c60640f8080b01a501c980c3c0ea83c0108a84011851340343e4000600c00d8896070a100031030b2120440c505414020500c004480a20510046140645030750041c1455051103100c0c3d400d00390709984501c141d400840b01240e5034041800c0c200100005003640d80e41220003101c00f8050003024022660703480c600c2901c810110340740f04d130105041c0b107030141c100d4000581c042c2c01d0790354030f40742c62a66080c00e030310650780204550310b000320050012106400503030582d407051351091 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 385986223 1250 385984973 385984979
    0x1090c17191112030f19050a080609181218220c030915020913112208070609060813021309061b090504050903160201140c060c2d04 58
    0x310502e0341c0a41500b00a9110700ca11124500308042c00303000e41000c0180d942d40c1c91074a9091b40305400051031006002c007c2c00f40e02517407504840603a500c8003003074914a12a0b92a1142c0a0f074008a00011031a98011140c000300f07100c02060003841c2c0c11010070010386002200d103050220041034465000700300d80c170300801c80d1480c1110303400030401005280b9002c52003401c01e854803c00720f1764014004035216400110000d203030a00c09500c1c040081160400c00a100300c030034101e45039101d03543c0b20611100b00078542d400c2e10280305c103070640541003107021a40441d8440402400301c1c10f85000d04004540d0b00d00000c1c5801e01641c000040382c903405850642d000c0d147c4400c000c01340080d481c00300d80b9140c907940003c01e844840c01108015003039030341c1c1d07403800c581c501028482103646c0502565280d800800040c0c030848400000038840590a2818080300c038071070780ca04055400355200a40850003204240100804004080e044d00d000c0d40c0d001d80c410041324540418000c00303001c040440840248010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 385987473 1250 385986223 385986233
    0x18020108090c03150c1c090b060f090a09080d021908090a0f060b12010c030b0a0e010e07050a050c0f0106050f0102150106050a1b1209080a080301030f0f020301090c1719 74
    0x244d5045800c1c814001c0c14041d4041c05803000681d6130b200034142c565145650400c2c44003200c00300b174100303c050704e580280c419040041060900300030203181c0707629210705a1400b0047c4940480d40558140310046403501c400b003142085a451030341501c000940844007080c0c044101003580318103150300caa082082801c803a9610b5000c0c01000030100e5014080701c2c002c1000c8142802108140c0c0f0090713400184802c01c400c10440054590380041904180444c01801030790a00d0304a02d8200e40030341800b81d1504080700040743c8600c1007409212503406922045003030035a05401032010395004071080b03400c080c66403004a0b035891030401441c40304c84803c3c0040240358081e0000784030222952502d4601503403503240c02c140138103a40c04111482c020b201d4014181a03031007110000074101c03800c082d2808003110f03207840589010601000c2e080f0010803290340200600f610600c10200d0307024000388807511442c113000c41003010310701c40e07940720000b4a607071782c40390311300200d150f0715410702c0d81340901000f207040c0d10b031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 385988723 1250 385987473 385987513
    0xb03010e0727140f04030207080d1407020301060f0902180108090a0b101d0105040f060b0a08100e010602101a2404081f0e03180112090618020108090c03 67
    0xc561031280c0d140002c031143d00b950180c45110f1a5950b1070401039040c24500240380541c0340c3d002826940080000f001081c2d404102d000705010040e50450b281c2d031880c00041c0c0140003e503c0000820b0740a81e00044446280d0068510010880c000414200c14000155400c503800c40740c0d01c107a41c00c062801c800003030040d0740b00d41d000320010000069464903446441c0003145416400004c0c44250341c0100510b150501a02c0510020010b06010940c640101c00c051401030001c00000d1110040005000192400b01c0c000106a01241040c1a5a40c0e2030040d407a504201464840d03941024217808031000301c1c0e050072441d0b4401502d10708089079002c858414042040a075501c445004000c0001c02c00c204000289032500310762542175260000c80b40b02c00c100c0c2c0400695080940041c071410440c4075110b041c0c0e441655017801e05900000c1c140a901c00240464040100003074909040d02a000c0c2d1a5030740d0420f250710071303200c00d071b02a00c2d450350a0366a0300006000c240e140e407024005800f4031764a410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 385989973 1250 385988723 385988789
    0x3130501060b1c2307030b120d023013050117150607060921080f01360e0d0e0d050c120f0a0b0a050718030212100f0b03010e07 56
    0x81c0c070302400307000c01d004071240c9403045e85d4207000a602d40d03031a581140b074480000741070452180002c14040201c008007940b11b10320013074480100310005025285103e0700c00401c400240c014201c081c2d403440c1400c861582115180111400101410314000c40c82101c1414540520444111020b881c2003032010072160b03034880081110000d031070342049000102071940e03049108040c0044680481d600000040101c8401859040c0c840049401000004c92003064801c81c4035030414017590300f50301802000d0040c0320705d01c00d66030a6454581e81c4010610046600d0944150a980b9a09103000c80030030041c480b05a480041c086400061002313049150110344000c64161400c140c0307001e5068103801c0e80c100001404245c075400800d00c104500c0d81d1746032140c541d20118a04100f0349a4055200a5606403100e0100900840020b02000c5440d182040780c1007140700c0500041c0b2100c40d42e0028903000d4140307500e92600030344c24004440d8241e00d011510341300341ca07003076104801014420115400320105400e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 385991223 1250 385989973 385990001
    0xc020c1003060b0f04060f170f06061c0b13020a051c06180504030e0d0b07121b030b040c0903021012090f050a11041b110c0603130501060b1c 62
    0x82c1c0003440010300d9000c1c02d14000c51405840e16640b0f089405032038101081101402c00103105a080c5400480041c429003003440a418081a9601c0303030301058252052891500b440040040c44041e843d00c1d681100c042401c040d1500c1e410315900101850580c01041c00f10f00100d441840380006520224035402c0c600ca84100e00451259a43e540505050042d14803e178881c9845030208802d143c2c22000058122009640312040c10201c0c1d2503449410002600f80c1007009401a260741819041c0d804c1401c22103c3c114010b00d001e41034000c003800424805281c00d0149051416482c0c0c02405600030204483c0c0150803c0303039a0440c144220b071a040c49a00c0c042106030307143c040e1004264074008480900c1d2192004204a00550810b4000240c14691043c0f0450030b0120347c01c1d802a16001100e0209924200140c8000501d040300e804c00c91030007a49500100d02108205d8071003c402140442c19000300000c202007521030400180e64032a44117110350a4007520300144546a00354000651070080c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 385992473 1250 385991223 385991231
    0x3f03130b0c04050402040807081204150e01021e0a0b06190b0a03090b0403052203020f0d060b0414100b040f12031b200d0b150d0c08030a09090c020c1003 67
    0x10f03000140807038009411484640d446114280151001005411000240700c484181442d00e80780705c0f52803620301c602001c810481481c011590917402003080d0714240329042c440800745c1d95480e0006555000c0c1c40000e580c48042c60740415028100b003d0310402142d08003010740045824801655610303441860481c04041c3e64080b03080c04245488003017805248a580daa6940d206c460400c029003d06c440c0e0404802542c6400800059079642e4041170700c040e003a40e403200d014105061101c020004102c0150f042230901d41e8545442d40e100d211503200785612075800403066141e1250003181d00440c00340d201c0c1489169801c0c002014020001c0314803906c40e10b4240c616070044401c005a202210100710b59803411a84d13200100315410030382c0700303a100303040d5441c80c40d43c0d016480e501152031000d40304032741281544106072010b45814500c004401d400c0304441c0700850381c1e4114a607507580030b03180c28000101140004030f4180d1250041c40202c41c3c841d4020440c070001c00c001c2112401100030781d0070505030f903 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 385993723 1250 385992473 385992479
    0x30509250b0c010b01030c1e080606040302060f03070219120c02040f0f051b070b0117190515060a2d0915031202060c0d0207053f03130b0c04 62
    0x11900041400710b59600c00443c101c0c200300000b4095928540ea07102c1403080c24900c560403440c0003400001d50030801d2038034840a48440000c00c51600c603070f400103500400f001800c80344007500ba00045010f03421035802c55803040460001c08500d16003010004003c03119444080100900c80d40300103200c5800144001240c240d5030264104440000d00c81c460317500c1d150307820040d10700f40e0b91148030b00d048041c0384038900d464240c0d0b84084d241d40050054401c15040341009a0304450104003881074050508284000b1032558202541d039a126081f80065030840c02c1d0001d200c90070b26806070011141d060048219200d4900c0900d03510182070b40352821411b003444800105c024560041034120302e07004c9a03a0034082d045042c440d021040d1450804250740c070a50600c205d0503258000c540c85546500c0c0c005840e0001813900034204401203110400c0a080090442240100910b10495a8909121000d40b1620150403550503003c1250303129aa6100c080851020815070f94a15030721000c160b41d59450661 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 385994973 1250 385993723 385993739
    0x6050a1b0e03070e07090b030901020c0604051f1e09060b0301110a031a0f1c0515092b1d28140d061e060b0a0e0103050925 54
    0x392000080c03000480c92442900d0314141804914040c000910402480b80380c210805000034450344030b0394801070301c00000a201d500081d81a01c5511480e10f003656824201411709555a07102985003400c05e032220100c0400c0b6030513074803030a04c1c0b040032106004126144031018100030044c40000362211500c46441003c295020312544503162a00c100b00f1b5240c8066400080866003900d070422504100c03c0040781661343d0340b08a6056510007240d000ca0b0070800c0c1c0411484904410000911134441c00c0b500c1141200c201c00d5052240004104071650042c48480ea0060480d02d4031030300a1303511440300010f200c60f1040300445400c201d00070f50600d03441c40f060040307004020440f5100c0e03c080c0302c2e00540c1c000c5114a6420038001c1108d890600204084000080d070094440c4100400165440040e132040280c1c000184400d5180c0d020104004c690b9000101e05d681e0002040d10f0024080a402c0007070342d07010740308080c003400200c03005020030041d032002c0c3c0f42c1c00904000c6e1704041d0060980d00082c07040c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 385996223 1250 385994973 385995011
    0x2101136040c0e04090b091006050306010e040203030d110301090b040b0d02040b0402040f08060906070807020d05070c0510170a1509050606070206190306120b070f09050307080a0c09020c0a06050a 86
    0x5206d001000c1d01840d12400042c2052819500d2080060a2640800255500084980c1540c000700410082500c50b0710001c0d02d180b151107131f501440b9040a5014240d1900c41000d14125504900c05201c0c440c0301c40304101c02c90384200d807142c4c0c0c041c40f0100c80a015042c1035121b05801c4402510040c5859240c1d440c0611481596022010503800907007007007204403061084941003141b904040c00e1904000704041d4886600b054040c08200e400324048042c4280e820318100200405458122001103000000b440c90503200b400c242100d00110120340d40c60454400d8401500c18101c0c16141d06082c41340300005032901a0030a80d00401c10b20402d005640e800c1c006006c001c05a448415101c16005006019600198000350f80b8424284e81080031175100c02000381d0014061821809104500f041600d41701c000c0d0f042140c05200e589408201048000b0700005c855005201140c890f69581107100141d01c282924a1202e800050154000590359042213401510824000c00d44400d4100c98059103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 385997473 1250 385996223 385996241
    0x30f09030f040b041403120d020a0c02121615020c0f0d0b130b0105030105010b07030e1807020a0b360c06033301091502101136040c0e04 60
    0x800f400150400c143c070058100f807180150700350042d100e0000083da2000c1140151400f0120713070307500083d50076403080c072030200c450143c0e500514120f0070001c4610354903640d40105030a0b400101040c040401d0748a100002c018001c6c3c1254002c200ca508000e05100040c6030300d059080e0041841146100060b1500104a22a0740c3d6000107a149080a090400410406a000500a07450980140040740c0308004558585805050205030454040003140305181c03960400c0800c2500360341031115469003c00c0d000803c90061018030f0310381e1214180c04070b07400c003154074811762003961104501018043c091400101d020110a4800c0000d482000c6015035108840e00c4404c07001a006154800c580800010035040205410078001004600042e050100500500103541d2800041c800074510070040f00207d0202c41d441407106604006001001e07030043c80c412400f0310f408003c2c44002c0ba001080c42d5900d825915040041449040240802801c1c903848110810580d8207c0448544850142c0980303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 385998723 1250 385997473 385997489
    0x51201150506070627260909060d051203060a1a0301051908120403030807020a030e04111c060603050f1612090212070f170a021005090904050105010e0f010b030f09030f04 75
    0x44217441d1614404021045001040461845208600c0b803c10801a604195015940b0035995106c0800007141203596103c010114031071401c00d10b0205440b08091400303030300117403501c103803143d110030f0120304034141004808810070381440100300305d20304524003c0c0305540c210100b036111354840c2092401c1c4004c40c40c0000075a400040e0400401d648441c0142d4040d0691000e0120040c455600801c000c1010f10365611413501d51142c561001003a404582d080d41440c1303228030b2000c1c1c1c2e4654203006880f0343e201c2d5402107807415001a01095514403080e1003100301907012000c42e0305096054605110b10b641441070300c0d0703030b8003110700040c0c035288a40d00d005d900e001c008210851604103010005000c81e00450080704016010321400d010014250710f4050b8112520035060540c44002c841c1c50198070441540003000000707020a00c070040d44564166401040700c0c00c0d03c0e5076050f41c8000400c0303003886030b060082c000308000b821200503249a44c2c2c01000d1241a2032401c2380416219140d6007003908100d038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 385999973 1250 385998723 385998791
    0x120f110d14030a0f0f0206340e10020c01080a15030c0b0318010c0f0813082b09020f120c1302040e1506040302010503041b0b03010512011505060706 65
    0x10620360040041d2007003025505d00504407113a56540203446140c0a003584d040483c0b581000b1500c0385002626900000c03c450a8960051040b8002071000d040c8000342d60007624441c00034540d0728030118140b82240e4060315451640d45806076000c5c0100781c0c50300843c1030700b00b481c00003000081d444020304000340044402c140c1c80e42001d84002115801c680005c000700c0c0e140c64188108160061130484144040d800c0c100420790383c500510b5200024070100402c02e41d03001a1840070b15000b4130a90002415100215916186c50303420007084515207030010754440e000c40c1c0d40c020989810207400c801c100303812084d104000b040700b011a0b10078903001350400315682c010074103104c00b040c4a190241e00588060310703d2150254a40132a03900d00c26400040e041150000004040c46031070003000c407200c041c03100d00d191030030344c0c51036400d0254000703005961080b0f01c4001400011001401000a142c01414211351038502d481c0803c04258000541191788613254400304420281c4400b950705140b20720780d9801 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 386001223 1250 385999973 385999987
    0x22021603031b0306082113030501021908060109360606020d14030109150305030d27050d080702190b040c0b030f060f010e060304120306120f110d1403 66
    0x501c40c0d040440b180101450120100416540060040322505081c5203803074210107003918a9002d8410b02074144002180200300104010055008002c6c03500342c030220610000752070804813000002580c0b001c0c0003a410f61014081044086003001011070002c04901d1020f00c03000048020708240b140140f10b4075520001040029010f2040c0b04c0101c00900d480c0110800f182c1d08035400c0e00041c041d025040b655103151006641080000c48040d40e08001169280d0300d95100a101820240c860100c480c600480305802d0060203040c040f0032250f1010180901828101d03049840e01001480b01d0114411116060702e040c00c80405855598081d0a004005d49020b04181c502d1aa5a500c140e4207280c0070010003100300000031142da0088004c031404c0d92310040c0d010040341c050042e20710140e8000000000c0c0801c0114011a034000d0250341c1c0c50a1107901e0f90748030074400300c2000c00c0740a012569030103071582c00607540a22122026000070300d258040c0150741caa1241c1041c1001c03c1811a500000701c40d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 386002473 1250 386001223 386001251
    0xb09130f051f050105031504060e04050d020714030a2004110d0b032b120204060e0f01020309030a0204111201032a0f030f03020a0503030c0d0b040501052202160303 72
    0xb02001d0485861080640d5252400083c00d80c44018100740c01100071003049041030740e403034201c00d0050a401c1100106812300e801e00704e440300e00d40c646410140c0700742d01d800078807003141401e00940740340001c1c042c00d41880240c50b90400c5800c101d0280088003c01c0e41585240c0c2d483d4031034581c1c404007103d802e40d00c88070318019000803119034000003803090f80004025880c03e04401f500c0c101c180002e03050382200d10b60340c500c10b40d0808084880204198008100031030b01d030303602a604a83d03811080b035840c980380c40c286006a84a00c240701c05107815800c00107039500981842e4114a11505d01d0441840c03401c01d408042c030044100a030002c46d0030b07404080b192444182081840f20102a00c0b41804506628219103501e4844480c0300007044e8200100303c40c1c090500a00030660220740190541c2e070350b46080e08078402a64040794883d842d00785005041899400e240c80349505864000e4440703070040e400309034105007490820388030144070f81c0c0030401003804400c203054402e40750f41310340c0703012030705904540c64 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 386003723 1250 386002473 386002501
    0x50102070b04050904140307120509041401060203040603180609050a0201021002040b03060d02130515120a1208060d0f050601030c121104050a020c01060816060908070b09130f05 78
    0x14840c4001c003440240600d0760b034801810741042d480000e9902415654880c141140124400034141303c6060f1809900385400000401b004241203d040100c2501100452082d034001e0080d00c0050744280070901103540240d211014802140300c00b0300d0308051950720002030700e41041084030142c0000410500b15601008101502c41d414002541024207100340d00401d804000c185910a0380c03c0e12919003503445e072400109884281c083c0501192410190102d103558440300480e0056141d010400c3c0d143e1800b00d03900000c3c6a103d802c0340c4003030b1300d038250848209502902e69a44010409480030008000390301d9040c040e442440903040755890f42c1005e8903000075591085410480d01d992200018180c0c00d8020b032551021940040c1503140c200c0030300002c2c010b40c252481c20350b1801d0b0001c51100e40000715581c1c0d80c2803200c09050010380711a0200c03480141072143c0d107501d501540301400500c0556014201d4900c016040d4850314103d0742d40d1205443c0c1d60a4080000c42d0742e8014060940324400d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 386004973 1250 386003723 386003729
    0x3070f0e070519120605060304060c08060f0306011502031c0e010501050105040b03040f170a080435070302100c050a0909020405010c1403040909121707090324021305010207 76
    0x201607040008040d0b5401c11002c0f1044042d00b0000c05000e200781c2d02c41203500ca1400780c0005001180c603440c11380340560050000d5000400802c103110002000d03031030900650051140c0107000703010581d2801c1303618403448070403944000c15404107004105082950401c1d60180c04420070b404520030340083c6819003190810303003009040000411050010130808400c4076006540b02c004200c0101d0907090414203940310304003498000d032000907415032055004200c03500680c0a8000c0240181c1038200c3c01950012043c00040a80c0c8800ea09083c10b10740b0001412909000b40190fa646200300c00c10b4000b02c1d03001c03645402c04542c001c02c02641180d4030419420141446110861416041c10f0020b00850007002e8018025103100141100c201d609000351001000d0340c0344d0600c091141803508104144022608200259251041d21000c00c1c20803241806420f80c0e85604890906503250000d003206c00d20f80500c165190000ea01110490500c01403803207070026480c00c507919041070002420180b82d58 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 386006223 1250 386004973 386004977
    0x2011d0d06200f13051903030e0a0503030d060906140d1439030601290403080a020601030213050c0d0e0f06010e010501090812030703021e0d05041203050906160e03070f0e07 76
    0x300c55140780007807098046c0240c036054101049141180d0001071a032080e20b8000c1074141c007010942807503084447d00190f00341c4407008400d0114580310302070b940c90384104624082d4010300204500c40480c3c80c6042210b80c003507420096880e000341c4280d00d00e00100d080a000c021289441104c40e40c1c0c0c11000d08824814441280a407a0952421401009580710304032181508044038284c420005441e4048800460303018a54540302d48038800c0180d01d83d071091206a0184d500c80b6000702014090384100d42c4280c03610004e103414640386c1d031903607002400900251007041c460034000e020303405003c0040b1030090502040c20a174541c14078000500414140d13014440d035901400e851000241d1150a60b0f0740005203140060301c2c3c09244400d030f40030000b0b180030030441000000714030300310b04004d410991065000c2d4142d015a0103104400320102c420407604c40d103a6802c520b000c00d51604074503404540c43c03000c518204440024020000341407880d541e01080300c240100c10100558038058003000d0b442a414 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 386007473 1250 386006223 386006239
    0x3010e060f03070611030909011e050d0c030602071509060e0c03030a142b0e01110903060402220f14061012020f12090a02011d0d06200f1305 62
    0x840d036a001c0fa030040704140124078811407207680042090f1400e1050042004217139595404040d403814007d601c00d007080182000b03004ca2171341044002c1c4e8010542c8180c0f20441545180c81d01c0000790413118085404005209520f07452041c2805020303105c46c040c40c8005a4505011649480c01c010303940c00c6070107600300b8440d0724041134001c9c0040f802d660f04a203d8a548054801001d1203200101c025101c90110701c90764010901181e9001c036000000d584000c02c01800b030550707180054001e14582650562000d0006001030604241d04801041240c2c25414000c0e410740c8584107554410030300c22034150b0340d00000400c0450102082d6007042068601d0500101c2c000d0004250310310f0f02d155116516000951100c00c0a10301040303c407100c1007400116001c1c1841f11815848103d012402e80c0007500b10916840c0c0e64022001142c100000100100240c04955543c40302801c041a031691300780c0700403c00c0c800e400c4400d070010508034140c01c50710ba43d160b400c0305220007800b6a40d00034501881e04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 386008723 1250 386007473 386007499
    0x6040b0103050606070f171b190b180c030609010c12060b040314070305120d0f0501081c110d0c02031b0f0f040b0a030c090c110a020904021302030c03010e06 69
    0x2610b011201c8040d0090103002d8a5070359403c0401c40351f240221700140500c4000307020440000340001c103002402d400e03c1500e520250f0414a5a03081703641b1503010b016120220081403000c2202040c0b1041e0028a8064804d00c07261000002d0a003181283d00c4a442c0e5143c45a0b0040c0c84c0d80404c0428580384496010800342d41050240c849a01840c0002444e100b0410040c14604604105c010002d59010003110055825200110055084007807a018128106541107013040c519019003810303100c001008012240008100311407060750b1205920500035124002103143e00244400e038411880343e110201c3c4c03a000e9106140c60110500c000b04075030900c108240350180c1c0c4440e8041203c64040710212130001002000500605903034200b658401d54207440002000010907aa0048502ca501e00308100c80c0c00850507038846184a90303401c4150068a01000140b404901d1150070030b00181c2401c0e4000c880304c070640100c1c1e1040da10444403140200c010048014000c00c0c03c3d034810400d071407055610340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 386009973 1250 386008723 386008729
    0x5030d1803060b013b06070b1605040e0a1d030f04180b0405090604050705040e120d060b1c0f0903081902090402070b060f0303030108030a050c0309040204030b06040b01030506 77
    0x162400020b010036254400700d0010380c49007442904080900e0350915804288019a44565403100100401841141190440d42c54044140d41d412900f054402d0b1242e5181c982e0180549010221001800818440428281c0d2101c186070b00c5005081c00000f07414a80b03882040d640704100a240b540c130703401001a00c9040d6030039001d40302100c8100d0981c2550100401c144000381200107081c2c0c1c4c01a1034602040948400001c1d40740c0254001c0041ea00d81548500a110035141a8010304040e540311003090b111581b40d00b4000c020001e03400400040c810740b100103004003503103d201203e84400b420390344088226424403640c1c000e1101e826040265404036503015005c42030040220780b85180841c1c0100d09040c41c0d40444d041c0c10344c020011581d840d544e00d0103c0c80d021041c0c170418041e01100e010a00c8508000080780c1c161001c00b401142454542c0408aaa50788200340c1d10406000500c00340c03545440722700241002d98866a04e504242c5003080501c01210b4010074640e04160529040c002540c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 386011223 1250 386009973 386010017
    0x112030504091109060c030a0311180607020f0a08030304200904150603051002071b060e0d0c08120a030c030902060d111309090210020c090a05091e0705030d 69
    0x80c4886030041001890f0070391a0502d402040d4150b078000310001081300e5030b06004401042032500c2a142044021000180341200f4040c0001e8880200c852040241151400d00060030800d48028900f560054000300071030500b080a900002c079660001c024401007141d88074040712501880d070300300c44a042d0fa41001034000a005040a0f1460342071b01d01d2000c4403a039542024001d503800004442da84604404458000e5011100696065160804884150f212940e000d801c40342141e80e00c41820111004002c40c2407031a071811249000d0001d80021551814401030380c8a1002e6010503444544c6181c02405851000c0795460426180040f080010b80c1e65400f40c40902000c01c8000560540b00c882c03800c002e00c80c00041f851040315540d000120b502054100780f8000b80709460243c940301d102003050780c1d289604000b0551103481d0000252102034130364031280d0b02c00740140803030b0401b2f400c07210030203900d4120303080c0441a42c000316420b0000d03003020002c0c00b842240e1882c0c80343c4509001c502c015006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 386012473 1250 386011223 386011229
    0x6010c030e03010f060803031006030b0303030c09030a0b070c15140412050c0a050c040605090c0732070f1d0a05060102121b010c0c150b121e060112030504 68
    0x120032001d1078405991000d600c9140004e1030940c00300590364907600d585a83c1e0308100d40d0403000602e440e8000c21054840d000e42459480040d0055055484003500c41206421200d90b01742c00d4400c1200c500081241040450300505141c0c4640640d024141811640c80e990103401130400340c28500103095071491040c0e0b0650241e0005440609465210000c481c144a21240c022561285854000c14820f001c00c4030011450111010041d5568900902c41541d10490b00c80c1c070205c40921444000c00e6607041109140743c00c10350510440c1808025411040300c501000340d9040c6c0c07081c00c1c01d0201030f4840b0f80034005043c401c222400c0b08503003603451081c0250001c0c0310422a5440c0c402190459008000c40490304400a442e141c4443c05442a0001c0d90104100404250b0804440401c05801a0010b041103078003c813840207024015200d10b0082d0554580c0e16030404010048006044000d0040190118050b203582203d40400e9171094034000043e0440019004280492400070390440d00b2a0700b1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 386013723 1250 386012473 386012477
    0xf040b0429120c220816080307110102160905040b01050a05060711040b0a0303050d0f020a05090603100308180a08192d03030608010c02010c12200a022406010c03 71
    0x1d030307039035100140894003900d11080c1c5201c001034401000c2d00d414001130801c0c1d4191508071001c1d00d103c09150140d0180038803410440d60010409480840c03040840200c3d20101070040b948603072080354107154a0102640310f40441a0341d4000d00c07080181814440340100011513444a00908110024505215107000104042c0050040324204c1d201c0d90424000108014070080420f65a800c000e0600d03440001c180421070300e44004004005154802d441030480903a48250500e1110740502685910241480055038800c6000000242001004118180401c154142100144414800ba41580381c000c9542d0350041c680080402d03002001542009801194501585001c0c0d030110362482d48003040c00102c81d0b41421940e05141e0550044000c865050000304490780103410b04900322144002040c00051086505d042c001a5076000056a4100c5500c1c001d0242c0560648003816030080702501c015030000400c210300f28034005082048140c2d03c8800004500d04400020051100940000c007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 386014973 1250 386013723 386013757
    0x9020d0905010501060503250905210601080c04290402210f06011d0a03060b032a09070504080312191811060c07120501020f040b0429 59
    0xa24000140c012402894002000708407550319428003c086500860f92516003201e0140406900354241e0f540d41366441555640c041100d08000c10401e0021038000501c4010544460b030150462051101500800c607000041a800100e1010700040d03071040034052044c80350031450701615100341014110a0305c801c40300141d5407070804d280e880000841c3c0020201c540102803c0100360b22800e0078240c02040262100d80d0020018400380b0740070346520f18060340151451000300001010760b0444520346100600345c800c2c1ca2003071540d0b00c00f00441d0070b4414040c504c8140c0908180c3c2401c48025422961b02d140207498942812041580c1c0c0c415044900b50200e4000001000300260000e1021640b060a0083c440594075600c807a40c517000d09441a10030b9861241203184a14101c001c642070b41c800c0070058540a07243c1003400b01002100790703040c1c60035502003018662a80b08840240007900010035a076441da07040c146090400e0310792022000400e0806884900041d9100081d601c0303c00d44064030071 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 386016223 1250 386014973 386014987
    0x100905010e1609050604020304030e010f1b05061b04061d130f051902091e030304080607090f05040209061206010c120c02040510050a03122601061d0303040902 70
    0xe004250000011a9500a540640e2500111105100100d4550010900041e2660010402203200030780f0003c000c5000701c034943d55154011800912052298100300602800c21511908110f81d000400c81e44c0750840001c0159605500b00d400e0b545080c0090614145424024041c0c110309858003d07003001c0e051000541c400b60b40b0341c01da10002d510205010b0021040a0940a014001c01d58200f8a0440102c0c004540c600c69031082e9503c1107001000f5a4602400d91040001c0000745004250140010800499259001c06c031030745c0a207150396a04450303a0329100301210031003080e40000d4840e5004205001980e030781c040a0b01d001880e221a9205980c4038100186e44504886a005090b094071500d11030402d5080005800060700a94050000c0d039241403032003000840c1c82c007421b5405035107424248042050102d10b200081200e05243c4044040310495068012902449140c0204017400511100e07500489a4198048044490a441400b01c000a44a0056005028250b9400300b001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 386017473 1250 386016223 386016233
    0x615010318050a030513150e0108060d021e041d030a09120b010608070c050f010b0301110f04060e01180807051005030912031306020c0321070203071112010510091104081009 76
    0x80007d2000b04601500b1101104018000c5401c4ca030401e40842c05080005070581040c03800c91036a168028160000721040781310720718500004003106070300700d6070343c1400c58000555080d00c03000845050005588426080000828044003070300000422191014201d00044000741c20f5415031310142081801c69544201c03c40741d46200407409481071141d4105201403010662000692040c1500248404400c0d07070107e405d01e101b40d00d4048040082084104480d23445583e6440100308140341003240404445018001c201c2942c0082c4460782100800300440e15145600140c40520340c00e0960652501001c00c640ba07150481c0491070707c03a000400200440803103003070407401c240e20290071521420101c8046a0321740212414008a41c96640c1222000b1b900c80b9680f032180d4070960056282c180c1c0c0d6503d4405d60322000042a8101c00e01850700c1e4003485080c0a214401d016000e030050340c00745444400c034180c40c0304e40c0c40c81c0d01515040106000c2440c0c00b080291400808101c0400e042c2141d10705 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 386018723 1250 386017473 386017507
    0x2030402040e1e07050111031905120406020d0b09060f01030507050d0908130503030c06040f06140103050a05161422022206020712020904050f0615010318050a0305 72
    0x4100502e00541028118940505500401ca0541c500c201e82c45540c88100545a03a02c880c008002503238024020440326082c3c1400daa8001c850074900681052002550741030944410f40342150465004031b030758403c182d802d11030f603901c000003110202c44606001d40424545100c0002d000e0403da15240050000d9000e10304996640c0c1514800f0441c0c05800d01f8011610f4211910b806101001c00e40300003218a0004181c039050f02ca00806008252a25541c83c07040c2c2c0c4d001c1c0811180d0548400300b04024503030000c43c0900035400744000c0d010f20001894180d08000914000c8140c449503183c0a003e10140200d030000c103100180c8511440320514480d201654086031280c800d02030002480032020500740e9901405041806101d00e02240c840009a84913031480c001c810100c1900500d540c003515160343c0c8a90030a0048040e5910001c0103010a0f0500701d0458000b0055160b400e607400c034070b50340340c450070001e00303e44039070002c29040030b5035030f9901d80f842c06001508010b00801c00c400e5000000f02 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 386019973 1250 386018723 386018741
    0xc09010c12020a020f060a051209010f020a0f1704110607030507021e0109080105071d0d0203010606030507120b0901090b12060f04021e0a030314090406030f05010e1507030203040204 80
    0x82180c0080714034201c000c0d51103000300422401440511108000760900400740c41c04101c041d1251030810135000b4400c6205100180b0420b459900c4a0070400350f41e00d41c0c40145441c0044d603903501074006c008a03026040110100d4030030886150b400400c0003203003545802d124031071780841e101070703486146003401c40b070f203008401020f9407092001035290301c088201d80900050503002c2e21412052680d9644181c2218022a10400400c5180115050031200b10a000c815404020720009001519402181c21a600380c0c1018011944d14000d000031580c0008240d9120340c01c0801c180240140f00010580c0140e044c45400c02c1a9240c400f040c05950b00e20000c0e41185040c5802c4404038a07082150500401058400743e01440d158620703600c8898000741a507207100c201511036540286150b03000c0720300390890b620900c61000d0a1201d0640d9941e58003c0000079405990201d9000c202c60074002c0c2101ca80480b0560300c0ea0104000e0044104240350965000560b424016144e070f445001007005415100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 386021223 1250 386019973 386019983
    0x1218040608070801050601110703031404120309090518300a08071b051902040e01020a0206010f060c030206010608060d0605070305071709030912010f0c0f0e06120c09010c 75
    0x108041800803001450108070f5450f04020700003611400015941c442000007075509a41011b1030a0020074010320070b054611b00d4400780c0380c0c949503880002e440183c54000e0120000b074164a010010445c003805110b81201c5440034600c82c82519142a59645a0645007251082c09803502c1c401080c0c41d44004500355400701d0b5a4aa854061040050446008503001404a04014421082d081404601d40da009901100428010345042c0d00c243c410900480c007241d00549441b96020900340078000f5100c3d880c900d800604040d410841442d0141c05142c11000810040c02c0d6a080803982c00603505044031002d0a0100340d83c0c5504020460b000240c1030007070242030078881405050b6500d0340c05244200496680c06100b0b140e0583c410302820815600e01c0502da2080c0030f12540d80c5480d2204e01c0303c44852400010300b0440301c45072113050780c00320710f05a804100f00c090300700c010a0b04000d0300c1d004442c0494072a4580b50000c1c08940000e04041c0980e40000c3d8082403450a590140503240d914075005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 386022473 1250 386021223 386021231
    0x1030c110d080a2a020d0302030c0a03050622060609080a030206010e040c09020403111201090302071502010e01060f06200a0f03050702180613020906030a0c02071503050a0617121804 80
    0x85000749020b203131103158403c018841d02040900c5640b00307100381e0740501c4a18281b07078502803010b40101c000c2e06020b00940e60007038185021603400843c0c0a221005035120501c04140d032850400040c0146499900101242e08003054507030009078041400c0b4192120900b1296040d115410400e101c0d02484d044030384010301c0002c01105000807440c4164002400b290301d642010413040c4a242601c513040c00041c090390064405014140b130002e5446001180d92000240d08181e0300341c01400d5560b958400700180c00108414807160364480100344001a155131381034440b29042c81440d644502c00070004c0c150b0710308062504100b40c031450488403a030fa001012800c101c040480040800242034230018420001000e051042c10058000e5540b0084002d20310707803c65859074400c1d0701408030705145000b1409402c00101d0038801130185a85100d81d1680e000a05140c13181c410390448800c2e4003d02c14a00400d0000d4510000010702c1c081000710041d6a139407035600c0c800407070f40820400002d40d0b0307210b170034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 386023723 1250 386022473 386022521
    0x121503070923102c18070b0d020c07030f050c0102060906011203051902060a060f030201050d0905071205030304110d0b0a0c090522060915030605090c06120601030c110d080a 76
    0x381d00740803001406200601c0350030345580010303500314540c1c0300c0343d03201c0358200700030402a1550a13400303004450231032000903141544401c0200c2c03c01e030140e04100e034200c2807541d008050010400900060f89000c1c0021301240c1401a40160741d84814070a2407022001c12304244d04061003201500d0521a128038001031000105401a460b84c004460740a1007500d00100082e00e2600c0c0a45101229010b8403801d10740121841c100000d00340c880c4041d1698418904c0015001890310562800c00c4e000d10050b64883c10b1515251880305048d1004a2007410034521180204408241c0650450300d8103c0008014070550815146248113a110580c00340032507203800704410107042d100c100441c0b03410040007056112002034044034845401000110503400003880054000c2d4800d50300840d007002100e010f810300400084240c0d0000d40d07002031a100310f10070b100055815001d0b6004e0282e003402c151421620041110395901056003165081200c0030b400308824030f00a0b0700c0000550091034154600e042 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 386024973 1250 386023723 386023769
    0x904150303081f1d06061210032001210603060c051e0c0303061201060305030307030209130b1c0c08060c0418020703090303030902040212150307092310 67
    0x1c2c2260038070400f43d007040740e001955407801d070010141da50036104080c1020788086001180b00b4010840c5400241c100585640070030300422580c410750810115101d5a81149020b030100940d40d080c0c22503c040b140441c0315140c0c2c00c000140317510701c06444c0407a403c00742e20110310060512903002401c07241c60203070401d9002c0d900034001e040c03846e1010807111030406501002c4840348200360707600c0320702d801c24001b0401c90314120f031420149085c03d10000c00e0041d126260107085d03620507140040802e41c000354101c410b081008800307030f01000c1c0501c10420072540f03001003003401280c1400307000d4401b000345000c010402144000c1000e0304041c021200c4520b0040458100ca900600803407907400550095844000002d0084603440b9234150b40341c0146a1650740d059001c0d000d102c901700c7c0c0c40741c3c00340100400c2d192005010361190506954003403c0010719414141003102da5000782103290306084c130703554400c41d40c00c00149803031010384486841c2d0703a5440c19003c070048064200c107000b00500e0701d050440b4a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 386026223 1250 386024973 386024987
    0x302071403031b04050a060c020d050607020307140f0706030b0333130f020d08090d0c0f0501091406031b031f05091608090c060c03131a040b0904150303 67
    0x85070203c986030040d80021140d18607000d00c2c410702c0d922080002c014042c0c02c0c8030309800c40900d480038060a942d20000c1e030321a410070000716140001a40042440420b06c424207505600b4150b50030040c0510901c091016901c03401d290188106140d154415000a0f80341003142401a401010b9058264040ca200c0740c08955440302503000601e1822000c036490942480c2003481160f030000c0201003d1000c0e900344a6064910f810544801c1010300551035940c4801c40d25214040c410641c00d4222420700406000f80b41141d00003504001d031240e414007681c02e0541c60f00304003440c11207500d41c40382d803010f8a8101c110054580042d5100740402070006040041680d044640c9000d0451241d4546610910440c000100c45505141d2003040907031a40c2d90007400741640000a0b101030701c010060130701c0462900d50100142040c680e20010703900340c00c0003618441c44040d082e051500c00341781c0c1030b40c082280b2500a50040c504050000254502d060359a5840030050504010400c01341d623a403420090001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 386027473 1250 386026223 386026231
    0xf0c110607150f06050a031e02041406090c040b16060f110c010e030a05030703051003081b06010b0f09011404090908070201030c0f090618030213020a0f0306060905040903030207140303 81
    0x28100607554042c8103070303402004d055a8024041551052464580640a5076811458401d0304107240000015844da809001104000c00340b8109040c00c04500307024050000415010540c80305203c20701082001e02d003219146480d0310a1000814141e082020003000e00d4184103c81520300700c0d803010501c030035202511000e0f00c003800800c00080700e003280c141c0328486c294907140010b02c200000340c0c084d8081d61100d40c21210004031022060b4903a581c0c49250703400443c0d0030b07416211821181000c00700801900c2c2c050049211500d00741174402d80700d00264041c02001c0c5041c4210001c90300405c0c200b00080d02c0048c216820107014030646e900b0301c0342c055030042e031045c1e001a080c05c48240899000d140c82102400450f6600202d552502130304982c000703854900894006900e600c0000583d640050034511580001401617440510f0f440103803c0c2840080e05c10245410090708010700c0c1d8109506074100c4405a0f00803170001040d2a0481c020312407031034000c0c030781c20780c1042d545c03800d240000165220b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 386028723 1250 386027473 386027513
    0x720010f020426060708180c0406260f0a080309190609021216230d08030703180302030d0c110d08011503090803130809031e1c0f0c110607 61
    0xc05030f030480f8164860700c0c225410400300340c0343c601180540444102003c0a118100142c030340c9402c10344c0004060f114142d0100904080c2182d1240d400711340c00003004c044515110052040070400c401c0c080c1c84003024080505040c0d4080300055058100f40900348544091003d1030350044c0d001d26040c4018064001c059007e1010040552031000300080c0d0b400e54200a007010700d40071443c040b805541303c1c0c155840c01c81d000410b8500402c07261590000c4283e018800c8411a40307a20b01200020100da012240c400f000c00755074541e0703d01080e008022554001c41007000420045019001552a03a509583c1c02c40743d40300b02160b849105600c90306003816161141c110384450781818100b142a240240e6000c0d203203080070008189003d44000d0f4480540c0d20440c1a6410103030f0346000030b820442a41ea803038440c80040040d0352001a81409540c011040150f8140165031a404d8018a400d801c0d40c122030903c00e11201e62405e101c40e5001c5048280c2d802840c0f0f650324040351030404d030314000c4252a428 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 386029973 1250 386028723 386028779
    0x4030b01080a03300f0209040f0204090f06051008041e0311060f10120f020a0e07020d03050c030f0709090c09050f030304080309011202130303030605180720010f0204 73
    0xc00412040102104007074000301326140c050402e0b8090700404500f6a074040880d070800418805072528000c04101c01c80d84180141c0b6540b8122080c0c00b601c00103000121514a801d4041c4100d07500c5070241102c528541ca0000b1003a030b1645840350340041c2401d140300a00030740c00d40310410903a00c8118102c1c2d10030440162481d035140c04030001d02400050b10004080c401c0c9480500c00c0761003031582440d4050140b00642d650b10400d40200d0265a441d401840314044144200000703030b60104080140c0d130010703250410661501c1d6005840c60700014011804189854000c201c0b003a1013401ca090141600072820404480d1164029000500500c0340c140211503811910109103404400d440480e10b44801031441e06e1014001150455003901040603102c2c3c2c02e110b0072001054048c90079018612039240012070508040c00c2141005240042031111a4500d003008211a8004004c1680250b0a0803281e40304103030800342c80c05020a000107144680c404100011f0020400000d10186800032541c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 386031223 1250 386029973 386029997
    0x60b0f0d0305040504020d0b060403030905030d0f0c11370611030d110c01181502070c06030e10050f040c05090408030619080609010b120304030b04020d050304030b01080a03 76
    0xc6482041031015021032000d2008100d50b003041e070001c1c1174506140d0000141605007000281d219046504150300081c000b43c418001400c1c10071010310001d50034249980381b460346003030003000c44c45220740080100312543c184034070790340b55406c0061040105044105010142c000204d099190041c0c01c1c612510446800140c00ba0040c17000000e14a500c1d400345207000b2a0080f11400fa0584070304611001c1005c1010341d01036102803247c0c00c0200d29500780041e10b09960304200c03024010740501d00030a144104040c0000034132402180c4101d45641c00c020a0425920001c0340c2408000b8039416100c908150421007601025903065108512450982c00b11944950902c0b040860441d8000c09501081002c124181341181c08881f28015564002c1c040b541c0311a001c80c20034401b0387d910321590f910f03010360701e8251500c1d803c2202d0000102c3c5c005d5040516684403222861005800680210f0303510405c401403200500807280070316007080140d20956074841c056a0742d04c08020060f00054910001c503 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 386032473 1250 386031223 386031229
    0x4030f152301060908060a020a020f06090105041106160f030e04020f0415030c1205040c0f0303050309010b0f0f090a0b100206070809030412140a061a0f0d030f081012060b0f 76
    0x1301003a41c000c1c40080401e0399032400c0c42c2c4001d51040d42c0400c01d5125241c00c2400c8001c0400071a486009418004251820240750149503030500d03000152141406118200c0c18000d00200100c600d90003000d846c14610060805441c091313260010144c12034000201d0b0340403410014001c00c12614881243c5147c036004280840c215a000c01c0402d001035032140d6410340c051038503048542c210b40140d00000d482c42e500d6070b8511442c02680c0c011400f080c00801000403c201c280310303549841c002030b00d01500803004000040c46040318504103074813981b1080c0c04074880c110554004500c0200161a07803012000b1040040d5860504680300790006200700006000f00e5404410755040313408480c1c1c5c01d4580b000c640d60341042485407100e0807901c6d200b841401e8020810034002c0c211082c500301342040c201d004480c04d010684005000b901d00814030000c0003400a540900400c2c90050145080805606d0b010243c8103440d01550007403440e03448440c240410320800c0c2d840140720300021074040421122901c14 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 386033723 1250 386032473 386032487
    0x5100f120f090c05150910112a012f1e01020304050610050904060507020313090c020d0216122102100e01180605100e040f0303051b04030f15230106 65
    0x14000c0094002d00c4406d01c40d00740b4180c01880703655141013114000d580c242c00301d03141c01d0135450341071040403160b072110b0310004c1c0700d8009814982085c82c0004440021010f200807044203c180c40715480408200d580704400c09225404200b80510760815218120030b08440c080e40055406846600405012a0358415001304400440e040501801e901c1c1d60b9a0b2160002401d00512a40940c0406c0003142d43c0782c48521342c014003524141d500004c40e507031410070003883d103d1880d10810540d84454180100310450504000840d10080c0e041601e0030920f180c004841000e208800228818503d10109016008100302c07001d244002801c01c083c014a414117403d98007414001d0303d2105507200c0c00c6c000306074142c005070383c00903580c0020000d580e91030044a480c200708942c1613408141c2803081c0c1e81015898080c00703411101412912104030182c00c2c407001ba500c46d92100503c125200f80e2203a0801071020340f6180c104500740070410001e030044001c0c9003405001104000154180c01c00482e5003406025 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 386034973 1250 386033723 386033749
    0x3024011040b37030203071709010e01050a020703021e1e0d02060717060f01091a0903010b0301140c0a120216020a0f0605040b130503060403021005010501030605100f120f090c05 78
    0x9403c0002c02980d00b0b05030700941c0050411010010b0382d50141c0306501a0321029409004080000246400504001c500715640501035003e01401000b440c40400d500040301a030310068558808011010004040c5c94401c80600c100c03952100800e04401072240420403a03c076103069002d45103140d65484003120820f042d003004149803208003011580034100410745031000c0c1010b040520b0201d45a84174080f003604540c50185140e030001500142509080c000c408184a06400920083d541607807481001c5000903d501481e10001c500002251b101d1200f4030103c200c1410210740d245040e80c070040ba8214040f0741680130314442440020001e0300b030003241d0122003244d43d4150905050060055040e8003000880b60300c1b140201c0c0101313850ba000e010290280d4429002004100c03010001e0b081503a00580c0010705040c5803090411054541c903c001d6485010b070f04e001c0c11140c00100d8103650000580d1000f02c0c50910344041c035400c09205501014a650142c1014101e1603560fa00300049400d000c6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 386036223 1250 386034973 386035057
    0x1e080d090b04090e0f42011811070c08060f0f01140103021c0606090b040807090509032206121b050c0a0f030903024011040b 55
    0x400c2207402a244c3c02114025100015251808a40700f146440c0c074106821500070700009440c180e02844031030399200d42d0364510a141c186006040070503003041d0881481005030403100f14070440342a840729480b0f0a01030302200b19640d11403140e410003800941c05801030039031750302c0b0300004170340484103200105102c0e50078940d12040c107078240b44004041c01c0041c103029045c15000c0c40a041e170581e1b0200c1c004240d10038401c0000300103250a4005003004000d5010b81d210001c100002e00c00394a01145402c00d982000d1400303c0c29484d035040f00c07442c6100d070001424903040c5c46110364071904c04030a40780d801c45102d40e54008198508507150401c030744031070801004802400200842e418050005021a0800308040d9a408402602c0f07031000303001c0c9a0740850000d2015001441149806c8405403512402c030802c040c40c180ca44220072000b10665024002d1040c1d603892075480715205c40c0c000d181c0e000141e103822038913281d41f11300d000040e40040d44103100f000340d42204842603044461031100200900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 386037473 1250 386036223 386036227
    0x2010209101809020c060708011d060f0109090e100b030706020a0b04020a0b03281109090a0b03070303030e01050a0b03070e09070b04062c0612060303041e080d090b 72
    0x303410252010940d40070b002c2c11000a80600040e480024030251902211600c00303010286041d2400404600058005804100320b1103202c0c00142166040203902c407400740d4203504001041c10042ea5081a0b650007024101e040151003107030795801198650075808900e1040c04a003a8917001c240e02c41500703000f0000141e100e00c0219011a1043c80501d41003400500074582140e00c40c8a103c12580c000c80e6181428150040105440319800241c2011004000410041b0090141c4030800e07900c1503003d040e220f40c0b811004125400e000c0d501c80d1000c0e0384000c00300c0314100d550f850041c0140070000241000b55182000081c0b040440b80603003240110020081c00071681017202c50190104090f00d000b025110b0200302140b0916038000610240c4401d0302d80d07811a40e00318110541070f510401c404141601200d000008640710700381035800e040510700800701c8507612800440d10390300499100445c50221036607503c2c0d8540040ba55101524415070030b45841c003030084000d48000c03036135118101000c881 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 386038723 1250 386037473 386037499
    0x30b0d023a12030c05031501020106090509010b1f17150904081b010c0504050105090d050307030e13180b130c03061a01020a080d020c070f18050702010209 68
    0x424180301400500c05004007226221010000c181004408000c0c410050a80c0142405a0700440d9040c8000b0342c40e0030301242c000118000c0c6079000c040c007240454040c88403243d038036078000e41117400038100c065010405881e02c2d95415018010420f441d078081c1c1441c0b4502c0714001c03000e90014010400d00c0d02c0d01d880c0040b0414485140309d42c01040c9044415410504060540d6050442e902032805188150380f2a0300c00c4051451414500c8074042d49a8034100d2440c0310550000d00307440880b0b0702400c0940c0c8038100c0300c0120360705080c0319070000c0c200d0100003016020550009002a10381a041c1e56441001041d003605d00101e4242040d90455030480120000020707904d840701c650301600700b445508800840b540d8200c07840000390011a030450301d503400c0619080c240401080c4201d0f00b44010203698009813a085030900c04c1ca400700100980025070141c0c0c150041000f00000c1c9003843e588102d00d80c0d1441000d0f46c4041c182c1c03503203103030909100c0400d5030588140241e4004410051804850320a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 386039973 1250 386038723 386038729
    0x20c030906160506070801060311090a0e0c0c0115150c03090e060418060b09090703080706020c03040b0705010c0806181501091503020306030d0c081c06031202030703080106030b0d02 80
    0x600001d80c0c02d4140c8941c41c00020300c080c40303101d00400c09034841982039410540040c05840c640422010215024018a070040d41c4d002e000da0115620507041d12141d84544203501c899200340744020410b0343c01c29000c1c0913000541c0118108480c1c3e0b1003004035905403000022035510340d1001001d0001201c022007403013845029101103820a900900009541c605c292280803030090700c4200341c94145e0340d910446200e0809900003940400b40501600c290fa0450342c5041403406001d2026010a0380480e900030b00800070021980544841c035482034840c150362900ca17010b8212070900d40000345490020548a06101440c01134481d60020070381c20a6890343e12a04071410020400ca040000f4244002103102c2c0b13003801800310700255070300540c0e00e251540034985401c81c9151990300304a400050100441c1c503250640d84804070b800e91500420101300e98850280666800242441113030600e18808190000002c00031a442510f990b842a070342e80710301750102d8180e0207425801c0300d024281e083c0145 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 386041223 1250 386039973 386039977
    0x302030c100f05030a20070b0c0406020a1b0305121c0b0d12030b0a180b0a03020906010c0c0513050106020f060105030d050706020403061802120309061603020c1206011503020c030906 80
    0x20001c080000e5401b00d9820081250441c80d40d21169078500150344800e000c000300071326074000b03690324103686803e00c0d1081c001e5443c04c0900c80a400101e00426110b07812680300c3c000001141c00000f1103424a103041d50070010380d80071040018024060781245032242a0b0f81c044c0030035161008100c0940c580c03107520f41c44200c60410281d2030070155940e450502640d2044114005840785c000540c010703040440e0351008450706180424420f500000c0c042005984402000398071580a2900d06018281407a140881c5d5045411031a1300103840705411070f22080983c4041e0403a49103608540c0d0400f448a0b8094030b0311000e010b07003034150700310381220840680201c0c018504a4402c0c6401490581d40362103070005c90301c10092828541c0c2c1148003080c10f520b13126008815141c083d0018614003100c0d5000503109208106d480e010840300e030001c1c0c500789070080c03050792403080014001c0c61a08030501c0400303071588402d002d1001003100c1002c0080d945d034402d10a0720301e00a603040003945418084003c203c46a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 386042473 1250 386041223 386041231
    0x3040e180c010c06021207020607030e01090c0303110f0304080c0a05010f121d01060b0c070b16061e0203041a07050903070e090715030c080703020c0a060b010e0315010302030c100f0503 81
    0x104c3d030200802001002c2140c0d0b6184100c0b40d83d409402503040000004055502403006800c0c10b0303050102d071801040000480d40212949401c122001840040e0ba9034103010110081090500000c200002c02d540c0c0400c51034604001126040074580c1c840c001510044040c2018000003002038810b8041400d00e544076002c0320240c0c15405035040320541d055425141c00340c00c80b81900c080410305902d40b0604104000140c040c500d0120b003071400203008103040003600c4034041c14040d1030b45041c0d1804016501c9403400a010410250360b2843c03d4100200e0407081c1012901582c1c0c43d000000b02011321030020358040c00001409170106510b4240b200c0807070711001e4440d0441d40584000018540c40c200b40001020340d0035100801c4c2200c07210b9000c0c0803030074001d000308141401001041c108640c046020700d001070380824006070f843c501c40300481c1c504e1006600160544100c100500890b0b84192055049034800ca08440c66007450703009020003098118a06004200011552902280504080d51380 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 386043723 1250 386042473 386042483
    0x12010b0a021902030c120c12010c020d0e04061208030405060106050c121e0a02060403030e0715030905122d0726070204060617330a030b040503040e180c010c 69
    0x7072403121000201b52409040c0034010710303404101a100385050030f48030100d9030018007000b001824846000652589603030414041009054085c4829aaa0f10350184000c0e00c0040007a040c041401c0c500b400c00d0354030584007a9030750700c80c081c00001c00501c6042210300a42d4400040c21541c0302021114181d074000700c0d1100c0140c80c0c074001004962411001802625545a0051006050905000d021511a400d00e8640c541007031800b40f000d02040040309442c410207217400540c051150a00c2802e01c110724070702082c8860002681e1900340c4811501c65651642084560344198028a64130068410f00d4401000c1c8202000020602c0d078500713004200a03915402800c0c50f04469034001011078076190800c00101c0e914900d00d51540c0c0300113011943c0115008903482116209a030b0001c01504c1190b1004010415060038540356100c0c0e80b02c0c4c0c0300661344450b1030400c605140c5001512034025000d04041e4206400000c0c0c1036100591401c2c880c0039084001d007403c1c0000100465021602d2941038403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 386044973 1250 386043723 386043733
    0x61c110609040f180213091a1503010903110129060309101103150603090a1506030212061b030c12060d1505160c170d090506070512010b0a02190203 65
    0x80b0011501440301e50009544030b58203050564810400040601800c04082c94548500a0000b0b2440b0101554406403041c207030503541d135030f0030704c270b6101522030030040d505542480b8210341096040001c010580c1041c00003441240c40740811111001404100104401842800c10b800d038141040110b800209010984082074119908035095843c02000d210b100c0340c0002c200615003c1c8c5820200310b2000844d1090315508040c1502a528880369002500c00d07010700240d200414243d074000c1004683c064030b0400d648500750301d5140c9078581101d02c0319400803004002800c2103d0041100c0c4203d01108410b4200070100003400c0c4101001400c90307401144254120303020a80420800014401940c0003003000c1c98109041c07820f40400101203030500c0381001c0c40c9070010355111610710b080c2055000c3c8030703210041d1034070040c054600c00002602a0080340d040c82202580600101a101c0320011000c8159a035844220303c2c1d48030700c0d6101001a08507030000f41013034000200d03d24842d800201151 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 386046223 1250 386044973 386044991
    0x15010b0903150f01240c03030e0712030518101d041503051e0d020a0b09150925030209010e040303060e0c0a080a0903080601050a021c030203061c11060904 68
    0x2c60024010303229006504203183c0104802000c0009040746a04031289002c00084400c40c05170100c00b040d81d004043c035031a00c043c00340e00f038410041e100090042422640c0b801c1d04a007405401c0d070344100641680385403000e20a01d601d04003140b4101181e030342d503980c1e080014040411504079060420569502c035448501c01003c106642202c4405940114003030031109001100942195942405075100f581248030070f002040d4021540c1c55065801c41c0102100303680340d507481c1f410840d1480116034480407607002d001c80810000f07111800301106104581c0d64080504d40c140305901d891200a510111203401031110400c011406034110b4803905000c240f968682081c0c0591000840341c0c03010340303000464552852544601c07100e8100d0340b003ca0400c03030790080d900c000f400c0300130041505061141c001140f0341a0780c0300300012120440280c101707982c01074403136074001c01946c425220709200e100c446003040800c052090081c1d03101c6510012004600f5045414026107070041001140d12035907400c100d03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 386047473 1250 386046223 386046253
    0x7150e09010b040501021b150c030405030604060b0a0812040312031b11070e090a12050f07030c02011427010e0901030803040204050c040f0e0c07050d02160815010b0903 74
    0x5020b00101001240c540d400c00000918001a082d078240700c0215851312100141c5420441c00590205140300503a11300c42a41200e2451080d039001680611076802080305102066104152000007103404090040c0d85521680c2d440443d04400f2103c1302d81000300700300241c02258044d503030110600340880d00c07013008904004001c0d01640540003242610030180d507240f10034003c400141040e004000824100220300320f55074030350400024122094401503203002401038054407420780d903255440b56541440d1030020004400030720128045640c90b40d0031800514642d0036113030031040c50909840c01042e0340203c01020809003001c00c0c14070180580c0281140c03502c10380305010b180202c9606a072404c061051004030b4030020503c050307811051009221888012019408680b01d52003150ac0c01c0d05c510b01c0400051140c0d00e002441d45c410400002e405a80205a1506d56101c000c2d00340d07655951003446075140c03410134031a04201014200140007007007130800600030084001c1c0407149842e13480f00b03207 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 386048723 1250 386047473 386047489
    0x703090210080a0e0a0f11060708041502011a03100c050408030f1b03040608040b0402040609020d0504060c0306050a061103190903120f1d0d23060f040507150e 70
    0x11803000200750030100031600105010b40d40c180c2c501303c0c0007031281d1550b54840303200202c10f0113401040d400450050381900e80d150825510010f0708594038036600c60f40c558a41c15100b0341010403c0155080c072545c410141c1302250300e0706203400c001d0040d150b01d480d0007481d00000e04104c0d6502d024001d0601020640c0041013005d40b980c40781410820740d5a00e5104205d04503621091110307545c90f8000c1200340f080079400313864142c0143d4800c0031003202d030721181700103800f924568001902c800d02c003040d054101401d94201c1d50089005a80c0ec01c45003920b54401c506903050781c003581d60088429041080038520904100e8295944002600e05003106080d90852a40b1100e1a4500081d852981401400040d4000c1c0c0305101241c20040191f060211001d4142c1c0c1903440401d41041d035100c012221034031a002200e10341c0d41c0c04882c1c00802851051402040b4a40581d00140ea02c40c81b0001030410102a100500443d000002070581904c1c3c2810003000c0121070000780208545c10403500b07881e031100d0304 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 386049973 1250 386048723 386048749
    0xb0f0405120f04050913080a2d030209040c080c1e0906040f05150c060601030b01030905060709181a060903070306050415050708250c02060f04090507050304030f0807030902 76
    0x500303a6030f240c1c60700e4104076918101400000c1490307071088041001513a1a01102c1c1180907a0030612508150410905500c5640e958800c45041c0301d0f40c4940c101c0c0b94150b0050a07000e108843c00c212807001d400b0102c032141001c58507000581403c01c0b20758140710499130340b94588584184054505410500441c0c2c29070446c1c1c1c040040c080c0018014011898215203402c2402051502503003412a24680d180c0d40300c1e0040e0425050540c4e4882c0405a80d00c42d4101c0103002d42c002c01103e41500709800000c006001c1881030b810010210041c940303810080c0e0203a01450440000c2c08100507031800100106548104451079040c030074120f0000001310382d4000c00744075a0040c1d0441c522140032401580c1035440040083c1c0401540004012540040421410b240c00c9003810002400e0311084003959007901183c0065031002001c104e5006c80400e0900420a84072801c100380025182c1c1d03502038030307280000e680003008141800c0043c00c00c2d134403075060f05074004014517010561140340e4000c2061004a04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 386051223 1250 386049973 386049997
    0x2d0c031103070f15050c0c070311011205090c0906031912051303030f0215060d0b2e092a14041206020a0f08060109092307020f0c030a0b0f040512 64
    0xc4004040135003035108560740640300c46009850007480c0c285607510780300c0500000303280d94002d201c00c2440da4800c0b50300c4040a0b409a0301007106042110686a4650103007a60034801d042040001d81d00341004900141c80c000300c0101c03031800703686941c2c030890500c442060010801100f03200000f102026601c0000086000c0d45900b0700301c043c00a00207042c290054040d89032150380b0000c1c05420303242d0340d25142410350080c4021456803640d0200c010310481ca840941c05120340c01c10a031807841c0380344090504444058104021050b240007401c9000c1d030340601305402058140c802032402d2401000c2016596500020750341c607007910740e072a0714080750051030187e40f101c0d408240081420703042402c0c41500d00c3c96041105a514048000030424890307030007400401c03615001968034028a4142c0c2000142580e4801081413801500c02590f03400040c0d40d039500d500c500305c40314100d810042014030805030442c60000050b9100300d02640b5050014208503203e00c95011456448100e60000d00410b590344 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 386052473 1250 386051223 386051243
    0x613090c082820040c0f020c04060f0b130302040203070801061704050337080912032703071b1508131209030c062d0c031103070f 57
    0x22078161403510a10107840d10b014240c048000c050070140341e40241c54598416801482252012040c00f040100520182c0d0031504110607040384c2904541c1c03c5641c864254200ca510001c05c03400c020a07a14644101d45141295980c127101440100d40101280e04440030410200d5907203901040c2280d2048448000054407440140805c0d54810702c2e20700c8000548101c85044e0a02d61107840d10b034418039140e40d000400c0342262003444100301d41800f51458031080070f900e11103c40d03071003c2c1060704110744800042c00f40182c080000e41021094a020340c040382140040100c5168421503201000e4842400d948014020400000c0303002903580d07500080a150420707610710f44480e210003e1089940f460a104200080000c503002c80c10900426a410050007240d1400740f41080c1c41d00c41c583e81002d00100c01800c004101c1d65004680d1004100382583d4000e0800201c02c000d0700541e11925101000030b4103c10034001103842803101c26035900170341c003d803031401507156076928005034181c50844842d03240f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 386053723 1250 386052473 386052479
    0x4030b060a09020712050310080a050106060311040f1e09050739080706021b010b190602031e0c0307060e10090f0b10030209070809061008150613090c 66
    0x4010800c00030b065905055042c000700d17640d021354440c0c0c00206102000b5000c000540030060082c810720041c050601664009101820701034042c08090189501003030415a401c0c032010b140c00210307411940701e0720b03050b0303402401c192a81d6a2140300120f004100d984906011403040101e100340c1c0d005504503246d240201607241d046400740034003c0c00404901c10421440c0300d00404014500100c01e42c010000da0b40c0741d4840c64008000d0069a0b48424804030b10b80501000d100151300c110080241240c206189429112150400840d41e0140f0780c0141c00a004103000f880c0c0030942c40c021082500d0b860360400b08400109403a5420488003550036a4840b1a0034901c03102c00d0200300185041c0300d00900480b42e107603c50082c800c86416004080c7d07207190340051002e4801040c17550245074024652581410031060044c84048103481034031450007148042642030304007026400494403d2805007001c03080f0440200c2c00f04000801540e0859101781c0c1103134082a02d0310655103541c1c03060000d0780c013041c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 386054973 1250 386053723 386053729
    0x21501051002030a030b240301090e0a0f02040c030f05190f1512080903190209090a030e0d020d020d0b070807020102030705090607061812030e030304020a03020d140304030b06 77
    0x410390125020710719030810214142d602204440360000141004102c0030110790100d0200d0442e021702070710340d5008480b000d0000941c2401541281c5c82e031002803000141e9540045d4850220100081806801350768000050615410041c4031a441c1d0400095982d0114901000d8800458a14040a00515501d12002e02a224200c244001d03400108596441d03600002081d14803801542400d140314260300081104010454044884c05015240040c0328007100755801208075200324850025040001c0d0800c0b80000d5141000d501341c0d48060507546c2007410f0100b24030204406a03040307514049180056211950700c01e0f846c0707115580c503c0e0503140180d802400c0200251842d01164010001e006002c1e07400400d0740c0c4e0101046a400380c1e01d8520749845001000d448420f4031805800c2e80826007441100c0821040c41c690310344091200040303050481e5107a106c1145c000754090100003051025041484100354014868280c1c54070302c0403075084041c070710b0708558011a59139015100b0080141 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 386056223 1250 386054973 386055013
    0x6090608011a030c0603040c0305030a09181803080604060909080703020d08010f260a03090f05010216180902060f0702041d060a0b19080a020a0506040f09090203011b02 74
    0xb102d40e06140e039401910010752904510300c00e040c070412010010405001400d850100110303400005c403a550810f4990141c5800d2407441030b0801c3c080040741003121090030703024510b041c0341440807040310f100da55681603440e018091302142d00150f94801c0031403211098402c0309031903400b4044007611212246402071600201c183e040e0100f10107200100700006031010141c0c16035480001c9500003403030b000010002820341284040c100d2281001100c14141c0004140d07080d5115441284c04050b15040166580c018a000004101c003030301508222689000808d12078400c802c000c00f003101c07821074002440e1070f0001c85e0803c3d0320540002e02601140340500c110b4001840d0000344510120301d0301d801c503446074401042d6520054031180e00451076074039110b080340c0414121900c81003854880c5056a924201185d049004003a943c4004c9281e20300b85066608880211304501d09550038080c041e00a440d001004a070150b413200310b07040b6088032500c2e006070b40c0350890f8010900e00c244100080420 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 386057473 1250 386056223 386056241
    0x40f08151302030a0b130618050609011803180b04033804020d1a07031a09280f140702011d0601091805010501030606081c090e13060609060801 63
    0xc038801c404403001a00e001c224a2030070364000100503c0360351200c5081d500300000e0b9400910b01450445401903481e41110366003000d41c000c3c8212056503845810550880d03528503102d2050240040c007200c0003030320410110b003044214549078920f8a0b80c40e104080103130810b07042101c210201c0c0030050010b600b803031044110107071101e0840c00c0b00700d0010032210f8400c9002d0400390040b060a03803450709001140300b101700040b2503101030150506d04034000500401c02c1200a041c0c2103400802c4010720710301080024014850911160851008032008143c00c1d80308620100040d5102c170ba28002031116413080c0c0003001c00020640c00c40745400c0d0710003400c40b80c0041402180c2400000c05020051002603150b0540e0407488002902c41051409201110420100206203600b810b00200401c1007903041082211005030464403074074a02051400201761007004c030800035200304400c1052020b00b0240030b81002a8800790b101c2e465007500c8400c150b0328103821500500d03407242c004102e0043c00f48186205 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 386058723 1250 386057473 386057491
    0x908062e03020a050f04150b0a031503120f0210050c090f220506060f0d0b010f02070602030d0b2805030c0402090303030f0402010203090603070804030f05040b09040c05040f0815 78
    0x21038296400203454040500444c0d000380d510403490945502e4540c005485146541d8200041e16074070a4507034a0b5078000e00c20040001d0501c1940b000803034800e1051010350b54450300710061000c104d542250340b600520703084021407180310b0075202c02410510689000d903084002c032941c0d8401071070600c00b902c2c282441c45400b4200440c0d1a200d00d4481012007004032035040404103c1d07484036000904c13a80240410114900c200250100c1005010350146501501c00c1e2180443d50b03c50311800d980741c070894410358015030001c109940841c3c02d203510a4181d1040182071052140003407000101c40c0c005e0403086140c050700d41400740000c2c6410000e00c070b20880101c40c20345ca0800d42e40c0c0481d440c0e01018040c4003500344000040b40440e1300a00c20b81d046900054030041c0c90380f600c2200100046019201a404105120740c480c400034800d01c1207a082c0e60704006410300d0a0542000d0100600000b150401006405d000116014aa80bc0210011704001e030042440c51381003285801c52000140034611 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 386059973 1250 386058723 386058811
    0x80a03140705130e01050f010c0201032304020a09090503070b0604060b0d0f1508070b0d0906110d11030408040e060d060609020a032a270b0a021504050616090806 71
    0x200c0382e600c83e6820087c0001c00c0ca8081c055400c24801a0083c200e1030340c114548a201c40b040740305a8003c4803080e41b18070b00031100074042c540d65103107041c200e808229000c0d102d600b08018440c0403c191159150b017001c030140001030315a40c2d851040503240c01c0325000030380caaa100c880001100843e40181d01039145543c1c28000c14628207014a81e4070070540c4101a00024080381c40e0176004082c2d40144195034000300240540d001004030791a8079446035050488141c40c1141c803c000760903101c10780b8410360b4040003042ca418140003803a03004000042100f54400a1000d40b030000983c42d0164400801c0301c00c90150301c511500b8805015600071582004084c4e0b034002c403402d8a100b80c0c84140400605504003003280c041d03a6500c0c0c2c5c0f03400000f10b0700c01c840e401d2120b6001410026260042c05003081315403c3e03441800214484a052a80c203544c040d10560000b4041400c0b660000c40380b43c1c0040c0701c1d0400303807401030f130761104281864000c88460494104214070081b078060034600d0030402c142c01c840226 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 386061223 1250 386059973 386059979
    0x1a0307021606050904090302010b060a020106030c150e060c1905060615030402180c07050102120a0506040504120e0d0609140c190603110f070609020111010605010c080a03140705130e01 81
    0x62244c080c1e580e80c5441940c80e007078844180b600030750045091b048007070035240d03603080b1965002e4043c1c1014402190310071410b110005020b014080488030030492036942030141040c842c20001302c1d411542d01c45889008584d003113009550001c0f11114228443c602904961601c8010461816034509110380f40743d00801c1040016601c4004c1280b40184c0f480c042c8450f500c0e20040c090382800b503114000d000390300c00a14080c8508000040302d1241c00038a03030502070f41d41e508092005a49080e10002e001460900c421401540203034120080c003600031740207100006254803154107803808410292640c1501507048600f400052080100e0a0000c0d80c1c10301581900e02c19075401501c051055800305031b611129101c480c0000d40c211003590750445202c81e10b0b1482410030b070000340820030742240400c20540740000c88090600a072402c07104d0503100c2e070142405c1da0311807401d03990290042d0001c065545824034004c011100b00c19000b201c032640e855442d80308040031082c10320019088801c00f480760304010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 386062473 1250 386061223 386061227
    0x816200a110405091b0607050f060405010207110a14310203010e1302090406051005040e0c030714100e0f03010e030a08060613031401091e02032401031b1a0307021606 73
    0x11407480341e0b0540e600c030b03621f115908043c0e0a00701f454015000502811040c131042c8001500981030890141d40d0305c940c5400c10108002e5000042e20803603003000e80100a810082c50300d140c00b0414088118a07041c07150761a0340065008501c4c125056460590110060145406003001c01e0303840150701c031202c43d10080d070b80c0001e07680c408020710080c807481c0c031000003403603e250400ea0720b4010480600140072050505d0003154031010f01a10f42d502174880c074500098102140030360b0982c0c05501400c40c1240c41c4031f00d481280c540c50b410141c681c0252005130709800f00e4800340b00709245040780002031901c480d003603c6d004020000160506110b1001030240c000300ca00d20f000000304680d44640f0b00d81920041d00340a074054503285102800c2c03959013200e04500e29900c41c029104440c402c506444a4410604084009010364010b4800701c411100c0140000b40c20040c07000070020400440111085d5201c403055440148a04603040d107003404400d1004040e01000382000d0b03510081e07032240c40e0f98113100b00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 386063723 1250 386062473 386062513
    0x206060411030105120f0102070b15010215011427060a140616030210060806010612141810020403060b090109090302060f1905040b01150816200a11040509 68
    0x783c544601034500c981d4400d81300070000080d00b06e82c1c4200079510b03955181030422107000102c404009003002c5d1921440030758404a1407403201214030060094503420010852103121060b200329400186500d0b015112048541c600c400b601d068100b03900b803078601202817080001aa0b84420882c081c803880910085e610074007034442d10114002251043c20890038200e00e041c2d000d070b9407003900038139000000ca407034980429201e05980140e1108070203050b0780240720040f54030000d00900c00c4503030403001c10403102c2850a08040e02a2510444000c2c001246400c41244c1c0103a208407141540c0d0b1540b0b14049c202000740301c1c0104489002000f2400382c903100a515080f004000c407101b2141080081e40e2206800ca80394980b5180a0080002e464503203400b00b000d40080c000c10703003802c028520b00c0d14840d01c194606480b582e0490181c0c0c0700440036180640e200c4d40c204001c0890340c0108405008a103071b0400c06650311501454281d00002882c00502048440113003d000060700040080d208103011480 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 386064973 1250 386063723 386063729
    0x3090a0c120305070b062d030111090109050405060109050901060207050f120d0f051c0e121e0313061107060606050c0a140a060507020a05101a01081e070c0302060604110301 76
    0x55a05465442c46c5c0041c141b100c2c0c0070f484107201c2c82c2007034116440c0e24500208458210043d0020810100a01003002c03150048e81c101e40d0000c1e804060900250419410a0350001d00c181030164000e516a0000340c50004260450740040c2d000c601c7c100708c2460214090324410405944003c040d00c3c0804c0f01e15112a003001b0450284425003614030703003d6100700200c483e080395006001203c2400401c00303d003d00120007001800c3e200314042c031800340700d680d4110780419408481a521744041503810101c81d400080c1580320000c0800c0c0f00001280c182c2c090009013010110115584450a10b001c1080305d00681181c420410300348210f24405c200080e2000c9156005004544008084e940385854030a400b00020882c9091009006000fa0006515100030340b0500a80340c4160300c005161046070346217001032441c04400240c010595000da50a02c5d0442c91040c40021040e0251540c010310720f20035031702d5100056190110200785a4140304094000104403000d00c4202e100c1a4031050502040c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 386066223 1250 386064973 386064983
    0x1317040f0b03070e0604060c110f091b0708190f0327140114010f1a07060903031d06011802030c0702010f11011e0b120607030209041103090a0c12030507 67
    0x219100c14020381c03016425144c02002160340d2521048003d104044606c8100c44021054010031202d180442114550b140007808450707242e070715800c6003910344041c1c400c4000d5010041014802054012000388000305540c20414a950414440140000d4400701036601305450103d07903044480d035041000342188c01100240310005990300b0240700984002281c05075662034042c840c110001b139850b216040301c056241441401b41e07a1042e1045014042c0b000d100105002c01c04840019829807009521500a2500041c84084c0c0710780103000e032400381001d4841d91f001d58010400c040000381c480c00c1e4049541419425030614042c242c015001c0e04000074140100034000c848114425180800c1d12607141c0c000703120492102005422881d00014840201ea04100c469105401c109401006080c5a84010101c0790303100c490071030003034100080603613225072540c0521044000b118044c50140b08120050110280c8624211581c50341c1030384801600c8440700460750209030044180c500c0b4039080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 386067473 1250 386066223 386066227
    0x705071505092b030c0c0b0a020f0c01020a09080f070608010311010203120a0e010606030b0f01031a2e1701120c0b04090b090105030309150711091317040f0b 69
    0x31002ca07050244074207020395100302e90001c0e00400302d2500d052205003000c1c1d80741000740c544020340c100c8440d500910054006000c00c0041040c007240303580200205008840c1540c100280f03010250709903070101c1c1c10080020005041480900000d21406901c1c0085070000c0059904d4064003404030001484007801d4200004141100e50b40203004558295040c032030584013902d0500c811000911014441044545c41c1210100c0e0343d41c0688600742d00e031480285010320503034100f001100601a8040c910545413414a0084680c1c0c881d144000015502a00b1344040ca11243c035108070302c1d65546001d5000c2164941210691900e452082ca043d40c0b03c05101d140c03d00703190b08140d01840300560100d01e00b440005400140350a09500081d210402200c4003401640d82e0002c040d624001c0001103640031802c10170f003940803a1048010300c900d0380705040b015403041d01d1703400180c3d071400708031040c1001005000820b030800045003440320460041e020170605150070700540190011060180c03e15034600 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 386068723 1250 386067473 386067481
    0x3070611011506090e1b04050409060b220b0906240405371a18030a030806180705190201150609260c04270503040e0705071505 56
    0xa4008104100c0c50020b0220016528400200360314201e10844c000d840e10f41e8041010b030002d4a003510480c90fa410051070400d0b007421304110041108180031540c160740d030201110251650b403250011030000702c42d0a036088031a0180725099602002e10584129108000c0108580d9200e498a0b00c404410b1031440d001203450704d410390503200da50407207a481408458400d2a203044440102031542181081c2860034481c12130001944c03d1502644190026280b080c4d201c4003694005000881c3d2044100150000000701290504a400609a00240d910740400c03a07582400c0c20180c0c210740040e5603403d00d40ca80607000401038000c403080d05002e81c0e51210a0603040b4400d420078034000b000c01491248840d511140075140d6191449908c901e030142d00e10005244a403c140c4640301032801002d81480488402008014081616020f0001900b2003554043c01020f00a4440705840b9400030365882c0d04100018100100c01000b200401404000b1040052145020312242c545102804205a22 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 386069973 1250 386068723 386068757
    0x105071b0b0114180a09031b1110170f16080c090103023f070c2a0b0a120f05041e021f0e1203070503030c0c0129091005030706 56
    0x541001d108130700001c003006100f07414030140c3c01995803074032a494105060380c010303075050707803c1036544070280840003013580b22052802c000800308400340c0e0038981b160132002140d8940f8070030a025603200d070385400d61000b001240d0b00021202c3d800348156041150b036900d4000741240c1d041c8a4441e07030504060300030540e19000c04600b8400c00c80712040044105c1c01066000c2810500745107608182154202038020469580c00f400256201c10b4110f2450324203c613401b50903920005007503d004503082c92964001032030048890190044803c0b03640c40b504030780c181e0300004065502c0340170940710140c074160501c000181c804110348107080301100d451a159800d8000103941c1600d8052401240d0f4403000c14001d1075500401c140072450302160030345441110781c8040b41c0e80e8006c07840001e102d43d2042000c11000f04074031001e4400e040c0d1308000801c0012008400e045c41903400d0400254811000c0c0120041c1e25050800c147d010111400320b80c0800c1c03030135000070f45c1c5d446180b2a500c00d209000c054281030403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 386071223 1250 386069973 386069989
    0x4030b01120f0b01030602071506050d290106050c0721060c0c0b0a090510110304152414040c02030a050f041a030702070b0306010815011b050105071b0b0114 69
    0xd41100c0c100740f41d581d403400c1020295114040860b0400d1680c0000788441401c0c0c418a015900e014151200c8200b641c0c1d11048c0050b40131404000c0e00c00c00c41403a89010340a0300f5a030b80a0401a51981c0e02c40410b542403500e41003068004000ea2103041020021080b4207522005001d07802220204000c2142c1d40309951070100050007070103602a80080145440701c036003003200030174032600032940748a050b18161011079030303602c003504121001000454007080390020400c01c25416400b000034a04041246103840706c0c40100f03840c5071400424001c00074824040701c80391440d00161014000301510300b00080d220b104001e01c0000340b00740441c0000d908010b150540e4060401201000500125003c04241980040300c82c2c400500c80c808010407449000c806407805048107031101744050700d0342c0032140b4503400580f483d5410480c21603070010b0b010520401c12000d170b82c06500000f03140e0900c594000d0810100032441034520b0111001c0350005841311300a01e046036001d20034503119100d00c00000e2034103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 386072473 1250 386071223 386071253
    0x7020601031716061b020f0f0a0602071a0103060b0f010206130b1005040f0911060a1e031823160b0a0c080a030e0105010f12060902030f01020d09020f01030204030b0112 74
    0x500e445c001e840c061001d8202c1d04c04880282d0202e5a1002110802c640d03034040d1501d031420340e600400180800221250041c102c5988181c1340280c00c0d00e60301c10026200c80b8240d106030760709900c0f40049195402d0450340c288a8903400e10103000c40307180c20234a0012031806081c00605440c4c0d5034001401d048450b0488a010704030040c801d00c00703002501c0703440001e0504c80400341c83d80303200709080f506203180c4001181c4400c09145c40780a0420b40f0a649908000c0d0200b07282c00615880b41075214102522199521aa40c415004600c0c80c004441100110321014200c0c11030540c0056460b5139900d14401d00b890445000c20310b141d990b603110841c2111000145075006026850114105100d80e405d9009000601440d000070440d0383e0341c07415040140c466602c00c800c603000121200300003250154121000050015003150f14604005030001e08991240c500c0c4441c0b00d586500700d03021484d1108840b05190401d00c1d05500706401c0d0340701d0060769030042c41032a0f50107003085041010883c5a890011034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 386073723 1250 386072473 386072483
    0x20a0c0311010e070602060612010c02070306090c0b030f0a06062105040f02120d031404020105090603060103060e1e010b19180b0409060e1303051812010203070c030807020601031716 80
    0x10380f0790342d42006c1e542e40025078203603100c1c5510004503260711038140301d4010031402a0b4010f00965185485030f80081c401a801990240341d10400802d160030301100a41c06101c2d072070740c680351070700e0810722441c00c403105a00100100b142c032341030710b00456003507203226500340fa88100005451b807140c0c41d02101440b818a0000e402205880e0f00c65440f92000c80c184020079101d031000c0c404d9044105118103050780454000303011034010300031111141449009554454070605001030003540b280075045000301d044528007941442c01d001d002c55400c5181c6054018040c401c009400c2002d519880361031059003c00d8041004455000c2c4481a591401205d005007641401c59030385980354079034500542a14010f2084602201d0302040510b4110000110080e815594203030400d0044071030100d544800c0700040d039210f5070400307145031020f40a200a40c0242c445464503100c1d0b00f010f01e8081c106100080c040310554226000400108a1211141c00107141340c2014903507540f1000c2d16280106040c510243c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 386074973 1250 386073723 386073733
    0x30801090b0415170706020607050307140d09150c020610050609130906020304030e010216060806010203130e0f012102090402060c06131e1515050607051f020a0c0311010e 75
    0x1840c1e1807400807403074134502c294155401d05d81ca544042c1d81d10301d4192a482c00003801040010070140c421200040e10311280c1d05040c0c54983d90766403003020f0794011113064840025041c14080c0740c5106110b100581070113030018058510b0300215540d0041c415105040c0603190004410b0001d60b1a62514088440481c0341008080018145070000350400c40c0c0c1240801d01c061100c09141d8000602010319441a00c003074180a81070000403511010042e041e1410740c4030911a00e417003a41d00400c200090000c03030707281c7c02c8545840c410303000040d80183c0c8082e0b08400250640d040da2950010b4103a8025016503181400c1d0b200c51004c60764034403500340383e18103d000d080d00f48031601040400e80c3c07209500452003a2820445200030144100c110700340289110a05101f0b803000c0d15954110061000c40e51201c0d640d915542c40124682d68052101100c4540050030399028030040c0c88a841c3d0381342e043d40c03811801c0c0341d0030500c05088070b05c2407400502441205d90381520103603400d402c105003020119003994 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 386076223 1250 386074973 386074979
    0x9060f0406121401060e01080604141905011b030203010b190c0c120c09020309030403020f06070c03080c0712020d260d09020916020a140a1704080c040603030801090b0415 75
    0x7480040c094000002c4d5007402e400041601d0130720240740c144ca003550090074503525a47d4500003161460074043c02070f03010302003001e1600000c60041a901034028400810b0b58564075400d0003584000346880ba0030b0500c1800103000070644c0381c0c160780e441d0b550b10803e4044030b940c105090760515116440100f182c29803410100d07241e00c02401d007030042440342d80c41c10b00d01c5448025880503030000729103042e180d038000c2c803040015180500c1ca240700c09002418007483c0618035241c2071145900c541050302d07181d400081020000300300708022002401d440d890700c0c003801e4869000032440c02d41070760050182030b2100c03000d8405110030501c085c042e11a086000c3da0390068225210054208800c042c0d02c20404c0300c00164804007013842400d4203401c2d903805080842026540c1070040d03404503160142510600c8601c1e000601100461540c000a0f114004c1d2954605207889141441d400882c03401581030940400029803c50f04440c15111816404a064a40c10700454002d1242810b1207080e81c1000c1000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 386077473 1250 386076223 386076233
    0x20c03061501031521060e0609030c06010806010e24181b04030c0b03040f060e0606120a03140903010b030102072a0b0703030b01030902041506031a09060f040612 71
    0x74010215003a00c0c244881030301d941d214070010120b4403440d1400b0394403250280844d400c202c0004219031182074000b607002c141d19200d0745828001c4401080540c07001640641071602002501d0062030301d8001488150b04040302d1108004016085010180700041020003602c1c0780c14510030b80c802c02428110034009812040c0c004040705644d2000d0305e54100308a2581001240e0484040e40d030400760404a06181000586a95000902c10b5422855030ba29000c0010b41c80c0c080c04000e5075030000140f845027895410840151210b0755481d90540c80704031b0074400681c110340300750f4080110889060b200d100003008640505000c0c1480390b49540b001410004000b520981c030010214402402301e400c66981480c000c1510040c000d200c0004024410302c000a4440d4104d03c002660600d004900d41e40a54085010340c0e1000081110300c03a44600140300c4981c1c580b16440c80401505001801d0006400c0803c1b480c08014080a0245400040c80155030300c641d00a000100440340d030b00302075940d0324101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 386078723 1250 386077473 386077501
    0x1906020705011103150d0614073218030a0c0e040605011706070c23030d18030507170f0a05190e0d110a0b2205010216140f060d02091306030b0f07020c0306 68
    0x700b164030481002c4403235002d030300c2403d00784031005054001031a0041407490540c1201d404bc060741d0381403040c01c3c0b254001400316612800200030306480e6490303509052401106680e4160021010752070003501c0714413030003800200d054001d00103080c083c00446050400c81c0c03a280607070304816043c1c050500140211a0004010001e0ba000054100302c966400d80a25150882d11b03003014001400c02e118000100b5032400d002c5100784070301441e0030300d492841c504040440e00000120004034102045988808611001c180b9101115140205a84907064001020041480f03000b0381b40100f5078040d034225813214010348014056020143d5218074142038540c07441402da00624980c00c0b0b4101000465500014680c0039100c0d19800504580d400d18800c0c1403250140801c4075800418000203010f10b4a80c45c0040c51908000d4034090b83c0ca2031500103024200b01c034a40740c8984540341138810800300d60040425604810807000c1c40c0f100f503c581c8002c1340340c159508440e0340d05000f00000d019101c204441c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 386079973 1250 386078723 386078747
    0x304060206180601150302070f08070201080703091e050a080403050c18011503020a05090901090c0e060c0a12020312010b0304030909021804020901021906020705011103150d061407 79
    0xc200c071420380e109411030740b40900c40080ca0410341e010742d00501c40f010751035110b01110a5035140c0141080c00c15112040c0395901043c060303d00290000d2030f0015540c2c000503807a84940c1c1800c06101401060342d8421034006106400e040030702c0d10810070b0003046024440500d085412103403803a15140c80381080340e151200d00001074032610340364038241a60b111519443e030403504c04a594100c084207a400a13000f035448000340c003003045001c0013403c1c1e2a03900c10300c0307a501a2941190008600c3c241280140c0b0100f400640c042c4034000900802c070385004005120001c0c4e40d404040346280c080c003020300b070380b86003e03400c5110482da10207070000c2555019034020f5881b039802691842c078200d945000e41403c0b8428004900f5103070100101c00011400c15400a2035090302c10710456691100f201c1e001e400107070079080d0844502c0c1d000100042809001d0140564042d1400500c0f0b19504052114070340814150b000c1b5400303400200700c0b034401d0003000c1d400311b220a001c0c7c0100100c1e91801131401005100c03525 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 386081223 1250 386079973 386079977
    0x90f0105040506100509040c0c0f0b010501080916051018030303050604050c09030c191706010302100806100323011509080606060f031f030c03110103020f04090218060c030406 77
    0xc2d000501601c2e01c01907900803400640c80d80c0c1e2400d090101404080c0884240200074009484031200c0000e0881c20340101e4a4025000040c00b94103200c001001e100300074090940c2d40c2d02c003050324005e40c4207540b803030811200d0450381c408011074000801d550010880c20100c0142e031030108000185501504203610501c800c032800c015a07960380361005081c2c06040d07041c5130190300602c001d6900d400d14503048441802038074044002e45135645020600309480c012600e096400c030600400860a040d000c4800c18040303400c2840c11840c000000c00d00c0029101d664104040e140c4410001800c01102c4401040022440c001c40383c0d0384a10212800300459a1030900040c002c1c94005030140c40424898080c1d48000e202c0c0785000c42e036180c64142600040d08080e01c94010300100c4a00750b030314042c1c000045204a09408549256041c80c1005100030911a41498010400c0b1010010284111416076811140040c0c480d403034403002c102c3c084950141d1a0304170307000103119001500000041c20480310302c1e03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 386082473 1250 386081223 386081231
    0x7050607021623010e030609150105060708031311060403030c030e03210f0d06030f12030605030c041107060504081c060b0d0203130506250305040f030f0e090f010504 73
    0x8002c1ca40c01d140e800384034000d20ba203006203000e012880f40243ca0fa6008a052510014026900c00060b04041d0103803000005584800c4001d002103040c4078041d40107020490392541403030700944401d41e00717210003061031a2910031150072a00b0002610000f92941178094001500c1d5074a81c50702402007910502c056012440e03405100d10245000035400c0280d06520198000346440c5402c041c5040d001889040d1600f0814030038403104090314403550004502a0010281242d0b090400500395181d05150300c08150070884203000580b400030b407881c2d42c40401c0d40e00242d0514515002e5440d4007686800a041904050600090100800107800e00081d000748803e04413040400d41e5007194494410404090028068038200404580c090340c0e0140e0f6162100340c0080f038039078541d0708048013210b050450541508000006001560100c1c2c4007140718241000641015180c4140b00c03011000300904010000038544c12041c42440d042501d54400741283d5014200b0515408001c0c40900549015520b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 386083723 1250 386082473 386082493
    0x90501080d120b010306030204290907080f0a0f0218011202040e01090902190305030a09050907021009080c0a050a15051003060504261908011511120705060702 70
    0x20104910a0901458907a90310003420200d8002c040d1107a06452814141e03650303000005606c1303e001ea5040d6089482d0000900d04003091401617240161000ea4020070000081188043c6c000d56002c1c2c02c02c201c41e42d400d5050b5944d040210180441c1c3d41da141e492030002c11440e001c03002d414110000224240c90791090003180401e614100c0c0514801c25084440e400c1c01000066595403190041a0020300307107101142074998107485104042e801251281c0c40050103d2905520101d40005444129001d142a00304482d000350f07a00050281030320070b1a9200d1b4504100840c3c54201d034010000541510103031621424890b0315140c0e00c64041d1032001c0303140c4142c42c281403d8031400d4401c140e1b5031383c500515425900c0d050f005020040080b20380902200700c0b50404001e840c90840000038441e81941d83c1d0302040c050842c0350140c1c00041e414032070004010312003e0741d0582d50f100c03c4441490412580401c507100c051034002d4100000f01c1d2000f000455038140000403441c1c510882d459021076064540d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 386084973 1250 386083723 386083739
    0x307110d062903160e09070302060c06250905040c020f0f070603200304031101060504020409091b03032a021c03021b0310050a24050102011a030d1404080102030907090501 75
    0xc1c0c40d03c0d219070301c044c18100a00001042882240d00451000200c5000c0c40d12680419019882102c803440d0b142d20000c100703c119000b0007494007085541d502d20080342d920048016201c107800340190ba01c00c070b807204500350300c0318420410000c4d860071000450b5401c1501d0001180c5807192401048000303424241200154961964604070fa40d451a000030300d10380d2642c900300c6403401d0555550800795298140050b950341c8600283c000780009000008543c516032800506082100c41c11b040700c1755241c1c0d020400f098100c69803036110741d50000d501140c0309580050241101c0c9100b0000d43c024000d5005010b858000c0602010440c80394003110640e552a00910356043c00b0b4804a56243d4084104107401c1c40340d54001c548c0001701c1d00b0380801c640b19030741c3c05a01c82c410402088a00501c0e007040c10005036030709024411072041410711040f030312103814000c01e80725080d4003000303014010044001029415a00222401460280002c54403400d207940d003107031a8040d5210306502c880c245000485c3c0c00f0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 386086223 1250 386084973 386084983
    0x21b01020915210a0518060f01290d1505031605010c03050d1e060603060b030a020304050f0d050409051b12091c09260307110d062903 59
    0x400e0062806490b602c0b0005103408a80c01402c10b03c40c0c9108100910300c0c2110000c0800740103125809011803240b070040c111400c450a8203d075405143c0c0050188034420010b548818103581c01141d000162912242050405071503004070b4802c05180042e440d150011241c1c40b0b80c450468020510742c0040c1c2e580304040d03843c1c006640e40300c00485d1001c0100030642c020031000003480c1c424103000d414034100c5009030007140c00711000000800ca40b030580e2a255040390bc00c030400340c19142020000c4038103080078905103000c010005500f031a4004041414810208080501e0101141c00c48000c0300c213160004255401501c16030440c1400c11340400c592020032141720079054008502035007010365404026071050bc0182c4440f0150007840b0030340030240030300e100c110a071a980392151214285014100140100058051a5040c05807515000c010801000319158190480306080214076403e0001c5d4a012400c0c0c4014025443e112090039083d00c2c02e0806c020825074244941e1131501d425050644038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 386087473 1250 386086223 386086237
    0x4050102090303041e080c01020616020a060515090903130306020c03130f0f050906100c24091104050903160804050604090b0103050a0b0306180703020306040c050a09140a0207080702090109021b0102 87
    0x1d40c11190012f5506a1941a00008844644100d4100210300e0301c071101204c405884250307603d40e20ba041c50045051040055821040290003103241c4106554540e54460140c000240115000501c1400c010001c10603129030395284c5001000c410340c1c030342d003050840004c0c4c850b101024410107000620740c502100e03994071804002d01800440d00e150181201c0c6800090030841d003440031004031240d28600d00410000520701100002510755050406a010408000e54a48114180410044074180100507100d11414080c1111a010100d250284036800303590006a002240400c0001e03007401540c000c201c00c2c010a8800b08042c0c0c440c1e200d80d00540b403104002a07090b900c04d2000c2610141d916910700200901e40d010341c0c3c2800e4889d0b0001f0700380030f400c0d0b174240c0c0d603903a1681d4140110f1510140c6200289031303095081000d07800d49069040541c0e0011b050490666000c601d010034800a4000c40b501e070f940c0180320400ba5a141d04505009421040800f9011010382c0707510481800140300300d82c04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 386088723 1250 386087473 386087477
    0x60c05130b130302060f07060f0b03191109041e030216120f1101140c010501050301060815040803152218080702090403051213111005090904050102090303041e080c01 73
    0x15043c00d540a010142d844911944a2060100850350200ea44c5104d02c20115420400114403490020b04051070078442112000d80c1000c0900101e001404805860031500300560f101041c0d0340c1d46080c500e00e15200309a9108540c140d40c1e486000f010390108481050000003051258001c0d140c0103c4608040318400003400161541500c00204000d10101c18000e0814981009400e521813500c2c626a08070010b0001103030344800040c81280b4007800b440026003c11001041007405042c2559404403000d48040c4c4856000408605c07120114036602072194005001e5540927031140d1015503800340036144014040c0d00d0110300800d07040c010700742c08103c150841115400c0040315001c02811410240c002c4040c0b00c006c01084021101402c2100d00c140304241c5a20802c1500c0c3c2460303640700f0800203405201c1c0c48010310b058076058004041d40c100c8003051340c00d00c10650b16403424500901c25240025494800444c0c00104807694500000c030240c1115244801103607940ca00e01c1d0307503100722204580 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 386089973 1250 386088723 386088757
    0x3091d06010c0813120b07020a0f060c02012019080907030204181e06050906040b0403030c090810020417010c050702010c0c09060f09050f0f0112060207060c05130b 72
    0xe10340c03080200500c120702a0500390b00c2d0101c291403400c40c140203076000e0032054003194000b00c20b0001c41c09202d42e1201c4103001030b0003440380545c0c6010b010000848001c007500e030f1b10590480303ca403007588002c150400c8089090f0340002c6516090503150030540c071032140c0b804910207205403541b082c8540f500134141c08004180d4076041d542007101400003d50f003200040d204000b1180450007010003c414415807000041200c2580d062007416100000c211407990784c09082444000b40800c0007980d802030700341c0350015981c81100c0c1c08481d455140c1d800b4400510510080d41d01c00030301c0703074001c004035034035122607103041f2480244c114266042030079880003103201070280340059405128034a0620344141c0d101078041e03455014680c1142e107146c0001d01c004091403401c4c031107640da030310031141c1100921026100034500703a809000780803c140600300700314840c06001000c010302a010f49441c158407101c18070101c0690007004045c1c0e0800440394440020524001a11714141021100354040340c0080c51 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 386091223 1250 386089973 386089981
    0x10c0e01050a0f1103040f0609081f09080d0e0607110c130b1306080a060c08090601050f0f06181507050303060108060a080d020a0212070501050403060b010c1b0303091d 74
    0x16a10107012125a41404034a14001403074a900740001e201030b0407c400501d640318182a070040046403650030042455010800341c6182e54051988140610500c001c081001caa007442c00002c140100f120040480e0f040400100f1181c00c00f00f1820b01c07070180d95841c18080c0301600324055443c1e406c241c0d2a034014020002e6000d440c90300c1d4120851656010b0400f02d100b0900e1600740080310030640c0145025003010342140d04104d0a030080e81000c81082c580103c40341031000d00c1d243c5481c810f00c26940708001c1007805842940300c1d00409208910000c2020b42c84106204450710a00266400948a030b45070200e080c404055050548034034a402000541c1140c0d40c54006481c43c080103031220b68821903262000503115000c02815407801c2c565030250a65461510510800b00d26a240302410340d00030010a1100303907072000c1990100c80c0c00c0140400c64884207401078442131040c19000d8158140c0c0584c1d8079049001c020310004480c0700c2ea580c0d036902c550b00d130413043c0c0c11209111444070b504071717500110b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 386092473 1250 386091223 386091227
    0x902090907120605040f020a030b01090506060903030a080907090908071a0705041203090905190506011e081f03033513030201060807090c0e0a0e0f1008100e010c0e01050a 75
    0x1039000d03106e40004404006941c0010750314500a900440700405201c00610914072280161908981d0079140c00307007070448201c0001c0c1c490150400e107908001c0f4010005003041d4042041800a202521741048801c2940c1040303d0f096000c818192200c460340c04820a05001400076103101d440d1566401d41040e041018030040000e12580c02d40c1000228800440c0c1d00c0d0b12071041c103001c5c4502c11000c007040319000100d4410b45200429441c10301c5900f4006420940c10303030345502c104441502d00941c141d91106d42c0380d201d56006035581c0b1071001030281d01004064001c0c0100111200041043d9100781110071950804605900714001d08040840820300e2844920115418181b00303000116408e6104c543d0180703031518544c0000c0c00f05403aa80c0c0b514603940c22210180900c0c0041d04c07620420340c10104010404040688540031505041000031000a043d83c01c0f1800380100b2000e0301c521003078a05c2903801406d08040b41c44020f500e400b03c0c0c410141d000b00242d40c0441d0301030311030030708022200c041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 386093723 1250 386092473 386092481
    0xb0d05090304261c0c060506030a052d0d030c14070218060429010e120c120a0b07170901050709150302071704080f070609030813031509020909071206 66
    0xc0010244103140b070b0982032a1302590000010390259480c0180c10302141400c90503106c0c0030b884d42d4040c1d08401080e8012a0340800d48220356600d400c025014000d0b003000250456201032a403030701c103015002403954055416003080b01c182c0956640c0588621148403410b40900c2a03100095104032059101c0c2c0d000e48508003c0e66001800600c0081c000e51038040a100340300070302d40c03060000c1070404443c400c29a045584001a04015100880001018800070f941d0b119a5281244200a040c00d018190b500800c4045206a80000000014244408007901920b24400401c46c07d041c5600000e000000501c58144030303101903500c0300f84503843e00f0080d6000c0001d11910104054082140d1004503510503441d803002d0041ca0082d90b075035840d000c1c2040c00c200d10000140e40c1504000c4041011903442240c4034252508980800c0d650401d004001c01c40140b29840188a44580310f144608800d5075030100240c01c1c02500c22050660301d4886064484500e0700841c0c05d80701007200380501240032640 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 386094973 1250 386093723 386093789
    0xc0316180f0504050706030c020307020f090c160b0624090d08090303040807090506040608060117071a190503010b040e0a0b040921140702130b0603010b0d05090304 72
    0x21002540c801c000004000b518811581600e00382d001450030071442d0b071b2610070449489061702c051400c08085600150241030103980399427041d8203500100300d183c0c3e0f0480490342600841c00c088000701c1020b240c0a02403540c200d03600d0340300d101260000e40f11011940c2d10b4a40800d140c101440c07812003030b1010843c0e090550300c42a624101d041c030114243d500c0800c01000039040e02001000441d203085c1115060329002460300b03000d1420180200b00b02034001032001c1c1902c0c0030711fa1b100c003500c0380284a40e14200040e841010911625848203e101110310000c00c0f1544820a000342c031a401c044003901d0b03e110a1081c5210f01e041000200072000c030030315041d500841180700210703c04039074400040594152800c10340b45420880004c0c2200ca4841c4c60381c000b00703d0b0340e0801500c107000001d0040b005008030300d0040e0140c00c1c1203028918071543d540c0901c042501c0240301d107840e540c480c16010b07110f410040f035444241d0300d400c0120301e80590010a4074211061030025059255508911548000d00c0d08 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 386096223 1250 386094973 386095019
    0x50d0203040608040b09100f020414060909450c0a030302030306010e060c0d050a08090609060606090d050d022116140304090908190509030d08060f030316050c0316 72
    0x2120220384401280134480f0241100000540c44900f4800b04451070f0080d0be8505105070310800218145484d02643c144d030200900750400f50600400340080a000d2000040d0701001d00e803140d8042c590f07110700300500207204400d0100d4a400d0000030500440071405c2c00050050790080c0001182c0d50301c6004400c945500140420b400c000016800918040705001107101003000030560202e080c2e4000c0140da4000703010002070400d8103207907106640f00c6001400d514000c80000440c00704c0c0392a4000b0b03016945900004841d1450450040251640c880c0382c03011420182d0f413121000031020303140940c1c043c021540803485002c1302c107580d480c0c41c5203e171520489060006100c00104c04905100d00307a00305018084480d0358407805039a100441d400050340c001800800c0c00003d03810344000a00310805280f600704140241c80305e00003e01840b290101c460b80c94400069a09001c150315002d00308038501c69011281d0884203541056220712803001c000031000c0c01c5201c10845d4400e110542c1030708080388 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 386097473 1250 386096223 386096233
    0x30228020f0703120206061c03030b060405061611010c020102190c0e01060f02190f0b0a0e10020c010509060601171f06110f06190b0a0b07030804050d0203040608040b09 74
    0x1042680d4200400760b0300603a002c1c080140f40e1003504d0b0301403041d164450f00496030301c1130512000e8100b4103034403c01c080250030503a480140780000c0c1c071240101c8000d440e0052031143c03101c84a100411004806a1048a4180c21002c0704401c48d40210010160142c1c160050003075102088501140c6000041c0c043d034800c00c240704000341e0b61801541ca5400790060b071780c07048030f01c1d01640c0d80070340340c802c200385546907608000c0881c10201e0a0100103801c0c01d0344c0f20003840a00d44400360110064400b220005589004d07240301c401024001e0760040ca01012501b00034001740c0d507400f0a56803991000c9400e1400b01d8030041b03280e1002c1034640d9003140e12521003d050070010b664a5021400380d0a260803003c08a1505a0341a80321141000100307078000811008103a0b900e02200c540c5e801c101090803a1610546a11491045035242c1c3c40300d5001e050b030b60000781e848285c40d04000303041c590140c606031141c3c0102405196403910100445041e03400503250780c00b40d511180e6070700d40b40c0700d001000146e9501403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 386098723 1250 386097473 386097493
    0x1407061b030e0d08160b010608010308090f0d0204020309100e030702090105060f04080a03050702091b0d0c020309030a1a0a0e0618150c0a0e0409050a0f05151e01050103022802 77
    0x4c0d0400b40803c03d1011402c0f1403002090316102c940443c040e008242841400401000010f0114084039900e5800390354180c2c103124550041403040e40d1800000358030900210400401d010001110400f14a412800b80803000c1d030384401540700c1c8200c401c0650003c1c0ba04005024a003000f40041803500c0c0c10314412407609540e084450b0900120400c01c4000a000150104c20341c07030100012030b0806041925100c510b0b405503000162441560101010a6140c528810145000340b00351010b0541c00750a8400c07102071441d09545082480050303a0a56400701c01244040c50a4810a003c508140000306920384070584030b8210031650b88100c2c105445103c1c0001055400c401007207002c1c4103442d501c1a200e41c1161005028100820001d9020358034001c1c580c80400c034005501002260058203c0e1440059410041e00781380803c2d609206181c2214113201c0105510030420124291244501049980b11001181070388a04868020110154074100140c0500201c8070f0f407290384180112104880 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 386099973 1250 386098723 386098733
    0x160312120605180627150612010e0903130b030105360408070807060b011b05150a14040c03050606040501050d110a080a0c0503150105150901020c04091407061b030e0d 73
    0x1480170190030031110301205003d4000c034051503011203a07038100d45070307800d004101d01941e90b003030014840c1c4e0740450f0030b0501243c42e0714000d0003110000c13090106580388c913a031202c810b440503038000c0c4500c90241d101c3c00510501c501e401840d403c0061415080c1c1079a03001d42e010502c11812b0080c10a032650f110800c5658001551040181a0300344240d001084517655080090820004060a0302d00781d6172084440300000da0204440c41031358001500840389403100c4108000411184c519884948002400e0200b84a81d641d0003900b1240314500319541c41d07840c08144402e0f00d9081c42941d810442d40040d040000c0e007106512040c0250152502e50203c0d91803209604e8801014801d6860355002a0103020718203041c44445200d1070317a11000c0c4030039450304d404680e0005003000060160304001c02d0340c1c03e03181e00c2844202080c1d48000c200303000c00c030450704107140d504840040c0c24044c0d02c180305002034107a0003180381c04403040039800070b0b070707840d0a49407029107000740240c4801e940f0240344c0d402e010010b5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 386101223 1250 386099973 386100019
    0x90908040e3313090602120907091506050301150e030d031d0a0230030403200901032a05040504060219082203021603121206051806 58
    0x3100070034561001000001d1120a040802e500824a504036480c0c4901c0c0340d222002c3c942c6181da02c8140c0000c088009040c072500034000d490b00e051196031003406010b10003800180700c000382c03141404200514000d045104914001a10030940030803010320040016510190094100010904240040409280000b4108070300c50340d148000c01c0e03a4107945035011060303c0c1ca020598132043c1c02000340e814541c0025440c0d00f4010b040002f11500c40d00b45c100c028071103501e81d01e1852200421203844580740d1912003901291284090b0070980d000507009180d29241c0b0043d4100c9400c02440144108216424020300c9003000e15824a40c05840d00020b2a4440c0c3c4601c40c440d9020754801a00c0c1c0d441a020440b40f1000d0f0a042c00c10464000144048000a5070440c04244101d030350000820009144c280e0410a13000403200c040c0000744000802e000020742040c810b081d19a803030803860060130894004a52a034010550401703181074482840044810001ea04070b0801401303845d400001c400302074145 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 386102473 1250 386101223 386101231
    0xc1b010e010c30020d020a05072601060305060402091e04150e0703050a020307060f05030609041a090c0301050601110615031213050a05040905030d090615081c0206090601090908040e 80
    0x10794500042e50300c02550610400791741005910207030001c0c2d44c03a034844903070321000c3c0d0046500e041c8003014102800c41c6250040790400780406c009002e0640d0f41d06003103817150030803074041c0c8c050310b03c40000072414031004590100c2c080700540004481d44a031342350680a40c401c0c41000a100b03644103044032040804204200040d07214800420003410640b06050a1202561021090009145003401c8079a04801a41d5001d40e064030041c804e985c46041079179010445030f9140d0bd0000c428000e00048003000300c1ca00103543e205400030301a68480d01c0045580710050001d900464000c500403c034400704024410003c11300040450740f40005000802c2c1a50780b0400b0304280d50f11650300e00304403d04265030080000d140854040110510b0740d192542c40e8840c1c906496402030b41c840e104001c0100ba540641d00c00069007417042d0407035884403032a550f5516440040707500e0031303220006c07462024030000e141407161040b1006000d0603460b06d98888042c000940c81114800001e00000c00c0b610400d040c1030f1b01c6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 386103723 1250 386102473 386102543
    0x30c0a14070e01120816020a03081e0c0a0b0405160609030302120f0412050a060609020a0e0d0305040302150f030c040e0702161811030703020c1b010e010c 68
    0x28400c60342610501d000040d500440302941070800422100c0700000b84105001d070042002a0344582c405145801441200c100941c48549100c0110521a82c400a0000e0101c400041c5006c0740b02d508003111240148240291280d000321507440000380141c00340790300030344100112021419401451201801550081000284480410800d06a0412004060301c80d001d01da50b20f00503c0d030200c50b9039841980a03503620f508022415000300320041000d01c002c03d8001d0410428580c41c0c00c00500039600c100c62580010741c207541c541c4428940a0001529142c0c140c40da43d10b414650750a104804201c2000160350320805d1000d41d000300c0407000194400c03880e032403140f0f070b482c1c3c148850404041400341c081c000710740c4000360142c0c1010550003141c094910811000072081040f44c4840042c10201e0290384080d4004018410342542680240c0f00c1e0002042c240c611b40050018200071a0a1484455001a070342c55840c4003203500555401130352078002c1004c0d4020b16442d50580b141d9420125503010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 386104973 1250 386103723 386103743
    0x260108010905060703110406110f0d0e040e0601051813060f1d031e090d050304120506180c04180209070c0c06030e1005100e07170f060112090302030c0a 67
    0x10000d05220f86a031001e0030b41020400040400500b04045c00760b4050f0000b071181e000d000340c3d0100f90411a0030421020003080702e80d884d241d150010507040b0f00900b81802641400b80e140d020510100703e541c16104003030038442c42c0c43c1e4080007925402c40080e06a60504100c110f00b071010039010b0181d04546000c5000c04a1a4800d61078a01c1d080030444021030f54540040c040389030040f50107282078007200300f241210394036030f1402000101500c00c0340000400c2c070f1100103400540301c0d082c00754a400e480c4c003920555050b80d4403548840034070b400010001c82c468010a5440103030307103002c3c2d00c454610b1500e8000c11a000340300d43d010880c000c03c140c6400021410040302c5000b04901034804002038608cc1c40c09029204d0004001d07913881608500000a154880001403440c4801032540c40c000c0c401c00404402c01c0c1030024000e01202c01707610400103007030003c10010324401009400302d8003404040c0d5480b40062840403807480106a4280304a085000401800c40007200801a20b1802030262618013 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 386106223 1250 386104973 386104991
    0x510021e03060f040507020c060d140901020906120a0605060301090b040b0312070204050c0708040f17010603030e042003011512200a030207061103010302010e010e1026010801 77
    0x1503000c000ca4459000d200041042080350380b90403075545003e907403d880100d142c0e15000c1c01a404e04824004e01c68011401103910b08020440e6000991120f19100c215006074070380711301840c2030384a0303000c46d0b680080c41006a441c01ca00020901c0e07500030150b038000181661200001002c0c1e41c000e0303009e0858581ca0340b441d03080380c1c507161080740340351030084000b4040b203518888004100c0c0108403001e8412651200011158214182225180b40e8400c0328141d540352195601c401d00222070140f1041190b800b02c2a4410190520415051380c5e01515691507040e245820000505420040e8029442c80040260f180b60a004e01460180500784440c0a0b40c0c2d4000400805411411030282c0c000d506043c1c07103c4500113000c0f03850011b060443c40350fa035903c9685074242c0180c030032458000c10451030400c4c031800641c0c0c2e20780a141a0f9200342c0e10300780d43c50150070044440e111802001c41d40040500d01c5941c5541c001e001065886a03142072a648510104541c9051500700364000402c1da51660514 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 386107473 1250 386106223 386106247
    0x80d060f06030b0117011503020702030d05070c0e010501090b03071110020913021603030c0215070801060f051e0d0f020c10051303020303010e0c042c1e0c070f051002 73
    0x183c00300300c02071a002a4004210b02c07010345144062080d00030a0b034841c0d01c21910382c0d200f90100e030851078002e0101d0b007400ca0000d400411a40c0004000d0320420301244001c18003040d601c180382d0407030303005075108a4006c0c2000321b135a01c180d1000e024401030180310f0444001c00e484c00e0140300011100013000503120380081090000e801005032041c0c1c3e03520710410260030412000ac0442c274909406280001e0841413aa0080e4075290790320b860020401e1042d410080196030000889040c0d4a680d940d0241101d642c070030030382c1c1e14020400840140c034080c10700b442014080d0300c00b800c0b00b1456003001151840030143c409040340d00c107001c015480c1e000380f15516081c0490380150764000040c42009003000304181c034004d44a005c103000305903172000e0748004102d00c014080140d5007d400c0b4159034000401039020b5180744200c030541c88000c0038113087d00081320541e41600c200c0e00305e0807e84044039103503184220004039502082e0110780240c10203c40c0000305c2c034100084040703011190320051b511241c1c0c2d828 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 386108723 1250 386107473 386107481
    0x12060a05010501050426010b060d0e12030601020a0f020f0409050102030f090708030f0f1c0e0d020f07060c06090812010807090b0a0303030b121b0f0901050f0904080d060f0603 77
    0x84141486010001001620303180d1841130071140110114031b210a054010303075400f40c400d500e030142d404072000c903000b051110b66038000d040d20103040e801c0716900c1006003040742450000300e0380c0c42d001d41c1244d00700c00081000152007880680c4014401600222203400050480d1900304041d2002d80d4040100040790240e000101e81046106004201c007515140303d40d99288100c09046410520104001c9904035170036090f0340802c451000c1d1128040104040c0740020b0a80f03e089a40c41e02c28411070104c1540086810b100700307440c800140020904190301521001084442120710555540e080d5012074460b502402c0c00c80f00341c002e8060903514108029107002556004081c20703a1074042001c10540d6101002803c80e50705081c0460328030540800207440c48550303521600140030310000400203060381c02c4141c84080d021541d01054804e1002400042c40c0c0074021300f60080c007200072603440751600f030445640c042c0c420744566180c00040107e4005681c0c40ea8050700488001c1141800110b405002d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 386109973 1250 386108723 386108729
    0x309100e03070515131401090203010204180507090b2d030718080304080c0904060b0904030203032a0d051008010c0c1406060120030d11040e0106050f0a05031512060a0501 75
    0x4030040c13080c00d242c1d0071500e880802880091001071486a01c2803541429008a191300da0014001c6444a030351302100400d901d80300c816001c20360f14180000d0a0f26010780e484005803000c6580541c285240d0708030801503102d1180d50851060031800f4004000f008900085104000301c2c2c1d641205807511402c1c03c0410083d982183e040768100780800d10000600141c16a000c40084840800580327031820518000c01c5141055504101030302c04010500d0f40020003035000d9112016840f414a5441144182e89520740443c02208a001c01c00f411040e20b0036040160812442c5200c1e11000b95a00f03c1c1908440040000030007144d000c0c04007070284220900c006020b034035414081d00c60341c07070494002014010312038910140c03903803850100c117045481001a511144011001004031306080b40106c0c0c1560040d12601807412a0100081919031240c0141d56240108020f024244510742205407459000180420800d550401c00d000403541c07034410175041c01074400302400c0d460a0030b028020950301305070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 386111223 1250 386109973 386110003
    0xc0406020d11030d0915090501051f12060209041b1706040c0c02010c061e0204030227070e0d23010b01020c060409020c070e04150b010c0201090b0309100e030705 71
    0x40701103802c0d008401c4406480342200c001a141ca034a10f001c60752051a0100403940c00d150040c50001c220056002c17500600481405c4031f5410700c003101c80060403d00380030f941000d1103c4c41440000442c107030003030210201700400214094a01190b0640c080d20a0f1000c240041c4603c00130300da1001c01038a071581c1002043e5014451041907001c0a04071047d04c1c80000c0c10064150400300901419a220480c10b111011004203850281e001d2000130b500316000a070300c0740d9400303d1070314101d611561080070f0055500807404690f03601c011084e200007025102c615003003000030481000142801312580c0c11480c0260359880d80315101140346084503480003500381507500444caa03001d181c0d00e41c0c0c241c0b402c13109606030140e564102c0010701424100c00c0c0c2c0c040001d40741c901090004016592021410700c07182c903203080250810210044030740c1c240001001e400304030003900c103001000801e00210750024910342211003000160f1104070407503a44c2c8503410019000800c0d07103400c1140038080c10180c1c807801 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 386112473 1250 386111223 386111237
    0x703080a140105090610110601090603300c0f05030a1d12060105190e0708090d030b0f01050a110a0c05030705030102120f0403022506030506030118030e010e090c0406020d 75
    0x2050126101c181c0c040c0217540300c2c0c5000f144000d001ca00ca000110058080c00003629002d507134820304540501a280011120f00c2c0d40804c0c0705000091030040502640c000008212146101242c03c0c1c43c0c5990102c001c0e20364400662111011440400c02011050340640c0e8500000b1422080229209000c61a8510400c20342207a114600000515241540c0c021118083c4000104100a15030300c1c6960010314034803c041e0400074001d030010030152080078a00c1c1a508200c0300c441007101200d10805400351300002100c80e080403540300350080c040b1888141052040c0c2d2514031041d910b01107159504071242040e85034203214506050001400428083d0025802c011110000e80b5122900402d10390300b0500d00d00025050506c200407200100c2e5031114140e040050450308802082c003a4041d81e4086410070707010402600b814400c12110f000d500720442200c5205a40407150b01c80b0129040b8100101c5040d00510341d40c0e6004000d001c1e070802c25038a81d980e480c00c00d019041c40795101d4440144862 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 386113723 1250 386112473 386112479
    0xb04180b0a030210030e0106030c0312020706021203070903050f01050406111611030c10020303060414060108040f170d1b08010f12020a2111090105010215100b0703080a1401 76
    0x718541101507990445580d900c421603018110020180c01e00c04500d07a41c20a0030020a00803c0441902034074040e007640c07016070b1134580c4180e9445001740308080c01640000c85100010141d82c001d160048030628003140c41d203640fa02c5a0340340040d071244032580c9964900500c010415148076600d2500c404001b0035040c69a810300c03810440360801000b40c502040c0911071100d6942c24071001c4c501e440b0007401c0103506008100020742c0c0c0d4004862140c02549400a0302c2d00034a02d588205200b444142e40714001d6031740c0c80e13803000c0184900c0b45049414242964448920302d5120000d084221080325000840003030b040140e00071503209034040028442424010310030800041c0000d0b003941c519a0000d4030310700c01403000c540e010210794006c2c0300340c80107004203410603005820300d00c801e00d0003003c0c915410300484042004244003803080c0d50160b40500e880071106007000f0035655200340d0710000b0701e900958801c1e8500c000e030710810080740000c0130b05040049840c21440303445100103100c0700e00806581 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 386114973 1250 386113723 386113729
    0x7020732030c040c08010311030a0210053601021b090106051605010603080301050f030c090a0905010e250603020304030c0215090a080d1101140f0603030d060b04180b 73
    0x58541042610228045144502501c080101d16044040070348104a9180081d01c000e1940382c0a00045816228041e50f0000d42e140c00104207280b81e070001d008100d410300d1100169060352141c0c40d1a100c00c0d04002d15849042140c070030080513000c500000d0346030f4450240c002410040d650740002d42000d00f0381002c0c401601d82c84441411b546550a14941c6ca0741d09800301701c45901c50b500c00420549c20081b02104009500000c0c60403100706440165200350b0000c105500c401051002071741040381040001d02912030794000215042c0544000120201002c17111401c00d01c0040b05400124100350042000ca80364038220001012075140031815400c040d80d0041c04044104d001a10508610381c4030840b0a4802d0304540702c0401c000c0040582a41d0b61040588660410516001280e00c16040401191040c001d6075084c1c0d48a07400d0510580d2a0171071850031480252540b41c241c0f1050014149455503032150034007414404800c244c480746001e00a01d50701c4607201007884403a08089016003192 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 386116223 1250 386114973 386115029
    0x5030f0601051c0e0c15090f09100509040f1b03080316090b0c0d030605100c021318051606050c0a060f0b04021303020907050301150302030402060708040905070207 72
    0x640910b80280d403458102c158031880083c0c4900c0301d0b40b007490508500c43d1a4000504500e0001041e90203044040781441e01055601481410b190410801c41d802d01e01807410110300760380807128108150340107490b0404554660000c44081b650f44c2da241d41a581841180020304880b90206540142c11905554480440d0302000d0141f600800140c410640414010f400e00c0000c0d04100c02140e0f190383c414111540d640c00c03010b1039040824500200440d0034101101c181084400540b86c039400018168240b0140303004850500300080d07651085841580602440300c010b503405113004005000f46074103540301929141c1e10080a000f0100812985000c02141c03180c100380d0404030000b400c105600005010b4030075007440a5000d440003400e003420036005621003068a0003600e403c0d005030743d0780744140c2e5075110030b004528070742c44107860703049541d842500110340c800d20103400702e81000200d98945450341c10030341182ca489501c440402814a42c10064040245a403441d443e4104541c400c27015148 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 386117473 1250 386116223 386116231
    0x618060501140d090f0f02090c0f071502130f2c0a0f060b04121b1406030c090402030124022d070305030a030c1e0206060607060b0306070801090c05030f 67
    0x103004038888001501d0f5510480486400544a1814481d0b510300b011020901d000c0c103c0c0300d1004000414985194201540e140805a04465107040ca9986074410380d6400c101015044c00e40820150b4070510b08018410002c1001c00c800e002824105504001d80002c1c40303a180b01c0001032031000c5580d8540c020500c0d41c1281c1072100009402d4250b415070000351400341c100d500707090700000d400038100c44074424507401c4030300401341950511203081800424105910070845024007108141509180480c001c0d9007224080492038a003850080102e011307a0001d80c44178603600031181b40c64207142c10bc0316007551003203681c5c8090204a1581280700119141d2084c4c0101007804c0d10030359207140c1c1c60400841c4c01454002c42200c0d150707819180001c0c080c00038040c10800240032442d200c40d00955050050002c4504c0d50040d10055543c20140a05034100000aa9440352030346901c08a98a080c081280501555031380c04400d90b0421120500361900c06440e04100b19041003008900c1c8440d010503600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 386118723 1250 386117473 386117507
    0xf070c02061306080603010c0309020901150203130b0711032a010201061a0304050705061c0b01030902041b090506040b1204170a030c0e0111340305010618060501 71
    0x450819001103030a5000e581d18251941c0c00751500030544030b4104c0c0c2902e11400048000740001e003050312046040d603039401402034100b9080b0005100003407882c403000d40041568811a8100030b40c121000b07007030f5881c65100022038040018600240f0101001f03c0c000c00d0419002080202e04038024900003885204c205a0301c18541c1c0d1400c14503070b1003904260001c2003041160244214000c014020a40c0141c500b1501446000130000b10b03402c1c0b14013921070010000800340078441c9808c44e240041e1180001050405aa4091200c016078031441403e580850f0441103020300088407401812007000e540005110700428802040400d0b6001d049804e00b40d04640c440060b51500e103404520701c2c2002c0e60800c02c01c0c0d070224940e903a642c2c0c56400510790a0030340c0e0722624400702035001540d68240c8100d601d0703581c1c0c0003081211107030074080004641c40380550000799034260503401100c2032401e40e40c00441b15030751101c1c2c081006240c03003074801013420403121040104620740720018140382428084221 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 386119973 1250 386118723 386118737
    0x1503060303181201150f0e01050616210215010501020705030a020f130207300801060e010207090f1e02090306040b0408041d09010e011a0111030c1b030d080f07 70
    0xa481e0f400000d8006030342c0301d000384113280710b08858524041c82030049803483d0401c0788002032284150200c141c102c40010f0300a41c90306544e501450343c03180d44000d003954469181c00c0600c1168868501026031402c50303a0141003a0381101c00408481001a8440c074115030100c6420b1155030f501040070700001b135040f03c2101c4404584800720f01c3c00a0380d001d03808842480418643c0a0008520214064030302545140b02403d080b02603828801d1550201840081c2000c40140856805101b4203d2007620500480324074030b031b4034254901502e4801c00b2088031152181c0c8001203665060b46080d01100000034290b06122800c0c001c25502c0b0f40060000d004043d600d804901070103004400c940140001c01c50140711245000c90700004007100b41e0ba84050780d803074a0511440440103220b0b00b050b80083d03884d4084290070070300044540d04c2c0c04d0b41c0c410310746010402905103809001c106106501a0001c540e0b141403080034101030502441303a03480c00030710849030100020360140d500c400c0d60021407030a00382 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 386121223 1250 386119973 386120017
    0xf0423100501090209100305130609080d1505040612211209030216090e0703020f0f0405040c05090708072f01050708010e011e0e0901090218061503060303 68
    0xd19020205904252051405002140c28551a00200804807080e500c80b03c8950072100c1c100c00702c0c0c508444040700034081c1d0020380001141600003428585c05003054a06004501d04d408085501e040c0078260018034000081105040c103000310001030086045000448003d0380f19611644104ea00d80040390141c03d0041143d240121080c4020314820181000060030ba8940613580342c03851090102c0c0e0206000d40010781d04041d0060040604010000e00080340c42d5a0a00c40d0007501341c034005030700007a203000c05a0140c0320344c45120310450040c00540c0804d803030102849620078000e03107040100f2901904001c2050342000070680100710024210696081e1900044148411808802d8855003801d06010b0f00303541c0a120581070310321220310200240d0ba0b450078800d1301c21044006c9864403010340c4041000b884450900b42d84070076030400209401d101c0d0b030300040001c05020b40d171007180561102801103074104661101c03c19010519410f24500707210700000c3e660300902688502d400a241c09603 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 386122473 1250 386121223 386121293
    0x2060a03090b0406060303140406120f180b1501050901050316050d11031008030903100f02090a26060103031704020d06060603060303170408070f0516090509060f04 72
    0x501c0c06a040003840c0800e00b401c0c60914042d000910047c1c00160000083c03a05048540045038101c5080f078032003492944560080b007014203200c0580512940d42c0721800c090785101d000640c04458890238140031146850f0880c600b552000407000b60403c0010302c07030702ca0140d821000700d0340c01c0740c00d1079210b4034640002c4100b142c0b2807044682070710060b814119040c4c03142c000c4901941c040c0440b42030702c17044107440c0c43c3c11603568000d844025605034451000c11801c049180d1061100c5c088130030000d85080c1682c0c002c030303024502980c08840108900e00d240d0502e142c001e0101099188444044c10055246460003401c240f080e4083c0e00d810004280482c0456440b881e40d00d1000343e1001c0b0900c03040c3c1c0d40350360203001081e20344010b6000c505880319064540a16481292155900100250604c0c280b03880746030813405803100840d21480b0324608410303000240221080100714021022501d40f80030308800d81020009403100045c101c051061200140a40c54510801d4540081c45082c00c1c45041503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 386123723 1250 386122473 386122481
    0x2121602221805010b09090303010b13050d080319050103020a061d04060f061101050c1602030a150203071205040b07030f0209150403140f101a060313050609011802060a03 75
    0x40001c0c203854603108419010411041d6980d041c040c4008110040c0e49000b404a1404215980692500100300500044001c3e10187c80413820200b8081c0340c40c2c4d1600007140c9220480582690410004010006071400688601c042030106040c10301103945540d011507000703080c034000c0c402400b945440203c0e600002d900444d9881c00010014400142d8500426541c001980541d43c00103a40d400508225401402000e00849600d00200e140c144003140490f50300c004010101d81c0360040020704004902204100c002c200c4000000607607a08100002810310408001c81e6100241040c080002050301c1c28001e5500c0740c18dd080c04112481009c0c2940d0003031041c45040c40e448024034004501034a0b201001d032003968400c48180006014588034140c0e82c401a034a80700540d8440002d1210003031041d0001d000b07480c00c2e0b004180d844640680003404580080380c0c1100c04400c5010100107001d03040200319003241c11000204020882c54020402c0e00d215a100a40580c3d00010000c030000e1103580 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 386124973 1250 386123723 386123779
    0x9020607060f050a0b03030708120402010216090515010c050c04051b04030507150e031f0204030b010b07030905190e09150f0a060f0b030402040911060d020a02121602 73
    0xc1005442c02141621004082c03c2d21013060312494060f030600b0500300001240c1005402c610841c1c00c2c5502c4105192070404000c10890450203541c0308858104c140701554400741911445c0403480c0e180c0030141c91307542130005807030034100002070790184081000800c041c1d00c3c8000c152408603103690740340c0400f082d9403d82071040c45a0700c80081d00105110001c900c00e01610248400c1d01080d03441c2001c11194441143d03c12541904000c03104030207259015000100100790031005420643c1c0e0341c65180030074009902012564000007280c07000c266015201c500603050480e20709800c0711403200c1040d0300b00306c00d000300001a41e500000c14041201040002c40c60384044200d00038a290a41541140400c1a2851284c00381400400b094004c1c0503030701c402c01d071852103007000c0c20365503640c00300005032492580580d104207011110245545a14005042c80c4000981c003584c0c4d40e20a000c02841d05500041000b4121800d01041c40441e40074800e1991864040761009210300403030151a0304040006 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 386126223 1250 386124973 386124983
    0x90d170a0b12100f0204031e050111030412080a050106140c0c1306051519030506010507020a0b091912030c14062505091008070e060c01051005101209020607 69
    0x450200b0001002405000b0515408010b010f01c2d000100168241d000d2408010005070207a540c9690740144131711500c103100d005800103d0100c02031054034400354000d89094907800e07038810820070300c590410f074440c0c0c010b042c50b401001550b1401c040207020350308420301e600b0700050000d850074400d0005c120903144100700500c00150542c000a140000b0081c52103000d01070b83d42e13290507030100380100b03007910104040c400320070003040070002d0124021724004000b1414040b051240c1300c0540c644e21140800751540c141d046030389194280c104007080c664481d912014484070b02e070500014500308000c007141c0d6494100154400018a0055013240004007498030500c03e010402440c0806154040d03008001051143c01c2e042841d030342243e9a2054582413504940400c07401c5803d40c1c0b04008079580b08405d40780c00111100c06000003041e42d44505880a40c980d110000d00840000780c007040d5008041c00c4a80c00c000d04400c1e107014043c0c081078074002900558559410b400c0d51104001c80396929842 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 386127473 1250 386126223 386126239
    0x60b060409110a080c160b13050105040609050f010e1b0109080d0804021e060a2a0b0402030705040b10080a0b04020f0d050f0c041707080613050105090d170a0b 70
    0x307051030329049803071400c0014402c1c00c0424560100501244c09800c0b5418801904d003c0303c0d19124100d542c00340a2902203002386403000081407080c4038003405a0320804011079861b01a0030680d1034100c5a451103140380e49001050485010700042415182c1244201000c002180900684441c001c41c2d102c5030050155000100e01240d220b4110780c40b81d0710850300030513110031a484c1d0f4401e000c0c5003002550000020041c0700005c078044d07040802c20f90300555410b10b0000c00d00e40c03d070101000008040b43d05604d40000d000c1189018005200948404e44081002020301d000003000042142200010310010700007090800312035812020410790701401c255030311f102240804500340c0c0018202c030521032401d80460510a03c200c2018002c5440ba500d4a04103407c2c15070b09071350349101441e4410248120000011081d10900c0128441e4458081412000d0f4a0303003849801c3d070301d0040200229030070a10107040c8054000c00a84c490a03030034002e014a50350b036400c00b40d0050ac2011b00b11984080c3d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 386128723 1250 386127473 386127491
    0x1c050105040c030b090d09360902130507020a0318050a060f030c090803041a0405100305010f14010f110a2109050103061404020f25060b01080f0103060b060409 70
    0x4000d0b548100c034401c090310a456900c1d650302c6500d60b840441c84000003044940c1c01c01100503404001c1e14100c0442c440103d4010803003030301c01092689115241052074a440311582913141c02c241030712040500f041c05100524080b42c0094448000d500010140a016420180e41d180060104000382001410000b21030f6168070014001d0715401c1042400242030030100c0c4070061081c90880d080307400381c1c0000c42c02c1c607050198003400c900c07203184c141404d0754050100203220b44e100105215000e1660b1000589035040a100d07050306903540e0002c1d06171a03481c42035600e20342d07480980c0004281c2280f401544107100407940780c2c1001c0c5880c8014040d4100e24180c01d003070340303c1d0383c610303001c20100740c1c44680e010f0795940b005405948141c4504042e402c10045c1a0810b410701e90010a441900544244d191603a0364480c0d624070060109006401034150340b091007040601d210f9185c0b40f072000d0030300100074640141d41d0b1186a2050000520b0b0030707100e541e48002c3d41c0b6000141c1d0040d000d8101e080c002c00d64 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 386129973 1250 386128723 386128733
    0x2070b0d18171c0207030c0b0c070b130606080f10110d0c02010c030c0908031e040503030c0a060c1407020d020a080d0c0b0f010521100c020a0b010e090c1c05010504 72
    0x3da000d0039040380564418040e9151148220390050354543c80b01402500303542c885520008001b02000c080003000c11800000902c0000401d110f451829030204110403281003c0003110480d41024490354811080529440000030b90144082d07084800419010305102d4031428500031007014032100c40c28451031340c0500d501900203203500f0b55107a804202d40880c10760100c0300c4220302c0c490803029801c10880d201c2e9082c1001c01040d0420b40e959041441c080d074070004245540d201c40354841c610742140e2500030030441c450194407009103861414034100300114200400900c111a0001d201d0114074a00200319191400300d03a00a01c0c41405450401c40810b10190910194aa08031034a4007154005802040c0002c8080e05941e0050009492032081c01d0380c0310303035016104045101c0341c40b408900d03402e004ca0034001c0030240e6031a0b90107000e02c01403a1030610300c00d41041e00300c4062807440e5001c101000d00009508d49004408a515510f00200c2c002300d02c00325170000501401c4c035403c001c20481840 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 386131223 1250 386129973 386129977
    0x1e1504111503010b0a080c120906090f06060618031006091a12060c0a090812071a0405030f0a030204030618150b010f0c1401060e150102070b0d1817 65
    0x5401c0c0c1d040318604110301101c03035882c0b100340a260360a402c180110b4003074a00c144000d59001090000241c0340070f9000410748010b2808840340e6125521140c200040302c0000e21151200b001c0c4040200b000e82081c1c2c00182050103000c840040b501d20007e0821900d40d0304101d140e0100c44461000c0004c81d40310401e0300080d01484000f050a00d40b00e075001071a500340060040794004030341d40502015103c4a80d958a00c0d8001c040c0705041140c0c500b03002c51024000d01c6618404440422400e6445009290190700c14010840c40b08a1100050400010400200440b00c105902c01c107241d42e180182d103c268000d00864001504140c581841d0022100741e002e0001d135401e010f040f0f01d4241d41202c021040c140c4044808003030001d4000890a06040e000300744498645106103501c03120042042d4010b42160172660004540030303100e8062100030080c2c070a100545900c00c0c80648011400e00c00c1a603030394443c51030180821035403242074010342141e40b02c80714030481d88010030110b0b0b103040040c1e0341519 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 386132473 1250 386131223 386131253
    0x21e07090c0504030c06030504170a0c03030b0f010e1318060c030b03060c0910090306091115040506030415150b030702060114300d03060e0a0e1e1504 66
    0x1a0345030050265000c2d000b0015901120b03405040d542c0c0103800d0550450203040044d008440218200c2c3c050301d4200c0c007030409861844c1295a481c03c1200322428014160f4034900407090288119920710f12150340d218060b0000041e056a0f0b46075404098001203004001201c800c252030b410005006003006015080782d124803506685c144030701c140320010162a10300a81c0c0c0ca65004c18208221102401d00c102c42c00384040460070130411303142d40d2f52920390645540f9441124000034200c000c003901d02e003c000041450911021035130401d130810000c40e1305444094070183c00701d52511282c210387c0750b194000410341440d003c694076105595100c0d925540e082602c0036400350040318008101c2c1e0309405001c1c054800d00502009208a070f0301100103000c56807031030071504441030108182082e0800c01032400d90b400c5580e00085c10340e15250020b03001000181240c6c1009041031b860501c1b4200008a80011a9559681100380320041d940e03940380024900d084600c0700c2d480d504000a2101d440340d030f0030b08 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 386133723 1250 386132473 386132489
    0xb091e10150b03040303110d061212030204050609010c061d0708070806060a06050309010f06080c0102010f180308250e0918190c030204090804150c1a0601021e07 71
    0x2a15541c81c80c80c1c0000c8505001e0094034440034000240400e00c02d802c40200c19040c45d011a14110300c400380d01d4103131034154004141014074072780710f14104900c0c0308549440449500c1d08505107400c141c0004c0040c03083c0e00c0c04604211002c410841444810f80c80b041c0110382645209101e00002040b1a0f1503050a104081c0c1038091104005000038020405a11070356004003824a1241403940a40d0300e0f41000e081510b1641d0f9071502c440d802451442048090550704000b0f083e0f5010800009007075801c54140340c2d20700ca0825410b4481501c05920f400115681818403500310341c0e51284012490004080b007401340581c440e0410604c81e040201c00f200703d9419200752042c3c0d41c07040002d885201401021501c1a4002c1480204543e098045406824410080840c01c283e481e0000b4054940300355003943e005030001000c01c041c0c8050150030040803d41e00b0f00000013501d41d10f843e00c010010b00784116003202e4140008000c1ea01c04d01c413114040d401039103442400000719480d1613a41d80c05000d00e0742 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 386134973 1250 386133723 386133731
    0x10b280305100909050304050411120901060807061407110d061401051008070c03050306040b0d050c0a062109020d02090a20070b191512150212040b091e10 68
    0x812030868084e90380c681d600107009624103850142031100405040f010b070044503c090150009041c0c83c0030944e8014540b050010031200d0420700b909003804803583c0518103010400c0400f021914294094640194004800000c00300e640b43c0812105010840e0091426140c0a103030121004c20403001c034180da0003901c84072504040c1350010354000405030354100100702d400b107100300001d20500045a0055002d0700100e494a00d01000c40c0c0b0003103222804076030070f4101c88050403c40c00e000700c100d070041c450b900c0c1407400050f590003200b4038800c44c455490341c4c071078446180da025501c2e6000514400d50b0b0103007000c1960f1400005900c0202501c141c1603600b11404a02c40e00b070820f11006488881e6080602440d80c1e40b12101c0c0c1000d01c1a0381e07440088036645a5041034008005411800300a0141c400301302c0d00441c5a10306458040c0c84031003400c2e042441404943c04a1208004980c0d021343e000705140d586840d4100d5041c54500711440e098044190b000762201c070040003150183c1e0340b082540c0184 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 386136223 1250 386134973 386134979
    0x405010605010e010203190e0307091b02071a0a03110d020903011b0905040b030703080c060702190f080315100e030c030604110105070606030b0112021c02010206010b28030510 77
    0x440c101c100520044c010792042c80400c2c204c584090005000b940c09040052a03e2122408a402e011840d444040c45656070640030403813000281d4162030303044592000e40001d07820300748103001101154030390b4024060045504902c0314001d506c0148d100380c0c5540540c0e100d007190484034010303501c4008090b009500744548500800c14802d11941400768070748400c2015170034031003408010078a407000a0350622800c40d001010070000c1d801030031900320090103002640380001010b46040040303400540500c0c41c548040307022070f80c80c1c3d44162000c2c2c0e02182c196601d03103a1701c2c58051000d94a01c46590300929041e8040703c1103030040054046008250207446518160900701510b410b800c0702c000d4015291140018100d61081d001001101e20070600040c42036100d40310b40d940b000d8244c201c00070003240448403070203500d0704180d0340030201140b03a2003840c019150350000351500c4042c81007101125010401d154698400420f1f041d801c010503041b640e0a01d0304500060140030161400036041c0303040103005c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 386137473 1250 386136223 386136227
    0x6030c02060609060d030201020f07080403140a0c0b0c01020d15060906170f040302191a0f1501050307050c06090a0605010b0a020307080f0c0a1104111303061d0a0b040501060501 78
    0x241c2c41040020002e02103956480180519001d0122045045550802810b0500186500641480d90003520901c0c0c846003180340511103101c1c03c1c1c01000c415030080d142c3c140081c400c0050360054030074200e00c998448640780140c0e07003e401000415943d560919104123000c0c0b51010982040321080da070f5225003250394250540e2484140441a08404070070300005082d604003580706601303d842481114189101d1820320a41c05101e0201152039400b100003108410020400e81c0b6000384401c0403081003418641c12401c54046c955040605020780400002c92071030044080e500c01c034441030240c1e03000e0b00d081c500407070311102444000caa040d4a45000800c00d21500002d41d03904040e55001549040c1e10b5031034030001a0464000494008810440c0480b007140c2070000c3c0c206188121041d5002000030320800041e00e8068240d01400303601400130901503181d16080b4011650800c4001840c19a080c100c3e24814107481440b0341c4512a203100c80041140c44003181e44540d003c4c00017005001d80b82c41c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 386138723 1250 386137473 386137483
    0x50303152e1e050d1104030b010801020c3a05040503030f03100f05010f030b06130303050d0f020a140702030109050d020a120509060319060302040614180103120f0302091906030c02 79
    0x51200089060010200c0d0404503440254a05c950240f103500703141c3c0d82c2d5a0148540000d0f040b0403110394010448180c0c400e0104040c603a2828951030318a00812000c600101a841c0341101c038207002101c00545d090340e4040c10884010b048041d061726622030000044447c650300c207403143e14900000a90004000c4000440d140581e00305a6400420544800c011400f0303000390400c050340260300300020781403403c00c904072000441c030a0700e9441d22008405020011192010255500d030b900401a0301c13809a80442c9499120403040442500d036401070000c6401001c0c07890005016106000301c804516800180c0300d40414402c11000c8414155034130111828054010300d1a00004140081100070140e000d8103107900e41c00110001d81e49540e0380028040c1ca00e160700c40340011071510340f00e0141d801d02c45c1d40c510740b2440210400c1621b524503603a48001350b14003e0301004000c6e07a40b02d05101d8a1081d011078a000341c0042c4413424503205140c40b6480c030032080c130440300800c1c0b50084c604122400429 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 386139973 1250 386138723 386138777
    0x1e0e011e05070b10050612040209070e0609010f03110703023d0f0b040f050711011a060705030c070b0405010305070810091d1506030f030403050303152e 67
    0x10780c40e4203107056983c1d041d421210190204c10f000f915a1808941c507100c6c440600003510949032848400e0803d0700600c103400c000581180200070031005803c1c51500d40b942241c000d24401c1c6444405002c2c213020480043c40000e20528600200040d14000e00d5800258101c06008080c0209180c00c00d055441410340c0d0444403029200640031780b0000d0903015a4000100b0080c0500c0c082614800030000408403140034181c19012603442c0d0a008035694441e4012120655010003040710403002c006640505800001082c441d140005450080210502c10340d10100070000440e001c4544440903840c01c0e4219024140c00a440c01c0d0004030158841d0042d1406060088151101c0ca820440407170b0160041212501c900c0e401a000c1c529409030821100306800c03e46650210b0780c0c2048020582056114965105194005e00003030000c108040200c03604100050301150050b090440402d000703201d42ea0448038480003212110b00e1039003607800f007003031059280c0e038944030311100b549180351074104c2d500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 386141223 1250 386139973 386139977
    0xe030303040b0109150b03070206100501030e0c0910120804090b0405130201113405030a050d03050a09021e030c0a180f020c0a080c120313121e0e011e 66
    0x80010013040e111a80203020030303520702240707051060b101d50601026a000351403880c0144d0013541008412846640400c02910003480d017413000c4003d4800c107e94544007043d4240c032a5000700003040800342230f4601840140140314517003c600c3c4042c00c1440b0b80360814469038544505251102000740b500d885200c4c8103108200542c400c03440c2640044800000744030002141d445812410900480b012440354a00000303500700c07401c10040d54641180395100340e03100d9030181e400300380130b64001180801e8110b80b400203860002003668900026001400c02001b000e9044060100c0d281c41c1060241404011103100354100c51801e000307841030040006162184245448284105c198500000c0d006180c0d10051000054100764103a01175506002001c4412281903000040030a05c025060005644443c07100f082e650851030100d01c48d0f030107a074000c00020a8102c049076242d0103680102055218200f01d6040f00f034685c00c9a0001400c17501408000e98049076511380110041044a421251922119 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 386142473 1250 386141223 386141243
    0x1b0803040602160c090c1103040f060f1707050304030e10050306280611100b092e0306021c1a122404030806040b01020a1704050a080a02010e03030304 66
    0x54951800035000350041100070f0803501000c8002c00c010380307000d8001c0c06500741d0001d64451030f4000a428994880482100781c0c205200c04c000184403900d0020464030642410940e2200b10201252101501c0300f00d01800b01c0744001b030011542c0c0c0a000385100b28860f41b00c00d255400303083d042100780c01c2e80d440b1490001c1c0d02080002e580c2e0400342551011050701d810124140d100707000608503100110340003040090100c981035a900a010004080d0210149004001801c000340101fa041540108080503581898241c0c0010902d060f5507103e0007600d52a181c840c45480385040406940084002101c540e40c2045000e500302280c4145540c030424143c1c01018407424109210b40e18132840130b640301c24020302c1c501b00300b40032000a00c1e80e0540d070390b49050841440c00307140150a102c00504128025442c120710a03205036000910300d94580d40040354040d001c083c42c201e096040c0308540100350004414100015008000580c20b410139100341c94103000400c051040c56541c0c00200ca02411001c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 386143723 1250 386142473 386142481
    0x240609030703120c0506042603150f06040306020a1e05090102191b0e041e050a03080c09040c02030d0f0203060603180304091d0c01020d0504060305250f1b0803 70
    0x341400880c04014105101c4c1200291179140c200b610454003564850b1640b440140c0303004222400621115441d0030071b13411402c012203004d10304400c1064030350180c1c07802c2118241c65075400095030004c56010a0556940c1c0041170018440da0781031007040300000100c0303940c0311194003480c00c1d120b01841c1a4024001c0c0e09488654200c900c861010588140b1507000620900f100c080300c920002c1c141d44000c0103a075003080c1c60070764094942080201d41d41c601d01007003140002c2c3c001c5400880130ba0989804081a1200808840c6da4400c0c8000a0fa10501c1c0200e4524110380100140010484881c420400000300c400c001050f4070007250303810343c0030608100042444c00c2c000000c07081d414030642107a041c00d448800c40b1003126441a001d91000043c81c546003800001005810a051000c0c8058039840070702c03460192080c0a6070141b0404d03da1204000b03400b805440c0c3c80d8629a00c3d110308000000014a4805800007100c0c1801000003004980340d0414030480442c5011804d9000403840e10310f0703031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 386144973 1250 386143723 386143733
    0x403031d161502033c04030c080304060807050309010608072c13021201321003030e0d0302120406111621060207020d050f0d021204030605060d050303240609030703 72
    0x840b2079052a4240105044071609241724244444526141002555580d003141450a10440f0325403180501e0380c8104400e010b4580c5c8803c3c0190400a00d0418580740d1b155030200d070340588126041600765210740c1d080003492080700d43d0710b0080302001e844540070341c00d040d400c1e452002800310b0780c0d045021004418440141070010725822414004000026050030b001141d084892128103207010341c15600d110703800d50080c0c0c030a000790041c030003542c0440c0591031903a018003840f8440501034858100082c50500b414000d00030070901c0f0500d503a845944588403030380501080e03810303604100d9510850700c0707003402e4415500d03803030042d41c118420019094205100d00d00c00105183d50458200342c080c8024001a1110300842c1c0f40144601d01804800642c000308904e8035400c0b0502c54115405040e4000007505403800320b074203994010702c01250a5407000e02007500c1c0d98171810700400f1407000000300404030450051180100001c46a6408546446020805103028100c24258550003218041001030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 386146223 1250 386144973 386145007
    0x110a050c060c0a051c030b060306090f0a0b0402120f0709080c0411040e090d121104090c260a051006050a08100b0f032a120403031d16150203 62
    0x1201001182e680040e65907801c5e04000d4610510000401080710501d2415018007403800e242505441150542c5003140c0060000900a01200070340f004000118124520ba504000c94002002e0810340d507464007001c0400034040d01300d880741450101d4001240840348141480021a0700800042071300b00b1075241000000d00d0303e4040d068500038100300014640072201300340f038407642c4240050100038031a14009003548002d010790b5100700740f4290000303505200c000c05403000e41e05804000582401203000a550341d5a207001080c2d0400d04e2100c1180b4100325600358140304400320001800380f81c6420301441054000c80c0a84c90104800b0302c2025000e40c800d40b1042d920030f0f804500445907a80e62440703c48154400c440c164403403000041006604000303003050600034180c1013840c48070340c0030504c0c4403402401144c82403140750b03920201050034980b20340c0044185480207000e50f0a004401820541d64818900848000344070800002804000b2200c82d0500b02c006600038502e400c0e14001c94001705 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 386147473 1250 386146223 386146237
    0xb06090108071401091203020313090e1b040207020a170c0f01080a1503080f070b01080c030a02060a12020d060806090d0912030c050304080f070b1309090f1401020a110a050c06 77
    0x1200d40000142d86c00ca40e1300200240c1d0003031700034640e5040c00e0090300c0d004000d82d07002251090f05210500741b00010020f428210b120b411540945031440c0340c000200070340318204000e94810211034020a81c02090301c0c051526083c10800c58624003080307024410021040013405012072032810025200b02c0183c2c214045205601480c10180c544942e20440d0700c0d048580c40600003100031500c1740400c058448064090716042c1c1c000c220441e03800c00080d58030145000001c0c0209004904a00e40710700800c1e080c400107001820075074403113102030348a2000b002c09100700e4107280708000100324000d002151000c110045a135540840509100020240f003071407140807010400e512001c1800b06006001801c040c0407400040c2001109400d4418503149040c0c01c03100903c03a04100402480002e00184012106069400f04200c1c0d031608000000b10a0141e0260004c0a0601071f4a1304420650003000000c1041d150070610200c001d41304c40d69001950760003010381d44000f40e581c500f031800c2c1d0064060 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 386148723 1250 386147473 386147477
    0x30f01110313050c0d1104180f0210051303050109030e040c0e09130204020304080a0311030112060b010c050a05070306060f120f051c020607020606100509090901061e030b06090108071401 82
    0x40000d0704005c5004500b54441c240c0365078242d8000d080140c0780500800e08104c1082c1c8415900911326211407910200c2818000d110b26030302c00311490040d000300c0c103544a140140c1d032103440040d502c4c00e03c0d502801103c0411000214007100c1d0311b00626140c0b10303140c0700c01c05079510300c1c0d0600310300b40c188003044e031015000110400d0001010001a5214002175100c0c5200d031009a485040310940501550b10040c0418200c040620051100000d01e001e0100415080000450305412280041c2d400002c3c40c54003801d20302440380006c00340301c80060710004581c03041104000940d9a030008a405807031038059254600b03007100040c800306c6c4206455041d010f0103502514444101c0140075034a002d000701400b000358112a041101440c1c05120030b5a100c80c050b81c0352401d0301000d0340c0080c807902c0f40c554003900c52501400410200407003580b000020344803003a000700100c2c0b83c000400038002c03058482151310500c088009942c0e410006105030489140340d005200e02401d200294506003a221b21041c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 386149973 1250 386148723 386148733
    0x10801090c0c02040b040b030304060e030f06010305030a030504020d171b06060604090f020d0216150219081f0602070e01080a051c032d14040209072708030405030f0111031305 77
    0x1440c0e2381c00d00040009010f80c1d240e24400600040503d4180900c01c02e0707007842c1e0342001d03004001050300071085940c004014580041e041d911803001a030114110308000d80241403540c3c000c00b07441e00120007841c105074290300c1c0304100314032500d51075502ca00441c0d9450300700c10140000c20100241c2e03003005108800a00303000d41007090213014a022a0058425401c40041d0ba14040091040440000c1242c007414642035140903030110034a1524045410340800b041881000220010251000100415540381100c400d155940c60000d58410990207807500c07030701005000080c40000080c107084e516900402500c03148001a0648480306030700241c3c1020301d0f4844202d18440f4503050b41c4100e100c0b602c600000700c400a02e4581c0c00c11910301c079002034501c2c00e16506200141c2e03200a5101d074880c2152900281d40444190400d03e241c1d001070080c41000b40384c6d100031a01403000701c00707002030710000c0c1c04591150900d002880e0a855040080b0204a0000c1000c9615810f0344d01c10210701c1401842207a03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 386151079 1106 386149973 386149991
    0x30b280b070218070e1e030a032a05160611060f060607021305010806070206040c06080703020c031c050619230307030f02010801090c0c02040b04 64
    0x8055040494244219500d03c1d29101a4110894040e03c05092000300030302866202c482e03140c407540452621500c01401c0303154010032540028000d150304e6001e41c0342996030038007200c444036407183c15002075444600910b00741c056080c4148018040c56074025410703d0352a09a03004171040000c0f4490480c226100000c10b80d8000562280780741841c0c5400c00081c04520404e04001e401003800c445101c05011a0b5106a04131003655003a5000355459600c2240c0341c07601210014200007c504c1e003408200d200302ea1140d40040981401413506003800e450b03602d0740d0003000c440d80201c0f100820720b1119082c1d5002d80c50700158107a40140a008150860f008a080c4a020303c1080107041c0d580e02d400d0350031603240c60b081580c0c0901a03410042d00c0c0c2c10661220454184140d010a100700c0000511084601c25414081042e507511408000a030b4204005040800840340c2c1c40341e01c0b86055 = true := by decide +kernel

theorem cover : BRFrame.Cov 385971223 386151079 := by
  have h0 := BRFrame.cov_init 385971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 385971223 ≤ n) (h2 : n < 386151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
