-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5288
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:22:28.952598+00:00
-- url     : https://prove2.me/submissions/ce57266c-726f-4529-937f-12bc384fe7e8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 950899280 ≤ n < 951079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 950900530 1250 950899280 950899303
    0x21b100e1501091a1309030206010911190c1e02090901050f0a02090607050f030a090929030c0a030b01290f090a12061d0a050c12250602010608 63
    0x181c1c50700e64a0320305100c01406131211021136040454083c4080e5a448200034a070b000e8a0080100720140316080207420240140c1c07140b0005410a0880100c3d1001c40b0104e07407070f8102c1c1c1c21484c040500f654000712040c0c140c41000500e40c041004250750b4001941d02c05031617941c03080300c2e03c5695695450a4600ba15001d41e040046070071381c28040ba1400900b600170309405500604524201032842d210646032a0407040501000c0d080010f03840d0410b40c1c00141800a4800701805220b240c1064025500400e0410f08801c00708982503050070310356506101c00e00700c00c42c0c020000f03411355480b41042680e0640a208803c0101550038100402c022190301c01c05602005101c46410314001c121000160780c00100481c0d40300f81050380205840608204080406005000c0000c100805440611000c40400c29082c40c59021072905000a44000780648104106884200e0035640c031402c41490100d0840901200401481000c194640101c500a080340c0040c1e009012031a624005a0b48a0001040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 950901780 1250 950900530 950900563
    0x51e090a050102190b0c120114270402010815040203090c012604021003060b12061e130f06091404051e070905071202070f0b090d0507060f021b100e 65
    0x403130b0b001003294400360941c07080e0b1880410f450b00c281103130a0407045074244c0040b42120a1103507001d40a0628072540d191440d4495480707018645848141c0642990042c4001c1c10031194600085034070305542a01e0203051000340c0150740782e0130034100c259180c0034107405031030008004030184101035007413100c070000d05845c0007000841c948540d001d07c4908241f10500505041e11003400060034001140200344100441c02005c10038180481040b100c1e03106041413290603202d0003001a003994890141c00f81d003c105200010b03a12818200620241030140c0c40811030b5460302c0e120840c00d04200c540c20348640c2c80381040c0d560011101c40428800004c0102603200c036480b500c4240b11000301a48003a030081903d0405503c2108680f0f2000281d9103c00f07412100f8101c8008120200469503005640009100011740541054080b008000c1c1c0603408014020030b40301c1800e55244901c2d80d044407c0300d1b191a102180210b0712003902580c950160118590191414400014014010a00c08143c000761074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 950903030 1250 950901780 950901823
    0x30405061b04180b030f0604030e010c11120a020406080a020a0e0f010501140904090c0e07080108060601201605030f190605041a0f010f050604050d12051e090a050102 73
    0x307200000c10f103800c080c003200701c81c3c0d02c2c040f1000c1d41d902041046404440d0400500043c03500b4a001440c00e052265154140b1040400c0d03a40003a10000c2019560002554142000300790590001d25210a0741c1c4080c0d040303841e01d18042055140485c2808101d030003030342e020541c42d603181c110207410502150b460303d105000301c006001c03030340c4200300300074060320f1905800382000700003000203084070711114045526059443e0200304140b41081c420f03070b001c5260b00303051201d5850704030142d4446500828942c100010000071080000c640c25000482c4426441240c080790400120389e40b00c40c280740915413091150320507101540d03c000468a101402100706881c1001050b903480010708800b810413a6081d00c041d44504454001c0401c4601c56020700e000b08141e540343c800c040e40c459100e43c00c0b890080310304110510003a1a81040d0420965104114080c002a4504100c0d170b14051895007a40c0620400a58440c0c043d1001c060408210115003003948a0382d94001680c0d60b41d00305109900545e40103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 950904280 1250 950903030 950903039
    0x101206140328050106140f06120103140703080c0706140304050a02010305060d02130507090f051507080c0a0303020405010e0907230432010c2f06070602030405061b04 73
    0x14142c2480b007010354807031080601a00c1d0b840b2401e5612540000ca104031841c2c0044e8854904810102100b00060300c07074900c1d080307a441c1070384044801400080c02182400143c401c455804000190085402540c0e161f201c00e4040e240540301c00340c1c0d114502c00200045003d86010500b441143c3c040c9901100501c017100b071030390054020b0100141602e9010302e2000504001d80c403501c003500d1210b0140c00c0005000d29102030050701040f41c64011203109800c180d028000c0b92904c1d0b14003100321100c03182c1c00c4e45403480da00d0120300e10322a900645005004628440c8101900b58019200b503c0090301d0301401c0100c880b042c800d40480440b819070008282d501c0004100320300700d904d03918103580142d58500c2c00303449180e007061500035500b02d140040e40700c0411514502c51240f21040802c0f091074480c01c0075440f510b8400085c081c142d0030600201010f00c04040e89580c1502c00c1d03c000c00c014145648a50250030510025002240c00f620701c0e00500c0c1c0020240000d02d180c1c0e00c4440c3c0b0b4504114240f5081 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 950905530 1250 950904280 950904313
    0xb0625020f0a3602070f0b0a060b0a0503040203031909091a10030c030f1505030f150c2b0507030e07060203040b07020402040302060f03011a03061f0c021012061403 72
    0x410900c1500442460307003000701c03d03a55000920060707000b078038042283d070366600c0e002c145800300510b4014458a842018456402200304846243c01c12785042c80e2241c91720b0000030300f5131181000000c8500400e03100c0c0c00d00c039a0000341c3d0758200c0b45107150400092900400a4003130300460b07d625640700c251401c101c1d402502070750046a07821740910380090301e1100f00c2e41c1c407000c031507140201070300c2001550310070030845ca400c200908458030244007410640c41c1c4d40c40e0880038104041c0c400071850002007074681c452a11003040182804200f20130264074901004054005c00e4103071403000c0041c2c1407141c04120a0b000080d44003c80d241d5500843c0b9192900c0303a10780403074204a208a07030050302000000f001da583d580107845020003800d41d01d9641d500d082c1d610302c00d100303030325580e019452030900c20080c1a0351017088100204032400104400d0b0680c51000b1a0f4043c51b851009502101d2042a85869680182a8441402000f0b0300308003051f1100c0c200307a845090741c2602641540082000c9424416 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 950906780 1250 950905530 950905589
    0xe041a130308070f110601240201090f0303020702191203080123010302030901020c120903061e010e06150a090303032004150e13050906060d0b07030b0625020f0a 71
    0x1ca407400d01800409641d07506d04101c001c0e07001e001024054400050807505801203180c414010b80000c001440981c2d40300c120b46143c84101909140e80400e0100035900d81600585031040c00d2582c0194480c2c44180800300c00030003000540005026900115078443e41c8810010340344520440042050764650044000c0c0d400205081040e540038400c10f10604030400c421800e0295810a9503107520700081498580130005024549640580d91400d14408540d1801415549181c1c2031100c15903503e4081540c1da00110b4103808044800a400300c41036a20010000a491203030b03a0034030504d003c9895802651201c0c00c0801950b000c00c000812800d0300c15228010140031900784a401d1a0103a00010183c0f103a14840b442e020f81c40c0c1007041643c003000c0c40309075070065040703400a01c4003610ba21074601041c002859003041c103a484405100c03a036104e2040d910383e409075a0ba2a80c0400c0f000310860f6000e124160100d004940c0c0f01c203150443c1c6044164401030b9079902152154414003c20000f01c0c40782e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 950908030 1250 950906780 950906807
    0x102061b160c08120901120c05040522050703020c030d020c070807060801030c080102031023060c011d0a02030c1e13020a020d020c031f02040e041a13030807 69
    0x5100700034000000d2110300e1805a0079006142480715203140140c0207081c006094284d40c1c440000b0403a50391540e07088041900c11000e0284c0000d900c04113072074140c1781840b403a081564401d030744040b1440d400d039100c07100c0d0b02191008501803041e03071180d043c2542680a007421898550b0414050b4814456240d4060b200c183c0407182122074582e034030700a4505128940d040315000400500042c0240102005110010804035000b1451483c245441d00001684c41c001c40c51329040c1d01412012031200210845040d00e801001150b890b14007450b0f0900a2098005d10803210003014035110400f000810072815441d0042c014000c0440c801042060110500c2e04411110381d003084154860344946510304000452040018ac0c0e684003000b02078a400c00244020085611280510b00f190f240440c1c0d00c0c001910f080000358840f58880502030103030140d6000752455040c008104800e004c3d41e4111881d15441d6030500d200142c84100803155081a20741001d07010801a4005c42c09040c4a44020000103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 950909280 1250 950908030 950908081
    0x105070204090b013503191e0e010e01030501030f06020708070b13210903170f1c111201181b02010911040218040b062520010206 57
    0x841c0b00c1d07444181044007a00704060714690340186081c0044900111800c200d445840044600422050385603a80f007003e03007100c442c14451007a00420390040d41c1c050302c00a440000f526145403003100c02440c082c030100030680000d50403002c00809500038810141a2504481c07640e010400e00e4440502039070140b401100c1c0910300708071540200d00049070150140000c0781501061031000d0a194491a00d00700c0d030a11040901e000800d04243c11035011000c403940484e6030810311240161651060080503003807240d40400188442c6181e0301c00c0c14280e10885024001c100042442200304114000e00d4030b440303400300a20004ac4050385200c4c2d5480c1158009080120301c12540c0402c1d00464101c0e40c0014000d07139151102002005008030602404400a82c0e045007042c0320507118081c1000c085214900540c1d8441c0d1006940c0c0700c034400c0b039034200482c4044040c440c02800d008418840c41800039504103900c0341e01d495040a840c00c0a11010505074001e004980700c40e00703041c5040e841c1080345070700c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 950910530 1250 950909280 950909291
    0x20a0503011e0f0f0e0115020a020d0203190f0b0c0a05071511070f020906120c0103090812040b0a0609110a3603020f0d030c03140421031206140105070204 68
    0x1c01d10000340100c044c10310440c040030f070945062503015520383c2c181c01111000000685600c4015800901c080070103070100d40320f200101c203038000301341814450003a000c51105002c1c00b46041c4041480500365240c41011f40c8004c540d10031200030f84900524100c0d9001540402c011404a41c4040f50b88210a013104000603840071108405010755014400448005251711041029850078506056100806039260b0000a00e1400000c1e190b0401c3d00c010750500d81d481030f290082c04000c2c425204c01702c0710030120007a02e09041c10040501d007000c95550f00d600b07080c0040032902500c03c1c0203658240d02c1035400711b03082c01070320071054407085080c80c44805024145182c0011482c0703e0301084074041d07040d050000c4440d0540c01800001104100528040c0e640703040d022000a82c000350f000380c0190180f800c0c01c07038504004c3c40007030340788203582c080c461a440c0101c4070444103034070b050300c105524404d80b00d80d2071000c013070540c41c4141d030150700c04d9100d0400241840c480d44e5014800401e14584000c000042 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 950911780 1250 950910530 950910539
    0x120224040504020a09081006051c05100510030b160503160216140406170a0201140f0409052203080613060e1e100e010b070206040306091113020a0503011e 68
    0x301c1e002203040d040000d5203170204201c4000e0a001f4401ca80540c50420321005042c8400700b14000154201c080103a40100a0901400000c0c4445555036180ca00e00b0312250800d07800c1c452101044d40419180400b00c1004502c0d0541c40391404501400030b0389445085076500318600c2c0d04040f40030103810039402001482c0c0000350300000c0303180103070902606100f00414680c040c0700807600c194003d120f03c00d034401803403104000700040c94038426509280440765240e0171880b00d55031b030281c880400c44410021174041025103041c0c22007446a43e11818841c1d8031800002190b40c00d81d10395002402290022000c80c0d0a4144044101c41c1030070700c800c1c00f06189a035800080208102140d4424581ca192603e9048089000c3c0d07141d42c102c100f1800e490b0100781030180302840c851040c81600340d10f90000a1200864550b54140c900a5402c42006c20640909041c10f44c6800d140070550b6104501825400709460598420b4803080308440d940c8600b10f030b080003035100031540720a101da080f582c0c220f1b20015 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 950913030 1250 950911780 950911789
    0x7150c0c050d0c05010e07030f02240d020a020c0d02010806010305061f27050a0618030f030806090609011a16052d01020a052203080f090108011202240405 68
    0xb9440c4065958409011141d00b4401c0c00c540c4100508921b90300800001c0000c0f82641c42914400c0303404441c404030144038004201e00401e45080d013241e00400c003142d410081c5110398041e040e440c08940035280c1c2070440104228118064610003400715055001055071544a50f0086501c13003c0540b00001001c0c1884205115000000b48070000410401245000c80c428000c5441e80d8010441d141e0909030424000400044140c01070000300082d4120342c0303250f1800305640c24000c41c0c20240c00c02c120001c50a0090080398125441400361720000042040750030311440083c103c81007180310524880700300440031039940c02a000c0d0380b0b2a10454405a0210f4010711041ca04510030700c0d00c200c014400c1442c0381c40805034400440c005030740305001a00744d4581001c2200d00a4440c4200041161780385561004024a0303038002802c59440811415050340c4854000c080b1404241c82d0861507a036904400000f6100340342d802900071440402858500d51060020401a896070311a141825124000b26 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 950914280 1250 950913030 950913043
    0x130f0b13170406090b160b0a020f0a0c0b0f0c0301171f0603020111011e240f06031802100305070c170702040509030a0905060d060803040b120106020307150c0c05 71
    0x1e062008000340c20004690805203000c024850812118201011403400010310300c01039502802c0c01100500082031551213074110f070354110040b0505500e0321007805006290080724034088580b102c3e6840810510981c040e202c074807c0000e100028696030a1000040c0718095240000e00980316040e1200581000000d580e07006444003071000501c54510b000040c101d036120036041580742d1600d05041042700c0101c0300c003125900960170200f8132082440008610510b0144281802503c100000c200300004aa441d0111055580c061004920704410b030640901c91440080d4801c9a040482e10b4080c0250002a401905070600075040103070350315861860000c01d04081001040007030984210300e880d10401c0d4100485000850070421600e40c050661051802614030920300461a0b15018844d50007a001800540c0700303803603c81d0742d0741c605890580c00200c4402c80d42204c0d180081a10341c4000300f6502c0564109900c1140b0481040f4044002d005000d0f500003084510424000840c0041000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 950915530 1250 950914280 950914313
    0x1305040603060b090f09250e0405060a0c171311030a03021c0507030804030c0206040f08060402130b060f0c031308100e0d050405091504180b130f0b13 66
    0x41006101d15040018401c0005e14944002008100748555040c0001e20300080c600400c000d0000120310301040e0025480c554480040c1400c00800c00c41040030101c0d2250290b1129203060000c0300c080b090540d103915a002010071510380304000075060304050400e05220a01500c0c01441254007540442c1c106180b40300241c0160380a141da500249070303210303151481c140185c50000e0130804184c0e00101000d2000d8800340400c044c103005003041d0340d0307180220740090003180400075070241c0d04c5880a49668084900340d22442c42d044004614a2060150103400c0d00000c25851400b550144844803030741140301e226203944818840c0c80740d0000007240c0c00000d46881802409610036041041061302c4d41c052140c1c280e80c0107414040e04290700842a2003c0c0c2d0412900e004142c0d41e0361069494038000001002d80c003e0600b00c00b130990001580100100901624141c00145c0c0c4501804450805a40c00144661041c10340da0011440e0b401030160003c0407003802c890800002e445000440c000d0048 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 950916780 1250 950915530 950915543
    0x51002060106080f0112060c1e030e0f01020408030f1c020f040302040f0608060628060801180c0203090f0102010f093e04050402121f06080c0d081305040603 69
    0x18000c254100e61102c0c0c2c41407211541300503541c10304c214000c58041d50748004086503250800040c140703000e080900c100c1001c1c035800d44580326000c1c40090141450402c3c00302c9500445503484455030040c0200c5083da050301c0011450401c01420340d513665407081490150a00e8030a1064400301c0884c00240704444540f8001074846007907004000072600b05200842c280c52500340104901140856416030151044890244602003800100c5d003402006030080c04448810002145c503541140c2c2641c180c41d0565a0350a260808002d400300300c404140b806405a8800c4c003c100c5d161806000c040c204c03034410b100100e181c000b108600340c1075a0f156078044500500c0c4e503c2890300801c040c7c62041c40c1d8000310354448501c1000c0c8100c456000324038240c0c14000e0751100c1c00070741075485054000172900011822107001c0c9182080c03903d007032011268a440018200080013548010005031003170481d1004224854001c1641d4447c0203d9000004a00c500c1142400014143d5990321a60004600a29 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 950918030 1250 950916780 950916793
    0x120d0806010806030102070b040303180b09010f0c111207080f130311100806120307020603011203020d110309010804030909020d09020306130309030809010e0d051b0319030302090a051002 82
    0xa00142c0389903001420369029030320602a071008140c0318400e0540154060900086004000074201c024043c6944050031413401034041c007940100550080c0d4129030300010801c00c1c4d11509504032071030411030014241d035901400d4941e00546801000300300c902d206200e103d01d1b002c0c00d40d0507150603410401c12601041507070074082081c41100c0c02d03e030000b01c0045a00c25805114650041c00e00600504550f01441845402050542040048a109940050200d912136941c1d8404081c440c001c550200c006008030745880082500445040780440c1208018604224400c2c0044032404001441601004100790000481042c06d10041a000c540b205002c24054840e005240c500100508070007082c0e00714800a0001c40c0d1f01501c482c095a0344031004640e50141d000048800c242c55038101d07940301c001202c0d000304115000a00c01006030344022407040d1511014201901c6e1002d02004501038101c800c448070000342302c1c0d402844040401400d0759542ea460b079000c2001d0030b40c6001d80300c007d03a100d003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 950919280 1250 950918030 950918041
    0xb090411030607080919020a0305030301080a1704030b13151b0320030612010b10051b0703150b0a0e010815130305040303210e070603060e040c14120d08 67
    0x501c54260f1000355070a0101c95428601c0390039607501c00604480301551400c4480b18119030ba1145c1d401c0c001e41d0003074101c940720b50b15030000f40d4680c51095003c90300341d49802d00e070381da80c0c200358401e07102140d810012780d51440d0303680b003a0440320b401045402c9070081c0d5000b601c036411040920450520810b04c03822200d588803c90030280c1103490b0b8044464136401c1046c4088003624013401142d1748207102b0f481210b03035504008038081c0134110b2941c0550b404940c0e4918a00e40990110107804652900e1080754824940d4507581c036180ca90724040a8039120007014803041c0e01d040354110800c10480030708400fa00d1642c4204118241d0f0003a0031940b11604080c6200118180c50712100c1d0f00301840c82d8880c8035005442d54080c1243c8201e120040600c0343d91010120f01c46003003110b85041c1c1d03281d03000c20f2001407412078415854025038002e00d0042803a1010100b40b20440700e03003461003507500981411801c0d081c0203642c05030b22281030f0425480080c00000c0c00e101c28090202d015040010744540e802030911 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 950920530 1250 950919280 950919283
    0x501140106020f071212021e030a0f08090606090612010e030306101d04090816120906022125031106060d050a03111006171b060415030b09041103 64
    0xa03031283c3d51944c1e00602c010b000100078801d60721082580035802c80000f10340c00a0580c03c160000491400c6540c00c1c0c501582c1820020000340040141a40c807480c40c00c0e2100d90070349200710207807004015544000d000803254200f0500d80f640020000f00b10018401289080030309540701403141101c1a0004403d00440d41400c0d07011400f01c180605080c2a15860b5030001103000b040c401c00244210b4565110100b884146022a403412022153f480f208030035600704410b454407404504000949890b0380001c41e144045564480d004080080d42d01500b405054800141c01c4010401c0d020b011604460440343d461940781c0c40940e01c40c0d2200b411078444404803506210004002902074004004404001400072600780c4040750305040090601c005450381600e0040c243c1c00c9511450326100e0080382a5840d40d103010313103442450b4120341c2c40c0f18041c0020320145c1500017031182c10000c00c0c402402940c0340b100d5011741c0c424283c600010445d0000001686000c0140d03411740c0c00c40d0f40101043e406050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 950921780 1250 950920530 950920543
    0x1110c1f0504150e1c050d0b0a0312030b04020702090c03040201020d0207051c0606050a1805071407030c031808210a1e0302071a160806131a09090105010e01060f0804020402090409050114010602 85
    0x1003c0300d14038009440c503154401680441ea1114040cd9541c10160301c80380d440d80d050382e81160f00a0101042031812201151040c0d10580b030583c050f07c2100704240381907100058680581f030004d04034104140c6149510f9140e02c2c1183e00c03c41d82d8039115000400c0c95150030078624001c0c40100c10b4074034031840342020032040b26400b800e00c104211501500300612141102141d2180340d052030300d8880d070603641c101103440c2d0501c461300c2c40c12100101da001031130880000704080031a1a4070300072166420b6082c0d4002562290411f200c3c0450f040403120741042c014010200c400d0450782c01d0151030a451559a1a01e0402c082602e00b01d1513015410300a098200c030104401e030601c2401d2600e180c2c203010300000c80c956400c0f0b203151105615942d45da0300c561444036003c00d40d0f080c040c0c1552190304103942d80c140600002d0017083c1702c400703504e4000030704248555401d590202950329601c4060711544c0a10000e94804901c603030f0840d031614114800908244102c845c0290354400c088025414031400074103001c0d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 950923030 1250 950921780 950921801
    0x5010f0915060308040b0f09090c2a121b01061d0a09240204030b090102070203241f1517060105180d0501110c1f0504150e1c050d 57
    0x1840c0400500000703002d1030407101981c1c030046141f074807501007829208031842010101500000c8a20502c80c0c0d034109100a002c1c60402083c010b40789640c400f51246415a544e8529190381e44009246c0c14886103c40c02800030410240c02007684070f189080682c02e4071191790200d810140051521241a01c109808a070401400710b4148030701035081d00c481d50203081c03081e400c02c0c182c002c080340282800d200794115001142d0100c140c4145e440d10b0611203000350007800041c0d00a015200c024061580340d04e40c05107203090300303407041f030382e103031034044900001e8200b4a11f00c070f0b02d4034044800031801e04501181d94141ea031003a07644541c424078160b001d04c0100400b0f0b080c903051100c10700000070703181408661221400382c144c414030002201030828a0241800c0100e030006018000740759241c100300170a1900240b620340800d00020034800d425801103070030495010307005503252040416100d4139600f101e14101c400e401269052900440440341c805211402c0102248002030f40361707102a042e0080c07507030a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 950924280 1250 950923030 950923073
    0x20315060d14010e010c050c1011180307050d0803100e070207031106090429030607081305070906090e0c120309130e060411010e240703050705010f09 66
    0x60400030003040c880c584030040240240d4494403849001602544200f200015610082c84840c6110303201034a1a403023000341c460280070300f541c440c50000b018042c0031107141a0190785440d10f00303076090011216404003019640340c00740c0000040c041e550129040d030740c0c0d4041c28040b603603800d20045458a01006a1100c0c841c00410001c001c3c2454000c10208101c030b4000122003144001a80052141d10075401c0b00c5a000d4031780a40c00200100800411400031a4224009401d0700310300c0806581c2c40c404c40b0b0b5900010b10000014150100628050008078414000c6600d0b060315964003205640c5039802c80c0344429580c050030310781a0400c1000c0d1100b00d80c15182010302030800104140c803131081e4a0000d02501ca41d0500710110413099008418170f00c030702e60070b541c0a810071389802e030014020903400c81e00061140c0c4182c0701501d400f0245c010700c02061034006000032081e2880c0d6006401c03082d403e034103000b01441088042842130240500103a0078080c001440c1641c0c2c5412413400b004840d998100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 950925530 1250 950924280 950924323
    0xc0305151e010e0601051c1803090e0c04150c1406090c0a0b2b0e010c140909010323070f15050307080f0a0b030d090f08031c09020a210203 61
    0x100c1d5207840c0307411030f00a01c6c0440e9189004c1029002c0003200c000280d20302854483c00c25040140912030f800b40c54800d5036041c0c1ca4960b140078400f00140103403800080308400300010410495896404d80690710141031484800e09a03031100c0000542e008802010741d0804020844111000e01c05401548412200000681d0900c031118005010b600114000c14840812420080708100540c0e100c3e21001041848001c1201d24a240a802c2003030101d07000c00c4207100c0c0c00e00d5a100c50b000390740c0b5060380074218140e103a00e9910307000443c010a26625074005500e0401c02e043c043c00740903a8019144644c04030610600c0e1403014204101c00e07031114010003c040c820301400e44d13403101c1c01503003011407040c1c0d401c900d8a0319041d010003000290809135042c8a1680c401490581041c410703001c0315445007940f0342d81e580d0742200c40d0302c0344a8403290b800c00f0700000d00e2131060f012155100e21102400640801d0303026481c0c1900200004014844102030700360302c050030301145020080298a10318810000c560b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 950926780 1250 950925530 950925539
    0x1d0108060907061709070302030604050313380d0f140c09101115151201020406171807081c05120f04060e070f080c27040c0305151e01 59
    0x310011031034000b04070f200c4c80c80400c03070140041011001641e00103055500906051400b00d0340c0f94810100c5015003008903400040c1000c03610f00500c145170102078202c07880b500242c401811580411000c440500040c015100070080764428002140303058080020100d018550b1441081e0000340f03a04904441004080900d4a414800095030b41c11410144400d540144090707003803408002070413501c05032200422003031100f14200c04601c0c00c41601c140030218100d02d1707940c1c241d2040f030240402060341041d80408040a01d100f055101511800c030f0552110b603d4510f07418011203900624841d40000c0031142d008440352921258108a030034403034544101e03582130030030301d180c020f04020070103002800050620000e5040031100d0201103094070b110300c3c0c454004182e01c44050040c4004c42c03003520103003522824915212131182d0025803412000014465245100d070340300400458443ea800a030010014030100040e11304504400120192443c00c188240c0000c4c4c0b44150141c42c06e9a000010013 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 950928030 1250 950926780 950926787
    0x806010506070b0411030a030509044b06030c03030210150902030705090307030615091a040207230304210b010e0a0204030f0b090105240103151d010806090706 70
    0xb401182e00040104403540c460400b40f002441609146070076000d07041d43c241c04c060740200106025035007103400300031500a083c02005251001407181ca40c0014079440047c600348091030940c080110080c080d00481e87c0b1a1450b4180e4003039510407102c10000000c1401059014008510300d11940c0030701300082010842511111b20f6184a000100c1c1d0740000810302c400d100b00102c2d01c4560024007210181c40e50f0b85445c0c0c3c014a8442d018180c0303800540008142c5004500440c41080c62840f00580e01030507030000c0000030751058001f20307001241916041145002e100040f60045140d002440d100d030b1814031820180607840040700c1c0c80b400c1c036408480020b061050850305503180c485072030205691304c4640c20b0080c03041d904080c0c1107011940801d010844404401c5214400c0b040c000c1c07003507031181100136441c0311480f440c001c0080c03144c9000c84603a500c01d40c004080106218181014250340c1c0e286024010312450a420282942c400148581c2d141040b085030803426401c01400c246141c104000c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 950929280 1250 950928030 950928037
    0xe0c0c03090d08121504061401090512030c0628140f06011211192a051f0b0f010207080a030c050f1911090403050913060923010806010506 61
    0x42c1c865102c40e00102c091040304800d582c4103410780141400c0c1400d2003030084414114000703d1030f200f0742c140f40010845044901032304a81140c107031104290141800104518242d003a800345100d80300501240000b00e00422034603002c0c10910790301442104011104440b42d41c10110543c0d00035003004040c040146100b0700071340e84901144502d40746030700c80b0310048030005105140c9102c2c203410440407041650f1610000c0400f09141d04100c51000d408101c151200c556552140c5404000d1041c209603003da02c140f50f00306903118100341c038940f040c042c00721508080e00c06064804d680c0c4e14850209942040d500f0810080424001402c840b441c1c003002d10b0740e0302d044800c02800c11141083d52002c001003088940d65489c41403081d01ca0581040001d4824443c5205094510048002990409003007000740302d80200d030556201440c100004050041b1010410b0303515141658440c4009044001c600c80c840c00040d88401d5801050f440b101216400d1806800c040c40540021004218607078944d000c9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 950930530 1250 950929280 950929297
    0x40c080d0c03080a061a0c0c0f0306071202090a0f051314060f0d020d110a0e010501051204030c0209150114091e13050703051e0609070809010b06040b03010e0c0c03 72
    0x40f4042e40d2500100c03000360440c0d500051302c000f00f4052011040150001402d4088440c104640100c5102001c000314114038503503640e01a0099804a15124410300c2c00c80f00f414004800585404180c2000c01d4a94002ea402064a040301410038000d62038100b66200a2542890302403000540c03801ca001ca0130f11024066900c0756090061101c0716071103030302c400c1d940940c0003011034a0455190506034aa690f07a41078091098048400c040707480340803055210f044c1e40e0183e5402d0b00304070307000099009140000c0e000b6024000e2903070745480140d90b03c0301d40f1803246044040c5105007100200000d0207450825a20b400d150000b401198902d40b50380080c550412200d2041c0c03000c00e403401000c42c1440c140c00807041c141500305800c000c82142c15400c003600607034080220822031250345040c2c20a07100e013511150b52292500010035040c5104220140d00081d540000007001a16840000c0b8903038095802030740b8a20001c0010000e8480c0b00c110154007485014200789812001001c0c0760300e91007400c81c1d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 950931780 1250 950930530 950930537
    0xc0d020f1318060e0f0708070c0c0b0c060c04060516030e03030c10050903040e0c0a172802070b04111306060201090b01150f0f170405010b032a060702030a1a040c080d0c03 75
    0x2c0960f4401c50101c000c152b000100e040080303484010410701944900030f400c48a104100120340440c00c250201d50072101c4d9980c941e41850400605a0342d01440300105070104140300d54a0700299a0034401480c000d40ca070001412003801080248080e954020055921034006202c1007204044001407032340d012000209141d62040c0c41c0c0419205034003444070b001d801e010520200024811001040340c50320600c0041c1c030032411040402113082e846078900c01060912204042800980311540c2842820402001603215003100c0030074500b11041030f400000103031f460303258020500c1b00340d4150030301500084002034801c503081c002c060310758105405510104a01c40c40084002803041c0b4404200c40402800b01d002c6003070600b0014040e0401c07450403440b134052040702000281030810b00f06800340208203018052141030301004040d400854090340c0600940b94108001b6464484030314402e4402c5100055900b0203080565450302da40e0401d600580c401021282c0c02508101c4440c4842d50625 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 950933030 1250 950931780 950931797
    0x80d03111303050601061404260a02150a180515130302090f0a1515030b01140d050f0708061f0c0b040819080c0d020f1318060e0f07 58
    0x40d4090300c2849216181d201001c0380210100401c5004504c29040322407a5407003600d003034650003075100d0f14466441703850a4600c400031249006002c000450314031030300800507034211304c10f59000b00b0207015455031107003076540b800102c00b030000340c100b801801c880071010380803251641080d000c0361a04c80000c40a62402c031010645e4048510440e0f0f1704400f441d809094107185080115000e11038420560b4a207100c24101424112070310700284100341260500b0241d044401104601507005000e945071343ca040080d42090b10240aa1070402800343c00b40f00b07000000c161610100e24010100e002e0084820410f250003445540e0b65080720b5032038511840c40020705140496032058640002034003008101c181c4c00e01c100401e002184000d4a0020402a82241da04c40c052108992041c8101d49241c3d581105001a003801c0b08243d015205500d1081443c40ca081d00c00061400e0140140e0b09c44c0c010188080c0301c80c0c03849500c5000f840020303c90f01e400f226440c00d00c0c95060002742c900a00e55020001c502 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 950934280 1250 950933030 950933051
    0x20090303181c030e040e19030e12070e0403090819021306170c0f0a03050709090503090604090b011b021e01020106210b0f07020a080310150203030a0605010801080d03 73
    0x400603400e0080c8110420260b40348914018010002e140c0103103200301d2402481b03001c3c201d80455041e07816000881c03c5040f401e86917800750b4107203140c440442e8200305044040705084408110000190020b985001c0783d501e018500149900c1d85a000201c1c203420a007012910280d03056001c2885541c122000740d40302412500200041c1850382c050000d08440300d90300480034034042031a01740c01c501a6851020004844244008a282444000c0444c0d1001c01c0030003603800603a005410f41445002a030b40b61050942c001802a00250458409959101403030746c219070b0012030b464001c0801b1403e1002e480c00036000503004070080300040c00300e5201213041a076a0ba200b9813198002e03144000d6000307419001074403810141c41c414002240c00c4040c80002c1441602c03102d000c03034070030070302a401803551005070749c1d0b20390341d9410252880c096000648004582000b41c503000c00c203d28802c2e40215100e2604030101000c4c1c680340e07802103052026800050052000105041100801c4ca003030203e40404038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 950935530 1250 950934280 950934289
    0xa082a0a030605040303050901020f07060e010219051b120d02070201030e10060f120b060d141203090606040902150a050d0905150a0212060906061209012009030318 72
    0x11061000e9008804038008810041640e02c12401103001c1d40c3c081000382e891426035805c0b8815492400d0b6a01d80602c4004006030340d81c1c0240c4814900307407002500b0000300c210700b1443c180084011402080c00420b81c00d140c83d001040303040c461403000c0000e0000b850404002c00c0f49100c1d41c510780c02d5013900018004296406030700400151440300040360300201e022601c1c00d008040070b01844802015802c0c0018031900845001c46070f598000d080024141c403031604100c0907071109142140c0007845c841c0000866078060040d800303116031080c0055940e1604c21a0182400c0c07005105620541c9083e40440250f10b4050300309000b034403255140381d903c050b641c005903000d01450300108000727420025140c0c10814013054451012803000103010843e280d000f1030509030301548800d00c402d5100758001440700c0ca008041e00e40c002c0e101600d40707172500881803c0034070b14503400c80ba039960907074441084036880304106201d10080c42200852900b00341400b8000790305c1e8401d0011601c00340e4915010001c581c1d48 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 950936780 1250 950935530 950935603
    0x2102a0204090b0f1e0609010509041a07050307090e1b03070e030f0114010605120c0a12240501092702042304140f0622090614060a08 59
    0x821059003c1c6a00d000c2421400913035040311a1205c10200402200045040c6100c2c030780030303020007840700171a03a01300001d01480800040c0259a00800303e6100d4600c0701c10f40003014001c0c603803036549503601e16001d50041c2c45480158420044441c3e028200308000004540d400e200f80050301d605070b560740b6428801c0f0b034070b48091007400e5414061000380c4401c007e4154010802c12000c44c000c0d400903a6200d1050301c0754010704004503038170039816002442c00100d00c402804883c80c141451f0710205004540300c4100c82940881c41744021740512852900e10f1050030201c020082443e2a1200c58100f1400b00c0a1a003103507244d000c00003000b9480c1d2220560303901507030b000d4020459076001c4410051100c008090760754448600451501c0405000c038440c3c040f50b42d00c035441c8c8494400e900d0320342c8024132110740740c14048008004a00204401d0711121801100200b48c022000071614042d503130306000c000203003c2c0403d0321583d00c22004100f5684080740c0000701c0d0b0004101a6440c00a045990281c5c3e070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 950938030 1250 950936780 950936783
    0x307030506010216180c02010c05040b070f0c06030b040b060f0d0203062b120f0e0118170c030c04051e070c02030303010b1909051e0d0204060602010902102a020409 72
    0x5071800114500444001071094007001c041d05006009540f50141d082782c80004403500012010081030010f800030340c00808020b84a001358460005040e10b03114040001c5401020000741c50301c0070240d16142c1801170322248402119014504441180380b030f540c2e0b00c145031003400c0c501c6d0044006200350f40d800341c0c081c11b00e0303040c0014000540f502881600010440841c111042000300c00b205165603c03070810412815095220b40d0131040740b43c3c00554403820b15010059a222900f207020031401d04a405000c4880d18120040420381d0807034007014244084134503c6400b4074075080070880d0075001c4c2c0d00b88011407000000c10680c04d85406004070b4039050203000c0a905803000100004600905600034145849040e0390741c0c82c1803809410886941e4031901c40c150b48854074030380c0c0c002000030150241d0851a00102290110342403640403030180c61180e4044000750351b54443d0b50046d07040025840c42411071501e400c8030070b0003640d007811000ca0400a590740c0108460802a811034990360320072802c06 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 950939280 1250 950938030 950938063
    0x4090b0901231f0e030601090506011224030507061428090803160c060f0f110f07090c0201150e0f04020607051501080f1b120a0c0f0302090f01080303070305060102 72
    0x943c4002c101a2040c2a40b02c40d41d40284185000010401d5252184500401c8160744011814085207982c2c0064005603120a0048011342031240508000d110884c0003944502c010b45052440e00d907000d449814410403a00010070b0411402d100d070141e02e1100c1e804907245443d40c26400588103022201170045810078103080c0f100280340e28814218262510102d4491403800311010b807a65421280003a09039402004070b0440076031078402c0340c0920b00d0202000032071021140c0c13202c0324208035490314110398000c111a564409050500650a009280540740881e941070aa03d103401404881c0200081c502c0f07901c4518003011500b11b42d1680d04443c0140d0300b1400715039035059845082c03903003005c0038411404148034000001b1034400c07001c00c1c0a0001100d4000d10148a59680203101000307120b44401c45a0307000310f03a41100081c0b030520409019140c450004402503096206101280c1c2002c0e080108001d241c00c01001440340010490740c0c40400c40c0703404125901d980005034a0301c0799900340003628 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 950940530 1250 950939280 950939329
    0x1f0b0d020c1204081009140d1d0901180917040305060708180c0d02030a020a2301090f051003060315020d1112041b0801020d0204090b090123 62
    0x425485402424018000c00203603140100180c04250540c4501d1040001c20b401c243d545000c030010951000181074019903901c0f0100190562071820302680d03455040100d4050041c000c4400000c60848010f00401e440024031541000d9561100b80702201602d000642c0382c800e4441001854a000c040c030a003070f0681310351502c0d240d140041e25008125207841c00100044000340c2e140f480303c0c140d00d030701c5500310700644501d00c00c1c2d6080c0007040c844e001040c1d03010700ca0b045804d80181c44401c0244020003500d0a8044500108480c980d0605840b90b42d8a041090780d680504c440000c240c40300e000c1b5103003140c400c011a1032041055024003080d6001900c2001c24081c2461800d08603001000304c1c0d248040d04000d100f406804076403550040b170003981c158041600c00140051141b0403a00a0100d40101803003290341d440411600b03a034002d486400341c0b141c0204080040c003003107000e03500000a045980d0141581024aa102d003104004c0d0004052080d88036021441d4441e0b2400c19806000c0303515004a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 950941780 1250 950940530 950940547
    0xb07060b0112140a020a210506030f070501020d03021c060b03060307320d0b040302160608070e0907121514120307080912061f15081f0b 60
    0x5000842a9078085052905003a00e901c01c02d20460070082007940250800c0d48503500c981c0002d4000c402d040041c4802c0c050104800e50400c040b03075440a851100206583c68403100b8941400b201c8075071945a035100d148240503a03a008210400c03101624034006860b001c9030901000c40c540c2032800d450180c0e140c0500441c010388904001c61140710203804489810b591400d031851245150780110107000034081c00344298a00e00203d5903102d000c020031000712015103803642060740d5406d40e0b040380580d10101340501c40b0201d142d1154010013041c1000041403500710005031414992324510380c4614200700010781843c0c02440307100c1f03117103152100402c518042041070f0801400240103802c0300c0c03600c0a030f411000e0f1500780c1c0d188100000c203a0145050140307a645405054002c0703941243d010321f0110803208480320400049229403001d61500002c186200e01c07103d60000b03140c000312501c212648010240036004111160020303c0c070030f03003881080a400e80121880410b50010411600001402e14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 950943030 1250 950941780 950941793
    0x31c0b060c151503030f03040303140903040e06101b08041d0f010506090a23040507270f03021314071101060b13033309110406050d0206130b07 63
    0x903091140394018421919110b606141000d40c0d08107841d03040d0700406c16180941202c03000395401c03520900380030407031400410702c585202200300d41d1002580e00c0072400f00240840e0f0540b240e00150701b642c0c00074200f0345000c2c00400002c4a00c02d0408004c3e00c80400800b00321502707080303500410700c005030f07160f0200a80114410854040d281d4042c0c41d0081c800125051419400701c3e03019503001410742050918202d41c4040e081444a500845604e540c030003900c9a032250b000340c512070803842c1d03604c0e00c2056941c03d2400c20480d401c0354003c40d24090643c10b10141c4002c1c10306009880d0126420b04230391656122031400713014003801e81e112641180d010b005e010ba8002120014090801d0000c0c805c60340c8400c92660a4010b500d04c4150030414400204046550003c066030030440c100e003805000100c010a15224252039040b050106a8502544041c0100c150303543e2030302c2004071010b100c0c16207040e0002d250103414841c042c0c464080020321480010200540303100038003910381e83c10388072220790030201c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 950944280 1250 950943030 950943043
    0x61905040e01020a0201050c0a27091a09153106171005100902030403170708010603060806040f03180905040c03020405010e07141804050c0301170a05031c0b060c 71
    0x2c0313016600341000310349881041d000b5600c0fa00c45c00d66482c10208880000c403140039101d40480f04c0b0a8a05290209980005002e042102044008041c44e10303041d200a01034054001000b541c0c0840c20004103298581d130341c4011002d42807281d207602c0b005145190040003190006090484001d20b0000005103105004070214441d2901f6030580c0c4180b00d009082e44107491040701d581082c039103400004d200358142607000e560028000c1c40c5ca0018903858015003c00c1020959900000c10594801041501d5060041300007a0a8041c054101401e05544401076001034840090510669100280c05100072410210062156810070302850401d4203104401608a01081c0e02507401c0c00c001040400b1a6503100d40640704179910b6012b9510b070030400c1d100035007105400f01c1030307030b4401ca465048582ea14011580681c2c07200842540c1c03940f4210300c000c4414000380c0700381d8450b00312940c00e00100b000481a81d080301f44551400200c5540e503244d440041500c0c0f04403035400200800c68900e15540000c41 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 950945530 1250 950944280 950944297
    0xc060c0607110a151e14010f05011103040b0a0c02100c0b10080a150626210703080a0603060c08040b06030c061611030d0c050706030c08061905040e0102 67
    0x5504100e80c801c0545621841c0080c40a8807078400321005000d00d015560102d45c00484004016502c0c0b0b0711107020a0641d90701c0410350450a11010050242c600084540f200811342400c007058401c0300400f07499103078040c500c80c000081d00b006c200345072414060f80c582d10300d043c0d004080441800030310320043d1840385c240703034159000312468002443c0e80c07488000c01c00668400d080100210a1030b642c401d00c0b17060900c0003110020f602c5007030000d02c40101c8048031402d03000400e001000310181d581028600001d0b2510481000c02041820139004600400c81d074040e40c0501e080116076079401c4821000d082143d000070240c45c83c0001c001203060b40709221341d003d24446c43c1c05000c0758441c80d0800da031340c00c1c1000e0320340d5120346e0401c051200840d64100c909007240c46032040920000c2c10b00000b9080441004c40400400d003004218002c021081c801c40c0081c01e418101000381032180240103000341d00080c812402184600c11034101d0042c01c1020314000c2200502c1031103280d4542600340c0c041c1d041800b5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 950946780 1250 950945530 950945537
    0x1b03060b0406050f0f0301141302090603010207112b080405010e12060c280f0f03140402012006190c08012409080609061602030c0c040e0c060c0607 65
    0x340c4014a460b000b15800c030740c001030103084540c40c010704100081d85902000d59042d941c45012500d80903a80180c3c0780300752500d0803504c6002c09980184260404028030f00b40c800d91040100b8000200855201c50403144240c2c3e410080300d0b15880401071200540e4140b180d0703401041483e1041014540040080e290281c1e6000c1d090300310031044c0075802003448a4490b0a401c4a0009146420320001400e8141401401210000b044862500c400c6100c803540c0b4000031140420040c0c455042400f01c88200050b24080201000208542c01a458054002410801c070380004814140d1008081a42c1c448504252292800c0c8101d01076a0600c8101c80f0b82501800d099000001901841085049401c8002003440ca07a0000c0c40501c41d64040c00c41c45130500021040c00309103801e04002440c49600c4107002446281403030601e08041c0d40c4080307040c404560007001110359090001c20f052065440540b80400c402e6085040f0b5410002c420302c0290704510085540030b4030410005541d03009010644 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 950948030 1250 950946780 950946791
    0x905101d0a1802220207140f0609031e030a0f1a030c0109031a061c0503030405100b0f010f02030d020f0403110303090d200619030c0503090a1e1b0306 66
    0x1000300148011440082d600403042c4c850044c2c00070201000b80c28003220ba440c01032801c0318680d0b8092407042001c88003201580021030401016900300311294000c484040194104500f00c11480000d139109440442c11940120110b201c461031a0010040c0e5002c2c0031087c003901c032003010800d41801000341043d2203441001c0400c8441d5000c0c1390024280c075000012101e1000668280354035910010301001c0c1c10130200122181c01003100e2030a00c000328400c4001d141d0701e00b09820b25502d030140000640301c1c0d0750b01e042121804c40d41d84501c0a42194000e0a00e00d40d0500c3c242c10503030a6004071400313000c0c0d5500015007102c1d030b01101e1000380b081d2441801b85c1e0a9012031041415900d0040c2001550826040390441001c111701200500c0025241204144141d20f9207000c203403560031100504010954403096820256014014408100201e1418078207529080380074aa440080310009005615001502020410000c5070b00d200d082e08914140410142c51007405402c41c0288000d0360040e00e0310 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 950949280 1250 950948030 950948051
    0x100c0b0105010503090c0609061605100501090203060a17010615020c01020f0102030709030f0c03021005070b25050c0109080f1905040b0d181401020c0d03090c0905101d0a 75
    0x3c40a8030f0080d8140b0f0f0040c501003000005101c01603112504050f030026051081044005040d4441ca450f41e1040d40a026034540404144055a2040c1c014401715030040c01001140d03100d049040e02268400c07908450b0f08250300c0141d81c014085504440e051182083c1b000041540001d01da440303d1f08203a003150360303101811031040e080b8007056a041c0d00082400344104080b8030010080d03441e0303500034a04605201e43d2980000e00c0c001480d800d81e00401c10114000050002144200760b21421040802c1c80448060590286039040501d02e641841000f107108010035409501080071107901c1440241d07a0410140c8510140c0c008144071002003000c242e00f07417038040c03048040c0d0f0704441c403c451072070803d04201f81c028050083c4000e107108214000a0304004900c0c0c4080445d0f41803d800001a941c2548507945420082d640c01c1d09000d25080c00b80c00d2700041c0300902c078036040303642000000543da110011034188003a1607510460151210030300b010003041c2c040030414092000e150302040700c00c104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 950950530 1250 950949280 950949287
    0x40212090615030105150d03020708010e010507120506030c0909011d030c0706110312180102072f01080c07050705130605030606150706050c0d0212010806070c12030209030c100c0b010501 82
    0x3212500003050b40c6ca004040035042c82d07201080003c0c400c1c01900c01031501c4011080c00c41d2501010108980c0d160010b0195194110b41c40841c01b020303601d4180710514000340070907500d0f031502c500c0f14016200072000650045c402c0d0710a004040303c800160380d40e030f4100820f06a81e60001c0c2e02b00728441c003030002c00042d914007407440c00862412800c00717035041800450503121496002008600d01d014007500e1251283e8081c4001c0c41c0d518455019000842c00c0b140b40d20362034003240705041b0481031390440c08032a16138000b50f09a034810600b0980f1130350742e038041c90000d04080c401c0c0d001c1a0403082c111000c5480c2d02080d00b0100503100d0a400701c901c40c0e0380d2041003004040d5411404803203180c040040f18041000e58216035441100b03054203a241014000b0030004030303400300b44051204078401005111500703050004036004000b6240c800c00d10050358a80400c0c0114880500c014141c0c0007a0202c800e4506100c1840c00c000300a00d60b0800c141c20751350160141048200032500704d03500c03000204242d0700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 950951780 1250 950950530 950950541
    0x1b0d05060106030b03151f06030e12070f0507030c1a0301060c080c0c030f100b030d090506030a200a1214070311070c0b090a06050403050d0e0402120906150301 70
    0x420000401040c1d1900005400030440c0814180c0c043c0100310340100080c04001c034a41c0a4134110a030f202850f070080c3d00040a00f004c5400c01c60405091205030410312a0000d030b084070705400c034281d107641c407c607918114507081e04079180102240a40040007091210801c00e4030201c80201e60480ba4007440c400c9190702c03e1109000c1d850200e002e80c40c01324045500b80e8050b00000d104002120900810720000170714110705249ea40211742d1099854a11030305140c0600d82e00228144c0c014110400c1a40015103d04024000c2900614010002034604c00d0340da04070445140e6100441d40c0c1c0e2207980714090b40250310801c001c0c0c012901c6081c002d041c100d0b551082c90034840c29881e0003680781e20343ca40100c006d4084800110480d0f1000d11142020074a0054003900402d00801400ea884019400f030207842002c13075114000f441000d00007000840ca01184c0c1100004103440c201260f602c9507000140240070b2a01140500a0224100003c1410001d28039004000c00c00004008001d00800c060036600b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 950953030 1250 950951780 950951783
    0x6080706030b0a0b0d1812020c0306010f12210909050606070c030b07090305010e0606030d020607050a0305060d120206042d02040b0d081801080a020f19140c1b0d 71
    0x34400c3e9020018102004050400d075244580046074003149000e101d884090800c1d41514103180080c1034046990301008008048001a009000310350300d8152004085034842c4114440f8404062600701041900b1200f0418141c0c00703100002c410403c00707801080030545001d41d0701d90070b1500e070100b41180b030300b201138507100c1d540034002ea00321504541d10105001d4010f00040c060221440002c000201c00303001e0440340e402e045004001524200d010186861003521420782513400c45014403007610b0b40801118000f00980c01e021806480360b1001c100351180c0440040c10040031049a0803501c2e5001c501540a03a000b100042c00c00c98014100714410401e407000000c142007810214001800c00390804024a0350080c500c21059145481e03000750ba900248141c10350500d04c0451600c6580c102c007280b0f41100044508500f8840140c150000030f1040500703441000f50140d07486650544a07604012034152908031140d201c010f81d028441d83c408601104e254003c0000489403a01e0920120003001c16 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 950954280 1250 950953030 950953039
    0x519082a0604020f0f030124060e1c0f020a06020a14030315120102070b040503030103050708010b060a0e130e0d031b0206040803040c0506070b07080915010b0a2106080706030b 77
    0x241c603580e0130856822150952140c000621881060140e90280304106800300700c0ca220040d41140c0ca00301540c070b000700750411018000007d40310724854036501e50050010b9000550301c3c04601c6030f0b0030b000ca00881d522000030340c0b181c82d0f40000710b4059804035003418114820107a1640049400803c143c0b80c1c00121030702d10107501c850408250750f1500c0320b00300c1d60091040700018540201615200b01580c0d0840e01940c1960000004000304142088080c000304200b000030040800501d00060140c420800b14004002c1c803030359401c18903614000d200c004d469404504001d001480c100d0152034078101640040400d182c60720070400d0a030740e60481000722400741e016100d40e9482da90f441d24a40c002400984404421001c04201c545800f0000c040c00c0340a15900d01c21841e154200501e000d200030840f4505820800300302c05035402c0200103e0554020300d00d140d03110320312400115401d6441442610840c4a00da00a00381d4030040c2d0f11200c04d882d4024162611191103a9090f42501d2a40010b0303a0031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 950955530 1250 950954280 950954293
    0xa09080328020c1e2a03100c2303040203071a16060204090501230105031305100e0c18010b090a050d05011a0d02060f070519082a 57
    0x404181c0030707110100501c5107440719030408140025108030b801105000c01c1542c014210903149800e14681501c814000300000e00d81060746650850b6004001602c40e14220410340c031070f00040d9814050b2207410f140302c0c0401c00c4496005071005115005545420410034801c0210040c46000c1d00c04891207142c0180c02040020701c2c0070402c503100c5030044512005190144845025a030220b071101d0203060241001584039400c0100759002c5030b074103038045d81f020103070840088080790a440003011241000d003001c507140c0d03070343c0e0000d16650f00c4883e03070040880c0152800421083d907564005050b902208003140c040340f608200380048a03200b42590010041d82200400c11540200004c01d010440a000d03500c0340c1740c0c0c45011815000900a040b240c0d42d460f01c200010412000b0803500341d1400856007a00b07a10b0154000c00c54502c2000020b407011800011400140442080101c031515101c0c041061080380d40c0c02c2c40403ca4100e0b0003424560940f6000106074402c0c002003040301c461482016006 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 950956780 1250 950955530 950955541
    0x60a0e0f010311031501031e05040c061d1201061703030108010c0f081810020315040f1e02030a06030c1205061006091502160b0901021917161e05060a090803 69
    0x9001c0170044043d81011b4036180c0b0214014203603144980e6800b01c0503408921800d0a24101c284407101c2d07042141040ba5080302c804480441704002c414070481038990703908044400c01c00c0340c0034000b980c02240e00e9160007004802c062074000001d60480300320000800403800102c8040b10b80e5041e4000c05070000302100041454050381444016155444400303d50241c1258900c05c400c0e604202c50311850022000015030b52400c2c00e014144414554072010403c04105204640600342c1288420401c3d80c1e020001462050fa1584000e0103160483c0c03c03e5501030307840b060ba4a034030f09125000c468900418002c55541032030032504000b1f03a80140c0313a0144c2c0310300348003450300d1405105c0740050440c4103e0114001d10840d40142070082c0148284981c0c0e05c0e07001000184c90a4290342400412481c800783c0301c808681120f20b904040202c10116a5441c0d20440c5020048039000d403000e03010b403400d01641c1d880d042005000305403c51041040d11500d0b038a19802d4800c4619a400103803901d41c0400015a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 950958030 1250 950956780 950956801
    0x80105010b120702030702031221040b0c0d06050d11011b050a0609050a0b24121506150a0f030605190e0a09050601030c0e010f060c081305060a0e0f01031103 69
    0x30350203040e61045138105041a00000e05e0030702240c0702c1c1c1e0000c00000504ae000034141003440666200c141524140c00d080035552480c0b103080003070058426800c08624520ad048150300407000600f402442c41c130740b00601d41000d48a500703a9001042c08603044111065880054078485070301b1942080162160195940302c52019060248080741d05014121b106d6001a41030824a80201c0d115105490720b0240d030002e00c050b0440c41c1010b01d11807003090318440c640c0c1c03c5c001041245250310392110b0f0850f8440e080866142040c1c0700e0408000d40020410018140d448260400101600c1d07a041c802d4030360f90000d020b15082100e02c0c0034841c0314510b4080c42024402440741d40c12070f80c441d40008121401d41c070b41600705074003070f0001c482c543c50405041010084200384c0b81d01402d29042001c1c4224607181d0041c1c10301b140f084006110403000305d150461064038544c1400201005403a00d03945402e041801400034202d00b60b014400d41c1d841344030031840d5201c0c0c03049118001c0c0800e5401d203503840c8c510011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 950959280 1250 950958030 950958067
    0x50f040f060b0622050406080c030c041d0f010b03070f05012726010b040b03190201120608010b0a080c0a06050d0908040e15041e1a0603010b0c0106080105010b 70
    0x59040300042194403041282d00302d0002c0c4074442401914140717800c00040200355401640300584c030b40d000105c10040e0307036400309031825819012030740080d0440130310031240864000c1e4021180980500b081c007030a446010b40100c81000c0d81101520b2490b070700e4000505040d03156014250019152101c00b1142c229445ca0807011001c1d50000500d030030340e0b130b6554400000f00c81105058081910018241101c0c400d014080b84200c04540c00d202c40380210021a6036070412155001800f4604200c010a590094a07040e03a4414088010700005031900e00139030282046104090047c40d94480010b1007a1001c00c120f58140c0740203080a8030b5500d000c00849290b013241100301c41c000c2e5180315107400500c20700c00900051080140444035807614440540c2c2e0314943e00c1c1010f01444c00c120b9160b298141d510154892885804000030303e0100701c050b408941d0036015040d5412007000000400c030802c0d040e000e4000c900a40e4024000301ea00c82c0702140c2a00d00a1181c000740c0002489141d142007040300f4103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 950960530 1250 950959280 950959301
    0x4120e06030c0421140c03100b030c012d030507081003031e03020d0204060c021801050a030609060b0a0303200c0a03080a0c060204091d030715050621010609050f040f06 74
    0x85030031054554503142d1302c1805c02c00414620394048000d02d191070406005200c03418580c010100034002009020907211a0982c0155042040603408100d041c006120010515030140c60704410241400c64081c00400d025541000406c1042002550709a07000341304000751396041d5030b80f035003151015980b64070301c1c01029044401e0503001d0101e41741103661440a44000c0002d0342d5941c0b62000b41d401400b059500f0010340c0000d250500006201d5074880303d20000480741d0000c4c00003803151440c1003900007494802c0d583c65000d1148800003092540c0840c250718600c40d200e840c140c014002c0e0f0311841c0e82e0606400c1441c0c018050303000400200c4c00b0a409485080c3c2c0609241d100c000a50303948008a80c0190800d00a0550b94040040f01d5010044801c0c5071007213000045140110548583c0400c00c6851050f204158880002411303540302d098810156852a5180c100d00c00c0300521400d001c0c2000e4080c10700024a403d00190808404d82c41580c0150741004d0340803000c00164407600c0180c02c18004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 950961780 1250 950960530 950960579
    0x1103070c03200d050105062e0503040809030105090d0f020a020d020f190f060e10023a050c0c01091d07051c0902040506041e0f0f0504120e06030c04 65
    0x61020082d11244043c107001c0303225800004407031030b04100b0000440041140c002d4802035608145081c200b0908410394080400d0500a0312680e451034507441d07910818400f0f5402d0750a2100b40711420b140000c100b040901c05460384c2c1c103036131809202242e44001080000e54020209074110300582003020500649078000b030318681010700150000c1001c1c0c0c42c40c2d0301102a030007614108200c3c03603078004a40d001303840d821981c081204e45034038002991030191521a032016024541c61a4681d09407000794401030310352000c0300100b03c54440300a805a0800c20780030000c0e000300056845035620880d840415601c40c030b905002290844a278400400317500903c8081807110400900c158840e00d001d054006030034100d0049407a001c1807040c00255400a0840c0c3c0c05942040c0b41e0007241821000c00740701c42d1a03220f1000506d502d1400244024082035052855880d20300b80500051080e110b0f9095103211098449207041c01e4a031052140301c0c40200e91100e15400300740070506c649950180c4c4603280e801d9804 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 950963030 1250 950961780 950961833
    0x15090f0f04060602061b1305091003060f020a080a061a0a020102040e0f0402190b180f04020706020301030b01120b060d060914030a0306060516020121090f02011103070c03 75
    0xc282202c1c460f030080b0016901200c100075015101d8028510506400b04c8018240000070001135400c0d481809002c0c40390380800e000520503010300380ca410003150480414070040c414540300384025401125801e000600d103500088405000703000e11400c954443c0e12404003010900303201c0e4866000280031004554003004001200000038001e64001c081d460040b03011403c0620400220042c0729411a6011081c200200300c40d800c944152204468480c00940b0381510340750002d404074962240e0581e1241c8040342420038065194061416030380300d07000b07907000f41c1d88a145401c05140c0c04c0c113004100e0b000340c5000600341d0070031f991213848040c4610310204000b201503607025584200a51040110303480403c950310074aa25000e1400141038905101c3d01d44810141c040b0b00800c889030000c1c0c140321250481c440040c410002c05600090042c808000d049001c0c68603418803c040300d0140e0005400301d81c08512030710080b040b501410b920100801c101072450340c84241e03008100c54034880c41613169 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 950964280 1250 950963030 950963059
    0xa03050307030b22020715050405012a0207060e06040806162a020402070c091b030c0306061e142205090601080a2706020304052418030d0603061a15090f 67
    0x10b008d000d008920480011622104600e50840c407010b80e0b9801c0307514000100240032407540c010a850040e01c81c140740c00c41c14084401c0204101340b0480c0d119900c10310460b0100b080d030b50100d9000c40020745040e507800d04050518141038501210074081a8682d0f404107018500600d4a0b0b4001c20046100b250f00c10300103581d8a94282c125442c205060a882a0407192040019858445c1c480301d88240c1c02d04102123401e04034024521566240031040b10440310b419440b84a000340c0b18444e0401c2142c2c03030303240e9690003501a83c448105840d0a08410182c6403004102071400e558a948280b030103a40d50301e40c591b20b0b61140030103011500c01c83c00d449099480d81c0b40801015440304000d80d0301500b00540d03203040524103145051244489580d443d0394070142010308020000325a074004807620402e541d1910310078641400c51007106c1c0e00c8081c2c54a4600c00108112054210118007001c0448000803004807105000900d41c40a4400324100c01c10000b03c4080e11349032205240089000c1c1c901824003506 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 950965530 1250 950964280 950964323
    0x70c060603060614011e17041e03050703030e0706080606070609080a0903020307050604080c120f1009060c03050105010f03230c030919081b0f0a03050307030b220207 73
    0x541100500d010110f600007801d58011b050a01500309200000c2210780e00c17054028941107540040702120640c44011a007030042880781a1509000e8020b2802c0061080c640608590320601d0100e000c02e090040c0d1030610795011034254102c0300c0030741303450f03480c0e55900d001c014030365002c404104e40d203030750b12000480402c145501810003c2c0041c3c65040f4a41d0460040601d000f4480d07010070b1007100200824081a1008038240ba106802a26852a20701950b00d840c3d007488081e0300e00c244140728540c034214440c21240c1003041564013803141007141900c0820f088054a5090299601040000d1000d80446100303a010b030038941c1c2c0d030003609008000000720211100c0d00c1600c04140591740842440281e00c1d0500c07072136200040c2c41070f0380604206242d45c2c1c0c40c120700840c0d00440100305003201d01c0e11960710900c0000daa481c9401e0030f40e51424918980038205800c195000400a0701d040d950650a00305141c2d00300300080405604840d030341203c454032001e9482843c0459113a020f02c0050001100c6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 950966780 1250 950965530 950965541
    0x101503020c07153e030409140a0f051b03090c040e1e1504110414040c030c120213051b0f070b31110d050114010602070b03070c06060306 60
    0x11203c000d541002c0180401030000079014030340c25a040b03d1180007203801d46480058650b100d92116032921507440513a8250642c05194444450a806e0854000d10350302e50a00451180018083c00c00c910303000003c20a0848600301c46900f603950a0074046a10880200702460384005034000300d130125860034001c5000e90b442e400c10401c156000d40b0b4800780f140300e00202103401181460040c9910382000c64011003200e4040d00c0600b00c0341880e140c07841c40d9111600202c00400c440c1078150820309017440c001012800911043e40c1ca0070100c82e02065500342030001184050b0020840d520b06000004ea03200180701c040c150404850142e000d41600205420142818035019017000c0d80721407150a2511008200804282145c4202003010780300300d00384000c02a80d8209083c40c000e4116151518118045006890550103086034029004001c4150006450101e01a10601091340d0b00e0900381d9803208640190800600b05000181001d8440c060300008c82e40280004640c40e90780ea00d40208694 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 950968030 1250 950966780 950966789
    0x203071502060a0501170613020105131d09030a170a14010e041106030c040e0415050a060801060801050903090d0317040c140f030613020613141305101503020c07 71
    0x81052081085420f414400c035401000203c0c80440c2e0b100c2c1c00354070191103150041c085010030010003591425640b26400340e0300d694005550382c4c0d10964840d500003002002046800d1803003c5e82c00300160680c00b0200603103074402e0558441d51081e0f0700c0184181c0361280001c0c035110240790780708001080c1d0100e60705024000c11401c9200c0c1d0f071900345810b0a041e0030907400744803806224100140301010b4020412507048401224203405a500c8a1421040200002194201c2c9500b04004d000b040485503100108640d0a03000070801c40c1c0e9a9030109099410407203141c00315410505c011622400e005030102c10052091a192005c11503c0480012442044d2815504182c0240091010342c541e01201d40d2210001c5580d007a040522000280d560716004207600c80780d5039449a010704542b1500c00381c5d8510b01030403e4600e4007d0300c0301450101c0714030300c0b09003900c070700c0c0f1690b500358013401039104007405130507131401c01410203042c07012002c6020181d101c40800c06508010003170b0000400d101201c00781 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 950969280 1250 950968030 950968033
    0x714120408130f15050a030f0c110708070302130c0903080c010605011b0c06050c0a02040908070b0c0c0a03030209120307061b0203040b0334052502010e0d0203071502 73
    0x5800c030000c90410185950065214800c3c42102805001070546901800450764909260743d405002c0d0b0480c0601085d0070740803001410a4186907100380c201d04034104100340c02c2c0c101c401c0160307112081c0d1385d94205844080d402441d162400c60648105401c00030b0440e2440c10008111641d80e130b2140b42c3c0c0ea0120151039070a13552440c0a00c41c1d981e0007a0910029071a1100041d18521940c545c0b0703840c400b40c0e110700c1c01440f00002d103070744c0c0000b018001c1c1c0b403201d0b8008100300b0811907582030080f410b91102d40110b800300c00c1400000d10122b400010781e81c65061500082c508008644d505500070760081d1000c1d5403005099101100000c420401440c91510444c0e0200d103000001010007450f1916980400641d08144402d11060484100b901c2d4000c3d002c88040c0e40c052050030701d64058421600407000700315801042c2210341600040144034600164009602c1c2458001410304800c00f2407078000d00060344596503071020b04d44000c60303011060004080d64800f036956440d01d00001030301404000075 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 950970530 1250 950969280 950969287
    0x60705070215030f06090907080d0c0b0603010e070e0405070e040501020c0c06092b020a1e051f03020d0e0f0718090f020d0c030510020403150b0102060714120408 71
    0x840c100012032460400416400d5400c0d410840070f550490f4038000c1a81b8054403c03000000d814800402401c0003c0290005444e60701001c0000240b11504000c8250340c1030341c07090080350380360405214030b655840364500034150a03414102c40000340ca10141c01610035101c1c5060129891003102c040a0207184181d000603620018080b2140c100b8800a4115100314014404016a40c0b07403030307510300306242081c1d6411580842081c0d01003440130324484065005107000c040031a202e500e0345410208441c0114015406d540c0d81c40070041c40c5e414201c02029041e2480060a080a00a030041d01c8034515014011039108614113a06151038412084008140d000720f5040011544290040f5050100400240701c07010079074503103002540030038400074061031010340120140b0902d081c007840515804015101d505240c48182c90203500300e80400c0d00c2801044075202c840b03407400c1c818807000c0001a0050441d0790f5441d40151013000c001c401c502030011040104c08000c01d4000e10b10340c0705900ca02c15140d00c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 950971780 1250 950970530 950970533
    0x1e020904140c03100e1b09160c0803040809090c070203280f030509010306050f090112170d06061116090b0103090209011818030203040506070606050d0b01030b1006080105130b0306070507 82
    0x60160180c02c2c1890a034513080030211241c0341c00421f15032000c0700c10401500c401c5d081d07804035400030382000c001c0e00340e0002005100030054104010030083c503040f181c4481c5034490501100c024422518000d46c1a800b91500011072900d01390035070324080841000300300d09456a1030354141c1d203d4140c805c60009070300007400751740f5681500c0351700c01610090703590f43c00c1c09000d0310101e03499041c1030080046062007000e51100700a01051501c12030705140e000d9039104da40c00040d0340c02501441c010140030405801c0c0842030780000046030041d24152072421525145885640401404009602410951184104000360710b03540380c198000c00d24689035045107d0991035882c200c4004c00700c1c80c1c10104580205001003640002039405540d01103501030344c1d400032468248001c281540c441030700204c0c408100d00c00d000e81100440d049900907016204a81d880d01d2200c014a007481c01400301158034100144820b003060f0b11040300800444000040540040002030700d0324400322040c000248001400d0030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 950973030 1250 950971780 950971783
    0xa0b030a06030b1b0720120c1813030e1302070302061602150c131206050405010f020405180907031a19020909060d0c09050c071e020904140c03100e 65
    0x194803036140c05001c0344d0b440b46545101c2251207001005822494020003041c0580386512010204083c000c000c94460310b1200301c043c0e00c1e59020b2405901c41c01c104440c0e03e02141601042511540300044650410050b9550507542c0106802425401642544c079001000d1020710040c0300d05402500101001d2806140307428140801c045100c0854000d280f10b1642030104444a0746c110a0025400751200d4aa18a51410300314a81c40f424410389191414418059103074021800703180030390001d0002455140ca0303241a445940305094110041114841c0c00c0102d0900c00c90300803019000b9124410742e00c1d1039400003d0111100580303140307841414004401640010740c0c41201c0c070710405504182c2010001002c007400140482e0245032203101080c104048004907001420210004000c2420020040c10541d0800c038401c440700300401c4126100c0c0510052618410b50b4002c164100c90340e40c6036142e48681c040706180700e070039100c1d15120054540d400d01031002e018204000005a009038122540d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 950974280 1250 950973030 950973053
    0x1110702030c06090a0b0c0c04020706090501180c0501031d030a09150306030302030405040911030d081e01080613050a0b0702030a030c03180201260f0f0f07020a110a0b030a0603 78
    0x144101000c00030b504c16526030541c0d18044400178500140c94665249903582003035880030f12194414030004600d020826150300154116000c2e000070040710b034403200b2103400c034a04105c01424084002c0001c10a42d0b00c2030b00300301d540071140074090700358a80c100102483c5070018a2244040f07461a0350034414070101c007082d43c040301d10601e414001680341da10701a49912907401400c0c001d6444005440502450740b24401080c10040d0031520172000012005050100643d03480c40050090011480c0f014083e03280241610144c4018000ca1780320804031104424807494100c03281d0140c003c605d0041030356841140d2090070300e900519980d080c81240101250080400c1c441810f00d401c5e03101c032727048100424582c82c7d10790a0030441c3d600140d04210b8496400c4664415900c040103804216002901b20411802010000c0700c41d26103440303070301401c21902e504071038510050b80301d01c1900c0049843c04441003200c1101406440c0410303103030602c1d682140d10440d903289159843c0c0d030080007003102c000c503134 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 950975530 1250 950974280 950974303
    0x2031c050f030c0406080c0a2c060a030c02010b0303040324140c041406180f012703021906140304020d021c12110706140c1e01320709080111070203 65
    0x125145c0480c00601070401d09600030270b4003460788241c0c454202e010340030811618410004240d2902c0300c000280c010302070640140800019400d0613003011b01c90500100303507010b603039000f800f90400c04804110200b070704480f02c0d9011a0180c4401c00b00041c0e401850f0150b0150100400d220b030b445090082801c1e14603401744085004200400401003460801c00841d540d011080380d00101003d0600012141310034035030442108510783c083d407110340d0b50b000e0b81480116442034072003200403503140c0d27804080707580240301e945e0100310718499a001410601c001998803d10051090100700182d401142107148103101526060904942d0881400500c802c0520720b0b40a526010f0056515003441686960003885880140500d0744044c40110300000152084c00c0c410000f1110000c110000030401d6100e903101d0712809520346401180c1400c0c03440085141c0e0400c410600100a0010f003104c0c0d08840d004042300c0803c441d44001203520b000a0150b1070700322a6910000780c580a182c0101400c1c0403070140c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 950976780 1250 950975530 950975551
    0x706020a08090d1704120e10090f120b0601080c0c01060e241011070909050c0114030f040807020d050a081b0f250f0f0e06090402031c050f030c040608 66
    0x78100050712101c9034195005d07a2146003d0700e04c2c0c04000d41910610040c602107035000101584443d80b0303036805114402100e10440c80508620390b00c4041212a9103038101c0503029000c0b601c0014400d500401c84103802c00369002c41c092900d140c0700c60160849600d80c00034602000c04030180f000c010400b0030700e0300d03c138000c100d001e0301c0c846040300c0010141030405582c0001d20500c05c0c0500502002803005070004c040c201402c6c0800182c40c50b08680314410501c20314045224580305007240c42c2244243c3c4c0c8115940013541440391540e80303030000c06821800c0201c0c1d100051808140005005100e50710900e403140c05c000d516030a911640300d051150303285040a450b40b05c0314031140b503098002609400d0b40c15010465074041e00350103d291010754036400c8014850080400012580011031106044480034155a052522071008100d80300320152030296065200035100180d01e40d10000050203080e035410110300d80007030303903105c08a2a0021039000d400c64001003010004a608031983c5d40e4807000c00350b03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 950978030 1250 950976780 950976797
    0x91e0a1415010c060b04020c06010b0702120a1a0a1d0607030b041103040206070804080d050306030c0a0305030904150f12050d02061e0408040902030c0304230a03140706020a08090d 79
    0x3810500f0898000e4519900e8034900740c0ca03500c4980c125015250303014103641c050340e180d000c100103651095078103d002d200000540e000c000000308a40c2d0606921503034030b000c807451080842e040720401910703072603c49584034094840d40c0d03080301c0f000000c0500c01010304070501d07002c140035048a1000f140680a035091900211602c00c0082c212640254100c0d0440c0d103442c1d02c1e0410000a0003940c02206581c82820640c0c414950004d024501c2101c08400300c503c0904100140295400c1c0d9100080c4140e1081c005404030745044d0300014881e80d401e04021310090359034840c0200ba080c039548118042000003000805001044c4458080140340340001c00560414074414594440c0b83ca80043e0304003a0301002c00c040003071003002c580041881c07a40542d101c0c2094200c11466030320a580440d0343c1c988000240c003403103500200b02c031003014070706000e418602d205403070980e12020312945d1600b002d54208030f610006092403010704008500396450304001c0c50001d990f0b40c900b0302c0c40c155140900100b207 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 950979280 1250 950978030 950978071
    0x806090604110a0c0c050405010807090b0409030518010c231b01020606120106051504080c0d120309030c0213150f0f1404021204061a010815091e0a14 66
    0x181c203c1d240c0d19020714009243c044c141c10020500092500402d5004e4108000020b503814001444815a904075000300007540702407040204503205030400802180090110350341c4e100d845464688816410f0610b99003200321940c4d00580e0440b00103140e250700c80f2407076035401c001c4030402510103040d0308601070341c4081c0c900200107561003500901f118443c50709144518010882034021000400300940281d649003070300780c12421550082e000365401480790048040c010f252510200c148036800604800559800003421009802202400d9042c00320000c11240141c40751980504c400040c0c00c070000d00c2405910303031104c40114550040c02c2284200c1301c01d11a02c00003c0b441c0d41202c085428208000301017602060203402468084106003400600304000c1c4107a42d000042c47c4460723080ea0060300506c0400550345000705881d48590300da85001104902e09007a03106a130040c8030840291102d01c60051154549a0f040b942c0c840305a4648a92000b01003d500300c15401524010200700700341c05c43c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 950980530 1250 950979280 950979311
    0x3070c0b030601050c0106060c021314070e0a0b0c030d05060907020c010c0303060b13090516051b1c0e04150305100c0e1c12080c1207021504030806090604 68
    0x600800c1051600000415900c1e8010710031183c10321008002071044640e14100034060724903000307090b4042c40c1c40110480b1007103a14810398001c107605a0000d0000d0300d5052048031051a082c81d00c135001018007030045070103070040b00580340c445003e20041d5554000d40d000c18003036650281402e030080136a001071000303082c0c011820010710f01080c43c02e500314185505080f005018181e00c03007105004001001a201d110580410f400d95844403420b0086460760b000d100a1710b40d400b03541e10000344d4144800c44541101c3c1c901d48148034850800c40d141074803d1004403003000e2416640201262210451b11124105400b43c89003044c1c4603a040740489107141c40e5152a8035019aa1100d000d9503059110381c6036014909960358150003400008415503c00e180b5003600d06507043c25205581028000100b042c4a0000584600709482038141080d00d00d82d840e20710340360301915040550050110b0400c1c00781d011082c4070f105501994500c0d0250a00070103001c802c03500a0107040c0554106500c44200005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 950981780 1250 950980530 950980553
    0x11808160b12160201060e19050c090a0303050c1c0507060b030619050a140901020a020c0a061b060204090f0501240917071707061d0109230a150e030307 67
    0x450007004981403581d42c2c000c134010001c0303802031301c007c0c02c8000a0124114106040402c10141d0f95400c200d2500c0c0e601281e00180104225590b1020034103c1c240006803150014294416414049a820b001801d80030300706100e4a4406100081000c00c40c081407100d54042c40d000b0721030550280405040a035001110f0440c403404030018684c4a4002c550340303484c0c40e0300801d598040c0c2d2010350124103100340568080e512120072900103128903165059a85007400c4503204803810b6440c1c101c003150201c1c070191f68580445d07106589060f800d0000064903000f6000c0c040690905440c002025810481101a482030f0500249042c0440c0346016851641008001d02030b00c2d0546010844001041c20852a20740c082c0c0242c00000300305151342075a0302d4000380050a540181c1c480d50985006003110042c520045200305001403002c201c00c0101c42900c2000d26405a003d201c40e201c1550b0300e2010841c0c00388107512105c1107171a1881143c900e594840d44400315904114041c520b450b03c1d135100c0b407800d5130 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 950983030 1250 950981780 950981791
    0x3070510090c060311070204060602100c03050c0d05100b1c06090b130b0f130e010501050102030307050a030b0a080f07050102280206160f03030b01080105012c011808160b12 76
    0x550380c441c0303483d1074861601a1b440040d4014410b10096856201c000c1d11078030100c040455160810100c2ca40450281c0111403040b102c2942c00c0341400501418040900b0000d070100303030000800200404d80210b250f00400c0218885540d1504801c406030659045810540c084040c482c80d041c140e200955a0200000542c680301001003070542c4100e000035801406164819807041002503011000706a036000201c0790301c010340c020444c2e40e030f8540c016603c0c1d2000312007200029000f080842c3c030090103a0f2140380000c101408010180d501c43c022546400100c5c40d4440460b030109004214569040019038039030b619038914000c1050418000110821081000a2048c0c1000c03518030400640c41615182003038001c444580002e04505028000309042d8640c0d500182501c0004603080d40200941c41e56441d4001c01e4a20100001c03500302545400c0303074041e6041000b04080000d4500c24611440f010300300d003102500c5840140c600c4292400b8060b0f002c011288414890810307422404200c543c1d015 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 950984280 1250 950983030 950983037
    0x70b030408071b030b06130209130e010b040f05040c120f0605070c080f071b12080d020904112104020907030c020c060307050912010624090305011802040506190b0904150803070510090c06 82
    0x6c2f50b0041f50140074100d0000c450f074200e49412070b0400309802903042540158022a202c08145031940b89861070031030102c802601c407101541000000a250307511180c2d1011a81c9007155400880781d4030038115038010320508200000101d1180f0600600384914080075550103101d0400d54a089948600c0300310301000906030b0b24010600d0b000e0100799804907000302d00c0050040242204c080131666079034100d00000307201d4800f0034420210f030b00c41c9848924000c03031300105607021a5a43e200210003034020700d41080114081e0840304200340e161000a58098040747d1205ea0b00d030680c00040c0000800c03031505200075681840744c10841c480080040001000c4a0381d0070302621000d0200075548280594801415907180c1408813904500305010107c0161089034244142d441d840e04109014910b600e0042c1510103241c401c00c1071600310320041c00910800f0b00302041c40940031400da01011101d0740480401e41001138070408200c41030101a0035001410001c00204c54161a9500300c00c40c030740214420b1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 950985530 1250 950984280 950984291
    0x506030c101404052e14030402130f110301080f12040b0f160b0105100503060a0605030901140a0902120706090603020f0702030f010f0e070b030408071b030b0613020913 74
    0x20502d541114003402d0050490f6003100310003010701d400d8400c2c0e09050140d071038a081c81d4000303581c42082c4844541d54109403450468440d134080008a9001c042090340f0306981c0c900404034002140520380d0f80b40394000360642c8a42c0b40c030014030f06210318031403520999001151040002c0d6100001d4606070340007500c0440d19006801c4902106118884060150012038220201000489000d03a8141c603003d40d042c4405c81c101101c180ca080c0400e64034294031003182803051250a1248001d0356001900744000f045003044d01200d404a03e10039503030004200c0d00c0350700c3d000a5041403412040d10700030480c024081b091400000a01018140c05180f041680000311040502079003411703034a2081c0c00400360f583e12029171500d94000c114003c80c05a501e4240150030b60b03048008135400d4115040d4070388203451955180c1c0c1c0c210290340400e0044440220042051000d00036660840700658410044c00e42c01c0d003810020000c0d1440c4200698802034010420109940c031654074040e500c0d80f420300081503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 950986780 1250 950985530 950985557
    0x3051e060c0703141e221710091b0b070501140402101d28081b0f12160e0c160b07140a031a03010506030307030831060506030c10 57
    0x30141620303044810817040403482000c00450709800c80d4200303058038001c018082e40c0f0b10b00181515a040b021607035030b4204000300b40002110b500212000380c440e0300507901d0003c0d000380d1104104480d03006a040640c010401c0c0341042024403030901884400c00806603549030690001d0400d2803a0700f0b90104214a400c545004003203400c141002c0900020000382952800d03448002c400900d0603261a05014410790001c1c1140e4003107a80c070300000d0744403070914400b41641c051101120054541395001981105054142c22091140c0703a40112940d0100c54003a14045012620b13160241c02560000006c0090380b0030600e111100b000d05541c4003000e100d2581d110841506c09000c581803800308003100040d00524650b0542c4100890f80c001c80e0031020410000301414200c80c021142e25800d03500400c40c4c000440d0042003400c3e0b000e22160070284462002c070000b85c0801c44298200500004007005900402c490750068031750142050340204030f01c1d10040c000a044000801c00c6405111f0301c510050f1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 950988030 1250 950986780 950986807
    0x12040e011208040918050d140414060906130e0a0e070e0702030c0114010519030503030c07050304080109050c150a02070317040812030609010b031005060a0903051e060c070314 77
    0x3801406001005c000c4110a04414110100d205030111168050f01441ea0040c6001d09149442a0b0090b007440e4109800c10050904111524540036401402441000d2aa90380c1000414080764000d000420081c40c0010310180100003406500d4540e080c1001450300410004521046807140f9403590b18544810005a040d440360070709174851075003003030084c04400b10781c022880d0403554103072090030100000000704441c101c96400010140c1e002000403600b00c6070064040d10515009000b600e03d0681e039412400e007100c206501c00c844c1c1e5004002d0760003443c5800c00c0448040f4850008041c5841c84554000351200302e18040144845004c8e1022006070902405135000741c2007034011a020004226400d0020380c104491985c0704042e0100042403500001060300d000341c20440005100500303000c20848960850811001000000b841c0000401e0081200141c00b001041003103254032441552303141060801042c8808d20743d010022040020380c8540c14655484040d05d850391210851080403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 950989280 1250 950988030 950988037
    0x10c02011b050d12111803071d010806160c0219050612060f040204211719180501020c120109050f030d060504050c1b0106090e0a030212040e011208 65
    0x1107086400c0669030100b0070034005941d0380b034031400f0b0320f4448200c0d071001d401009652040c91103129404060140d40040c5520000490351072100a081d1400e82d43c42d59034039100442070148124000f4039200040004000910160350843c030440702d64407601c042c0420291000342c040e0760003809611131403959003800c0c1d90b0b8621640603007001003042e07645040c40452003c074994162180c40c070811540741075a113540341c64801c071400c440c5640f80e03010300803845001d20042c1041c9050159124003005050401800141f40204181001c4440e8140945a80b00000381007070812010002c5c001c180ca0021700c5560b80009540040c014112041c480e58000c0c0070ba22405011031620044c90791182509507002e0b844080f025140303500701c0d0601000310595410800064600507107020302c20040c100700304403030116405214508146120004180240d4403407010003110444290b018071500241c2d2204101681400401421080c41d5001c5027403509050390070008032010320607030035808003806440080003500c5065 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 950990530 1250 950989280 950989307
    0x9180b010e0a1512020108150a050603040f020a170c0102060c0409090606080105090c121207020d05010e070b031008060903190c080a030207060b0301140f07111e06010f080c010c0201 80
    0x5600030307680d0207901102e07440300c813401c81c0480e5607040080c00004c2d6942c1c1303500c014803000f0968161a480c160501c8020752003e80b0503100d02443c107110302c0c00342e204c11051500405c507000c1d882f00c072031030300b00d1003036003010346401d10350f0b0454100e50117000604c000c2d501940d06660481400041007081850a070004003440d51225046508040030480c1003540410100c180c6642644d100303102c84040101152140017031074004040300418850030000d424540c1c948075289202d10000078031401d24440c40d41c80c011113540304080b00b0130000304001b105c05070859a40010000f40c3e004000905150020540324014045a14005040f4040c4003d5051140341c034800b01071342007030f44d2035614080008024080d46c444101600c0035401c2038040d20351820705101b500c0c03e03140032604081039a00c0740d0814044000018003848108800440d000304802d034140508030032400740e030b998000241840c0342c80e6070800300141c0c80044103100c0d51500700442032002c66a4a0038a4007481c00840c000050710060b659410f05405 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 950991780 1250 950990530 950990561
    0x40e0307051b0901050102070315020a05070f0f0201021006030507030f0f0b0f1510081f090e0c031c020709050403031107050f011b1202090303091909180b010e0a 71
    0x10145441d07010342e030081c10305030054401001036070703c50005a0713031030348103200c018071601c0e054140360252052940502000c00c1c03d80f03000e500c0c00304940c4421900106400c4285d0320358807a05064400c640e010008040d218480c01c4050080c0f51850711b42945601081c4009010300c50b98002c400100504402080c01040d88103080f0b400c582810b40240940d0003080307590f401c03010f4240480881900d4032454002e405a155900c43c4480ea84030b030082e02d02000341c0035042b160030165600229815103940a14007003a03005c080200540072404041503d4103032140489210141d411890f0b807604c03a070206401c030507500019008a095203031481c045008018440c1000c07205540400c4400c204107012620000400342d14000384a40c15882405400c0c5614896110010400420440303070f80c1c54458000e4000010001d050b00c2c203240c0e8039800703d0b0914101c0d07040b08210f01002c1f0740521540304584a074903047c6034100c0e134400103628565102e4285c0d9006002d041d900107440000120340400d65000039061221104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 950993030 1250 950991780 950991793
    0x1081e090f0109140f01110d1a03031815190f051312061b021f09060f05040c08070b3403091505070c05040207080f12010501080a02090f040e030705 65
    0x184007940200c080c00003c0c460007908041040302c2814010240e0000c90f02001905c0c100262607450018544081c01022481d005040c9500e84c2c0d2b8280082d110320900b40c84491031490541c000c10156409451a0081080090050328040134041c2100303866507105081c0035944080101d403c1d12140120900c4103800242001d0214a6004800300f85100341e20540f4113001e642240584401307056104111000140d00c861818a02e0b2520522407455080003014002100325443c0c540e082a86c80d04a4003214494550052204101e800c1a41c68002c1506102820040c7e0408103004918480d6410402c036880c0341d801c00c4583e490302400c400250030f2920248081c400c605203009071002415214080303240b4055031003150064020740c04c4518607035002114001c8141400304120081d0041c0c1810b9901302c405100a0300407001e0400242442c0c441810f40c03100303540c9850001840c0110090030b95004030f00601440740c03275889480c0322004541c400c0b5400704180e1440c844140c03541c09401005012440b0303c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 950994280 1250 950993030 950993033
    0x130203090705010f0507020f0913080c0f0c060703020703020904020f0d030f0906020d020303010513020f0a11060a060e0a0f022710080609071407171801081e090f0109 73
    0x907004044440a032260300c900001004160741d180a440c00c069040083c60411100500c1e000703104942c070425414108211008648071040c8036013000f403100150341d2000140341e4090000300f11a10150401703d62491521020b560000c3d1a20781ca80300090042580c80b000c2411941c0708902d01c1c0304800041c10100c044a000d00340100782200901140005c11a400b1001c00c80070f202082143d00c6c98442d400840c07071079107004103204e5110501e40b64494160b81c00c0c0300801c400b20440004207031041840c1c6d5800e410201200e081411703c00040d00118080303280406c10011a004c03111000d510801c154400a00398420030745400107840f072031215842d900c0320107034203466280d482e0301c07103150380c1d003007038642900482120704160351181c0152000d0740c0c0070340131400064410b40709040e0034101070a5651a41e0520000795186070214000544000c2c0b04100070582c1c820b00080401e1580201100340f802070aa07080128035071051203e0f0060110609640724000b880306a0208500032a03110b4040003084010781a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 950995530 1250 950994280 950994283
    0x1051903021806031e040f050d021e0601060c02040c12050c04031110170a110d05011712090f04060b1b0708010b0a1401110105150f0d080702060913020309 68
    0x101d0b00b40a0040800c01c074003034100b00e0306480c880c002c1074420a1075452066107800d0038520051044a1200e104420340000038010300c0140100c50302c5030020b12502ca1480d044040070200c151022960364024001001140ea01111045006805442c0001c1001049004640807110b0a0891b0b00b524200010701c50100141d00080003103034017805a44001c0c00490003040a817014000e0068000b076166040015081c050311a56900500d01180004801c6400e00404129401250369104c01a503194010800395036038008204200030f12401408020540d91a82d824900420041601494586441013329243c644c850405031000c0040c09440e0410908801840c1c01003401c00d102c030f4041c50700002400e0f4814001c160300444000d01d8040664107210010b81c0248403443d1039810030001c04241b0028100070f1141c0c0b40608507031100c0302410040501480b42440c018482c1d03e0080c411191180c02044d4004103a0f04407030b604440c0d4a50380e0101e440001d81754159401390042c9548000103119079485d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 950996780 1250 950995530 950995537
    0xc030c0f1f0b0a0509100e0406091101170f18010509011a0114070b0a110a02010903030501150503010b0c030c030a09060314012402100906051803270105190302 70
    0x11401e1105041164610754810346041030040c1e500700349032080c180302c507140c48140158400d003d50528141d2990300e1030300c2d039920b60003540c0907954540e9480038001031006c0f598407440c0041007820300030028820070440040003a402840b5215070101c3c0c502165105a2006003c060580d40c94028031490401c2403240c1d00030000d00c0003e00c01240a0640c4806a502408230404400b020302451410205107465801d4022001042007040560301c2004d5201e400303917007011700000021070b40002400100e924004e4115441a0041c070072545044010041c0c090b4020200d07810f607802c00c55002e49070308586c10340904c3c5010308401501540004114400000d1740071000f40101c074110354040c01030f0980c1d41a07030b051080083c040e1050f150310480010031640e001a01310240d501e070b144100c961300c0380d090300c0e0102102c2a43c1c03012100c068a60007480328400441c00d4185a902d0808080c62401c00135a21440b4543c1c070050101c02c1850340c0c5012900c50f80c0c098419168a1a1b038440440170404666038010000e50 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 950998030 1250 950996780 950996803
    0x4060b09040f06050307060c0203030f0304061d0f0d050d0902030a12030c0c020a030b1302040609020703110123090712120f030e030f0d0207061104031403130501050c030c0f 76
    0xa1505600c01c15030a443d000e01c004554000c0c024001d02ca05200003283e05002c07044043e03816110400c81c1071072609507180258822800384d40e0010740c4202c54500d01d1041c28282206903d59407121131401c1803000c0104056251030101d040c0b50f0341d12003010890308081d258009000e589801141a5078081c060712109484000916a60400c612070a0980c10b41d4040c090b4030029400c208045801d00000d0f0154100c203802c40c001d980354600d24003180d8002001d881d0150058441141c0202d9048205074028076003940503031000000b8001d09a0400e450b4206000000741c100a0402410210304040814010342000c2c3c01026024050700c9036034102100d05c2d0541e00c0040000552501000c80820320900c1a14181d04015010b149440007480e0349444030340101c400c00c02c0c900d07800c004810001d60785224400b003002d444544180c489245040c0f100148800408a800e1a04104103003281c00c1c903030351200d0302500c400342031441d1128000c5001074603500851072842c0d0381e03115082000c01008030010b50703502c106c0b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 950999280 1250 950998030 950998039
    0x504020a2d080604140a0308072f280f02040b1203070c030c080607080a0510170a0215181c02040c080412171b0c030f03010509060a0303020c150904060b09 68
    0x80c0c600845c0565503c030501019000912076404a0441c604c503001c050544480c28103c00361900343e06d40c0616260807169100075807a4440417041e1400c0d241041e801c0b549008824004c40d6000e0036480e2400004110750300240b00c3d03580d0b03407101d110943e10750792444621b204440031a622003040d40b80c850341210356800161001c001203900010b080b140000c04c144503042c140e880c841c440c3c40704406200585000342c1050401801002c3c0801c80c03c005400d407003100c10a942c02040e01c400e45005114410711002c040146440d420007030910010322416000c02003034002c0d5410342424a151303c0b80d400d4a090020000d50250a2200f000360983d440101139010f280150300301ca20708000254280d4401981c0700c078100c2413250480000340d03610b1000488280140d4030306d0045290040400c14030382103900036035000500c24004001400f01e13041c0049440d5200b02d0035150701902c0390079500c010f5a603242820040d4803c00e4071848401c44200f05109a82c480314010300280101500ca02880d00903170040e42089014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 951000530 1250 950999280 950999303
    0x150315040f2d02012d210507020a0b2a13050402090307060e1f02030d06081501090216080c071d0402010f0f030e0304090c030b040504020a2d080604 65
    0x20340c2d1501c58000e0504940c1c041d0480956540d401903913001d40756855503210780140d50404034a0740110116000300744540d40e450070f4074200e40c400004c0b400c022100b00341303041b45000200042d10f03400007807402050303802101720050b40e0784441c03a40c4680d03001c40b0700000c1e211005c46c0300d000c400200074001d002916400c00706031051588a00c1880100d0080c43c0c48258960301000342040418003a0455075650f0388050517209102d00b16441c1748401c3e14a58620000581c0f0020795403000c4842e0344502c0001d00600c9000c0c1854801d8080c0100c1105810f0044011b480e030300090400303180404100716140c2c07607404040c00b500e4a49900110791a103802e8401d46840500601603580801c60b040c4075903126070341c140c44aa01502400030212290000c624081c400d059862800d01d565540c00c0014000030090818003094515404c47c005069480303217026540260b0501c0b05100040e0340300c0c0300c0c1a041ea8151551503c40809549048030440d40e048000070b0f0516500c1000b1038465804681a4812401010f01d01d62 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 951001780 1250 951000530 951000563
    0x1e0c030708070323160c150503240d060c030905010606030c031406060f091503090d0e09041a07051608070204060b1e0d0902120c101106150315040f 65
    0x1141134070600d0400604014407041c804000b590044401c0c06100c80801ea581c41e0300c040041203d40e81824000b1400200410141c2c80301641c0c42540c3d4040d15074100440361101010074501d004a01008002c0c07134442603039500044c401e900050708103030850000c1c02030640d651000380c0140b22102c4068001303420702d000301c40025028001280200e401a001c9890242e400048110b01d8110320071182e4000718181104000040c840d0266009a5482010b0480c1c240000405081c00f800c425856001e0340d1140d00300008074400105031150075001d5407030402260b0b102d19007140e482c40341e02240042c1c240389280382c000b4070083c000506410740c400d94040005030f0b1510800350590043c01e0340ca4408038980c07042251440c9a001c090141e103e1440400f00d0140c0d10340d8002081500c94180500386517110550302d8a03039260403148260301c1c0c1101d08120700070344481450340b512a48000c107038071010380c56815000c0440e1400c0286100e000c20b9004180c580741090f14000c0c40c501001e8100707807000380d00202e1058 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 951003030 1250 951001780 951001817
    0xb0402090a18060e010e07020706081e1b0f0909130209010b13051e01030b09070c02010507050708060f15030d0c020d060f0f09150605061e0c0307080703 67
    0x492011004010307000031841e000b0403504920b241201241c000c1d4a80100084181880c0c1c0d965010300091010a075092410120080c503101203548200104401e16060000b090b030f0100010010b251200c0089055940c0e5128440b00a412620041e0081c00002110000140306001034818910129520001a160038002e181c58503440c14000c0d500c695040300401c03c40504500a1800b05200c0038400031590b5a5800614030301140002d460054103101c5200c0300660f85407161001c428401c40c0c2c041c80500380f0701001400c40d40c070b2010090503c08002915000d01c142005150000d0104808441c014030300680003880d050401c0c0c403400f10010542252442500d000304404400304203c0d6100d841c100255000c000480c01080c0c000d6030129074843d640100340125008503014082070031408600c4041c50326101d200e4001c4038194444031850414144855a115003c0300d1144900c01c6840341d1543c90f440b140c1e40c0a10404a0000e130901c0b00064103020012050301a103c118000e0f2a0500381c0c02d880076000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 951004280 1250 951003030 951003037
    0x12030b240c0a0b0c181206070f0c0206120114190605070516060906080c0408100b0d0516170a020d0b061816030e19031d0a0e01080106080a0b060402250f05010b0402 72
    0x81b6103404c00d200140410f80300d0308a041d02e070031262614201c41006500403550b60b03481201e60a0442c204d42d030051080d8810f900040721048004e56101076444a240c892000111083c05914108000007403000b0500c001040b00c00704030350400e09400496641c542d00980101464031804020a40c10f00000c0c0980c44503a065600f02c5000c6406800d10444e00b8100300001e015012603a5403004100507a075020600402041c0000c22a0b01004c072442401d098a01401000d0a0112031480c2d002e0480e400040c1c036070340b0b04400c41c0d6500c140e0454050311581c00041840301c046443c1d5000f02803403000c104183d202c16100c001c0380c800c02c0d18100140d0150703582c02c1c0e480340190345025072882c00410f081d0001a1098a98408421a680141c080f0307600c0e600016a85071003682c814a06000914014800400284901c1000b010108024003144160b03589403c0d05503c01081c0030321a03680490f00c800c1c1c0586240420004803000010107403100042d2070107100700b00c8210400e8589628103400c601640c1481d1086 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 951005530 1250 951004280 951004309
    0xb0f010807120f11010504181d0d0e0607020a0b070f0204050c070b0403120f06081c05161511070b070815030c090a060503030712030b240c0a0b0c18 65
    0x80843c000c0c0c294413901da0003800c20061604200b01000001610204d00049045981501d0000305a0480d202d803007000e032007024403010005070048158a80080c2c0c0254210b281418107650254483c83d043c0000791400b01c030766225014800b00040e00404000c04030242c101d10070b10885082201e6201e0302e484401900074148000c0c041407164003c9400b190190800102000c244100030071440440c40360744090700c0040d030002261340c0c401ca2110450000300003115080c1c200074a09982040c0041030040c001010404000d40001002452b520743e02d0272503040115018541301c1c403180e80301200d180100d45131500307c0f0303224000b8180d04089401c21060740103c902d5184018014141b40724210108040d801010b40b01180c125030311400060191802c0c005403400b24016071010040c0301c1d141c0004cc0541b240c2c000c2e060b2290082021a066100e4440141403070100100c820b03c0c0c64010080d1000c0c0b5041665101030015150394003004012141e41c4018104032030070300014001c7c200810240858a20208070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 951006780 1250 951005530 951005543
    0xc03020304111e0a151b030504050126330f04020a030207050706020c0306010f0b18060d09061a03071508091e03040303030506010203070201020a060f090b0f01080712 73
    0x850030320b00e042c0d20f1005004107041907030041041d00100040d007510340796200101c00c055551108656580001e0240c414070301070f0b00f140c40584c4099030010010b100c1c9005950612581c0524604c00000342c0901c0000746a01010f0804942880344500f032080e0b4040718091000f005200a000c0740c5155401d0407246000050f1030b00b40496064001c01c0083e400c0910301c5400c041e424084d900215404000303850041031035801406c000340611042c1360402105821041c400303100c2e080304015801031072084608600c0085000c0702100c0500b00051281e103d8214410303021414030b803112061100a50140d6200000414810708407801c030000e1503260103440c41444000c2442285c1e8402190051805c55403040480381603c50340000c613140c542651801181c801015400400c041c0b04050b0580300f0340390004400d0005500b0002d499000035035502481b500180100d40350569207206d0501c64001e00c08481e031152511000f4a040503520709042e80920036203a161090200019001103010100d5880503040351 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 951008030 1250 951006780 951006803
    0x60c020108012603070c0905060922140f010501050a0807060804060b040e03030f040501200d111c020903010510050a1403030f0d0902040e030a12050a0608031b010c03020304 76
    0x100d5283d4211040802c0b800007450389080344840d04051005140680c0304100c0c0e031201c1410054110101c82c00100014001c2030782c41c0600c001200642244a0340030000260394995140c5072524000c00454091110550300c0b9480c140308200c0c40640000c6d051740c80603103000d020a81e440010035a41c500c280302e8000450064008100440c80c180c2240700b00d82c40250001c18060710340c0300c00a286500460380c1c00705040c140300600c03003000350a0103115507101c1d15030001658010002d005141922503182c945c984140d40e180c0c7c0e01141c6031884240c820f62507014118002090743c5881c00c0f4040d50204210500c40e52802000030052840c0300d501005581c0f0150000b5016810880880c80300030780601e1643d4584804d11030628913040c024014079480101e48800b01d11018a07205100981f440b010414505400512a000900d41d2080306503080140341c9001240719110340903142c000b44000d0b04482201d010000707624000748110090080004500c900030000c0e04c036110300440803804161402082d6a00380c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 951009280 1250 951008030 951008039
    0xa06051209011413031806090b030702100507110f1c0f090504020711180402060901120605060d0c1e0219060f050a2009180712090302010b0a060c02010801 68
    0x8040d5168405030800000410b0714150550700410b400859031100e00700b441468003020194804400c0d101150900e1008a03201d040100103803244169000d070068000001c0001000b070b030f00c01c10070052104581744040001c0d003800c07030004040c12154841441e55101e4614240300303030007001401088854680c580400c0303005100b08111041c1044003044020801d0a40c0c01081f650b58610091190b68818401c0d200d902414006101c01c441040300b805403102c200b10100300241c1c80e21000c940000b442403a02045045401503144014003042e00010340001010a0348088600d86078407001003c0c5550715285032020320741d41100c421325200b0b5a654010307040010605460035030039074488203461251102140040f82c54042108442003102c0d540300d03540e11360300350420310100318071503140000c4080410fa00d840990004a151502d00680400c045501c2c0000181140d00c110900c0c2c18540c0c3d03102061010b042c00b0304001340a0880318806910910003000d001a10714040c1011200b143c0d4181c4a0b03010983c41c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 951010530 1250 951009280 951009307
    0x7051005070503130905101e06030b0307090f15050319060f1404060c08010f120f06091a0105040528110405130213050406030b010e070c2f0a0605 64
    0x440c0007290b061105006040001c0740c106000c2c40a880d48410001e482c0c901002e071f260041070305038482290380c034010f94001c000b440ea00e815607086d01d04504000c00c3c10300c2c00c034000c20302d8405540c0c00301500030b107440309202c590b2900c0d40010104201002d5103601d09a2184101602c40e602c0008001c0100f406445840c0091502c2e08581070120117031400040318070414651300e003900790495044035502d944c0d14028024541091405014240c0505408191420581c0000105c04903a00280005402a070031108128980c1c00600229078041800c03400606083c1262070310310002c0c05502d1045d414100002c1d0760000d40a00c0034083d982c841d5000a100b104510402c000f4074015203021054203042001103915120182606941103617144010394940c04000a980d0811480c0c00542c030440c180142013011030f082940c56415502d441c0e03099840b03034403031040990b2040c0c40c840001b40201c00700c020000d9018170303003802d000700040102500c03240c120309581001804805800340e200420024015035094014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 951011780 1250 951010530 951010537
    0x3090117042f03010e01060f0512010f0606050c060705031608040c0e09030a11030403020303041701060e0f04030206130503190c0206070c080d0203090306060f0f0918010c0207051005 80
    0x10701c0414400c84402c48007014000402c00b01d4030902010150116900d081c244650f020403003c0030020850320b4100303e201450b418007440795600c0f5144190484800d044294002e40c04090300e048104040c40d80c0d040d0207030841d00032070310f042820302500d0000b8a45900400c201ca100d11100c4091040c40c0d031800138151400038011f04282ca08149015020800303031844078100d405103070304400454495002c102e00810307031054818030b00081d400c180410801a01c00002340d03400e44110800c101a007008507a085801003a990b80501c2e100302c950024810010148034405024170702076400e95510b0f950b10707200004240b813040d000600680c410071413030170604131100b038200003148149007540c1ca28a0760b400091146d00102c40c10f85541c2d84001c03041040c07203000c00000c1901a40d90020b11300b00b004180020f911250001c21803030042901c600c80048503075445001c447c058600918002403820f201d41d00240d07030400b11080281035842c000e91240d0190000800000720340c0c004200d4505e0100d10b5404540981 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 951013030 1250 951011780 951011783
    0x141905070812070518040b0310020f0d050709060f0509010c15020d0f0c170405100b040902041503060b061303020f0d02060d0507020d050a1d0a0b0f0310080309011704 73
    0xd0040c0484440e1a982c4603003103015103035954070140c0b6442c0035100d0400844c1e500c541988030f141b03800e040100c60f407030100c0d07400139565422000685a40154a4002d01c03882190042c2e01c8003440d01d420001903640050014058035060360f14411140210003050f038551042c42c00481c0414410f41c6c00d03800044044000c1d0783c5072140c601001d03040051888030b51054a2445203880c00e6103440d1142c1ca0032055002075010044916411341521508198846548030300007100820040707620349500c10107075115500705180c4030360f0149c4100428060f495615000c4141170008903105414041001075038075000d800e80b0804109281d05105c100d00c1d51f0b080000000b50100c50765040020081c0a401680e500d40107442c11091948001c85c55203400c90009041c500307100e89401c20b000301401318000c0780d94085141c8a107012641e1000d41030110440000c0d14046031741c1e203c0c004d286800200301107141700e60800f40d806500300c2d07030fa100c4031251075400d0356480f0b0203480d0f803040c0003405103c24000c400340050495034219 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 951014280 1250 951013030 951013043
    0x17042102010e03190506060102010209060307051305210f011505280f03030e09070e0907210209040510120b0703020904051006110604030e0f06040f06080714190507 72
    0x2446503601090401d0321804e000f8003c1d42c9683c0c0749000380101445170325170000092008500d00041d540c0094000e00002e000b07801001000304038807031007204800020f009404010408541d0140e440d003110308811814200480501640580b91031615050044509283d05681c110b126a41480305102219000008503c115031909040941ca40039040692014000003001c11010074103600340074041d85103a4080601403980c00042001e4203510211100c1c6801d42103809603403e49600c58203c91103c0f074054100440e001c0e4640e00c07546070700c0e01c0e4010510840243d07001d009543c0c0b10100704444e040b0030703c1401c028a8074283c5030000035940c81c4545500082c5401e00509110110004c14110360088807804109000d00030140b06a940000d4400c03044c5495000030b2249180035a030081200d100b43d500d02d80a0301c01c503054030480351b5885040d03d01820b668691445143e558050041c842003003a01c034100841c4d158185081c5030704014046448446054000501c0024100002c846a600c034880c2038a18 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 951015530 1250 951014280 951014297
    0xe0a232508071d090a0b0111070501050f0315030607020c0307440d090f0e090a03050a0309061503020a0b03220303090206210907061707090302030a030203071704210201 74
    0x5584d40c410100d80640382e4600001418451040090140e01d0382c4a4410070a80c0405000c02081e0b038030031308035070207127108143d03507901c0380c4070208100e0720591201380c10350b4103005a00802c16170700c0d4000364070b10701880d00720308a51107940d039000c189044850b1141d0034070318080c0361306021036914101c140c3c0d0030000c2041d1540703010600995106074140216a102ca0000501d05a8204a00107a8100e100060308107100604901d0811440e8980c0d00c03611100001c003800008610001c040d8040c1e8040c6207115080380d0103000c000162038103544198420301003284100c010300000729001f000c0c042583d00c01d01030310080820b42c1100100c0d0002c01400c0c00411800c25403507904850050f00c8500c0901607070ba03448942c1000d4560121945480510004c00c0b00741c15900c0343c5420461207503c1900c0400d0030b212000040c030340b5260b0403011601d481e0503810282d003501c1506440b4040544c0080240402e41c001c5001e07042940c0100704c0304041d0312462254850140304c801e01c3c12281c01e00381c0d160854140c41410403804 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 951016780 1250 951015530 951015587
    0x140310080709140612100b0616150e0307050a20150d06060f020307062f0a1803030906080a151818030203040e0a23250807 54
    0xc1c10000380c010b03607038940c0c80b416640d0441242c000841c0d00000308880412089402d0600c1d01c0d521b0303c1c007411810019440305940c501a4480c4411074450303813405094410707083c585042c0003070001c080351941c240341c6241101546012002200351a07840c1d078418090060300700c1c1d9845140310030b005031040300d01665001803e40225501c2d00606400010102986c07601d4440b8100d002d012200c41c1c0d800a002c0c0100c580d10101140c1c0d01000b01d51000b42e10603400640c03d81d0304840032404800004040980c0302d0ba10548580b1a0f00c803a000e0702e805500e41d525814030542003240d84821030a207110040204080c12814807181d4011400651300551a541c005142050016031704002c448036408003110300e1800c106205041c0042c0a40d560140c03040301403080111207590300a40d284a14071450142004c080701045941031150080c2c0000580d02e0951070b084140d0f031381680404c440942e00c02e1460b9810a001c0c61540c40340f00d0304110400183d444d035004540e1180320035580c5003194039200c0c4148204025414 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 951018030 1250 951016780 951016783
    0xc030106091e08010c030b040c02060c1b0c03030708040f1d01150e09040b01150203120708090f150604050901050601020a0b1f030b0a0507020f0714012a0c1514031008 73
    0x20041d00d40307942c001c87c040c0110380500040310a503e1458003150080c07070820621040d50812079110825903240d00300000d003892002420410000041c5926000003c2e90005011401e030142c0f0580e04041c611300c80d41c2e0f9441c002001c50546207090710341c10b0100d0a00411140401c10060b1034002260300b03010640701489c03000912171540c01c40b01256280304075001444800d803d071030860428407030307800114503011800c034010000c0e0400501c81c0d020003e45000045584000b88001c010b0b02d61b0301c0044446100070480048080c180032501e440c0250710b800001030720b044050090780e00640741030700607019160366900d4410702900c005045210300702c9044400b8000c0c090000d0102c0044d4024031a0311560705000208106a8201800c040d0840d88901b00495200b800800c000c1c042742c030541450251400706c640143c40c03901d000d40421208042103640c002003a20f204810420a6124507ca07105c06600c4070800850703140121130b0040011007402d044845441003030300030350300300cad030396140c818565950707443e070103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 951019280 1250 951018030 951018041
    0x5160f170c0f1c1d07050d020a080703060209091605090409080f04060302030402030d020f06071206031a060103060803311230050a050703170a090b0c030106091e0801 73
    0x8042c01290034140b03c0c100031452150210070100b281960410300c45900300705075642d4003805028410840351000300d0031941c0307948810000349200c01c15960059aa824040001e4003d6101365002e04128000265849a001ca2802180481e616080e050002010501c4003e00f807040085030404020010301c20f2014880d4040c0004100756900543d480c41c0034414503003001d0002e000d9109540c44003814422148004c902c0c140d10003c03a01d0300c00d240305070040e041c1e8054800783c4c2c005880d0052140b80e045182a1003c0c2c810b00c62304081e00d05020051b914101035a4900c60315000c1c40c0c210f604a14203070001d40c06d50380f103049250040310b2a010072a4640140c2641034942c00011104511a500c0d50381901449140e00d5a4070018201c55407070700100b090015045100c0c17a03201c03800700314000445d142014026011100702840d21804d0341414502400e19a00400d8005400d507001c1d007044000400c01c4041004880c107a41642d13841006003842e15100401d06140e11110500705080a08041803040d42407242c2d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 951020530 1250 951019280 951019297
    0xc030b181c030b1c0b09160f030210182c07090302150301060503010b07050a0b07020708011d0705240f09100e030a03050c07030b0a05160f170c0f 64
    0x2060040d4000c0c1c0014044861110006004580d00411480a01514602400019007020052005507220768580b401d00c044103505001c1c0406805000c64840300503110442a68402e403800358680b4403d10301a80c041002e031000d002c410320707443c0703080c8407401c044030b148640c007003165004041c0800b010b03401c0d0b188603904690310800586803200070410b61516114000e400600c400415296504101c0000c20610050103081d591010006d0500100202000329030089034100d1141682c0d0706142900030748031110380c803070a18950300b04007045401100380d10681103400110f000034074203d480e2006102e44540075550303440f28007000b0050888091054002404101d842102a43e614000d090400ca4000401904141080b41c3c052072100292000101c018003e901803c21584038144003140c5c3d8a8400c968000800c00c0c100b28040c00070448468100a003e403403200e40c030090801c0145421140321210044a01c0050ba1000000310b412144100260b0014103111442e840c0940f28107107001da2358407040d072 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 951021780 1250 951020530 951020563
    0x10172701050a0f11071218031b14121c02210904060e010803070609021f0c050705010804170a0e06040605070204060504180818092508040c030b18 64
    0x110802c141da014481c280d94164136246241c186881034442d80c0c1015103017580b83d000d000c000300400c081031901212241c001c43e484582e0714409007008941c4940c0d02e880340304440158400d644215901d01d0940b00404494104500901950181c918048810780a02c007401055004c2d0b002210f5061000284d010100c082c0001c4140d0b45680c4c030002e03c000c4881c8e551005240201a10041c0f0000c5000b2080300d6a0580103c800b00d0809090300020300701c100e0303407000320f98229100c1680c00451504186080f660501507401d58584540c0c0c0da00565500301d00301d900406204440d08a02c4030020514064207504003a881c1c043d40d1120b0481c042200c03584140c01800c0407400224800741103182c50f00507040500001e560070b0111311500980710300c8680c002000202035410100701000000c000e0511440010390052040c1d01c5414011101a6020482d0624444001642c044810001d00071180c41d401203900a2031401803e246888262403003c0c00b0f002c0c0d040034211002c0e021010b0340c0401460403004034204c0b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 951023030 1250 951021780 951021791
    0x4110a0804170307120c120e0d08090625030609050f0a20180402070c0905060a29070f05120414010e0d03261510172701050a 55
    0xc000c40c41011045000e542c4003020401c00c070400740d0295003840341c54002a00441c01c0300d41e60800390b49261004c10f150310141d140c081300c010170800000d000c4404a102d51980e881607280c0c0d8030a0b9450b02c2d400ca41554400c0c820079541c62201c00c1003480850502c2d2103180000b8180d80f5458038a00340d403015900c015150b820241404060080381c8103091040d01c0c90b010003402814402003641135401403044a400d020070f40d070342d144900d48036501141d00655112000c51003042d2100c2c2d0f204002c010070786801f07000e00000346010960300d04050312058a50180c240500f140d000740c002004003544000001c4903000f051400e0040000c1041003000800441002981d8484e410100120349500c16a0201c030304100b8540861007039511000c0d00c600580d45c2518013401e403d50307844407011002c00b1004030404104a900300308110000051181441100210390340d551000900000711044081003111145205d0480c020404045101926118414201721f1040c86480411b1810382181d034115103400c00e198841 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 951024280 1250 951023030 951023033
    0x6070b060a0906060302191719090b0a020403050c0d03170a0e030c060403080901090c03120e0d060c261812071505010f06050406030c0909060305030a0206010e060d080904110a0804 79
    0x20484030010000348d24001a82d005991845040804080c2900e800c492181c3c800410000040c1c00902d106a0449005c0b0a141481b510f03000095000b4070090300c05024024040740d441c0340c0400d50300a0a41c1640c1c400390822020070780c603200418003800100d5641c0d42d8080780700c541d0209002a110301f11880020340784034074003401c02412000c00140032200e142d03d020b0140002030b18a907500c0003560341040c10549030845201d815a521132001c0d4105500c030f0540903000c0c00300882900301c42a404d810f59100343e11400a200c1c000c1c60408504842d20a1400c2e0500254036030243c88518441004800e0840d0421081c3c007040b80d04a5010700340c240c0e0340e42080c5026030301401c024021180100414840359001c507281c0400108140a140505400c254031107010100041c4184010303005000c05020803c003041c0e4a1070040d559621582460740540a044000100c04100d050f40c60700c114005001c1b1490010307181c4d01e26806501c0701d400d0a070710a6840d507003002c60303160340e01c0a00940085034a851506003001d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 951025530 1250 951024280 951024307
    0x303192f011a0307080706030207050c1f120b0105030a0b0409080a090518250c02091015020c01090b0c070315140f160806030c0d0b07030b0105070206070b060a0906060302 75
    0x1142c1982c020b50190b00c080140540003e0110100c030102e2800680301c1086161447c20550020035440e80041c84c13a141284592600f02c034506142d00076154200c84501d120114003d640701000c490b40401c60074800642c040400b40c0001502000040001501c140301c0c1c1d07100200b43d040460040d00203900c845080c0028180032040d0f003942d08090846d402d051070b01c05c0214030203484080391419009000500d00c02214003030894810042c0e40100050341038a000da8841a03281082e10076035061400121248074154008150104070307481c1a074403d034100381480b0322003206a11142d10100d1510030981c001002c03035141040b410450704d140b540410120100e44030107020081c0900340e00401030590782030190044840244813001c01860400c007080782c2c0c40b10006802c100344c6205103074214145003046820803004140c004c0c455601da4801300001d002005c01101c0500078198000d400103010009071f008a0040e82d050740d031080000f0600240303039407100c00c0c00040d103460b03500403400b1980204880c030b00350780c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 951026780 1250 951025530 951025571
    0x807051008151c050a080d060603090b010e07090801051602010c050f0712260609010f030506010b2503020304080114060f010804030e040e07140303192f01 68
    0x440c500a0441c0c14024224086180c5541c0b805120324041503200000e81424860540d0264002080d1001e0b9445800c03c0710b0250302c2035161080c072034503004001c581c550103403080a20040c1c1100c840c5642e60300b0100c3e01900b080d40039111034180a20002e000801c5602405828410760781c100e07085030307a442c0c1402c010b800c0d40c610340214020f00005110203100d010341402942d015580144904c0c450f0810044280d03204442d64041c801c0c118102541c40050014200e0007500a04064403120480c8c1ea030f498040c050804c6502008001c0c0d000306004100b07443c170401c094410104504400460a100801046030140c20364400b10b01680011a04101c658428400c0c51800d8000810100b00c924101002802c0ea41c54018807506000d5244082024036204000801d056507020307008103d1840e078208030a540d502140300e41002001241514000c5040100546200d00c0f01109442403013141e81501380c45000d0070040c034102403035946640070036001045030b12084c1c0d84140000010042c070200c031054076040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 951028030 1250 951026780 951026809
    0xf0703050403020c190305061b0f0f040f060c020a080606011b02030c0612071407150e0106030204020d150503030a02280f060e0f0d020316020406050d03030c0f02010e061b1201080705 80
    0x1502d100c2758070754541c04078100c0b40b01030030240e501c0340d03030b0307003002c00000140c0c0156006001d040840c4100421541c0d041a003081100d07000300d44900402d69030b4068659a00c5080f1481800203480c9014040032008004d54681013030720040c181c0b188000c2c64008122581c21074040c00560010301c005104c0391980002d829510000e0107010035180c640c1a445107400601d4500c9110a13195031000304413101b59007035001402969008006642d516001d82e1040e000d0220707821102c100e12403001c0001076134600041140d03800800c40d00074103a00c0305140c0305060110001404410001080105940000c00c0905a0481d0502c510360020b010303c4005132452030011540f5458080e903210800c44050560004152031a440e000204101450343e20300c081005810258440d07a00a005000c0100805405030400440800544e0ba001c4010440103030417400c2e81c00729045e0183c0c603001400800e0041c605003800c0c490201414102c9490b18501c0c1001c121201c81c240d0242c40c0303d40140d0303070901040ca00b14119180c0725 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 951029280 1250 951028030 951028051
    0xf050f0609090106030224270a0506270310020a0302250c0905060d082106151608220e060a0b0f0d110412060609050f0703050403020c19030506 63
    0x9821035011442860080071f4406650000308a516142ca065004550714000d60307502055040c00101c3c0c40850b840d605401c11849003102e080c0109450030a40107440c030200c41c6412410303c40c0f900032a2410441c01d00d10780b06400d4050203070b050b15242b1142c0024860340c1c250b03540051350b4440324154035075043c0d0003280072045102224050710200f055141000701f0f6420342d16000400d1f0325044001042d000320b00c14014601c0b0b40124074170300d240003040105203c2e503070030508009803651340c1000c0000702c4071035100a82072184148103881c0580b1440010681052245d0201c500d00b26251a071094126018050081d802e00021030501005890131080f5030000c006130352580032241014803410081c01510550b6400e03da000c211401c60003000c0c0c1001c60400050a0039a1381c03a512581c020040c522400c00980d80a070070040001070300e086074800c040c407407018040c9030403098844003001c601405024005a0440c4182810800c040d03072102a0b0300e80307200410410302040c03482d51802c142020001017030000103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 951030530 1250 951029280 951029291
    0x5040c03060503060f0604061208031e01050d0605060d150917090d020906060403140d0801060c0c210606081b0f0a030206030c1c0501031a060a090f0f050f06090901 72
    0x42e0f200010700c2c0750081e00102d031085050b602c0b180890010100381e41f10164a68603608484180b090460044d40906070350388108101d5110040d061040c8003007031149940144142e501c00000c99165400140c0080c0d0040100010551948a4286c2050f20103901c1009a54402c0e0503410041021041ca066022000d645410450360394009000c41d900d4543c00381c000c6c02200c00041b200d6682e501140d000e10b80c049072050b010f0006c1f0900d61f03130b112811950380001c2680c160000c0381203802880040000d036802620b90050303d0504820741f409070410b189201c2400c0440c06c0c0c0f1400118680580b8001d400c0641c01400f804943c4608a181d425646644501407108140030350480c0d291078840f002620340607120700f0783d01d46070a2604040742c0725030385003500989120f01c0101260340d0075030051b1303040300d018140a045840088a42c07800c2e11105989056012001a40c05c001c108016081079403408048000080d4400d0b0013140502500e80031284d004802c01c400080146520748a44042c1d0440f4182000b00300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 951031780 1250 951030530 951030539
    0x321050601091511010c0e01020607081b0906090d03080a0b09040203060106030e0a060203010305060403090803120115110111090117040809060f071a0a11090a17010b090408030105040c0306 83
    0x50140902482c10394240301400039600b60f0282d0300306445596011300800030002001c00c000c00e0042d810300e10714011b02030385010401351849000518000c080c05403080402c1a0001c215110592000d41943d411a50030300200802c0e83d200001290028020344a464280c640500c104007100c41810041e07210b220800244005610b0006043d41903a40c14103001411840711030126142184001008001500001c004030400c80c02184182c085c91180e29008030382519182020788a0150302c1050000c840c122004204061001094003145d040d907040001c0240241c407113203030a4860b0740e407c0710030b514030000b00043e01e568801c906a007850300800207003140d4105070f5940d080f58411a500c181c840c3c1c802188002885050b0000ca83d22150f1007044440d407100c042e900205081001c0303030043c400d6850007403200450301e13100c4100c1c2c0340b6400090401c8421410034601c8080031415501c6001190350300d040c250151380b910b4800502543c0125082901c9601d41020013003590400c00b400000c150a1220812 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 951033030 1250 951031780 951031787
    0x5040807050d0302010b0a0305030403051005070e01031116060516050901090311040f06081c090f12080409050c180f0604030609050a061b18080a03080c0f070321050601 74
    0xd059400c116070101e6030050301d0030100e015010800006034001d00c6c100d000010032000000400440c0c0c414030030740e10000710147e4500c0449004581c403c001c80d803088405403c0d580320350300002611442c0c1c007170b0500b06504080c2d24030703010001d40d204882182ea038509004074440540506a078544031440c3c0980340c80d16210000b000035900d80300083c0044610301e0780070820b95481d00110350000410804102e500d54500304a6651102d881b0407010817100e020100c040e46119802410030b0320040c5c61560142072505403d4100710707030071000c10703200745030240004075585440707002e0240202c0043c200551121a20b040314550304220500040c07280e0950303141c211150319940f00340c03002c036508108005100691400c1c070500b40304c00b006000f00811f1810840744aa8940c802c20743c04590015540c4540095092100c078140c0074041c0603901d100e601042003000003a204886041e40000c0c00d91140e803d04803141d014421030f03000b0803011804a04001c103060b00503c4e41c60300c00075625078a04020301c81070034143d0018 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 951034280 1250 951033030 951033043
    0xf032b0219020109210614150a05060306060d090c09090c08070e1306020c060a050a0f11040504020307021504030203041d150f030c030303011211101e091e1401050408 73
    0x41213601035482001c214922075035504003454200d1b44c1403100051509803010080c00840b1908000070b20001c900c1100d0810740c0259080ea90003800300d500d191174200c10420103801c8207550005458030340c0b415100044e417550012000301924503000c00d02c1d54280c50b1040c4007110b80d412a85447e401002c0030454100400c0a10b90000c0d41030080c0c40805e150341c01c01c0c0020307100b10500700c0054801e550900540c00001e9004512032a00010200403900c5402140c900351401d075000300b810f200c028130041c4040e1038035a005540041c42401203c101d00d001d00300340380802508403401e9016070008901000540c070450010049294044904500c2d4901030981851015101d803c1a010301442c0315900b240382c40c02c0080c0f4080400003401c50fa225a5260024006c02c0c0500400300ca0b040c80d481060911030401540d000000545901c609054000c018010307089280000c0560b030412a1017135000442e6190031030451140c2d4107841c0c240060604081145880400907034202d810007030204810070030480c0100740c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 951035530 1250 951034280 951034289
    0x5071b030c020f030615040b040c020312060613060c020316060c030c140717010b1807050d0b040507200d1b062c01050907140f032b0219020109 63
    0x101c0004a8180049404100e0031103002d5014420102441504ca640e18044440ca59045409005400c40801407006545007070520030003603402400f84641c3c4040182c103940d401030024080c2401c0c0128204a07400318500707a80b0001c04540803680031000d5050620004141c82110b80842908516040c0e00501044040c0005820016103818080030407004a81c2580c2040c100022076040a40b101000e82d4010043c03402a802e6610702608001142401c403015203c544c0340c500303602c00c0e83c0d8502005071900c4d80f1450300300442d252354030b054100c9980c031442014013030fa550350350b0303140002c60000442050f441620500e050310740c440a41c00c0303c40c0d9800300b036002a070880d01e0301445011000d86401030103040c1310302e2810494001036000c8028640741030880005850480000d1080d5100c0200c100c0e110513030750041e4000d001036020059030703c0c02c0200050f0720384a000303000c442d2020080202d503840310100d45c0540c1681504040002c5d07815a04100b11903404d505640c15080041495001030320360041e610a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 951036780 1250 951035530 951035537
    0x1703130b0601030b03030a09080c100203040b03070e2d150904020904020d1107200d030e1f1806050301180e07212f150f0d0e0105071b03 60
    0x501d00780d00c00d820906806002a0440740c0710780e40e690000e0151003150182d1581172040004038260f91500c068000501c22142d005145458100302e00f25142d0340c170040c000e00c148110300b004140c65403520100c0c0044007074491150286500020510354503032940c428094800d1042201c42100c0581020450300d00300710460700180d8032036102020402901650b5800c403c1c507450614964a03180c1d070b600050008070300c035511036217512140705e80c0c12202d20300c603072041608102030380311200010b030042c0d0b82c0d141c40d1000207042da503161421204540c0481c400f103440d9070000300310380030300100c860100c0d00950140009040c00b40c00c541c184004010012461410400030b030303880c1ca495007240340051208501411000900038951805a00e180c20702803d030b41c2d030464041006a40c0ca005108200448030741406107034004a461031014010060401c6c1c81d07902c0c900c2c0b0440104045202242948028031144002c84c401144151304814002d0844074010182030900c5503140495520000c040301d21105541d0508 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 951038030 1250 951036780 951036803
    0x708070314060918120702040b0a120f020d061503020a050f030c060d060f030f15140615040915050901050f061b01020f0c010e01051f1403010b100804170313 69
    0x6858000c030301042803461002e000ba200403240c0040c854008048247c000e5909201c0b0230488410311044807200c0c0300d0710301644a01d6a02d2000201032060f150f4106000a094608502c40c0340c8806e0304440300b6200d4a1046c1c0c4549904100b18100341c4582c50040004803000c0304004800d80c0404c0d200d200600d2518400d0070001043d01e00d0001c02e5020101401c54090b40d412880c0d2245024002d5040c0400c00340e031007507440303002983d00c403c55000c0c48800e04410b20714a14251650030911920742d544c070a0303030b0f40204010f020104501c0340611800902c0c000c01403840c2074140c0761005110000c2010307001382e070103207000c400160101e885510403501d480341c0616904845950303022140740207000b0340c000c8448461001500e00441c0c441504058010568600208a59228900d408030910784100b03c4060505581008000c550661088070701b058801400200c1c0f8803601d20001030088419040080108241400b03010500c00d0406c000081c0c0070100c481c1c1855802c110f07200b04042c0040183c001c10501e4000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 951039280 1250 951038030 951038041
    0x31521032508031603050105030c28080d180801050606070210120203010303050c0615010e010f20010c080c130e04050a0609060506040e0a0b22050a0b07080703140609 73
    0x18400d980290b802042a58481c1864203001811040e0f0b452400006801d140001c070306c500e404100024103d400405081001403c8081c424804580c005082c0403000e20b00d00000c1e107a1800d002501d150383d01c41d510b1404070800d00c00410720740703007041c1c101e100c071607162908002250326004111255940c044480e41103800307140104559207242014140c80260010000004040d0028041c10001da2070100fa100365603204521031010b45401c0c07840b00e0002e4198080b03680c45500600d103034001d100c601d19180040c01010046040e0030f0404a12900351a95140c1030141c03459800142c0c641c00c44070046503d032408205400c1080c2104160259000c100c09900101e810804100690900103a20010510a400080c03d0950007003008070b481038000e80c104900440315200c080b64074540d2a034081248407848c0c9600e0085a010079800c1030400c03000c2d0141a9000124404109101c0420300c1943c2c5030045160200000740f01810140089007810304142c0c500203021069a91154000b8040d2000c03449a92030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 951040530 1250 951039280 951039337
    0x150103050a030c0f0c060f0914030a0602130e09060601030e070f26010e0703020a0906030b0406090609050a290105011e44010302031b060f03152103 65
    0x4414028001c100e1172900152441c3c002c3c481a009081c070b074544203000c0341d942c1ca038902900c80080940c0e82c140c20200d0740c0000100b85501405520340b00340c035001965a2122520340d034000080d98140b10546c0404200149980d00d401441c031030f007440f040a81100d5240c11000c4141c5801e50243e2980c483c14000c2c01c8000c11008108622002a00002840343c0906013022b00e840700100d0005a00a291a10020428103580d002c0c20084070b40c4040d030741c000b50703039a52100d0000b8034090400300d0381c69031504071400c042a410062885000c0c06100c00b4540d0104507804040c100c4001d0b0404146c208560b401000076030780003424424050240c031418000e05100c80022689000d80010314400c001209440314803c00503000c034074504208003504000100080c0109002c600f6013444003e516174842854100340d00c003449245104000e010300141d04048481e0200031590700102e8942c0f030307a181c6c83c501d41c250510f01002002c008880c180d143d48203041a16080c140c403441451307820301601a2409040c08110741 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 951041780 1250 951040530 951040553
    0x90306090602090a14040e01060b1e0c0706090801140c03070507020a0f06020106080c0a0506070210140409020a02061e01140a1203081b040b0a0806041b080702150103050a030c 77
    0x200900b041c0d0a142c56650520707144640b40d8550b40691f140607407040c02e440d4144079010903141c4882d600d904200254030b110b881c040d50598003c1f10a4020f10422000310010040d66009d880b00783c44500c0f1180c100681c3c1800c44109681114001c0f41070310900c003070347d03e001044a03040300315071504680e02c0ca518004a9210341080d0b000d910714080d103c0002802a41c19800081035032403c01c241c400742d030b40030000c005442c0395900a159012008100b0180140752600b0391030a0740c00d031420458031070950744009488a411642c0701183c4207800081d401a115410311007945d10007222400302ca074403140075410310b00185050280d1031072206003082400490790f070410407000605e20a0302d0110f00c04c0d83d43c50020480f000c181d41d50164116840c81110140c051041078800380e030380422000e403c00070507841c102c0d61100043c00d1184c02c6680e0b500c43e4444000004904d51120701c03d07403503003101400c00d04802031802d42001041c0540420030b90040c00081c10214111060607010714040780c6408241c01c0c001c04164 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 951043030 1250 951041780 951041797
    0x4270c08010315020c1e0d020a15091502040605040e0106052b110d0e0c03031c02030604060801180201020c01031a13020c0318102a06020c0316020a05030a0201090306090602 76
    0xc28001c0421070030a03001806e403461305020082d11029406c502042e42e80b5544090000c080e4000b0700b03024a07034940264004250760703000b00c0380c0ca850216a004280102d030b0064010318001400028184507407462400e00900400042c50460319010701125040c01c10506260110040e003511303040f000b40c424441d00300c04503004c002400155121002072420700104100700c3d02400c0c1c0d0168404e0315855150210644041340000c41410b4580c820207080381e4001e51002b040700342d009503115404030340401c09228180d84034110100554180c00c0c94000680345c2003440c00c0c07003410103003010750300e0309060821001c02402041c1600c6143c0314500c5101703c400a07002c0c045070003440f03100102e804025084000700040f2000c005a034036403000e440e1050201c0d810720512510341c9a454007644024120103038004e0a241e1280110300c01800c164a28040383d08580c0300c841d6011140340300b194650f05500d00404103400410b0203c0c020544403842d0707030020f84950410320001c2e01b10baaa84580c102803200680495a884 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 951044280 1250 951043030 951043033
    0x60d020118060306150813110409150c02150c1e040b07080415020a0c1203022a13020a23040308040b0a08101a0c100204270c08010315020c 61
    0x2a49502c0000d00604ca503100f00714080740380345540043c0307a0140c00003601449000c182d102c00070980d51030f02c00d401c00104013055045a502d10810380400e07044440c017001c11060100210b1006000307a002441d18808180003480c072036443c824855001e070b5803012550b0b144141440882d0000e45001025042c6c00f442e44265069000010000d0420803070700020003e581d0312004021500c0120b620032652414202d0b4000d003103c0150b030b810700000801800b200402d41c400d20440780b886046001c03c1d0310b4117800e1071108140500045c1c0310401454040f585041e503191a01046003030079048003000700796161000c075151718401d2a0a8044c0c0000c810b2085602854001c1d000c0c80ea44d65503a042c609281c1c0c00441d1100c009904030010844408850704100200c402901481c0e038a89102000d845a66002950329541c07441141d050380e0350820a4000303000104044000e80c410550440d40d03000340125007002500d03009203019000300300b5130b402c100001d05403a00889001016180c01d504007000f07104080030002c0a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 951045530 1250 951044280 951044327
    0x43b01140108070e0906063d020d030605150d05091603030237081606060e040b16050f0a030e06090703140a08071209032a0e010608060d0201 62
    0x42c440001c1c3c00c40403598004a508544da55080500e0784500e02650346503400746002494002c0f07001074041c0b40c0d014402e06604082e141c0039040c41c1090b9880d1020f04580542c00c0028201c660581610803e002030905460700580c5058000c10340c406440fa200301d5116007980d032004124251000c000e03e00345801e0070b4400c00c03a015142c0c18042c3d914500c45206403181d0042400074074819001d81d2022940c025940b4100320b003141190b40b0308040750800805145040c0e03210584a02080160103000c004140500e50707403905091a00300103402d0100100b801c42d120070818480b11909038803004031280290b013403410a84909031614101c0241c0b003402d00688441c400c0c10140400d92501103804e001b181d2042c2c000c01400c0000f10340494990ba00c0b1100a03203c3c240910404021460301107c0b0b500c4031510349888203400d512641c2c1d241045000810b01072140480071511f40c204079850003070102901103003030344101c2c9602d0203030000c03c04040100308502600c04200302c0360459006984000300e01361007494603441d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 951046780 1250 951045530 951045539
    0x3041e0b0f040b0a02090d030c020112090609020a06020a2d02090a0e01050a1104121118240a03080706060e011e0506090f010809030c030a030902043b011401 69
    0x15662055078140c0e40300183c0c0003c00c0803400c280c801c489000f40c014101340700502050300c05071450003140c0c1e41641403000c1000040300c00340082c030a80d00d40c03600c5100c00103111007486c014403441d40203581045042d50300590004020681c5104541d058066640030b03201e0802d01d080141545100056009401854541c01d01076684519001282d03042104030003005a90740303081c210340990700f90208140d05814204010310050003042c0001203c140101d059a008140c0324011078030000f6100440b42c2545160020b0284070b10f1201d1444080c24110011849102400e20014040001030700c0020400e10001650340108811307600160001d200b51040d0a100f580d580d511003020303105101220480c00d40134600072505107002001c2c3c0e154500050000f5542c000403100640c0d2090001d052000c1c2c83c882400415400b440800080c440784050340e40c046809500c41c4103002c01d0310301d550200c801c40c01d42d08050014000c8010b85001c0c3e007158007242c0504c1a804200b445006151801d020401500d0a400208 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 951048030 1250 951046780 951046801
    0x190312031406090115050a05040b0705030a0f0801080318011803053f070c0812040614070302060f10032001020601170a030302072a0f05040c020303041e0b 68
    0x41d40403034001c4400a55030b08020004210002d000307018a040000f010700045900ca00d0180584942d0307824490314160f01c1d0031181542d500010f82c100c035581d2001030000002c903405460410b2400719414007280c2e650600d011651203000e4125410400032072010410060fa10411100d031010303100003c40c511141c0c803418040d480b0044405002c400400590ba00055112504520415401c040070b00e044030200f070081e19105644550401d468401c0c0b9200c0118260304180f00c0100c13003100c10102160784a00e4104064858241d55880300f9895109101000c0401c0e00412030b544c0c44103901046080540d15640d00c8914084140c2010703003d805108204101031a0070006003907094426000c03100d10b80c0c0e81d001d04a812091694800e01150005003005002070301a802a01001c2d10a60250300d007860070740f018050307452021000c92b6000f1b07964901005000000a007600103808160b070700b8415607040d050041d40d00d02c00540000d02150301d05034406004108441c500d091070b40d00400341c1155050201c22003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 951049280 1250 951048030 951048041
    0x50f0405121c11060a0b031203190501051804030c0201050408010608030909060406060903080a02030d0c0f030c02030c0a0201080a09080c0a050f0705090403080a110a020321060f19031203 82
    0x1044440d04110300c8416243c0a000c00394111428080245a40d50324015400c0c0a019950161600b40c82091030890051040002940c4143c03900c10268500700d00e842c0510050300c0042c4c5c07007140555090700060760140c06007a0560741c86078140c180343c14031034600d100481e5148182d0307020114652800001040030b035008402441106421580d2801c152190350800048030182d220f0b03440400c10300c01c070400c0020b00003405000d104083d030041c0ca007440000b210541c00d0b20111000c1e200068418030f40742840301e41510410004507011300c01941020350f4491070030780d107800c0000043d040c4048a030000722140565042060600c5d803000040e07032210300c5050042e40d601c0307104000f2030741406440a103001c00807002420400300c1d00024040490394455807010f5070a0341000e00101c01554076850186010919179000306400c880c940c0c0115910104200b03e00c0e0080c10461050700701403210800d0081b2507031411078510b00004100c501160418164540c561020310300e80c03001740603900e208a2079041c6a05503000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 951050530 1250 951049280 951049303
    0x70e09071d04110a03150f12051c081603050f2a0c0c090c1c0203040618030e01030f0b0307031e0b0a0605040605010c15240905010602010e0a0c06050f040512 69
    0x5106c01080044e41c4e044581e84c5004004051010060401c0040241000c00308054081e4085c1d40528116031041e03810a8003a400420204d8500420300c0b021401032015608454401d10f0304100d00d0030801c1c50800b110401421203070342d0801200080400306080b0060f030688012051186a51303104040050362501c00d40414644100e0f40c8400068084150384226203003608024107600301d1500800c84007001b50000781c02039404594440c031014114803071084102e80d1600a48030302a40d0110391000500383e4001890b40c169540c14184c01c0452a10002a25000d0fa5413080c03406895190483c1c3c4205000c149460160049050009101c4801c41a81c002070070348009039014000c3c0e03911000155519103900318010320504c2124540f082c85803055211420440d110003140310408040700c142000070180707270080407a882e41c1d04010132806809110b803010031840080500325507203a40e1503001c1c030f400c41e03442154280500020500200a80401100d01504009000d50350b1011422039882e50b40480010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 951051780 1250 951050530 951050537
    0x203040c170703081909080a0302061902090109210b0a0f060608010305030324100201050a050f01060504031506090903020102091e060d020d180b0f070e09071d04110a 73
    0xa100e62036040200b00700050b290442499490014036074420209035000e4003200b020031102d81408075080c40c05200824186010394000e110b5400d00c440405520000401d8030b4040c507104202d840f1503a60071002d04c84c222800301c581d103136a03c40584402001200550002440740d4507103410421100c2c0181d2121751443c10140701000391548406003038481c04820700000e02903920038000580c40b64504055800c88582000000b40c01124100220715551503280c40000541d440350100602da85903403180a5000300e0002103130002d945030406c060158496170201030540d80c169208030290303009036000359000b8250502c00300806541410028000d401c8050036074030801909010781610001d103401603981c0400100399500d0310661040c03070802580041813500710644c0320743c4041840f0b80000100b61842d07001d903480780c2151030040d05901070608020b00810070f100c01030710040242c2d101c0d205a0355100c0040d082c20140d500c024903c1c1d14501110b100c2c51684503040042c10b0440700c85620150100104549 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 951053030 1250 951051780 951051809
    0x10080415060e15150f031b0d02040e061e1315060f120b0a1401020c031006030b07050f0904051302090408221d061c0b0f0604020a0905011808010203040c 67
    0x1e0410104c0c1d140c0340c440c44900003041c01442086100300c1c0c011600001e620920020b900740c90074503001c540c1c03c20b280e200b00082d4049800c004c5014170000030340c0d1002040f40d000c1080341d151080440d094155211050113403c100004013541d0322981c1c40a0070481003c91003044ad40e660302c0b0010701d000724075100c100c0020840d140c0c05030040340c140603c811b50308004100300011400d0a04003400500b5041d619411482401500c03040b0361003d00203034001e20940e0502054440c02c504103000c8181000e480942004020015028030812440507206522002c850100e81c0340ca90381e04980d2507810000d03020758013540142c240400c0200c064002c02c24030b450008140040100031180c2c0040e16128030400316120b07200000d41d004095582451680100e0003407007007180c00401c01860341e01c84132080c0308840f607483d46401d010300d01c946100e10592010048a0a528029911b6070003095104c0c24410a818800c7d002885001c0103c40c03400b01d00601070000c000c40d12494103040c11000c0c4440c40c450040c1d080d0000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 951054280 1250 951053030 951053071
    0xd1103070f080f06100203070c0b030105150406141602090a14010f06091a0f030406061a04050f10030e0f0319140301060f0207172a10080415060e 64
    0x20a001440b40801a0303e248455a480c000d000c010702c45a0001d10442c081000010001803c00c004c030f0b4060001d080d11a42c0b60f6040905204032150b880c200d88400c1501807004121340380c0d01c842c11b00b0040100101094482c600d4007040150b9205402c07009510540003410001c2c054106e5003c00308c00e01c030000c00000305036a01c01c0c0000d03a408a5009003000111080c2040c0b18100044050190304010204900e03d0f1103034501c01c0c080c0ca5081075038100c070029102c801c02c1003000009180d40c02000c9280d2000ea242a2512000415484540c49070700e000d03c03200d185070101180640d1020b60221400804d5640003901e80ca5015160b0380031000190700012860914a0b04501c100c40c0030300c103508148045071442c0d090520542c2c0e00315003100f050f0210700c0340d1040401d200c0c002c60401000c0303480983c010f106941c4100031040040c2c40071005610b224a48046052240c0e41d444000101041d40b07042280c55a152030400c0c010407005c0c01400301c0c4060802000050b801c101031521441540e02030004051400c0300b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 951055530 1250 951054280 951054287
    0x260421050a0f060f060b130b160501060f0e09060c0712020a0204020d091704050d140106080304151d011e030605040203041b0608070e0f010c020409050c0307060c0b0a110d1103070f 79
    0x1100d56400d261047c54030700780801d000c507100400b00d031202c0c20a07018450242c1d5a40c0703400d46006030004100035280c903034204a07081d401c243d580e400c080e0b1000038005518140c0900c03080341c0503005010701685249481e00031400c1c003e02c5047c050980140040d55282e201d40700c00380182845000441c1c252001d10882000741038004182c0381907480080203840c6132400c1e5140d008498010946500f1155079800f00091514420002030004080111031114003c0159002a241c08100c00c6180418488000c801c04980c1e809410151501048607280c5082c00491000b01d005141035040300d034200e8400401c0c0001d01c0f80f0001c00c294030011045034180c1403503d61008554425094542c075021442403c403c4840b4600402d110b2894881031406400100c1e05400040c2600c0d00140d0542d210303088054240b00d10300f418409031000c0c7c1081c5c2440c4544190315a5200c840100060444008a983e0135800c050b11800c2d50480d408100f4124040c4101c140c03074078001d50540c1c829180d86c40030034909651490034500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 951056780 1250 951055530 951055537
    0x80105010f05031b040509030409020d1a01020d021203100e091005060102190f030311070c06023307020c030a03050d050a06080d080702030c0a260421050a0f060f060b 73
    0x1e941d60304d050724071442050001901c0040c0904800340020302010a00204920190030425203103c80802d2130044040c15040d800d2040410a0442d0001d80700c100005030000303491a040610f003080160780383e0b1410000b0000040c1078020702c280b580d0030420300040503000680748030880d01c0d01904114079124a4010f980c0c400c640c100c145d9940702c1881020300410300802d8900d810b41e004c3c0c02d0200c2c1000d04416682d005030722001c01101c00c215090710030b00c6216410407001e02c61754a0b614070300c0c90101c0300310302401050070381ca550301001c003d00100190f038107482400000c0311140d02070300303c8440d6469464041c0690708800031800d482403600f00060480d0b0000e029403012030f41d0b40d401401d44a001d500044a900200074440825480100003501098804121101c4210700540c8106400d45210901c80e458890300004106040d100340030501841d542e080700907001142c81c0d50505a04190b0346080303400c0030340500c0050000703407124070b0fa5020700503150040c003841c0540003010480d068982090203002d00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 951058030 1250 951056780 951056803
    0x50d0c020f0d030e2a212a12010e03030f160302040521070308130e0603010525120213050f0102070305120703092c0a02190f1701080105010f0503 64
    0xc0c00625500b51000c0642134400c10b0303100000b04c10b40008007010205110784424420406c2250081d01008240c01080c0314500702804440c03006424a95110000b508a075008218240304580495010f0304880003540812005042442945e480b40307010b001c58100140c4c100c520f896003440b240c5100414601c80d00c01c42d070503590024580501c10049070040c944a5003a881071200d1031244031000300100300e040c0c0c042d18446044030726550100c1e042c8a5881440381c00688110b00070303810981802400a403001e58416003481c203c210341c810f065200401c8036a901500c22410345503100041d0b00c1d1448021424035010b40b0030a441c074014400006004a940748403e1102603e1500100c07050786010000200608180e0b00916104420684507100c07200701000305520b40800c0c54401c0129008452280d010581c040705551045040030550343c02c665a0585190740d5008101030f11403410f074054001e8100f0100b0b203054140b2802c0d15038440f002580200020f00a041400404203400201d5240008140c810390 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 951059280 1250 951058030 951058033
    0x60703020903420106020604141911030111120c0906190507020f0d03020601150c0204021602040c0908100207032708070801060f0b070c150e09010911120403050d0c020f0d030e 77
    0x43d81c031901c4070403040029802400e418066891110080018901c02b044054012040b648201c43c03020100b600716048410414804030060010203040c1c071a00d4440c90f03110a0740801c4680d10520f03000010b045114905482401000706030400b00c07250703072110150032035510035a440000c02c948035007001090b030110030000740164000c400500c50004420100381e03580d410303414981c4500c460b6500007001da8104489011040c402042801c2c10b500d054000c43d440c02401b801c05100b680e007450b4102d511000c01c03103440d00010f41c000400c0e4042500c24540e5030313182400c0c19040280c000440203411016211480707440d01a102c1e011002ca205001803240070100d17010aa107c80d0100d2a201010005401130b004c02c2d652042e00a10014850040d80750300d009a00e95550f880f04480304e004100006503038107130480502d0514101070500143c120b44110b880c50444c181000303405a0b80d92808440d03e100f040a880d081f40d0070a210782d82240e40008865a01086840c2038a00c210880e0302e003242200c041c600e645225 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 951060530 1250 951059280 951059293
    0x61203030b191706010b03090a030e060d06090b1e0a170705040504080310060c02090106051c020a111203070819020d060f150207030506070302090342010602 69
    0x80d0107075005009880c0040c2400c4801d4150641d00040c0900a40c032000c0c1c916110391880f48100000d11505000d400b02c031098606508150b81c0855542441c04001010b0144030040201c269540344140c580d02803000b0010f0000f2511584090041c1504024140c064003200d01c40400c1e4140c860b84854400402421100f4080d02d400c031180d0551003a007503400c01c603009886010400f500d460280320301c12030090910540d64108503805031001c205651000003040244060700d00141d65110319241100c405140071610307104440840c000c00c1d078440c4415940300344005680e4884c107030400740b04942c0c80d1046003915002c1414070014240b46c4806c4a45000003007900340013458404460303840074602240032034014144080915030300210790306a002840c4100c0e050100f0451221031100340325407030384640701409000b4610340d40c0903a43c003009002c6c03030306064011441e4869030f00e08204d03490340710a0a1414003080d465204c2910440080b00c3c08010321415078000212804c04000d4090341200d50303640c002c141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 951061780 1250 951060530 951060533
    0x9090603070b0d0f0b090a0203070906020604122f0d030606080f07030c020f0f0a02131e0c1431030309030209060a0e0708090706031a190b03010f180612 67
    0x24204c507159401d5541d6104070001290f100c5002840c42485c00b400011390320f042c2600e000d44807240550003802103520007400c0100081810500100241c07003420400c0d00700c18078007032240c0c0352589001c80381c5800817140c400da0202071000441a1041d02e80340ca00700701d915180d40041300c1104084821a64089002c004108614846da0002100f000c0ca84141c5051403042d54009040008440e6035050b660b0124810205614080c0280c0e90030f007088140801040400c00d5610811440b002400041c03280d9504541e64002e005400a00750010003042481da0340b042140001001120340c00341120318101e02c18000d03612045050f041050780e40645400789480d10350390800c4400e04005150540128107410002241d031002c030441d90086d400c03034881002d24038040c00710b10300c0e020866000d4400c160500a581311a0200107001e646c01c0c50050b00ca120f10014500c0b03c01e0381144103a8001e81040c0c0300003000181f0f41a1400480080d105848444270300010040800c406581050113186000f6503141d0741c04c2e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 951063030 1250 951061780 951061807
    0xb07030608072d0e090a0204231513020a080109060f05010503011a13080a0311071d0916060537110c0a1d0108070b0f030411100509090603070b 63
    0xa00302d103c000104400c2c2e40ca850200e88100070036075041c10141e100881030301c21464240140f29920744c000300110010806503400c00000c8001501031109070561241860351f0341c95560006c8104000b03202c0c255030790500580000e1000109104a112003440c00c1d0010504d2840b142c684412220160b44403400c0d0390901c034131000e60420140e12140704d00c0d4100240c503480040021000d00804844000d01080c41c15414054400c890380b1912036069040803030144985140000c0303003000740559408180c4180d5950703202a1601100f150645165403560500042c2158000000d1440301140451030821803400c1d6100916007022251960300720985462016003107100d80030760a403400080c1c00b11208c0311110400315003180c035560410000070407100d00f0541d00542501005004020302c0c4000c01c5200c0c07038a000b40c0814001e144842c1d40c19000000802d00b407003050303a005140c14000801c7d21303c0c00800d4420107030050b40a01da4450041035006c00060075483c02180302e41c112074054404a240c070314000c80f030742d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 951064280 1250 951063030 951063089
    0x403050309031c0f0c03050903030a1d03070b1b0a09060c0f06051005121603020d020109090608071a1c020d020c03030a02090301050c03310f0b0703060807 68
    0x441d001d1105210781c611490016049480380615034100050505501201c641625040a90303101454140824840d00450000490398040d01c0c2c0e000c00280038450400745400d4240b100c0841c3c00a10010a003d002c1c42032019900b8024040021000c5500d28807940000580c0222185040400d880350000c114460180000c80c0c903c0d0b20a85c0c032450060001d98424086500c01d40b1160142044042d003030056007810400c03094000d8107400104480d4100b642c4080d4032034010300001380a40100f08840c000c590054241c0000790016140038000c0585880c030850340d444452290b0341c0314075000e6920050341190310080301c801c0380304e40c00c00c04c0c80003c0c0302404030040d500071b030001c1804507400c00900707550f15803d201640c02482802009a038801407002014250b4101500282e80c0c01c00c10820b00000c0b000308011441d292120200450350a40c1d10074a03940030400e00340000e0a29541e81c000801046070240c1014411590b6480401c19241c4079800c003503842090f40610521052801401c01040700c074034000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 951065530 1250 951064280 951064291
    0x10f0e0c070227040302100c02031303020d060b030d020138010c2901090606030513031209060e1516121d010e0d0e04090804090504030c02090702030403050c030f030304030503 77
    0x480460301041c422150100004440945c01038100190100c00701c1054022070140d40b08510007503040c80512a0f0504203010240302c02442000501c04440400110341c100c00c1aa130f000806581c980450304001a028091010300b509030302250355040711b0103255809140010704442c9090942c03403080240151404041c0c03400949a201006040fa04061b4808007a0300f000505070b400703c3d03040c1d454604000c0650708280c00039000d15003031008221540860064220309980c06151070315a400e5680b40f00c0d030091000c41d0025000700d00b4280003502c61000090034084015602c0034021050355060210008002404a0040015444015240441d41c0303030f044092084c94030300c40c01d0340c0c2403194400c04d402c403400c0622101081d08141c90030100e05d81c2100130300d183e034402940d051041c45401d82d1034007002e118600414004079565400302c1d007458400c0103070b0400290301038090344071801c0c01d01c1c001e51380e500240700488031403041b000691a00c0c107012a4961010f80458015801c685940d9019512900010305 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 951066780 1250 951065530 951065569
    0x80105060d08030c342303030619030f0602090f040b011209020f10170a151701140c030907060908030d020c0f030708040e01140f010e01031d0303010f0e0c0702 70
    0x100c0d0400e203010300b1103903800045441040b80705c035841c50841440c00300c1c40200070503007146000d280d0584001004481d84020100d4030321300900300e1492001450031039600068400b0b007202e1140c0d41048950b5005103070480381281d03039036410054031080009903142240640e0014000c50302c0365201d011143c0141074640d1004002503d42565100409c00b2155074100b800005510a0f0000d4101c0ca0051800c50700703c88041c00500101802c1003e40310042c0301c2d80b2441150310040c00c49204442000e501c4a04060103451841082e400c0c031904034001904155041034481c010224001025070149030703a5400c94260901841c00c03d052240680002c0d049208040c1c214000c050a000d2081c01c00c1c401044224480e0240316152400c0007a542c2c000c20058005c450a181c94000c4c003005075949003424012201c0c01d1810103d5051002d00482c080c05030b0b0003d10305c00010580b0715491441c008000b442c1600c90420070080020340d100c580d40450b4a041c1c88603141251300704502005800c05104d4000c1e68140c406 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 951068030 1250 951066780 951066817
    0xa0510091d0105041409150a06170f070b0a1718031902100903020604060e0c04021303060e011e0218060c03070b0114010909021b010207080301080105060d08030c 71
    0x1a074510a2218a142800d400024100140b00074641482000300344201180403043c5454040350641c0e60342070300c41d00300004420f104001030055249400c40c4001d0001290404c84960780c81160b19912095414000507500402d4404601ca06024094072060790f155590b0400c1240003006c5021000c40203030030340f480d40a03101c0880044107003c000800004004d0459541c0382d684a860090500241038980c0042030304201d040c0c00425400645580c0242d0481c1000500c40f0320051072a25080b11880d40c0c03500140041030b8411000400c04107441101c1c050901404030400c0d2085c0642200c101e0b070307240e035207510f24a8802d03550441c044d805061407510100c1103404c90b5040310005031903600100b40c010304603440001e51200300700262122600600c050405030321407240060001e0202032071405040b05065010504031046030000308650700c05104030008540c4d42c206030034244040c2e40309004e621050b41c00d11300414180c0c101200e1070016160054009030554945503e900190380c421200758024040c0f51 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 951069280 1250 951068030 951068039
    0x101107050601062012031501020a020913020901080d095003010b062212030c05160b0f0f130e0a110f070204150e0702010c09140a051009 60
    0x410006010b444551500d104070307034004110403c091206101000c041e04212801c000340c07800c05c1c0549401254541040a60b00039600c0101d28180c812070001e507000c05003a0500a2060b58101c002442c240255800729580c1c0c2c0300c026499480c178681011500080500c07404009251120041201540c50a0a2008a04819680d410100d101120f030220803445c210001141301e0b80c25100400c9052054000780720400c400b40000740f543c000d0401e007610083d20413030b0444004030b40703010260103071074446007104d0300790281d0600510484988034221614030499400c0342036000b0a100308000c0b0b61030015a90300d04030b954151f11003260440c1c3c3c41401c1034441485603100d802c0300c01070184082c0550b0b01100b8030615048120f00182c5440c0e0b0000085040b00304080c0100400690850f0040ca40503170700403e401d2401d40544e420b60303046a104003d0008075078240b080d0715a0642084901c031840fa0341e216022a12685014686202107561540c00103c108080126040c8010700381c45861041c2804800d10380d48 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 951070530 1250 951069280 951069283
    0xd170f040b0a1b0c0e091906050f0f010e0a0c110109030c02130b010503040209060d0b070201140c04060507030827030712030e07090203090313090515040e10110705 72
    0x54000340c1c405580854200c4100342d112029181e00000b5601c01102010b0944580001900c0b0340a0515201142d40002e00600e0b41005200c080c8034240002070710101090400200824003542c80074a90000c04005c04d80e014074441e0709038142e42180c0020310380b549594076990000d284400740c017020310107030000c81810500280314002e035650103521540e46003151481040500981440754004d220300c0c000c01d00d6040d99002060366070182d810f4502c0070f0f03d038503030f13800082081802e003000130300008a1804110400b82c0c10340003480c0442c078421f6851010744444203907480501070341c0503600c0010070900001002c207100e80c2d661034111100c07641d2684012081030390172041c2c020000300c900541d40002981d000300290804805505000ba01c0c042050ba802e017045e031911804d16103d074012649d00840821000e000a00c21900355075409407418803020f64415495018000c111000c60202c203940405e0b0700241064001c0701c41404c020806821401f0450240e40000d1071940c1d1039140602c130070b020f9140080e10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 951071780 1250 951070530 951070537
    0x6050c070f0810050c03070207031407030f031d01050301120807061b170907060207032a09050906060d0c050d1104050c04180c0c0206030604200a18050d170f 69
    0x2030001c05440584003c8029006a0707001901c04040e4090400070000e0850303000c204203080d664000305143d14448a02c2c41c80d8501505070f0000341102c210420480c04044d00140d00d200f401039000b01d2851aa09080c00541d180e00091155035440a075003458040061040d00040003c18890040020038191407503002c0301140940129001150380008001c4601c400604400c1e8020480c10081040702c3c10710100940300e060328071000389828156080030010313008680082e030207030030700c90a90000ca543c2c17401c03000c02801c01651445101d0203020041001ca0400002035120316401404a6581914201c00d1001c460000502914a000d502070644551f659602989004001c0301e24000c2c1c54030304001110002074030207c0c0d60203005d81ba08000440c055000814225100d030111802902c075035500000c2000b4060860451240e000383c040d10781da600300c0c00c0c0e001c4c0011f1300e010ba80c0d249130724000300a580304041460142d82d501000a00804001460105646818481d00c1c0e8500f81820009099000c141c3c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 951073030 1250 951071780 951071789
    0x6090203011409031317030910090e09011d0c180702010608012a090e040b0613020a110d18121106031008101a010c030e060c0325080406050c070f 64
    0x82002403484910385013403442e174000e441c0c0c1107441d022007000c0c0018036030b8034400c0c110710901134004528220300c05070040d4403840003400b003001204103c0c5080f1b990b480c024482c0d10000c03400c041140700080b0000300b0004840c0c01c2c401d405000310720b00000c01e055040d10351400600040466481d00004100c6c2c800a00030000307264070303900388140d02c003d80708a80450f82c0d40b030307161481c1008076903a002c00c48411410302160300250000700b00340381a02ca200c00b00d01d42d44216020274034010b0001501c14800ca920034008041d98074642c2c281c8100030044c460072100d20000100412006c20156030078800c0700204007881055900c9169000396968200c030204440f6001103c510f03420360040c80f0308003c800342c02d000c1e2400a20b0120010002d4002403030843c141e500c0100c0c00141004003005401c1d08140c01140e12841542004041c240c40d01184a0701d0b0750340307074402c941c40c85000d4007202c00c0005110784140c011040d103510070903960501d42009000c490303a80040700e15010610600100003906481e00c0310110142 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 951074280 1250 951073030 951073033
    0x26010b0a0306020c060f070f08070216080a1518030305060d1e1106032202010c05120a110d020a0f08091905030c0a0311060901200c0102150403080406090203011409 72
    0x102804d5451a042460040080301042c0c0b6110070131500076441140e405092000c1d0404442585441c80201e281403260703082c000c004580d072603020984500028403c10b0031403007804002d0034450010680c100344e864100c01e45840300040f82c00d0600082c0a80c00c10b9500c411301920840090800d911070451404404940510740031680e9072440078480e0324075540c0e07071480d401c0e01c06902d035081c0500302c00c010081d40d02040e4041c0702340301c41110441e071050b10f08544140e00481101d00360190905124000e510401d411030111f4180b03603621540c2131000c61908080031139a000342c280441552034000264081d09800c81e00b5542c00c018840c1c0c65074032044400366200b80410b2040d840b60518051600e0907200b2603c0074401c242c24002000010891002d507840d5900554000d929103c0070001070300c0b00304000040350641f0400b0340b0347c4012000300103485035021109908443ea50110582026101d1109440240002c3da10800050104a26402003500c80b480a0000035940c1c41c1c1540300740b040e000984240c0032a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 951075530 1250 951074280 951074287
    0xf020d020406080c0304110d0f240b030a0209010e06031c030f050f04020a0308182716090b25030315140108010909060e060c070b1026010b0a030602 65
    0x280b0b81d00c0181d51303030b1000c200c507081c500e1800e1540301e0280000b840b85049100b840700403c2001040103120082070b0702a800313124082c1c0103001d007000c00c0035112080c40ca00122850704a00d05403a150001d000028113402600c000c002e642000031a00d1107403801407109070544900407111a689610a41b074000090207541c0000f0f8a0301104903081c01d071000600b2182c003c14540d406e11003d603541c500b121003200e611840301343d0f540501d400707840c21402c0c0050085c0e9000401c1080c1c0003c961810b03903507804034046c1d071603000342d25a03400c440c0f011007959200c0c101000544500c41440316282c4407006281d01900c0380290008803d204412079125450200d0841c00252502029884d0948007840200903060480794040d41c0010139000a0215805100d60119991070300100014450117502110410f0021401d4881a240c441e05295a503407122000302d036901d0118000445000c41c1002c504242d50021210500310081040b401c1002c403940d50211f449956a5440c4080c10f946103c02d040041d40300b440f01585 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 951076780 1250 951075530 951075539
    0x11041a1c0c09091a04020102030a180f0f05040f05130b1003232b081003020301020c030c0d0e010c020f010932060a140d06030b07080f100311040e010f020d0204 70
    0xa200507600d01c0c2d0b0440b04c00a21005030f80204c02e4801001841c6400440340c0140070030b20710881c00b564000c0c2c90300c070695000410320103c09407140c4140c0310306950070300005030908164411100100c4045854511303500b06840000c4012000b076810941c14000441400d4907030303c803041b0200d103500d280e00041488a0f40040d100000780100d4940000c030654044002103540782482e51001401100410050740d100082d203510b0031222068051a00540219254120503030102d40c0c961044105001d20310a040280105900c17643c1301c00183d410607584c90034041c00c607500344041d080c01c68001ca41801051a000700303200800c0c1d52000d0070542a8000c1a00d40342004103000504282c800c0400d0107080200100d600403a08035800d00e204152019009070380c0c6c00a50f241038020b1809400061180320000207000790341d82d004449a000300038850b40140151503010588680c0800743c40700070a0001256948041c514096100c141c01500c010000700d00030900442c4281241d00c200c0b0606050f0368042020b20 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 951078030 1250 951076780 951076793
    0x30f0405030c15041404020d020c070303090e0103050c010e12060a0501050a05030a0c0531050a050f13061805070e040501150605030c0702041b090311041a1c0c0909 72
    0x892030304240c803c0345102c08016010f079801e110368052554502400c101000741e5494540c1211600b5224010841d00c03802180e49135500d90366a4030003030303000071040311000c1010b003840514a812242c0c40001094103401100064525100e4001e44992010501e5281c4003403ea003400341c2841824800000a01507040404001100c0d885422240c0280e003e10200f4000690f2003508005541c030846d0803580c0091107514401812040507074182d4120000303401c54411100c5c5410030b5008088a110074007083e514410300310b40c0b0145c1102c01a00150044010070045051980012280c4450080e1000c5004007922442e160001d40c0d1b214000740d4081400b04020320000388240007a441141d4038458440385080401481404003810911408078005420b80841d030320f503031022440c90240b1445014a071080100680400031910050f2a40002141d660030540b800e0b120f140c1c5200011454a602c4101c003000380154046060303030207a42640c60492003004511241c25a10007851990400b0400080b10328000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 951079136 1106 951078030 951078043
    0x2012c0604030506010f09020c0303192304061109010c1b2102010909050108150405030409060305031b2407031e0e120f040510020f030f040503 63
    0x10403c000030510720704a48006a400c0429981c40c3d4000040e0301c5013804007041c0c0e0300b0400005414016410039030041480e000b074002041a2440c208001c4456044403120a8003c0c0c0f60400c010810103001e15181c0c04580441c07141818410300003c3c0c0320400c1d01000034061704c0c1484c60421310307450000020000f0b2102080440058821034610f5203070800301300e8240d000031094500424050f119014490403201c42900030083e02d806069003050640c030240c82100c5500003008009403c840602a002c051030040c000b443d43c40502108250594a40d02c1a80059801010200030303440344000341c4503001803865041807402d50350808101c00a14581503201c1249030b144042d1141101158401e4003c601c4840440c2c80c614407150000b2000e00861070a41028102004140113508000c2a0824514546d00446604014440c9401e0035070704901040d541140001c41c082045203001c0001 = true := by decide +kernel

theorem cover : BRFrame.Cov 950899280 951079136 := by
  have h0 := BRFrame.cov_init 950899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 950899280 ≤ n) (h2 : n < 951079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
