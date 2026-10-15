-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5478
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:59:34.709647+00:00
-- url     : https://prove2.me/submissions/a7b57a49-31b4-4d2e-b6d8-69562d88a790

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 985071942 ≤ n < 985251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 985073192 1250 985071942 985071973
    0xb0405010b09030c0904020a051810051005030a0903030e01140615160b0603010f020f070204060b0c1f0b060a0206070f0c03051c1d030d0f020403022b05031305030f 72
    0x420705130030607280c070071003a252400090b140319059444140d101941c85001c603400001110100e00424400310a41d00301900c44080100c14414030341900001202440090105180d54200c1c00b0098041c1c02c0c000b420450361000c0c18207503002c0010b0f1802c03150b0107005004090030308650541c80e11804429940c1000f0b0460440c082c02a80c100f0090a042c10401c0440c01030b40e0298404000110549411581c80c003200d60302c00116000b03200b0a071700c6146000c42c000b4443c40103204a43c030f041602d10260051401c0c104040c500801035050040e8040d940307000c5075040e500c44030010800840d86400410092a0440c4018028cca418141504209489520301d001a40000560309100c003036402c1c081205210900b01d100400a903610026000c8003000c000350808800b10041034070702002d071402e00c82d03c040b012805040c0d03c55403000a4001c100da0079100c26100c40f100c8800e02003200d62020903142001a10381c9071560f01f100150b0440710640040401041c0307000c01034200d070f488021010340484c1c0b41c400c241 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 985074442 1250 985073192 985073203
    0x305010e0421140c0a0b062b1103100b2e0c05160f24020601060528200c0a03031103040f030c0e0a05060f24040902030901200403020105090d14010b0405010b0903 71
    0xa05460400550268003006444e081d100740140727018003101c41c2c020004128401901404003914050030300c07140c2c0c2d0310305d0ba01f90030046841040b41d2401c0003142c800300d0070104c03600d103030004050700c3d40d00402d03200791860150380e40300b48010318040304101015410100d0205a11840e0154000d428010300c01c1800c3c907503000705a80d41104c0481c2812615034201d1460701202c2f800a000c491129503061140800c02c9800018100c0400708520b002078071501d184001c6555a036a03c00003a5100395072500403c002481500e02c0c080004401054030b0505550742c2c1207098491554008070742d041040781051080704500c40c461580600920000d00c518281200440c1e00040c0c40c0204501648511044905400c1c010311554085010003441d1036440d5030301c3c6c1c030000007074100b03440034100c650070007034074170f1151202420003030703814003c28032162819103107a0064800d51710041c17a07a50032160720344403100850200c5041c9610742c01400000305450520800300400c68405070020740126409100110b52910000303107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 985075692 1250 985074442 985074499
    0xd0b0720060601140c01090f05010c031808090303040807150f1d13150e0f010509071b030e060703030c0e1c0803061807020304060305010e0421140c0a0b06 68
    0x805190542c07401c0c516425505c2502c4107400c041d0b082038502d40c20880c41c445020b4525004200070021f500b0034000403425680005545d610000b4111140030108240c00020054a00010222481e16550303002e541c2c244045548905d20000c1c03441203d011003070700300081c03112000301803070155841c50000e40300e02c00781505d010490780582010b4542070120481c1c0c1d801414082c0c0407002c20054240d907003501e8500c1100c11680d20a040c08000000101c60416058041c0542c489480d40407420805010883e091002c22201784c0c00c2100c200c5980300540c407581c000380b00d00c9020355808548031074a5000600f00d98480500c040c00303440034400c1d82e081e01d182103190241140d07001c01032079030301c2c0c56240c0010142201c4401d1400c02820010510003642d0700040140121003180c1c074240300c0b40c2e0b41c1d01e408002040040302c01504411b409604010344098410000c003c00c0120708140b10203803000304040f400d0b038128052410055128907a4403040c4486020481e50011088848800f41610354165191204035800e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 985076942 1250 985075692 985075697
    0x50607080c0f0a110c1e1509010203091507020904030509030d020c0f0409050f2410030b0606220e1009050c0f071a0a0504030306050915010e01020c0d0b0720060601 72
    0x465125000c040c002850791280c006d185440e000d4000c00441c2006030107008140c4214803640c111004602103109031071660034160080c0d4207250000c010700c05c40185021800e45140c004004180060350f40c514624041c0d8001d43d40c180e191100d40092610301010303110380703800755808160320030b00b0341d522003465043c251401d59000c29010554507000d0710b0003801d09044400d80c0102048603822060140070710400b00310030141200e15031100102c52420311014000038004170f1248001441354100341e0000c0c0400030600381400c6001c013036812450042c9200341c0109444070b80100a000da406505038075076000c1c004000c400c00443c28035008126951080c06408000c1e03c0000c5000f10910003426461188020444003075682468034508100040c0000c44d41200800d01d80240490350b03061822949201e0001c180d03011083c03c0308540150350102c000004035045204651070b401072a02c418900100a40c403450000800342400d0401034400303d05030092204144502c44507501103000010300c00e0f040542030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 985078192 1250 985076942 985076957
    0x71401020915090904111306170d0801030302060a021b011e2d0f060f1712123601020403021e0d0318051e0f040b0a180207020409050607080c0f0a 64
    0x1190020790394400f443c0900e4509180020115010041c940041000105607032b0100000e141c19900c2e01030a00010700164400300000d031800e03c40d5401002c80c402c5488030740510b4400344c05c0c000d0039201c91000d000c4c2181d1605115811b184168040c451541e161802c1802e0031101405041d17070740340311000c41108001d032a1075401c9290000382d40840043d007510030644050540b40e0702d850703418401d0ba128040591240e40305034a140400b91003520350b03144031034040803c1b58595400d02007907820085500300f0301c0b00e0b07064581d07030340300c1d140400304e4a00c00f4541001507200d43c51030041242a82048410b5000000e000350380413110307900c0600c00800207500d820846001e44102064201c00b0b0042e0b0080c1e030308802c3c50540030381800100c0c09001c100c01701c11030700380d03a81a140000740401c1d540180341b41d903001000520f00b800b014800d6004507025848004006040c100b5640025003a511080c50554413500090144070301030f42c0c89440ea039400070341d00c10f5076403804901000d00e407401c1c41240d84400401544 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 985079442 1250 985078192 985078223
    0x5181e01180806091507030b0d080c0c060307031d060601081603150321030c14090d1a010608130302030409051e070e120a020f090606071401020915090904 68
    0x80310140020302050702c11100149044090a65030f9407545941e03084600040000801c510321078000c58140b039101034a44e0301d0740c1c10382d0b60360418190400e21203040325010f0840031440d01c0d160100614455600d0784d07400b00b0000156115818048400c4441c140303130307800c254104565660400d0400340c20061030780364510f0742900e1004c110700402c4c1e1011031454056800d0800014042c901ea8400c007203486003034001220105031a0160704640e1441c05600110b03640f180c4005035140c800e8060204840041c0854566164542d03c140325040455039030443c64014200500141d540320b81c4d4107a2090403c0e4901c0780b1000c3ca510040d59900541c8218018240c6032000075100000c001045002603154501c504041d08041c000030f8080c507103254070305000e880341c100e604a2130b050025181c92510380151070034105800050510071041c0e8010f001c00e0300950100711000004154254001c400000c2400040e21482c85c0c4003002034020301c0a00c0406528810b02a529007a520443c2881e0000d6105003100302c0c0d01d16 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 985080692 1250 985079442 985079477
    0x70506030603070305030a1206060318150e06041b1d0f070c020d0606150c0825082206030905100506010311071b09090c12030c080a05181e01 62
    0x442c0c000424600000c01c03080351040d040341006140f0441d40105000040e240d04042f8102c0b920304021548084080c494a0b01041e01c183c2c480494551314030011071042d1061101a00c0c00b182510215503601c8101c000214203e4084464009440081d12030140701070b2000d603a2070764540113004c07131030f80e104550701051016010b62900b00380f031503014242030300b050091308041000b80994401e000700f4410310425014818410344084900345c0d4013141560402c0d00440c0c8819408a0100000807014440d000704000301d12082c000d810645001c14061006001e007005410400005a0100c01858181000140091004600308500f11003046000400c1d0359120012409403c405240030105c080000d1080c0a110000070340d45040440b03141c00100d89039490b20301301c08a803d58000503041d180711442c10f01c0300004c519000c00c60725029184c814952851034541081550001a450000c6640015400304c203c401042c0d00c0003241c4229000d00550b02d64071000b503141402a404941005240d0380e00400108 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 985081942 1250 985080692 985080703
    0x60e0306071d090c0309070504110d0e010b060f040918030f050a181d0903070507170a060501180515060f0a0516030507051501120b04020102150903090a0f08070506030603 75
    0x8100a05842440c10100484c07141c40d403041da5444024000d515010466050900580728503c501d4020285401c10100c0f06400505802d00c1c016007554840a0801c015070326007000d00503016156040c99902c51030146020201c90f048842103030740744201e41085011a812040320420500c060500b199a00d0240d041240c2101d00c2c040600c0000c03040d5640410b401e01c82c41c01010402c48024805510b40d00d50b100455a40e0207000720051083e48048011b10104039040ea80144482e80032049030600c00312942d03040c0580d0026042021801e44d07a030311607000e210b0030740600303a001124a0a44550003c941c00494514403c411504072100c00025032001c406102d101160915280d00703941a0424089140081c101e03408124251004d12a040c52142c0b43c0301d880103614100c601500c0c00d01c0c800c15095981d01b0800c0741c0148164194010700d907640e82038815800c8030602c104444805940c2c1d8040800401c880307050b49400070100c0b00000c0702c00b072018020004d0710300c0a813002103580940341d590307460001c2e01c1d00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 985083192 1250 985081942 985081997
    0x30b25110d211b02070509011206090503120c0310050936010f0b0a0509010b0403060504060e0303150a062604240b040605090405210c07030b04020307060e030607 71
    0x180b604056a41d41d4607400d98001d00c40f1110ba0940352010307959801c100100c0428020110218030b41d80030400012680d40c4000144c030701c250244c9044c0446c1c0d081c0100280000c8600c06011400001040248039800d51000c019040848005180e402c013a078000020043c00011120001e8454503813400541f01c0c0f610000c500352003080203105894060300407002402004084500503041180e01281074030b0249c03501c40c182d46000c01d4660519265490300005090080c1050b50450380c2c03505030004e90141400118401c00d00e8000e134080b02d00000080c02000700f280c2d441201080583c2d2a150341c00190052030f0140c108000c0109240d07502d0751300b094680e048640c501520900d40501c1e10801d2040d19402482032130344c0440b820403001e0340c0d503810f204590000f140d0040158000090700498401c54411500150340c0c00c910440c2081138241070b051901c0d42d1a081910749503400d030204021490b0401c5500c014010310700c0c080d100012200c01183e03480401400050622010800c2043c117400c4002080294 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 985084442 1250 985083192 985083257
    0x409030216081005060a180c0c020d0501140f1005120c040e150123090a06050a060203041a0a0f080a0e060c04031505010302130213030b25110d 63
    0x1c070b9510500d1540d90381241c50203c400c0c5052200040e080e25206c4541c00440b040c0300302000d00400c1c5031102c00010042c600119040c0300d1402043e0f000340c1c41e440c505480c480c1c80350b800041c40032016404c0c0c407440f4070001e01000344402d1a404114000494149103800c45009840d945803001050007414208400350701070a400c546410b24582d14040005071900d6005100e0b03a16003071698070359903080e04d0b5044202402c00c15004646509800b420083e8045501c0020700c0700010301c280c2c44400060107040c159010318010380c00450240604d14184100001c1805021300262034915048009841e075402042c0f40b2080c4192240052441c0340c0303030b8100e076612500703030b000b039543c185008104404160030601003070b118205190f0300c4801713085003885864162900102002d48403440c0c8104c54029503c034120001ca10191000004000b5020b1020300c0d0003040007480b15034444010040003050428075011440c10081c4156090140003c00b00381c48280845a2924001c4990818202091201c855469256 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 985085692 1250 985084442 985084483
    0xe030a08041208040203150a09050706050903160e13030c05010906090b0604090308010e060102030d061d062731030206100b03013003030e0c04050906040204090302 72
    0x91560310600d034030721852107040c0c070756610010303403a048034900d404440081d010740c404506100100c00c8031081c00d0344844c001030f02058440307c07940c40d60b0a01000e644030b00085040403400501514061104401e03d4035070b81c035489447c0d4600705040f1201c503805002844000a482481010b01d03100f80000c0740c03810303000002886042420301d071210062080e2101034039000c007884089041403620740144038015405942e0800d481e4204030101c049220042d007158103500c400c0000032030007821030183da0001c2480140103100d5086000f41d0800400c0000c2149121790204d01c14a00024804000e0110010302d000700c641c440e0703982c448141e4105004c98540c3c55a1004110b4094032806068a03040c03425100342d0985407140c0b200003021240c2c013014050b4000728201840140b0240b49122100d254522150702d4040e1a01c82c03190102d4036844400100781c00298990b6413820307540b1810030040000c101c003030b0b038100014505445987d4680c880540024440c80d1208282010b01d44208070382c00e035a490000e00d890 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 985086942 1250 985085692 985085707
    0x41e1707020102070e1510030b130c201b0f03030a211b0e0303041d040503040b040f14011b1b24111606080403020304090c05090301150f05130e03 64
    0x100d003081030100c900c00c086000240d01c6288c4207010303051441b403001d003601c9402d680c1c41040301d010740407000f02d11041080d50344144041d04004c50351140071201d10f9000d00055499041444224421100300c03c0c054100401c03024115140041110300e9003000e0300d000d100401520b030304940103504071680240b0700d50505441003108181415a0b0b85812200c2d11580c2c0048250014162203009601c50100101d009004c1940490a40d1003d154000d205600342d038505921111288540e81082c1c01608150103050402e001e1411503201a565441003420545203000100d61640300c0c10600c410014261803408219507036800c1e40c0c104510282058a02850402101410909120b480c1803503030800695a61001840254007040503254252a110300042007030501000b640ca00d034015108a0840c4010000001c0105140c40b981961030b0b403503560550f448503128109820740e00f4050711810074032249141045040d89641003030003110010348030101204c0144d15610000d06043c0d054840c9800001100d1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 985088192 1250 985086942 985086961
    0x20c0304091e061818150b0a0f0b030601030c0216090f2004051012140f0708090a0215160c030212060c1c090503070b041e1707020102070e 61
    0x30b006600c1003401d801c1c401c0c941c140e078110a44030144500600d010a4002c40d48500c04682c100020f80380d5503032010703a0340204075030b40d036020720504100081c641903550104192030314042c02440010601c0c02c005034840c82c24a44500032034400507010a040c5540c402c14040724500038807420f0002d103400c0300f10011560b904e50800f4040d1100c002182d104600c1e022181c0011200c50080003c0c403401200150700340b5041c5014072038003040941ca0030b41404070098420440c402c20340602191090307113071954450350070000010215020054a004140302d050780420024200004171502c007280c0441d0705641400400c00511010312801201e03000d01e9513100d084800348490303c50741c1012030784266284100e505141c0505c0c0e4454905807290981c8001c10001230071489100c6269440304201c00381c0015013005150340700c2c0e16507807001c40c0482d4104036210400050004000e8a0b025070b958003000580c4a24a540d540c615500c86880d00d41d8104030046511815a482004414040c0803040b0302d20596082c40002c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 985089442 1250 985088192 985088201
    0x101e0f02070b07030e06030601051b0114060d0201020d0e04021b06061509060307030e0c0d060510090c020a030305152e0207060818100203070c1704080a08030a020c030409 75
    0x11200903210388500010080700c51021070300d4442d019a5540d1520414000b040007980c00502501d0411030280040c03020303024009125a8550303421000014403d5403445d04003a4100c004006510403e10800c002d00980d0300030031154091601d525050070030b4181c21001038024043c40c01c00c00f81d034000c030f072034203905c03101c40001c8580c054881100c82140445180e072010303400b1b102c0e4001040d008801440480d60a41c000e40081c5072903844802603a00d0000880080f40e00d100d0100400da400075229401d0012501294100401819a01c002849458065140a581e9450405009081541e10000181c3c0545105610b168040c03004000c201c211400c43c1000454540e510b1160745c65003420101000814000501d001c210f0761152205900c564440c0645e180a0a06040c080494001d90660030000c1546100652007000e0030f0301e62880da1186d40c207000d5940802d1480e41c2ca0420400c22060045020001c0d820580c15031107402c090b42e80c0e54000706180079000310301140e211448042004a080c903400e820 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 985090692 1250 985089442 985089467
    0x912180102070e160f051e03071115161e02030c0f15160c05010903051305040203040b0a0e07081234060f180f020f030f0309101e 57
    0x701c0d00c5083d210303607441071110416a620721058240c0b44101400f2400751000b4601c0140f5401c00c83c0c100107281d42000410303c130080c15402d4242d0008104003141317070444049200f01091000a00c4010b200300c02140c2da00202816507200241500100f495007031045400c1d1105881c5c00d140741d4104507000c18003030354903000100e000000c2d0066101040800000188244d0310340d803403600821041e220340c0121910041c40204050401407400c0c010f80202c1c600b40030f0408420710a50b1000d0703841d070f0180100d1744011041e42005105030700410500010031210a06a0307003240400b1030008a01c50040070140c60a04568401141030003150b21113248000654050200d14003040e1504400c1c804007825541041004c03500c1001d04c0000c24074682c04106240d100c00da4180150070001150180790800b100340e5105040d013142c6131040e0605801c1182003a1807a968041d40660090001e00c0c4d003d0700841d16800703043c040d81d001e00d5082d180100d2140c070621244182050b101c000f6041c031b6101080040450400d002d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 985091942 1250 985090692 985090697
    0x280b0c0307060c0c050c13091b0f0602070b0f0d02090a090b0906010c05030a11011805010e10050f0f0411060c010c0801060e010921080c070f1d060909121801 69
    0x186250400d07030184d03403100c010550080240500c0c1100e2010404020703102d00403940195695408400007a800030303615440c240140c0c2404041c2454408041100c1403590041c0c411034100030700c10495100b6200c19101503580c0d00825584920050810b08001e016140001d0fa0220041c00d0005a01205900031400f034001a984120f855507030000556030124041c200400075403040200b031280c0c903c079201c907848422902001091842c1142e001076921441c0500982c3c1e2650740318924402d41c941048520741031000120144000e00c0c0c141000d400e11100207042581103540040010304001e006d01c05642c1110008001c192640c540c519518004d10340f107080c19010983c81d07000468800c0c0203099990507100141c1d0f03844e4035141055900e00d07941107440000c8040e4109504400300088400c40034260703000c404c6009001092507c401c5254a04071940042d44402c0303009840403046031805a940c0d80038400f07039142419a292502c0c05d5141441144103607498901c0482d045040000780190303107141d89003d0307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 985093192 1250 985091942 985091951
    0x109050313030b0c090f2205011527060513080d05070209090601051c0609050304060c0b0112080412410319260106030605041a280b0c030706 62
    0x2e003184d403901c124145542c3c481c0072841c541803513181c206e02007884543d50982c008041d000a951940c05c2e20b1013a0846460301c4140071302c100186521030b04042d0466200004103000480700c0140c1e0301c045d81c007401982c0c00c004001880d912000c003600d040400410301c1d142110f000b41c0003480d0080c90740e0071090040b0f1144160001040c2011000650130707040c2d420040104048c14a00c6600860329509140c040390140c0c2c40302001004110309101400c0100707070307648401e003102e80540b8100c0c012100581015205a0600d00541e0200d62420195016585640036102d582c1140d820308140c0c1c211a0f518a4241e2491032100c544c24502c1c4030001010300a1038402010070351088503000b40c80780130350110400061100d030002c5070307041e1280f0010404403214a40454805020210f60090f802090b04001c0109803900010859400c1502c2000b058590510321811040c081350001040500c0707100605201205220803c40c00407190203028006100350700d0080d5441c00c610b070381c03240c60f908031134802c3e151306141 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 985094442 1250 985093192 985093201
    0x70b07051c0b2b060207080309010c09060804030309062d0c030209012f06090706090b0a020303400204050f040f170d0f1b02010c02070b09030109050313030b 69
    0x41d0199410140b001010121010640c01048406420354103a1a001504400c83e41011500d644000c090145c00b8400c40c1e981d03460f000311403900b540c202004150410403045070400ca4542d1104039103400a034135140100301c40f0306a003094009404885440a1103410181601030390355075140009000c0c50342c04000340401c2c2c0340c10809900300e0040140321804140000c1c52421840d02c459a800000080d144040345107081c0305441e140342c00400c40d8042580e0303102e0783c818002d40350002101801000500307102c82c90304e00b074410300030344a01028020012a20702610720315070a4402c020000100210070043c40d1103d40d441182c0c070304030002c114040e40142c3c90703c0041058001c4141109100c1d0b40c101c020b522001c0e07910b07503d1100c1981010202c05030000103001100e08503a8034007681c092512034040c0803800038080e1458901040210304010f09580c58005084ca010340c0100d2081d0888240d10f6102d0b48407205117004c603001d44011003000f0800c0c000014002c50f12440200070a0903a8002c00001d5400d130358 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 985095692 1250 985094442 985094497
    0xc0b0706050c0f180310090803090f0a0f11010c120c15050c0f07060b0604091a090f0703110702043803060c091c06050619030c1a070b0705 61
    0x41e12040940300c0f01e0400000c02d1010074411051500304025003151071214051a11703400300c861640048440c14800810b1000f428810001c02181d1200f500c040c200035032440d0740c0c3d0b14010904640c014841c04a0096041c170580c01780b80030408031500316240e2a450036001c203000340302044c072103002c0b0703034448014145680d440c209105851040c03442d0004a85003060b404610002e5401554048825940714041c0c0c82c0c2503100d00014200400c0803060100d202c40842c03003440d80d1582400715042c040c0881e07100304a0300000400030030350004040d0500140c1d9004049180420f84503e000281d0000c1c10808803820408140c0d0301382c00d20303464414490f03401d5809820760144e582d155120883c7d1503031040340071480380c6480e04003c103030b000302c0203080c00c01641c952204843d400406004c244d0350301e503486003000801c0c00c00c2101c003c0c10060b820151405030341141d0301c81c41a10114090502624024200e410740c80c41d40e070302100c6d442da4000d10b4007900d600d00503e00070019800f0040800f082803002c04141c15801 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 985096942 1250 985095692 985095697
    0x813020405093301120c210b061e130e01290616060506040e16051e09040605040303180501060807091a19050604080c0a08190807020d0c0b0706050c 65
    0x2103a0600c540303c513481c0506441e03500c40e0000b001e03500c181c1d000c00009600b02054210f03801c20107011400020131181420700003171a0100074020346c0075894543c2144100040101d00d079281d50302c01c039481540058074480b88001014a00016070031580b0b800314801c2c1542290b202d86480f5810400a02c05c121040014804c050084c40d0328551200c9219a2140010701180c10940e4001c0c00034000140030464944250310b06984040111203003010010140301034208010205101d001e00c1c102e080418154002043c5181002400944400d83e41c40114080610903086600c1d51a944142e10810008500f0018000c100314450000c0c03500c22200d00168503040c0d801004000ca903880301c01c98611010b0824400c1030203001d440b001d6811a02c0305e010a01e0b0b5981d0b0301900152042000500484460704c0034411814095040b070251a03000030742003154140c0101c107020f1003991140d10b050715011144007150f00704418260041c10b1102c024008102c00300b180029046850041c5010702141e01c07200d940c841e0f1403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 985098192 1250 985096942 985097023
    0x509040b04020403050a0b1302180a0b01090b16050a020619080f060d060e07080f0309210a020607030504030803130302010524011808061513140106081302040509 71
    0x280c1006c0300a1002c28480c0d0440b80d4080e09040c0b1284c01d90a4560006200b1046104132080e040c1c1d2803802d0056600c2d441c0714801c0340203800c0c20b2250f01c160805100210a00400b050f000c0320404c1c01e00035904103c018024000d05690103031480b522402801000703818418000300a00000c2e5031038000484000c007418219001d0744001d03000c2a01c1c1206600c601c1d000e41025000141c507445041d10000320090100441c2c1d010a201001654640300200700300042003002022510310392901b240c01c1543c400d00450000601c2d641100c500d03540b04400e01d0250380600803688060103541022003004224170340102c00d002d54510a070300030030050f900c440c0314061282ea128010b0348c00c0a8941e094003a1540243c8e072082e8490410f644966005a0700c8204920b00041110703291500c0340000150700840c00c01c1c040a41c507580344458113200c1c40749035000c082e000c202c05206a204008054001c030320340c04145140384100a401400921040c0b6154407103a6130780020040204601d1100402c4004481080d8a02940d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 985099442 1250 985098192 985098203
    0x102131503020a050f0a1e091406030c040b092116060c0c030201030e12040807060e0307080c010309061d1b1002030301050405270c0a060f021c140403030509040b04020403 75
    0x40505c5207031054040d030811800c1e8000e00000d04080c45059401e8079040803011034aa982ca040c403802c210109038a52400d0800718080c0e1018070a0104540c07104003035405403942e6041d443e45460504000800d001034045030003500302005044008000c81c0825012041d104084406401540d50b0703100300c03003000386204e01401c0d0341c020010030710056100e904100f000d5442c81d400c44001070040003400605900c250300c400e0a030341c8001007c110458002c2d200e01003a08044000c1c04001c1d10f03214006481d00c030100301c031a0400d6038a40e03840c3e04000055002c00900760300c080010701d0020f03e080354150b403440e02d1401030740c0004000380300194601d0142c1c94842c01074800d5000d5030559207000c045c00040c080140c1081c8103c401c1904107060080d4038066624060803010050540054001c28048484403d8204000f080480c0081c0c8444540015900c5211101486070241d07103100610100d8440307216076001c4101040014001040c0741c3d0240190103443c008072810880003685074200701c100d1049200042c40c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 985100692 1250 985099442 985099447
    0x10501050702060a0c05100e0307022e080c16060b360406020f0a0807270620060702010b031603050c2206090e1c05030c07140102131503020a05 63
    0x84e07120380104c60000c0d100f0740440700c2025621f40c003002500c5034041c80c16003da20102c0c4001c1035140c6400d030401c0c0400303181400c0d8182c4401e8000d500004c6c03584030010090119000109103010804812a031040e01070f0301000c0303141d200c58502103001e02910700d90389101d115005802c09600318101c06646100440f00e850884c0b07a40740071441c000101000b481603540907400e10617100e0030700a83d00200b000300032503502d2103c2881e00300c5005e000c0c428240d181140c21001c1181c0020314400e42030141081d80c9003070616051903018884021442d001d1a82c40c50214011700c001c0c0048942c054002101244044040e030300c860b464050641f0205100d44000303860787d8000300181007282018008120b00c42480d40003c8503016042c0f69400c1521207647c40501410f949923803217941b01200b40080300c20540303080d0001042d982103c0e0010b180f400080c0180440400000700007042105d00d90701d410203038103002c0c025501d880791203d415860080610901c0b501344500c3c000c0e900c005109108451a20b40141c45860 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 985101942 1250 985100692 985100707
    0x11070b03070e010c0804080d1704020f0d08090a0806090c011e030207030c0501090812010e1b1308060906070908030f030106030207291506091804020d0803071701050105070206 77
    0x2c03210495014110b040c88103a110100215003240010000303029524010845800c90100007031600d508840c590742c00c82c2000e01440016a40d01005070b4200b0422100c41500c0303542824404818490b42e0130b040d40c0045801e20010b500e4002089951040400c501034513441c40c3c92500541d101c0024000040000c0c942041740003c490003940030f0405075000307191280304004c00b80c0d40e00707003160f41050054a6040010501040801051200034050312001c0b5012080e404c3c1120907584000c40300800c0c00d40c80d580413444840044055000b580200442c4040b10305d58142850b00c0c03525460142c031054001200c5000100d24500000110b582480065003014a1a1310b4898120002d41003000300b103e4003009c030048440c020030170849198913420115000029801c001c00e01000044464010380d0295005001c03070401940c03400603841161146100001c003668481c800244e41c0c0309901e1004107a10004000c0c000f42c96800a0700e07011100e00340d14155240e98030346005481c8c0d4090410020343c018410441d42 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 985103192 1250 985101942 985101947
    0x109052e0e0304080304090e013207050c0109060e010e060f0f06030a150c0905040c0903060b0a08031911060c070840050418080c0705040f02030711070b0307 69
    0x100815090402d881c10f25032101400350840c0d0103a0b0046403820b0300d481e05080c8861003803084048070400d014229001580800820342e40220f03000812920b001800000398405000e001101d5944c1c8074400200110041341c501b8034000c2205000e00a015881c09610454480c80082c04a01444a54038481c03110740e55000000c90304040284602d405014100f04400050b440e1581c032200b26802000c0070a0b00000310000902503680d0fa0300c280e01c1103080400d0311102580000300082500c3d00074501190034031142002c11904452035000404620000038100f80e090340403061400c4202050b0354050010b0351205c0b00503900d0400380d492448540301000b414000500113030040201c0010003d03070781015080003170040d09040c4195059400e821101582001e0360128030b0ba40800b4203421503040000300c640b180c040f044001c1c10903005040020004010781d0780300040140c0801441300500902404a001c0c90202c0650400e4401c000424040c00034407030901d83c040780b0b442c283c80c0280c2d0b8850440c0c0d03070b20004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 985104442 1250 985103192 985103201
    0x408071212020a0306060e031f02070501060b031501090e16030c020a050616120e030d02090a0320130504320303010f1a0a020a0204050618090109052e 66
    0x440041c4211059940398042241c00a07100000042d200042d00301c0c03805d04041c2c04940b0031500a486a0083ca541104400380700310814007503901400c0040e100e02d100d15045004020580020b80404800b200f00b00304260003d000390325142d4207a0312034071707400c2c0e40f0842c0424203841039500d68826064185442201032023036000c2c1b000030603984112148000584c5070f80d401c0000545040c0040022130180c10541500407100340c08031390301903504201d051a0065800d480c5d016070302c0048180740d000039104141e40e4a001030100595005103006210780880340106491440724600580609441c2c00540c0301d81c28988501d500c199040b051250044180c42061007001c1158460310010342000512440b006900300702a42c080d004824004082e94101980c061300c4d18a01c8400a11081c010010315500650105d000f244042c3e041d280490f0986030358000038825200705d1030400b05010100104040c240c1705410083d0594001c00558041c1a40c491040428281001014200c2c8410f076500612034440c2d6400b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 985105692 1250 985104442 985104473
    0x1e12041203110304050d030e0f0718060f120302011a06070b0a200c0f010605210c0d1112070501200c09040b1006090303080109391403040807 62
    0xa00007a407105080e10b0001030b400688040d60a0fa03c51040c3c0c1400641501c201c484c010050401040c00c880510a0580d547c3c1950080b501c0b1704054100000060f02550080710241035846403d9200c16251750a409085150000030b0b030041d03007455810100f100c02c0c0c1e101c0d1a00d6060190001d4500b4009842c0c6c48001300d0080c1151080300e966028055060080042c9c0580400d0b50168160380c490b03065010b01c1c81c24484c440f120300e0300c0c5d1400743c00700181c1c2e071041c60030b40074004e508061500c1444040000360400640611070385d0011032400c080c004219002284031607840040320401d86d00b00c2300b540d01030f50340e601c2401100e002c41c880c2c00c1841001301e07103000c07a5a000b58029085542c00f04440000c220700400c1500c007143c1002c3d4000078450114a006203002c003401451510282c02491500d0040c442c0406100f420840c0d60b6410f1184111142600600c80d1900001d0340200c00b0704c5401c0340c01210a004510040008031144d03031000c880402102140e000b41c0c0c0150105040124a44503181240300154 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 985106942 1250 985105692 985105697
    0xa0e071d040507030606090506030c04051c020d0803060306251b06180b09030a05070605060f100f03060501110a111306090207020108010501030b0d110a18021e120412 73
    0x803a4119611802154400c804039503000c80c0b82481d2a078040d261488a4012078400d070814410003070042889800d0700d048480448840f02007440b01c3c8045030090400e07000294100032100d100070b040c444403c00544c001c98050f422a0300b03550341c260b10413507600c0308020640d61180100368a040c0e0584242c1c0c018080f0311480400a544459a40e034200c11100340c0b40c5040c2c0c10316280c0780701c1c80a10120490403940800c88401541c0740012a8038000c2407481807080c001e140750303520f5010070903a07224a0403541c40108007610912200324104405020708080040d043c00203820b040f404103c651046005d2018941c2000c01010484030556402e00c85603810004e55800249000440840414501544004202c402401a03880c1d4090000400d10711050700702034145820000341e442c4988132410140103186e040010600d4a0003034100064110a099000f03041d050f880c07000480105040c1d600620140004010402c00016401103210040c0660000940c0b4034060400040c00325008450b013154107c0c061 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 985108192 1250 985106942 985106987
    0x609180715050f121e0c09012d0e272d01060c0204050c0f07150b3a1709030106031a090c01140406031112091b0a0e07 52
    0xf070160b400a40c004005440540c80502d052000e04151040c03952221090710300c850740145012403051190344200c000c124104220444601d40c2402a52007001c41310f06c9960170311031003151640009046500c504000c503c035154201d504082c40041000541c01c2c1d941803e40d0003e56583d0100403030061248489108031200c0301144e401e2400070000400b0f001e0811601d03001001500ca00500085400c02001001c180008200c40281030010406030340c405640880d6899040010070107488c0036060441100f904588004c01d00e0b001c412004504070a000d0510004080d080c2841d1804079262001c210040c0005110f9907146148142e641d0082515100c00350000c03075102d680e175459a2251035058820304c072040c020b10a018101e0024410045c40b600b091820340600d200242c9091100d2156108000900d941c0d0f1224040c1c0d1400e00054464450300d4907030340d03002d03442c0049080d1f489010b000c002020308003c916821540f482c3c007207010301c25965480b8240181e0b589010003694182480425022a80303140c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 985109442 1250 985108192 985108207
    0x3080a0b030d0c1704051e040e160e0a06030308131122050708040206090f010311040e0105100203252307090e0307020904290f060918071505 62
    0x20040c600041c00c5540d600c803210300050604c00e03d440c0805080611003031003088100140c0d91894103501c00c4002070400c0803001c02c0c024000030010030682ca124801d501076081001c00b030301c001c810458222410f8112201030b61b504c00032000221440c13804000c0200700c0d0740300400c60318086600300100480c070aa101c3c0d0b8180c0c01c104002000941c105104114488030b0303145e0504a840103014480c0c000009081102c40c0f820690b0004066004070314409000d51200720001c8101c0c2c1c400d80005035101302c1b0389025a61141c4925031009a801c090050354064031880710700c5011244000101da402001481c82d110350700c01161440039069407072180a1b140d854005804402140c01007614081e2114690000d10440780782c040c01c0c0c4140c80064150725101d81043c0030f14009600d039808a81c0c0d0055011840407003a103041c0a8a0b00704502c0d40701c0c0e002c01c107545801080350121200c03407201c0c040d8804030740c851140d0381c8241c184254411b20b401001d500303811405c400c00c0115108030b0344461551043c2001c41c1401c0a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 985110692 1250 985109442 985109449
    0x1150e1203070503030a0c0c11060a1206080703061401060804060207020a0b12060a120f06022203080406140921102301050301110a11150405010203040c08061303080a0b 74
    0x40038083c0e0b0150000014042d000030284954141c00d075036802c1c10242e814060311003c441c8500d090b50b10b4021900003c4034010750348142c1a0b501c0f80034282d80c3c04c12005031616034040da1601c60b400f0859015241462070400c00d000000303198126915a56203005643e150790341c2d03001941140100700c0e084180d81e00082852404074018102e0a160105030b034039103240c414201b16100e4180d0740b20680e8101205681004140c05400046445411183c05079458105e40003d0a6655000c00c2c501c03011031500c50301000700089030307009108803280c0740d0710785080c0d421024200440c1d2050001040d402440400200750036951401031005040e41c00302916444243c800d002c005584c4560304040034031528000c0000c1c40d9070b40e449998090041540200601c2d100c0b084243c01d079220310b04d901024000024000015840c00700004149a4840811281681000d10b00a4040e400c142c80c101c942d419502c41c00f0440d0000041c1d01441803450400101d00211943c5064901c2032014240914880e103501c80d8007081c0c0c8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 985111942 1250 985110692 985110697
    0x3090804051507120f0c140a1b03050f011b080a0b060d1e020c03041a040305010c0914031f020d090b010e07111b0f04021c0606030c03020301150e1203 66
    0xc0e00104241e0b20421850814130b00c0320b081130124207008411100072801e542c817200355000103920040100100703241407401c41c50100007041c000c02000803c81f551020441c0e000b0540c048a20503c215402e540304100d40c1030a844848046d084d07030300280d15018580340e11035980642c20092100000410040c0d80c80850f0095020040d1614202e440d00340c14621000201d42c100312500c1403100440c00d050f030a10400380c1703e219074480d1005d004119035500c1e801016041c04c550045500c04000c00403011421809803003001988580401c1c182c034141104914180400e44094080c501010307a900c62501c0d00c2c1131002904200d00074144640d541840c0000142c1c41d001c41e601918070180094018030300200001c0407030624210a02481e04a0386121107500d070800e82c0008a6002110b841002c1ca143e107010600a001e440c0461050217201891082030554036400300c0c040d1522503038140058560800c0c00d030180e1000b84a140d0000c4002c2d91514070341071003451307880c0c00b1440081010011100e5420810301d0768 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 985113192 1250 985111942 985111969
    0xc0a0507050a0603060f0512030d0c02060406060b1306180314030c1213030305070f050a06090b0612100b040207142a0102030d0f0e12040e1e04030309080405 69
    0x640c40200e0601c882c0ca03126034954001d200034601840441c0c10200390001c010403030310030030b4040c00d8080c21400303092400780140d424020100200b00240c0040480003940e55106580984800d0b1a000340032034480b00796402c4500051441c2400080a07283c50412074400b0010101c000252441c0000407000908602401c0034007042080255104c0700442c1d40709050880d80201c441103c681008860580007451498400312034160030b145842d99000d00b800d0034840380d242c40080c042c6c02086083c0381040600d9000c03851050285036144025a03a41c401d21940040d130200031541075000070480f0f08030400e01d4011090b41030000e00090b0900749a6a1021380340e46501180b40c2080d00b0507132408201008603400c032541740d0303101c0303424a051421a1001075200d01c500d04490303806c2030b01d40c10941e600041079002103004244038001c542c00c0c00d0440e4990320a507003040c09111105070040001c6540303041201040c24418000f01032401c10703034940d60350650041410030811036a0060500c000105c60b40e0300d003901c0000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 985114442 1250 985113192 985113203
    0x10608150f0603070807090509100e03030f06060307090e0c1204080c0c040207150b010e13020c10050f06061b0613020f19060513120302030a080a0606080a020f0c0a 72
    0x581002060780c1690103004000e40d020f030b40600d5040040c5040017400c81e080740c010160000b010744a40b21030740c3c207084040c11034216035410070003201c2c20301d5000801944207410404a0030070310781b81d0200300000ba01c001e8440701c00141008006004043c40c00400c0c0707810504018100340b07015000b001d1111060000c07030781500c04003c041000e1481007414001110040c031304a0301145020302ca03680b020b091681468810051603520300d00112164001c1d919442009401088041240c10790800305003c0d600a40c001d910600912413440c215803140d00505000d5603103107000041d540e50b00c00c184003140c0c0206011042a00d0b0800d4074030f2094806002c0640115040f035002a010715150062100c59241d4110043c003c0c000c030102c0051544014211034144d81291800ca035030f98003540484c03c80340380203812002c145194043d220003010b400000500084d81d29440e0004d441d5920f100c540d0031100144107100c0071a114800040440d20168001c1122000c840c4d02c10703040c6140d03a144903180003821002140d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 985115692 1250 985114442 985114483
    0x10020129010809030a300e160e06060a0f0c0b0f160216091a1f03050603030f0307030902060412050c03071a0f0904060302060d05040c06050a020d0c0302010608 70
    0x4032542e00c00000c0c0c0d40300c03440d10300a51400b0001c00d002000c180e181011080c1700704500903130300b6a0710300f0000d50410001e0b20460030b210540a03401a0f40e00c0f1503150b07854031345d84c0450391700000707122104002880c440e00f4000c041c1c42c240391500703805481c240c0d4048003440401545032074000008607100300c200d0180f0030104107406640740000c0c01d0000407080c42d000009660043e004500202e4403440e05030192031000a0101e0310780001c0081d250800b0401000310b0707000308002680103c0040c1d000c0c46489403041554140900c2e1109000c0c5520792042c0c803400403072420300304001440107000c2d07009001c065102600032403800e5a64400d01a1304a4000c00c01c03140d640180d40030380043c0c50700b040079030050007074440001130b4100d565152200fa48929140e40507000380118000000e6a04c0e0350140c1c00668020300101d030703210031079061880108011a021980f4030021400818003e1141040e80c02c4007440342c0040054981a40307068070b40143c580300860440d9281c09001c07440b0481072001c1500241100c0c284178 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 985116942 1250 985115692 985115771
    0x1b0d0e03250b0a0b100e06040b07030305101403100207020a0905070507200a12050f0105101a030103170d1e15080109021f090911040305010c0c11100201 67
    0x1180d0400901200851404c240300310b000c0b55500301380d08101d50410704115070406c111801140480c0500d5214030842400071400200b8982c050b04110b21800d1052515102544ca4502c2e0034030140101c2d0110b80c01d58458408040c011580d94024500c6078001020403040a5691242c0419284100d0701c0d0400110b001c15000100000c024050f9810540302420088008041001c900e11100305e102e82c1d00c080c0b00b58a049400d01c2024010300d005118610300034001440e0030f14405c008004580b142ca01400340007003800000e2a038640a0364181d80d8403400c01a11000042c84c031403043c2d0410681e2001c050344d03c55907107140c0d0001b40403249044171010f00110301c40a50101c04045400c0950101034564181b411031001030b0350341c0c01a40c480701e400480f80043c4840044044414588070303000764111038902540c09407202a00005442180c1c820402403021200d103c01c1114084002034008020a012208a901c54941a103000e25201300c98400022103219510000800b40320a542951001202c4480d41c03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 985118192 1250 985116942 985116953
    0xc02010506010804050607200601030308060907021f0c020f0a0606090608072103021c0804020922080f0903010204090e011d1009030c0212060a051b0d0e0325 69
    0x19500003800d00f8125054a0f040c0c49041c0c4440f001026402040100413801030144034984001c2840f0440c0c0c41103824039a102e103006444000705481c514403c20491002403141c074400a1a0900d44040441d5105212000314030f14000e82001000413003580140c00500032056000c101940742680540804100c071440c08004400303e070082d80000c42940c00501060001d00c041c2c0d00520566200c82c0380d240c04a5006003400c80c140350034250b200b4400410442640c0304c0b65808a402c07801280211400e40e4907490b20804613100c0d03c020415160044200036155000c41c210170054a0000c51408030340e881d0041c81c00009003280c0c015004001c070720b9915044101001c03000d01c9044620201944030b4603a03d0004074513150346000d010b4000c400952650400070401d80702e540c40220280d400703802881544040c00c49580c490320215041e2149501d0702c80000c8005813140000b0850003101d0700d0151820306940455400350108160803c441d1108100582a912488d180134030005616680449240b8661402 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 985119442 1250 985118192 985118201
    0x732070c0f0906051f05040b0316020d08040515040512131a040501050f0d060b040b03040615140427050a050d05032514160209101a160203070303030c0201 68
    0x12101d0b440c5481c1e0140125180d8420010000c0c104030740728042042c81240459841c402c2c0c0d001401d45010110500c8040201e80d800303520416400e40035910b500c01c2d4844200c81640007150090100e50000c0f030440d585c0303602540c4094102e402003058811118030a1061401a4030481003c0800b5080c031004000c1808080134186c10310300b03208a501c2c50180b8100008080380155820b20545040005800c480f00269030b1240005004c0c0c008142d031640e40d07a00400c1200d07001150241e07282428504080300741c2a40d2521402500c09a242c0650481103490922001b003c070404001d02180d440c81440c2d0400724891120030065110b10010084000c5914000e4107140c00e5080d44820300001348203212040d1106440c00b0100c0c2c80001d10384191184520b800c940c40b8140d00c10b00041d5100c00920645142201c04031841c1c0d01e4001d42e0704100380d0704c0b28942c9a480b14690300c0f602c0d208510034061042c661058000a01c0c0206d00c54601c000d1907143d50700000d040415540c170490110b075034eea0b10142010b40a005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 985120692 1250 985119442 985119449
    0x201021608070608091c0e2404060e04090605100f090b090414030702130b1804050a060902011e030609141506030613050109051e0732070c0f 62
    0x410400a00c1d0407401c0e65241464000c80c014418060009041d0000421031030741320441095080761039074084034002d07103180ca8408074540a942d1f10b802d130141d00d4113000c40c28641000c01001543c5081c0c9846800c85412808010680d48a41c0303890014020036554003455000d00451543d0003807280c40c144200480d94000da019000c00d40c1460b00b6010581d50380100d460380f040e003085c00d00d00d046180700c205504500c10b03003400a61005a060110416000e80e500208404009403051030100c0c2c622101804101c00031a4020700c647d01c024601c800158a079080b1059052041c14807250101041c090340120400c01e1440c0800241d8408080103210402d014588402c124031503004034500740519407515405c0202000c1d80140e00c00404950244ca076030603400054481600f00300310a503198640310000e003109860b200c8130000c408111030490074941c0700e01130181015844080f50600c000044009409044844c01c0c100344400c990340500e280710300001c01085204580d4a0081d90400101c00c100c56050341 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 985121942 1250 985120692 985120723
    0x2e0e100f15180c2607050f0a0903020f03030c101109090406020307230d09031b060b03010e3d0905060a06080d140d09061e0501050402160816021903020102 68
    0x1803110050400789018913440703261100588040c1c1d80c40f030030160b41d203120f8107690404028001803004d216a901207062400e40788200c0d021700302c9601c810201603880c041c040031400260016901c100c03da030910741c000d040300a034810505081c0341c0d90800041c2c0c0800201c030180c1c0d04c640c0003c200011035030b0000e00c10b00e8070100b420342e4070a01000c100042d02c850213090102d00b0820355551144090500500300b02c240050090140b5941c20198501400605440003000f4080d6007031241c8283c2120002c031f900c09920310303202440e00e561b42405c5a40f80f044808406070010a00d200c6001030051100c5000301d81d03d01e40108000d01c1d40e414410300010855070540d03c00c0150b50825008052216805040300e41c52204c440310b51501d814402d01e1101c0244501a8000c24244c03400c05041c05e0459207028902d00d680301008108080d80e43c80041c40264843d80c0c01101000080f19044000104c0300005083e42d5110104460b905645680c04500d101e0480084c131090200c0c0007508004640e030402621403d0f90101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 985123192 1250 985121942 985121957
    0x603010e060d0212010606050406090f080d14040306020403111e030d0e0a1707031e020d021203070605010b0309190b040605090f2e0e100f15180c 64
    0x40028000c004014003590321078484001c1002c10b55035000c0e035440c44040342800030450030f0360fa1301010700b20340d11502c41d26000c070382c4500f0009860741c0700c18040c0040b00c15000207020a0107060f00104d50745d40311604401c0000c5020310002c004a110f07880508080e512561035420320300ba00e40100300350751600744107132904000e01502d0900d241e00d000c076203008044a1400c1c0070811244c0030000800001403a006049216a01001c04901000000350102100d005486210442e0311035070354070708907801f0101c0182d045841000f080005042000819490034020800c6d2400c2c40580d45c0c81c50261007080c1e0144000f94004014031544440c01d0060b41c85100d6410180966552640d8850080c038074000d0014100c5581c0700d00040c00382100340264102904031a09650384110709181103820b0a003442c0c0c01c05000801c2034183e081709000c6c1d205002d50189140c0050648400742e034200b130041c01d051034078401c3c07842d124006900038000c201d0950b405089010108070003442400c0a44045400c624241010403011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 985124442 1250 985123192 985123199
    0x1c06090e0709180215091008040f0b10180905010b010201061a090102011d030a1d1807030216050105310311150f09150c120a0e06190b060301 62
    0x2480011982c4040c030104001e035040b00504030035111031070040c0d040f01000d004e80f515940040300070500c18000700e9840e80010403c100c2250b40c4082210000d003400e00000c3d41001003000402c20320b03400819140c0c4850041e072a001600203107040011140540c3d52a4021501044001e00500844010070320007005000e03e42071510301c1c40d0084200c0c03606d004c00d001802c0411079200f904060f900d61005020302010800b000c00c083d55070350007011a54000341c0d1749032003401b291050014002d42c1c4100140080c28200302040864200c2d40d0160140042c5503082102c2c001a0340d03207040300c4142d02e000b072000288a2a00e11988000d8190401c1e11001d400d004204104d80e02c00b000107200c50054251800520075002c40035610300d0600010445014130006004104a540d26601d401d40708000c818191403002c2200ca5440b408580d06603003d605c000402c1c00030060225610582a81c09452850042070210000041c1d9040040a33155202095186c0d80301411500b601d0140032030300102074402c14910f42c034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 985125692 1250 985124442 985124471
    0xf050d1202190e0301020d020301061d0301021608090409121107150c1e02210d03090804150509090a0c0801060c0c030b0a0906050c0406110109020a0605130b1c0609 72
    0x201c0400314090007081d1080f070a00762000d41c10f44100c0c1108000466495841d01c07800f030074880960a10860300003004200d110a81018001e440c1d0700200590401102a02a500c0c0b0895400003900c07e6000750350b44440c0008a01103c446000f00602a25075580c0902011207103402c0c0780007034002041c2c1d090407904a140d5150f2001c000442c56402104c03c1c03102d241d001560320151201c0d203901a42c48112042e88906c888944042140a1881c5104817101c240c085001034007a01c00705080130b40040002d010030001801d01c0700c0c070603000108507c4e006103001259000540510f400b902d0b6104500da0741c1c0303030016080350060b01482c051b1684d410500400d4929030751308518241a400010503c44140002c16001d00e101d4010101c401c0d40800c2c103121a18040019880d580c005215000019064600e130b01c1c01c4180610401030b61580250400c80e07010304101058503c1c0d408180084841c00345100300017154030710b000280c140c1d03088480d41d01440c080c100303040105581103a04500c42251504980c0054281d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 985126942 1250 985125692 985125727
    0x80108030a050a11100c0905101d010c02031902040606080c030a0213080102120a0c050c030f0c030c160518150f010e04060b120f01060504210f050d1202 67
    0x1500e45169a00c00c01c5101300d07500c4074148640c21251107900c40034008412603400107400301c035030366955461480d503d10030802003c16004410010458045ea003480000124503180d44039103042c100039008283c0b03540464135022030b02c44c6400c4550702e0503411000310315082c01107100a003594580b40303031542001071a070400780c400901113041065000a40d92008102c1c403008000401031a0021521464000f28600c8511022100c1945192030901000402805403056500e9a80741d45e00540c14040c0714446d150301c541c810010803907207100920116442403800c00191401d0368424907200c40683c5030000307200b00b90740c8060f034601d103804250041100d0121046000b0007104002c4958001e45801c80d001620500781008a95030000d05004010840750041e00003040130044001221030781d03075500807008150100a0150100041c41040100310032f000092840204454400c0075265485890b40c40000c04c40040508446a8005500ca18041034200c0410407880d0303441c031030952910402005410188 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 985128192 1250 985126942 985126957
    0xc2a091b1418060705060f06010915030504020d0c0b0408010506040504082b0c0504061404060e131e1407020705010e130608030a020606270601120b0a0603051608010803 74
    0x34004500d50030a0488885000308240020348229903800c13007400d026445072800c84d0070641c2d118045000c0384995100e0006001161300d03502c0d8160800103400d80c1180134081c06002660b022000803195400304020500440c01408990b101c40c0d540c601c0e00b0400360035184001d003007501c954985002c200104010404071640203c4941264420040c1c610304103038042460f40d494030340b0a141500e1800a150840c0090080d64600d0311049a09081324941b40e01c0b901c45c038010640094641d900c80c52050900070103c1041d20002103001c40e800f000700010400c01c04118002d1101e80c5c0d00c0340c090402580c2008101a004006c2e0301c041c042072801c280028043c5140c181c2c082d4000c2c0811621031000f0101035100b000030f410000203a0b6960194084001d5450078141c4920703108218502a9600d00038500f0b40c10342c1d4035001030420044540d0740324019221082d68440d00c0030320345c2d140ca1040c0020356030104c011010380340503180007030241041c9407042412140c1051031010301003006c2c01400300c8500041940e080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 985129442 1250 985128192 985128227
    0x3021207030b220e100c0908060448060801090e1209010516290403120207060204031b0e06030d020a1407050a030302030a02060c12070c2a091b 63
    0x1440b0041c00781d4020000e0912010950150304005104102c0540225500046c0b0342da9000c0c3c015140c018180e2039907c1958014200949030420b00301e0011500c50008070038105100740106200301c094816052065025901159000460240320365504810b040b40900180c21003000503c3c0d0500500781d54802413000d03a0040d15010880c20f02983c8681c0c200e40400084801414501c0c250b40341800c580b100800207000c0d90b08841807a0310381901440c509a104c3d6400d5928040301c0c4c001c03900040000d504c074241c2071b5000f5400b0000071010501c0302a0b4038034100b20341146190701d9443c0004c201000d804c041d014500ca5040340355080a07036540055407500190304040125040000400d415207844425800b43e0780003131800d10000281078002c4040c080c4500c0a4083d44d515a03600d5840c01841e10500300400d140301c00003004620300d14410300708143d85610030b0200000c61591100c560541c0f40500900d00384030a0b079140107002c00043d078018036020b4004a14407c11548008402078040d51682445d03154 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 985130692 1250 985129442 985129489
    0x1806040318060f2c06180a060c0201050301060f090b07080d0c05041d060a08070609080c04020703210e07180b030d1425060209211c0311040603021207030b 68
    0x2c01070740d00802c1c1020100504213a034944804051486c600401000640714148061001803d10f0041c00c0804800e94169101455a070030086c00781e402a42c980304100400c00f05801c0410302c40d5801c0010141107012b1040140c4038000340b0f1441d0241c460041d103581c2000703001c1c4420402c1740744400324101124040802c02c8140c0da22880400c081503980e5002c0b05c0188038016001031000d4000c03600f64240c4e5001c10035100e07080c00036001d00c800d83c070482400030300290206020b00d15070508000d280390342c000c000742c2c040783d452001043c0918000c0140c004100d1400c43c42040b899149861240452001c000d50243c003540900840160100d030410182c0428105c000401807001010210140800d039120f50340d1807440170301420319000035000840784d280030b142d102510b00350a0b00302100d1031084000c048001e00c04186074503d4034000c1100c0c010a4004e054544803100341c1c22403640c005e08060301e01d03940d0041e104c0400d0090760b0310a010241150040c1440c02c00c58519548602c042180c15130010901c559 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 985131942 1250 985130692 985130747
    0x1407050a060f1101150f0f1a070821070210050919050f0109030206180a1101050d090614070320071b0905070309050f0c0f091806040318060f 62
    0x440b401007400c03880085520b417002800f0140200003200381039031880e80100590300e440d04206d00c1c0c3e0001600a40340c88002580e60b0602d0a0f0001c00205030040c0700e200304a0506038078560054140c42c0800060144504030001c020707d1a604006c03a10131015103104c280800c0c280001e1403038880303001d5101d80d008945074024807020710108110140442e240400200400c03562428001d49400c029100703144003610045240004140001d02018596040381c034131a40081c1910054078540e00c8190300c110543d44419040000c03c10714400c0810311200c21201c00740c00c0c586160f006080303905040030925a22819030194060621400540c0c81142e8000d81010341c0c1c95171101030300e0307605c0e030503a0150840d07d04003010440c00d1a410340201403003a2240c8210b03100682c8058032140c0b6240726005054101d00e0303501d0b0511642c0380100b50550820400210703581c88504071401c42c0e0a15000300c9096020074814484001040c8400400380010101883c007075900314841203005050340515071150740207048408415 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 985133192 1250 985131942 985131947
    0x917030417010203011a040312030b01030e0a06020c0d050328060308031302030c0406061b0c03301b02010c1b18050a09020a2313091407050a060f 64
    0xc0e0040d0078500d0200074040d60305418a40030303500034041c1040221560184444403400001505c059039030203130905804005c0a44200e00828500c6030b1079040544641002c00c04082c00d0114141e41401f420003da40c440202c0c0c5068a003805901c3d40f00e04003e0204200880386100c0d900011080c0310560001941d10354000b50fa00180020340c001800f940400010311a81001c0350243c2c0b11140e03c264142e13844c440321202000211141362041c2004541c0b034bc91000c0c4041c2c40d40140d198110300c1582c1007201c0c0e41c0c490700c4100c610030b56243c88014012858900716800104807560350f4208c082454a001d0320341e00d0b50707128006510544002818489803040e62801c01c0680051070780016080d850b4030454641e0b4429801e0300c00800802c40d01d6148c41d100214800d20018000e10b418290040c01845401e0f240c610300350aa403482990744544056084445684c07a40c3c0c8819101d0300c440c60344030201d40c42c45c440c145040500142074034030b100d60744010402c0001c0d407606800710701242e5890901d1109000801c205 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 985134442 1250 985133192 985133197
    0x10f050f12041b0b09060c0a050703050105010f0806070c08030618040312060602060609041b030501060e04020a09090201080a020a020c09040b010f080607140703031d0703031103070201091703 84
    0x400151240105024900465106529100e01d014514900c0e01c0e041e41d01600c0b02d1030350203010314813146600304002c3c480c904083c030040c0700c11810007040f035001010903202d4900701b01e030941080300d05946400c0100070142015440c10f001c0e01c80b0350043c0c4007a050880c40a021100900710041c0070000110018545940b034900180100807401c190048516151400600d15010a41c006448618011740401c1c0c044c400103440c1d10680001d001c010241d03c0741c5e2503150200d4845004101c000360500702c080001070f8203000301c01c014805d800b2802ca00307007400c0c0b0400025900d10b400804c4401d203000201c43c00340c2c1c1d1003102c1c0d81d00118a4040180e40e804000701c120b0604106a0089401600301000d1004001c5400355150403606040c9450b0144d584070607003503803504003d64400c80090401400f4109400641c0010402c091090400181940103692009542c1501032800c008030f4119100400074541c011481485c0165040b000d0361802d4800e5002902c0c400103400796841522010400d115800405c004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 985135692 1250 985134442 985134457
    0x180b041502340504020d0606030c17010b0702060705030a2a08071103011b2012190e0a0810140705040b07050a06051807080c101b06020f270f010f05 65
    0xe40d524803006d86048050074080c40341400107490b00c4904940c0612400d410322540c01a40d8089413180d01c2c0460407001500300c004280e0344184100601070018600300000c1c010082d042e254556407541c0c000c4605013001039000c1c00c4102c0c9803440c10080001d0f800704c045600310b0760b0107004c420f00080b1403400701380105180c486042660005000e11140290802d60031201480080001c100d0b100d10780ea4800e0300c1e2180d500d80c40103005800d0101410100002c001103403011440d03d444080a42914001250390b1030f6944550300340d401401403004000c15601540b9046d1180130000442810580002003a900c603e10072b01d0814030012844100304030060103040c43c0c194010406014606120030b100c00c06e209040c0c0c0b51180c2e4031030743c000041c40c02c401040440034014000c01501220b9200e00e070a50b807c4401040d42d004107240c5400310000038001d032010b04224031010b030b10681c4800c10b8003031703e40700307091084a00c10090a585083c0d540e02d541d94002c80503420000e103000d9060300203003d402c1e2824041c0c0003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 985136942 1250 985135692 985135699
    0x312090d0c0f1211031b060c030903011103070809013303062a09080606120c031213050609030a3f120e070303030c180b0415023405 58
    0x80e00141c1410300d10100852140540701101c0c14500240c00c2640d1b4140905180c65140e11038503600407a80303820405840a41c00c0c050940745081032840000b821101407190b500c4821202109102440340c0c0031070b4065000b84008000c1007507850061100003140614405650f2a00c0d811281020843c4803840c5003009650000c0144140580009203201c100700021a40c1c681e4905c542111454a00c0b5640080c100c901002c0034080c207443da1740911095000c840340c0441203101d804070b142607a44003003101075000c40c2c2c9403000c6500c440308020010003258050b4000f074030525050040d40c246035008201e900d03070103a01c0761807001c80a20418025000300035244029603504481d50b6081c08520120343c0d9980203000c56a00c4610350904151031108803207030300c1010070b482e601580040c40024080e5004800d02241403c14102c03c144826103c840800c084d0401c0c0100c4002103010051068892522800500940050602d440c07101c4c4026000c0d2800045070103070092004030070500445e240c044103004c1e10024 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 985138192 1250 985136942 985136969
    0x2090606030c04091d0c19061209080d09050c04060503031207020c030609011416270b0f0d1803120507050403020604120210090503070509090c06120106020c0312090d0c 74
    0x454440300f144c01e030b60b005400c1710701507244011241d151922010440500d24404061500e003403040458a0701ca1090303503400202d42d150100c901080910028101c1e101f000000801c00d4409131420506002548441e107014500300103080c01a5680030085c0c0340c140340712841400003580c0b1650220b2400d81c0580c030440e01070040400f0311000d064103421800c0c4200c441070035070f1110f40b55160700e9030303020249111480004092070040350ba4902200d406203803e55461444110312501c59800c44150380c0300051800b0365020020b4090705903103c50103005a1341c003441e01d00035210307001c07030307e002e420981c0010060600340d94800c000341d03405004809590245802805c03250301ea41d2622142c1c00108501c2e1000c2e840b400b03015048194a40c86014410b01b5140c0103005050014601428403262030750142480c0346600880144102e01d88944020706035040703002c85050407951502c2000b074100810b00300d105010344c101500b0180684130440c1122a01001075400c12049071030742c206018020a69000980c814001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 985139442 1250 985138192 985138211
    0xa240e060a050a120c08060c0901030b040f0f140c091804031106010608150d0309050114070f050102091003050c030105010c03210e011d0c0103021c02040807140d02090606030c0409 79
    0x468038600e12140c842c26444c10804c1d211b5020b50741c0c0389401c40314440e0301e40d030411000310154441d4010f05800d20001c4e101080a01210f50705809840c0c282982c90030490b03480345621101100c070400150002c003000003035440c103404a40491681c1e010780c0f1000c0039400011303000c1400c00d445495a0040200580151030103561600c10042a1440a41e206880811800c0c04840146400c03a00651210741c55242ca0212600e080e0056848004100303e15940c3c840500c0304c10003194803c000750710400d03c11000140d460481c9410005007400e404660750070546000d040100000c24181103d066034001d08105011140e18a000c03504085a0200c12010a0325078031f100c01400c0c00c541040151600c003000900050b90400f1401445903003040364030070316600c03900074a03502c0d5019600420707034a80712a013100400710510745d00501ba680586d0180405d40e021032401c006102d00c01d81e00d5800404111011075546617190001602c001c0003800040c440c1100002160221820381c0c2150018070f401d40701404070000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 985140692 1250 985139442 985139459
    0x51b030405071a071a0f04260310030308070203040e011a07050129030f150a020702120c01090e010b0304030815030f1c0207150c02061c050a240e060a050a 68
    0x88494220b801c031700d80700810301406007518241c500c12401c584100c0e1003580c5a8440c28208028030381440340080140620f144078138400340003548203040c91114544845c0c43c52900030000c00c0c0003002c940442d0405c2c070050000c52841811a41103691507410820002c1511180700f00718462071200403d82e601c3c1c0703410121b01d001c0400c1c00e03113000425056000c81c01901c0e0024551680711035540c002403500142d08400d0713500f00400b04a0380290f51040b0050034181c0b9940400c404031020400b0000a511001e4840407a6a11082c8200030300401150815554540130600c0c41d2404040c1c802400c0c4580c2d040003030800701c0c1c120032203034629400134121003860420440c00c1c1e4490204172100b602c0c000e10200c501002c18000138800089951810b02440080301c940000c4480040e0700c04104c0c2e104500700081a480b006e294219030301207695030800101ca0800c008414208d0b06090442c0c4105000c2000441004481c00d1003071080703030508400c0d02a0340e900d5400041282c00e1030b401080d800100d2407008680c200d03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 985141942 1250 985140692 985140697
    0x7060b100c050d02031e130807030f0b1b04090209040b090a02181207030201140403150c02250b1606020d1415150f270a0504051b030405071a 62
    0x902400a4520f40800710b20300302d84a1040b51601781c0c0c400307007002d005c81c00c05001100410b0b00580c0d14402d441c0b01500c81010a0a0030380513441500c1c240d100400440a0060310f803101c81e0401c11a130300c0414200080032560080f40a00d01c240c800d22603000c80c9071100350300c554100d0810b00c100141100418a0715074038a0001390031802000400800700444085582029483d411440c5e130700b03c004202040c5987c0c011102841590181c00b0592814000000058024650b0b1501a90106004103060b44820f100030300e403002c0401c5400384188080110b00c40000a262003171b0540781c4036213405a0b48c041018007050340c001854030050041b0701c00180d209100a25500103859402412180342d4035845a0344006298400204030700d601c82106200400341160040040c02d40600d000f58090901e035142c608c0036000030301102a204c4a2010b400b02c054585424100480074217400c540400090400b0881d0380030b120280c0d4888040000004003083c1840010844140101900e0340c0c103181c10001d42122080c1038 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 985143192 1250 985141942 985141967
    0xa0b0a0303030614040b0d060509030c06040f0b0f060d0b07030605060403050a03090b0c070b030a11030a05010f05041505090405030c1207030e04060605030f04211e18030807060b10 79
    0x1244c031601c0d01186041c0c000e691450034001c106420312103840c2c540d80000c0030060040501c3d0b1108000c01c40c0b81400600c03880344114061410101303020708138148085c070200020f04103281c4e040c9880030800660b440380b200e8034440fa04840400c0103551208802e8000788625040b0941c04000828004100304000808a0b1224070a51722201e18030b6942e28640804e0082c004c000d0700d50b400040e020f0184002c904081d6500041490012441d0400c898228000350b000380c42303080d041a11400140020142e884041004050a480400850380810f0408550700400d01400d4400c070401d134081000d004041007602c034100151000c0c4c1301038108903915a0404d61080b041200441c000710140701c043e241500c10a03003103800c50f0700d600b46141d81e8034810400e42c180040048440c8600c0000400c007000c58420400142c102c151107614880b241d620400c008480900101800c0042c12071002e90070440f00010030b0100c1e984a01c0d03094880e041480c10308003902401020300d070000000c01016400a5125503040c010703 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 985144442 1250 985143192 985143209
    0x405220b0d0c031509121b0611030402010e01110a0201140c03040e0106112a040f020301062a03020a1209090c09170a20060d0e010902101112030a0b0a03030306 70
    0x104c01100d00050752110040602000301009054007207078002c11801c400000441c440640c20b419a80e03407030044900d500310f0850b1703206001c02000115600410f5140010109090009200d1040840c25680d408107000007070402010118815181086105881506400030142c9440f65245d400740f00880c0c1c001d02c900c200007807030011200c949810110b009030b0542c8100010000c0c4040746034041e400140841e00b483d400540e00e01c00c2d003007900000e2010f540a02141e591b000064507407800c003144140141860786d0807800382c120f017210001c0c1c0c000072013a0107107900031261008001c4809066031045000d0b4881243c0340c3c02e202c480b09955911410103401c0d50030582d146d180518480c403400d565001006070040440c0b2043d0000001c040e144117070703003600150051401745849040e50303214099440c0d03c104145161744034202c03c411807500507801041403020b4586003181b0701000242c90b6480407451480d010001c2c00001140d0610000d40000307521541c0503004c00302c2e85130380c0d2030020018819031240700c83c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 985145692 1250 985144442 985144463
    0x4050102210c0a14090a060302270f04051305032206021b0103020c070503010905061012030e1915110105010902040f0302100c050d081b0405220b0d0c03 67
    0x148965041c00a40200350304800c2c1802c0070409042a55009001e481c541181c1609110980441e0b41d00c1c0c0640c409003040756030158480804c0d0908480c2050400c8502042a078010440103c50f05c803030040e040303014401c840124154035041102d04000402130b03406401c0740070000701011140000b109031030b945030081d02820446541e0f024120380301d1f0b896443e503002d20100301c1150102580300e50007034024120540c0c01d580100d65540e0000303084031204042198203030444402c20152062403070700d0000505403c00b4108000340300e036500400c9120100c40b02d503c00d5400001113814560043c402c0c6018102e5240c85030f01c40300c1002005490301000c100107016a60a020022500e042e0600a59088a01030b501d00b00a1342d0640c0c0c00c00c0022401c100d084401c1190300700c1100b0209008001c0f60000a9468a500109060100d518810458034196541c00040301b0003040049850781410808a908548d00c84c00032a404481c254020301291080c1c550f10808801c1a80184880c10030b03680c085a104448166 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 985146942 1250 985145692 985145737
    0x3090b0909180708031b0c100507030819111c060f030320061602070e0106080c0d0f0c0f02060105040c09050108100801090807150504080315060405030604050102 71
    0x122911480c42040c0d0040c1c08840812840c4a00d0001050b4220040c402d880300e01d600c46101500c1c54001c1014101c915912030b58014004c8070901a0004206064448501da4084640060040d118103c8001c0401c0800000981400540c0c40c00c502c040032042d20034400040c40001040b041e4100308600001c458000d25050300d80c1c00b903841008111b8056030003480d5042c0c0b0b10346080d0f44140c45034403841e1054101060360124001c1c1400b4191143c0c42001249083d000c40303000c02840c0101c143c0010080d203000d14014000c1d0354000d200d1542c0802c03200b612550307079020038034550060200078110700c0000c5c0c00c09840ea018550092213020b0440d0041e07084500c0360703030385004100c151090180000046001ca60702800b00354858001c3c254401400ba01c403000440c1e403848210308513510a503083e00e0001c07010901504004c251200c0001d010b02c0600c0138030481c246602d0380030417403001606130700c0c03206081603400d00d082d25040159401400c0040640310a46440d06000d4041d5000d4104501e400800749102e5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 985148192 1250 985146942 985146959
    0xa1410111228020a0309050604051c18121109010b0912060f0403050705071707150201290a0e0a020711030f0c1009030b1303022a0402071a10030309 65
    0x3002501e441060b8060080000c068050082d845000702608241d100c3c14154007040c4208812030003140300d200101080f1250410010340e4403040c9890400b00200d06111394200006031001406882c45241d840b224051645401d440448440310b0a64200b40381c90000220000d4040103003c1c540000d44400500500c18422951a21402c94007032400c2c81c8400041004641700304050548580700c0c030101c408103a102d0829244403c070b00404004142c1c40a24140141c00e0320b101c1c004002c030440d00080c00070310030300e091111038441e0b94806003040c0e10384034025058a548103c07196008040e83c60b592913041c142601d200b006940b028009a4148040f001204198100058090ba000c0800c901901401e0039450810500703011922f881402c010540c0341c040003094402414502400080313407461541d030014503029003040c1040a9424880b55810302c0c060191110100d07100b8010350803030340140c0c2d0750703c2032928103402214080e003d005543d103030b020860622260f103c88000d4034002d445000322196241c4a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 985149442 1250 985148192 985148221
    0x90915050123180105040509090703020312041d1b0d0209040606051e0c160b07050d02010c14030a0f09140c0604030c030b04020d1b051806030a14101112 67
    0x20620340d0000b00600380030582d010f00c103600c2c1200145400b51600b81e480000800d0010140c42600b03140c0c002a804008614082010415960890035881c0c00c2500d05209101c0c0c03101201c10396110300642c400003400380040c8403000c19904031440e50040e1100b100e4002d22009400c180c0850b4007c2e4581040855042e02404c15070741ca0301c901c203070110030041210034440e0954210261405441c0303d140d0f000314210500d01c45820150907500c1e96562586800e052043c50600341d00c01900030341e40f400d2103100d00154040700c40300c0458080703171089039240c81e19440b03000204201412070304d405152000000402443c2203140584052070411140491440c1007001118480c61000401c14445002e0410018900c0c0b04c040381d00c07900050003490b03020815151110702c0c503040404040c0e00c40d14000309000608d000c4240c411120340842e100d0245182040c00f195852051a0000e42070a003070280448018004001040d20300b0032000042c04009003a80e8501c416030807401d0703241d0011000350300149450441042 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 985150692 1250 985149442 985149497
    0x18090d0e0a081c0c241b0203030112020612131a060a051e0a0e0a060b0418091e030302030a0b010f0c1202120c061e04030f0f0909150501 60
    0x6059282d000904442910035090040b006214003241c00001040030f0080641d031803198040c0c4a00b070015811004c5c4d0072a12444950307004800c103007100c2400b95500009030381c192070703296000c2c40e015010745c00000e150b80940c25800000e4150700e020003200d5030408030382d491540d2268080403070009410917402006441250070360740004c5014030030011803400c1d1002d405070100c10014801e00c9010308001c070304460395079080112200c54036000c0c000d06982c244034000081c044004103074281400c0599403044080d844000658a81d2500c41304414454107034070604249503422401c1c810241d06181c042c01039001101c8100c10149881000840d9500540305c0e408600142d80d90044800140c0c4d031740260854180721a40e0452140e80700070b2969168050003001c4a04505004141925200070f06414140504500d4070a402400080c040080d0304520000500801c80c10002c1c0b020842000448049072548e029030304003030038880c031003040711844011141940c000780d0307170007501c408c20190700d080400da441d6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 985151942 1250 985150692 985150709
    0xe0f040b04080a140d0b010f020109080706091b1403070509010b030601140412030509030f010b012a0f0b06010e06030631060e0a050f040804060e18090d0e0a 69
    0x400100010081c500805099405060401e0f10010164400032690440e1175892602a600d520070202980c2100781c0c00300c000345901c028003c0c003100d80e40341c100da4001c10100402d8030307072101c00e901c0401590700c0d88898008445d00341c04804540d100704102035100c000c1c2141d8040d010320580490703070703081c1a40218141c40d050900c0c5459074503541c004441c640343c0d0020700d0903d49000e10011a0b80d201c103250076285140650748854460000b50201402c01040c0740441c02d0607854000c020150f640c00c110360386c200801d005000011505118600e400084065000170b20110072401050708100007040540c0c0516420303a60305403d20122800c2c0110344c4030544909511803418007500140300200c501c49206603842d641c104520541c1c4840c05019129541c21841200100c0e40400c80408400c1c071525030701c45200f8401c85150704190300c44c003100748101e0041c0c07030411144100c0040300784c0712840007054403003c01560452519141030750a84030502e041407000003588a01003031a0381d18000c10b40e42c01780c40d40700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 985153192 1250 985151942 985151963
    0x1d0409030810120b060f0d14031b070608070507150c2106031106070c05060304140d090605120a1d0304080c09090c0111190507090c03020a0c021009030506040c0e0f04 73
    0x8420800c20210301c40d91a0b6000720000b007d01c0000c1c013103280c8403101010718402180c440000c0d070036000110360f1502e40862542e000e07041c100003284d44680d80c1500103005040181c0d5414150400802041008600100751070803d0000c00c041c590110702042e481001d0246020407130001705159041c1c444510006d80340c02c03c11030b083e01d91803030250024a00c1c00d2090301c1c0500003598413404140142c20845007507812986000000c0e002c3c070400d2191600d074000d14903103540390302c0c00d1070350140040c060202c5010354281c001d00007030007421351503000b0314088655494010008282e181119a00da000c2d009034070450040782381010860030800e11b468091940800540309107000c00c0011a00c1e2021000002c03400e10854802012014169410380d18260040000e8683d40782020501c1003038548940700714007010320411440300c034148d010703860111495040395025a803485105040341d040081c0e07040138246008000078007041140e840c0c0304000300d644030720039445140c1e95008800c40ca0f000171540544050083d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 985154442 1250 985153192 985153201
    0xb0a0824010806040513050f0a0b072d0306080a05071e120b0402030304031505040204060e0408030a0c020304051c060f11180301111207140a0e011d0409030810120b 72
    0x1500302c180d100364640b00c00f0309502e041c1c7e22901e240640307034107038030301d01d0b4000301c4114003072009504205030300041c0e80c2801c03e00e181c00c01d1542401c001d80320b9a0143c01610003881c00d04118420f070040002401d10708100e40b4030304418145580c0305c2c0a103110f04601140503403910350901044000360001c030713140c0318004d0010f01080c2d10b035001d0500c00204100d0b4107000800001c0001100c00e000c8030103107090014001540d00e0700e8414401200c0141c1c00a02c2c61030052010080002c50000480b980041011004550311040341d8041c1d18502a94024590006802d441d04d0a01038000301012031440c0a0704091045101c280041004c4600000103144851000c20103055010701b144c2842007000320140000824805a0120903220303000729403001310000501060005c03103035001c40707510484011403034547e1030f005200b1000b81000600b0388165050110558103078860040b103460f042ca0203807010b0414001c0d010f9a240040031008100da0103401c034101c0380303004200c51000030881582a640300d04060040d455 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 985155692 1250 985154442 985154449
    0x20405090903030907090c0c06094121070501060506040b210411061e0d060801140c031609080d0f09060c020906060702270a0c0e0d0212070b0a0824010806 68
    0x3030390140e410b02c0b103c4561400300c030034000503205950bc1b98004c43c0b0035500c400c506100d044a81c00410300407039005004003828580c2d284001004088807009041d41c170302d0185059405080640d10007a4004008500040c40e1161a030051004102c1c60030208581d038800311541e0b02405042e100540000755050703444010341403d030024071207100142d21000442c601510310345030b140d000f0f0142491031500d500e820030501c0b60900540c015901d0740036051000385402d4000c0e0000b80401402d980391030381004c0369101c0660081546030064450f840c1070b03031000707074610074003904000d032100070040091024800007031114440e0103c444880c0e80200300c959151140020460903802c4050141d03400034400c0308981003500003030307a80701c800814861000c0203440d021100310100d64880b41305909100000c00701001659036400d42c02c4880341e040f5a000c0e05030481c140103e16052041d0488101d1140000d40f48100642104c0c0c894482c480ca50034010005074400a506604884024400d0200b0b8004c3c000c80c00f00e15 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 985156942 1250 985155692 985155701
    0x10606020a0b1612060803090109120f020609040b030f1507020d05041a0405030a030e0102060a060e040f0813030b010e16050a12020f13050a0806090303040809010201020405090903030907090c0c06 86
    0x15668130b441c8210403016840201203c845a01840090307100280b020f4455030042c40030b50003000001695142d00c041e40e226442210900c2c80e0007485194009545010342e5519884001d401e40c0280407190403060320701045a031292495042071880101c00c000445140c0300141e03400392000e040d0340d400e0400d0328150194806801c100301410201d0303014000856151030170020030000900907564103d0040d034045c0003900305400509850016030800e442405040310400603150000d40c800240d242e0801c2d40d040080380c0303000316a07001d102032038052000000d01003641600b07816198100020003164031100c821315440c0348610a40c0002c2401070081024050144211500c80c2c03511410140c034080f400d944000107a0300583c00c41d00d1406429800b031103141010404d0501030442d4800400032070030148119a640d00005200601580d8002a2111a0792003901614010500a429088541403a0892a41300c0d04103c4d241d8007188900c0c5000101d0605a0064034030001ca99201c440107219640c69080141 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 985158192 1250 985156942 985156981
    0x21b0102070510031401060201020901090e060a0902030f1006030209100804141606110705030726070303080103050f0607090b0d140106030507090e0601020331031103010606020a0b 79
    0x18000d050001074940ca0310315494078402c00f02d03034000810343c84d082a40030300101d041e04228210380c41130240da10180d0700308052006890305040c41e09040e40d01c1d81c0001e81208080d400111801d4000b00610043c0c884a084060041c89040d02c56048035885d00011412405078095050b80043d1240d4800a040c1c028616507400c00e014000911740f01c042094218545201c045c0010000020a4401c1041c070b640950b00e56401c0d4000d10207010020304c4d00d000666680450300412060703044024001c030303080302c026103140d040401301010b4407500d5940341000303408120b007480705071620300520503605c44506005c40d601d032043c500380c3c43d0840d183c1e05211026030385030801c2d00c05002042d903a001035420100007121050080400c0d17030740401c1d10726000300d000f0304141c1c4a40c0004a100417038014041580c5c0c010003070f190ba4a42c1888101c2061000f03407295000745051900300300c4607059014020040c0800c5048a000340710b8140c0007801250340d5550300326a05c824140003d0a82d404840c045000380800304a1071062 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 985159442 1250 985158192 985158197
    0x306130b2d09030c010606080c0d0c05040810051b0c15061305310510090c0504090501050a150e0c0c010902150405130e0a12050d06120204050603010c021b01 69
    0x91107041c21144141e9000da8550b0035a034404510b280e04d410007402024050f0400341750004403400d1000c082030a500400c00011503107525219034030801840780055400818107803007200c40f000c00c0170b00150021300c0c056030307041e41001c0d111210010282c0004111020b1440791002091610129025010f80060142900780e0040a103148141d2062a501034030340120107102e00c80d8401d8072020f0b001d41007280083c44120121001f01800710100707102140141c440100504042100407480c0391001042070315800c40c80d8002c0c5022046024000f05610943c8200000c080401800700c01881c0c4144810051040c51b0303004055a00042001750f410340584403810300c01c0004511001c1c1540002d4080025140c0c0030650900842c00304500e181c00044520140c2c0c0c0b1080422040710441c0c5c2d00d6440c2c140001d03000c2c2c002e900303418030218a54412421100c60038000c0308100009600c941e00c1c1082c0c01e1903108141d12550074a0042203c48ca01031050110a69254006120803503140340040820170078140810705 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 985160692 1250 985159442 985159501
    0xa05071b0804090f1a01020c090f0919060b0f03011b030914191707030c0813170304050f0a05090601111513021c0302060a0e01020d1104050306130b 65
    0x500b90f0560081c0034194003000000301300d8890381079440010b5158810f410b0304641c003031080e81207545c4410b0b0703146400059a041d1101240d55980c1d45500e0b0850441d0380c01c05000341102c583e000d02c6500d41c42543c0040c02200c50081002c004400c140c203a480c000803040031200c0952212130340600a5101011042c8185c080000d003442c00d0300040d040c030048440c0d48011101c208007000401007403014011189540108550600c3c0f5030741c4005000b401c44560081041e100002c1010141410680c41d10040407511080340c42c9256a00f0782688070303041072082a019920090318010740740740c0013510200741d0f003000e400140e0030b5640d6401110481e03100311440086006000d000c043d068681e009251054180314000c141050f02481030101d07610b031002071004000201058003001903404100c40e81c10241170b00007c80c0742c4001060080c020311590101c040c10130724180c1240900c3c820744020300210391049041e969503a031450040e0f6421840c840005102c109080000b880c2000035203100c0301c003056508807491 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 985161942 1250 985160692 985160699
    0xf090909080a090905010312050a0e121b03010912180b07060504020a0b031501080c0d050115200303010b0703050c031605100b01020c120a290a05071b0804 68
    0x2000c5030380c686400d89668030001210101260820445002016400010000d0358599110101d040948138060420440c0002d03c410650340305002c4181c4070040100b440c00622401800c0580c0d07513042c0301400c90000402119900c4a1a0611440b10000d40003450707100e081c130f0941c008a81c440402074003403001c00107441307000c1403101d8030b50007500d01e0910448000455003001d004028541105501000c810001001000001071706405905000402828102c007180c803991002015405141c01603010b60f46000000101003c81030051681122a9240c0094201e00c906032075415082c1c416507142180c0c810001001005c90741801441c209009241081c108000c0c4517a8505651021603c103501d044032440d20001d0000038802245200c80010007048030b82040c000103504c2d607a20014080c850a5081c0485206880034411200c1e215031024520180c2c002c0a1000d01411a0b20364060300c83c801c0c42c80c0018820140c41c0b203014000c540c9a21342201d00264412003c0e000840d000302115440c90a00000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 985163192 1250 985161942 985161959
    0x60102031c0e0a0f11090a090302030a0c170c06010e0705030601020d08040f1709010f090f030b130204180b01140d02042f04080c030d1e0207150e010305061f0f09 71
    0x4070a1305100d1480a1607050819080096528018006168a900d00200900000d070000101c651008407801c00c084211141d007044102c42c054000f85000c6204001007000a0410109000d07040e513161a83c81902a223035a04111028042180c42d58056070080c0c0b00c407032000b80200c1c1902e074000e20465102d160611aa40c1c2c10701c142e407001201003000000031400c84981c0d82c020086220300340c91880c1560415180c88249594030900e40300103000c0d540c814012500c18030114648020359900500140701c48284d18540403caa014400e05a809100d1a030010030140b90030350b12500360700720040001061801075000c000082c080d00800301705000200b468840c7c8440d111100451150760f854040b525146440745c410700307141140c2407807071080d006030580380301140d002004400424200141000311802e041000ea2411105030480c0304000e02d15480c0039501980501c0d250343c038203402c0e40c00340090385401e014091942200b040c5584000405419005140e20502800484410328a080001140d480101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 985164442 1250 985163192 985163213
    0x1020c0d1707020609070909060b03030708030105011107060918021e0901180b0711060c03130906050102010c0c0b070216120525050f2106040605060102031c0e0a 71
    0x2264007103624000ca848100d0088900d080d844070580c0050b208925261595a0f143c41c2c090081e01d212540c0c030355200b01886025440440e480d600038003140e684550b40d08140c000c0c1c2d0402d200f202d00260581e46d40001607030010a441d000c55610340c4030f540d101401d0070384d440540c00d01001d07696221075080c880b000340c0400c0e02c66001d40c501c0c0c50320310042d80e03024890300041c007548480310442d0050001d888204485d101140445840035040b01010f610041c104002540c02c0c4588441d001d4144804540950344161070b0f481c2c3d40480340d4400003000350b207507240b0041e070a942d11141040d001c04d41040886020030300d030015185c2e11800603c1540c40c0c107011201c2c15142201941c0041400d888544402010040104104d410800340e04032240c100c3d100740b4808040a0803a030003101d00400c40d0b04260400740d2590103101c0c46024110005842c200b40850203640e881c901140c080e0350050400c401710349694004021104200a290f1201c03490140c0340d020071010f00f0100303100340c0947c4662084800450140000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 985165692 1250 985164442 985164463
    0xf1d0a020f09040504230a050606060a09080708011b0c050a060f06150203130f0f17010f1803020106290c101b08010501020d0503010608150604081f0b2101020c 70
    0xc032109800583e00000e03a20000b1b080c40c1c20074a80c046581d0402040e80020310300e91100c811a2229031324101000100d48020035a4040308480c454a680407400100641020009070102249041660f490050444074000810405010b54208031102c1d004030340e4681207050b03034012035500440c40d680d807208002c091312100036a010050b04042041c8022408001d10540104003088101c603501341004041304583c0b110344152040c0e007020001c2c0b034410b6030007908664801042070500304000d042900000f00166240d0800b24010351812b03002041001d14a07103195141704210f80c641d048000b442c0c8800c90190f0040340009502d2160f0f4403100c4c2d000c3c40034050381c0c0c5184020184104030324107016001d825801c06800540c1903401c40341203c08507940c09130942e411030b402c40c03505492a4403001c084000d0581c1604020b9000340001a002c10102e60000742d8045400d0114100c03d000e049020b80d510403030f0884022590310030000c4040514009448411202d007800490006281402400070035150980d4101d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 985166942 1250 985165692 985165703
    0x60301060906091a120916030c17120f070212030f040302030709050601050f0a1106040b013807150f0507110d020a2015040f1d0a020f09040504 63
    0x10300a100c0b09901c150034400404405554203182d5800141c0c452040c091829000c03482449a40080c2c021141006028035920840c18400242c079104c0c00c0c0001110384c40d000342178102d0120b5080740964a00024003400c000c0345c0c400701d9400d0030b40e2013200c04035981c000710b03060343c2c00210401c400c0044442031004045001624424607a01e0340f952042c13608000f600d901036688a8901020042c03140d070018221001c55100074461a900c00085200f49d400d5140f60b50008a544982c5042100b080250b0003554142d842e04059071070214a6000458181c8014012444d11441c1030410b040100e00c440c3e020b800c0e20f5104004049062010300c2d001e504581c4070000c1ca041860315081440b8405030407241d10252010b1080180110360300b40301002c0d5403030301c114a0040c00784405107004c00342e10b0f0000b000c1201d5500020601d204c1d001040f2034200303c40e0001e00400281142121002544030030003e02c000d001c02c003050000350581d4403c00c000c0020340000c038400a01c403108000120b201c1e0703124840c40c0d103d00c0c0b04c0e9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 985168192 1250 985166942 985166957
    0x30f150301023c120402040f020f030a050406150803120403020f1006031e0209060d02041e090b090a0b040816060f0f0510080312090a02090702150a1e02130506030106 73
    0x40161440c03118014540003100d10130010800610685042503501a40559012030503003410103001c0e0082c802e201006d0031078079002c014040d00c0c41c0d99410844c011401107005000f800c40500f00d000c80c6000c0d034481c80c00340758401c00c081052610740011055200d8001d0040c0d51116240a031101d04004000303181d030354015660361050040040c00441c0340389007401115044811100c03607010031403908001d0645071040210340d101001315036454103d80440420088000040c0005603428409880f414800f2900c018201000030148400003d41c0d1620541060389440d440c3c4450b106c0703c0c52a4001501410100020302410300400c840e409844481c054400e00001c0039614071300107504a41001e00100711001c02d046042062160010030f230340e03100c82c4006016001e601e9504049103826042d040007504588038404002c801a0081a83d02c640a0b1007008256240c3d00d65802e04116560002d0080903844e020000c80c001551a60203007440c0c085460024001036101c83c009220354000364001e03800601003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 985169442 1250 985168192 985168267
    0x801060602032106090a0f0e011104170a0b040f14060f0708060d11010e0103090213020a0809031c0b0607021207140d050d0318080703030603030311030f15030102 71
    0x2520344199881401d05020780351414502e002130310345d1401401d0440d403581c0380c903141802d601d0140e201c510040341c245c00810502c460300c1c1c001e02c00754010f4480c00d080500000040048444042030f2050740c01d41c4183c1c080015a01c640c0e034a034421034900010340741e0031347d5240701b0500c1c04010052a4003542c94445000b46c540b51044000740344d41c000400036801901000300200009100601c2d4a0f0100c009083c10480610b060300100c0c020141100069401407541c010b44801d81c0d0030394010110f1441940e2900d0380c550721000d50130382d40e204501e00c0c4517403141c41321035101204529a100000d07188008100e1441c1000701d0b0001081c1654010464010360006a010482001c20010502d501142510240e103010081e0721350f40d84640c000900b5400380f640303812404942030304c9200300100c81c41d448100345403100c0881c24020300a014502048001c82d141241e5002c3d00050481900d01ca40c21580000c55565690b04801e600e0300b44440107140c2540d024002c03141110b14001020740d51201100344000030070725 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 985170692 1250 985169442 985169467
    0x180b07050910030b031f0b150c0105070c0c09050a09050a11030f0c0a03170717030a0f02032203020c060a0e0a060311040b090f0a03050a151e090606080106060203 71
    0x1ea00100c0d805051a00c41e41d00403d4501003041b00d2080461178401c0d5103d200340901401030405510440d5001901d0a508161042240d000e0040c002150008202541d22507809441d2400030040c0034201c4c4c0ea5405080100341e14941105600180303950010404d0207803076403100d1400400403409c6481d4200d80440d21800c0c14108540214038054900800b000450710700031a416840d40d0101401c00d031254007183c400e03000c0d03450482d2280d660102104a81058201040e0b030203401c00c0d1285d585070f50400c030303200c1c005030790b50700a50b40594003a11845800d0160000f507001c010001c40710032019800b9094500703a00f42c2ea854054240c4070013039103c010300e00d141d00b01000442d01150300305405040c5030180c2c0300c042c01100816241603c0f01307051001c0d952490300d000550158001030041d544103050f244044200700c0041403244c1102c0c8542c103900d0034036180107920f40558550103060496a400080840c4280e1030a8100e030650314010350000803915141c00340a0b0035034900350840005a4400500381c08060b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 985171942 1250 985170692 985170709
    0x40f12060b0a1d090a0b010807030b0f06180703090b1305070b03070504061112070836040c0e1002060912031302010c05030d0c18050a0f09180b070509 66
    0x44121144500141841001d040f07064002d101c0001500c500e0700000c00290042100031722403900314441100d2503940f000382d581e41e10f0309130104546000c041d0300403411054260280c07a0180030010003148240d0049070840e015050000c245000305a00d84080740046100c08910f81c1c0650b4610000300c002c00100c1c1812403030200035a02c0721150900410400c410380d41c0c050295400d403041494401c0314806c103503102d28945140f030a507801c800b039000103d842c01c128005000300158154110503da2042d2103074403605402d0245980305281c611083c0a20f125454164400340b4121184e0800c4842c00c0303054004241e03045000e041d03020160744040b01744181c0c804100264055004c00480c001d156141085800809442d04100241802400300c0744030f00f003003c240165080c0300d140f10003c22034050a510000c0400080030060a040450a6008940d034100500c03801c096400d8081040c0c0c09038034200340a00200540d0807121404c254180e05c02c07001551121006000303220540d40c25454890040422441e03c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 985173192 1250 985171942 985171961
    0x1170d0203070b0f06010c0501150501030606020f060a0510030c1746060906091104021314150f120c0304152f03010f090501080a080c0102040f1206 65
    0x55000740007450003d001c0f4030030f080d40802400240c60310307501d4400042ea01d0b6840c1c0507000b4a25405d042e1203005038000040b030b00b400c0320000da0b41440030307603034400702a030301c035960041c2a2840da04254001a0f02d20703078035002070350050034101e91009016a203407079444c1031b4855034003c01c200b442c26101e0807450813020400920101098615811240c0c2551340315117440c05000d550f03405c0200c035001d07001c00c48985900c184104903000101070000d40d11a00d450b0340140500d40d030440c2c48000d41694900541000e00c00d84001d01e10258000c43d040d0706005460600b1844503080d6039010381242c084503003079052500500401c1c40e6200303c69459104030b05000080c40e00040014903a01000e004000129820505100400c021040001244180a646a1086113100b080c140099041800a14595018000450407651008001c0301c140d52503ca035041569000e11445c9182d0707100031a80c2000c107906030010450719841c900010714250f40d860f916407508541e0b91100f0ba45500c0925024244030031070040304400c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 985174442 1250 985173192 985173197
    0x62007061a12070e060604092c0309030c04050c070212030c0715080402040b0109030c06090305161203050f13120203010b0f09180c3105040f020d060f0501170d 70
    0x808612826070b0f264507902c0307544507805000d004901207440342c0f030481c2c1c0030744600700007800102080c1c0001c0c480840485043c0700802c000144248080c1c00110503104400c10050240516040410030407014000203401d02c03d450b10100040c100581c1c0b900844841c0424140185407250212101182445216440400c4041c040d4010000b001c2e4061040c945c0103504940018001042000407500307034175540c0000b02138040a070702c00700e06103410000d074808481c4074004595000c400d410000040b030710280329040441c0a25480c000003e80a10050030b40421116000d50600003003e0412030881d141c3e50004840084108051080d0b04081c060720f14440400d6035000b4040e11000d02050014200800c0e0305444446641c80040103c03050110f040c4450001b001100d0081411200060314071410103410030b814071000c000d6112611074095030b4800c0b070704070000341409900358080c00fa111401610480c4d2f80c543c0c0d50714519440c98644940c83c0a003003895085c4108071a03032a440c03440c015160520406 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 985175692 1250 985174442 985174459
    0xd0608070609050303190e0409050309040b0604080615010c0807060515060304050c040203070e0306160e0d05030910271502150a020d140a05090c0616062007061a 71
    0xa5131400000c544100c4100d800c2075590458015003199940c071a0080d0769401070500e0388441c00c6c40300c000701500700072508650801030a8446401c0212500c118405e68109802c40c400040c811031b012100e1700c1e03480e0030605054450f882140c1d280156a44190421071f40e480c0d4400620001182d0140034065036002520000c1c9903013001c0e21455a27031010b02e80b01d584201d80010010b00801c3c401c1c0c0548510100c042d04a48140c10f141c040407080101000001c070018890502070002c614183d6900400c80d034000000d5850200305a00340a40001e0700f51890080c4803071002c101074044000100485080301414180d00f05078100340f070312516071520284e880c0440d03000c2c02c54038461094010055400083c5030038010390307485941a0f5280500403140c18110540071040c200b09901c41c1c02c0d00400d204404c0a03060b01c02a14844041001501410f80768881c3c0f804000c40541c0040c8041d17001e400b40900100e03d90f09805801107040c05194028002180c1c00c6450f8204035441c1ea07031010340c04090000c00c80d03d600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 985176942 1250 985175692 985175699
    0xd03020702010203180111100e010f0c1d01030b0607110333040507030501020a180909030e0d060f0e100e0604050c011d030709061d01140d170d0608070609 68
    0x13503407401040031701c505034440e60b0402030060b800341450981a64215054034400f038240c13104140144411060708001c2d5007801c405940044251090344281c1680303845541e01d003207000e6012021a00340682d101e050556a00f4480500c4d43c414000e4250144a03400c9072074141c09003821705042141d0300e11140c06404141e891036401108020802e040303d5140030511486035101d00b413151612445a0007d41954070005151074665480b0850310701d49002119094080c07943d07a0400741c12961038007400b42c001965811500e400c0d2034030000540d03480d1300444010a640c0c011a0580c0102c50096540c04001e40c0903051a101c1d004903401400c0c003040100000c3c1c2a42e2409031103054841008595090400500c0c3d001c18103800c2c00c000d941c030302000018003102e100f80d0312108510014065400b0f85c9601480315400268401c541548a034161840b4400c83c1c3d072418880000c0c490700100c041e00c2103800c1c40c01c00c42c11203c07049403103025003ca69607123507001c581c040c501150b840c1000015086541003182004050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 985178192 1250 985176942 985176947
    0x150310170a050a0c29040b0a03020f070303050105010906082211040f020d1404020a0e04050304090504030e040e1f0c170a06260d0f26010816050307140604170106080d0302070201 78
    0xc031b0403550001070761a0340f464000360031002880751441c81032982401003000018954140d02c0319058600c2a00c502c5000c907142c0d6820f480c00ca2045802d080305495400c001e01d1098940c17849403007428803800301e40c4035040000700007609683d4100302c1900095408644041600340500a8994010310420416081c1c207098010070b8029103d40600742604d111070001c2010018100115801044000c104025034202468020800414200194802c50410300001e904510120b070420701c494050548285030001200c2e41e40141000d41c0ea4030b07083c05103e450404803200c08904142c40351090100004180e030034601c1c0c201d54610122070400c40741d03a030314544c681040e00000b407460b45880e907420301110040070340301c00f150601070010342100d0f41c0d4080e92050031161580c01983c1e05071203000307065610a6420501d452042000d030b2048561643c814602040b0504881c0003051450b01e0241c600c5260035210b50303225203018000080e07644969075602c0100512071080c04a152100f4a603c1c1c254601409c41c3c000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 985179442 1250 985178192 985178197
    0x6090212010509100b210c160213060b0c1f0506010906081012031701063204091104381b010e010902150310170a050a0c29 54
    0x42c0c0e4003038500c070380114200300c028a448500800010100039928050480b1040c50354981d281084807000c03903903011424540701c2100340c87c0c1590200c091400380d209135400f00101e02c0c01d41003542c04580c0e80d444000c03621035044070042014100c010b00800012102c0c2d29080000d912500c2d00580c3c017440e010038010540e81c0b2512000440e689454030001c15250701d8492000401140e01080c1109002c003094020180c01115411880d0f05000c2c0c8400d41d03030707a9038006859100b91005c040020700030152616003200d5400e402010002c403400900ca061030b840ea03040c1001c540325804410400400030504021140e104074a904014200c1010201a0100e903d200003842168603851100d0020110b00079200300c2e40320100249412020000380700003503402d44418020103582c03006901440310080c1c0c51414046141c100c034000e90b8149600040d9038688803916010b843d07401d210420030702880c002c04e4007141041010002050246d00742580c02494018180030255041401580c40503524540b64041e9259805 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 985180692 1250 985179442 985179449
    0x1200406050f07031202070303051801050f071b0b09030c0d0306080604120c0b04081b03040b0a0507050f0a0c090c02241b0315040e0a05100c140d0507030609021201 72
    0x210750f1642841d150a40b1400460489031030300382e1000c1000b1091646c5038008a0060314074680216083d0385103030342c01d8240e8608803520006813074a500411901c91140095880c5040036507650400c0c20312641e00e4071407440064aa13202d26500115114164000a004039400e030601420f040064518080c41c0c20349607480100041d100303401026440320903600580200409550007020058989068545803140d900403810b034840c1e5002a1410458911000007100d00340c0340e5111800d0b007400080306040794543e2002a0803030b4035000368003d800e4015401c00c003c0070030620410500c042181408a088100c2c0d81e01444c6a0440d408011844003450101c2e0741c6a40003103418040c075405a80e410105038400d242c1100a502103d00001000002140b5041d0300b90040da080703c06100d6140d20880c15980d4214203278020300141c004041050342c000b6285c1c061005d180740e40c1060419074058155680b450340045243c150440d80780c0003003104490b414410381025040280b0218200120000302030801c000500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 985181942 1250 985180692 985180717
    0xa0305061905130e031603110a020a090207020f0303040305010c030b2b140f0109050c060a081f0306020f030a052a1c241d0621060106020120040605 65
    0x1103c149031151a0000200000b5000c11a5a01c421840090a00290174541500001d00008005401d900007040d04039000e500201904c2207241004146002980002001c80e40043d205d07a041c07086803000d00151000314080c0000150b180c058140c054240d64525031080d100713010099010507850140d024803100030b40302808040c66006a494543c0e0105241e258403201c1e031250009000581130f05412802640d4807803404c0d900e9404030a001d00500b0f0240001090105000c1c1001844240d0351003520308136150012140c0c0b159980d240c403140300326844a201c018101030000200044998203000d0b03142c1007601c866072818000139820101c40d0032100c01701e0a10540c8030000d0b81c0485002d064a11300340c01105070408004d03240800c44a0050742d007850000c016034245103800020310076603c0e92804604684104410026607808040001170070300b01a07100340c00201c28255182d12082000118041c1ca855000000c80c81c00090b80100c00d540341c00a10006007108000600040398080203540c19008000f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 985183192 1250 985181942 985181959
    0x90c0e30031c05011203050c0c09010f090e030301050102061603091a0109051e0604020903150109150602030301080d1101094803241a01080705090114030a06090207080a0305061905 79
    0xb48c5400d82494984501c055001c48050004540d01401c0300205c000c5403078000041121020306100c481c0c49020901c20540946c0220000540c14600c1d9110040301244506d000210401a0384d2000c006100c004003200d00d0350381c54801846180c03503e1252580203200280d82558a5000500d40003021200074001c034041c40c0c010509407000d4804012850510308108102c2049617190929070b0010700c1c04c02110744204480c03038030015040e8004011203058a5611024101c00b41c200030043c0c84000750310311740c51919940d50322500d000c103204c4a402440c00f20581ca811b0180520140381e0194000344101640001c43c02d00098528180c201c90000c00312a8081290b60a1a00d0700030000781e50213400132202c02c01070618815048006c0d0b24484004048400d8840300c00684544d14200d070300303000d002c01460104050703503643d402a107a4040510b85c82500ca0402003640380e26446d420050b07070411041280c4981d4003013a034144590300b40c0900b951150041c0c4107400c1c41c4003400e45034440702421f071141c54001c003c003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 985184442 1250 985183192 985183207
    0x60c0109050a05010b1f230f030901060e09030f03010e13150902100512190209060a0207080106050108040803070c050a0c030b090601090c0e30031c0501120305 70
    0x290003416910350040d040d00d03500700d41e40c107003a4007a01511004500c0391420321400c100101c1c070f814900b82400c00075645c4142070404150b0003040c3e040c4001025540b06070a1001c6030381481075000841c8180352840020644c180307000f180070003000b4080d281804a402c180718403c1100d0200058034110744448003003002c607842c0c00000d416038a40b21a00a800e030140316949260341c400703a0b00400c844038400e517031044110a0341c000031146030040d00700022030703241c0010102b40c0f440041310040702202448076005103000c50340c00003e51140c2c00b1200b0140940c00c04803040001d00740c28820b050091000b030901440030318256440d00642c0c48001c01100070300012040f60000d1184c1001030a240c59400101100440d4403030402e1f4402c41011184904c0074412400007180c01c0a60303024660100389031340c481c0c1d0304000c0120100000011070b06548183c1c50401c41c0d0348005a2003601c660310000c140d105c0a15513032011910b100210055266181501900b00300040001043c21420480032540618086469840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 985185692 1250 985184442 985184467
    0xa06020f0f03070504030b090309100c0203150703091719050d0209060f0d180507051e1e011b03170a02130905151e060906040e01090515120a0206 64
    0x107100700e84040000d000c42001035203504040200b080d0380c0144c040e51590303a02c008a191b5070f8414414082c0e00300241081800141d4010312945180c01c0c401000c0e00d5001000506c0550180320440f44203001a480d410602c05214105807541180785461800c2c0e442e2007402c5001d0b20645496607259010044000303110881e040c015030694241c045d006115503503561082280d840d83c0e411001c80c0000003403502c02401c2030348a0306c100c0e1044056226000c2c01403949030508024004601c5000351090111740754039040142e40e461044550781088142d8031541c40c00c40c0000400c0850310181345c071203800410000030f010a0f0022900c240408083da01c1c2042942c5e03a0080c3d0000e4080c2e0542c64011b07802c00300340400c801c00c0f0703900301a00c22141c81e260209003450500400600440c441d0341500502001c0446205030b0600100500e0201c5000c1c240c54a8039646840304124000e00740d00c05441d095032001030240d0f44082080502c010601111300d00d003c00a000d142545500c20b101d0000c2c411000010903000301c95 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 985186942 1250 985185692 985185697
    0xc03040528060501060e010c06020f12130311070b04140f0d03020105150a051f031b09060207062a031b0c090501080d0206010605090303040e1503070e090a06020f 71
    0xa014000304112001007140359004100030100301c541c1824a40041405480703003035086401d0505070740341071510b41c9545030030000394010360107110300190820050840c0c0c042c002a039405140001c0606000114908000700040d0b06c14036040f00d03d4011410800001600320183d0f8280c0d5801c5400606a5501c0d0001422301c5404081850f000800c042c41d8605164040d400b051055040d0600b1001034401e42c403c10449402d2170007100e620840350303c214408901d242030720440e100c01c07a0034006803a400809000603081c0f40d01001600180e44610203000f40c5030b060146400900d02420f00311000b4111603203007440c0c0312100010640d40c2c0e0b4000700100c145445116a0514034020b411030074009046030804070201481409070759081800c01000149460b800188458170223516070240c2250790070702c41d0480d2076034045030045a243c4002d00021602e000003100043c004c8400c0c451b40000820044180350030a45143d0103112143d100354100880324801081e075012803030f40008016030b01c0280310007036003160 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 985188192 1250 985186942 985186963
    0x9120806220515040608030a033303150b060a0c052e05010f140603041113051807080714060c10050117010603080d0e1e0d1101050f0c030405 62
    0x1602441c480e10310791034081c0e00c41405503c0c1001c030b68200540050911056480a1050002c00d52040144084c6903201e84d202e6249020400000003078030a08450450010488502140460f45040c0c401c10401006000003d900150400305105d450b61040c0010007e020707100c002000c0c401d4024103002041f105001e401038402d0420380c1d0f03820b621003100402d00340b1048070303107486091031810f8000b160340e28041c41001c0440d0036030100c0a40c59203d039401d1145c0e9400141048410666201c40d01200303a5400c9400024000019000140391900100344216940500c00e10303040c0c0e07005040c0610221101085100588544040c604500100d81010501038480d82d0f442815601032510364501c80e20390780c3c000768101d8a01c030000740c034003113254100c0500300c40c11751100034020303501000304104100441d000f0301c041a00510aa404030755140c4201c1121010460402100d50400107448242c582c0000c130807294049403070300030001d514103031012b45002038000c2d0848070090004030004042000800010700079 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 985189442 1250 985188192 985188229
    0x1605030f0d1d12151b28050c03040612060605120412020f19031107061b0804090911270a050c04030f08030910020906090411090604031a0a09120806 65
    0x48078044101002c4c000090f20f800803030007495900c450044d000c02c0c040d50304100404c4031006003c20840302c0c0040c1a0340b084801003d002060103c0000158140007810080850340c0398100c0e40c807a0004140c00301c80094100c0c0e000e104041c450f4428200f00c1120061303129500a11450310b5000c03910007030381381001d09024100e040c8609440c00380a188541681c1007618441d0701c604040641c42c030306143e01c602481c0544030004030071035418080c40e0152200d2203085401000d42c01d00d001d403039189000075140500001d0710440f00304440002c9a080001d00c1040c588003030003044210407418a210400c815025100304001a1120049054200c0260440340116803100081100c2d24207850880042c1d002200c201d2003d008100340c1617000e0815000702e454140009000703903e0103040001300b00c0284020607180c001a1424004419103480b000c0042020398082c03455088440880f00320741d2a411320040806104600780000f000008061000300d000080c000e0524404559540011841107920b602c0c50800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 985190692 1250 985189442 985189453
    0x90c040906020f0c030d0b10120c1b061509061203140c150f09030702211011090f0301091a04060f0912080a33081605030f0d1d12 57
    0x91300d000000500b03039829110020700c084900d0004010107140700420309000f0074000590720360350040d254405210f00b585804c0121681444160100311008024402c40b44942d50b084030413800e221038054800109840c40090001500f080b841080c685a086002800d0126003c015207080c43c421056400302801c0c0c00444182c4902e4004c03041a004064604c0c0500d03c902901054a9103000b100315504590040c0018030351290f083d4448442540c0442d0790b150078050040c0d066425411401020640b003100c0d80003513220307014102040210131040c40403602c80d078500030044001984400392050720049206040d10960b8880c205140039180e4009029199460a44d60758104800c0e51215a800c010a80d560799082d0b41e460001c404a91070202600325118841c2513a0300f91522a0518101c10200c08800e262525034034840c0318542621420004d1010340303080303414095800c08000c04d0041e4000e81006040188214101605203101540d0344540d84a03400c80b84401c0d130310b49442d009112000700b801c444 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 985191942 1250 985190692 985190707
    0x30d02030f0c0a08221d07200d02010c0909050f0c130f0e1b07050a0b0907080601140405070503010b190c0b042303040302030c0d030c17070317090c040906020f 70
    0x200c0008682108040404400c40410800c1c5514001810a91310341c146e082240c4500c04260b40c80718202c0130300000e0755924040604022418000700000d80c03000c1d0000700b102c5100c03000142c0300741c18641020311070718503040c20412114044114141c01c5800300b079080355100e001074021182c0319076a8000f8a40364a005c2e40000d04205c01c1c030026441490440da00018000c01e4a03440b0a680c403d080c000342080d070021540c032000c41e0410030095080034810b4111294141d0740d0b0680c90821109070301c8800302101e09111000d40d4102409503d070b100d019445e20381d15642c10002e810310b1a020340101000806240000507419902504050180b160845c5034280c40d45840e280c4000b025010348038081c1c2107400c041180c602071100000b5101900d41c020b010300811001182480b039003405614081d0100a00c0c4001a03000c11300041403085a580e0801049030780764100d0501800515020b4030b07085805450323404111800c0c1001c11041400f80d02150003041d10030311810804042d00840101034a0b0441c0041c01382d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 985193192 1250 985191942 985191967
    0x120a051e1602071d041205040504060b030f0a0c140a030f050a020309070506030601121107020409122606011815032013300b01030b06030d02030f0c0a08 67
    0x3040c80720555003192111a19000900e10107030f00b80f000040b440c916080420000380e200c4a03811540c0d21b191a095040503554230002c2c068032415032103110340200000901600442200300c40e40c0c09419070380c050003c00181c9000038847d140701019820b502c400840c2c4900e906109030005100ca001c1c040c070901460802c0724101c40251b0041c0c5075900e051050340c00004240c00c00400356881064142c4034001e40f2102449000c0c080d0003540c125010101c000c0000e0801030340c50344070b01c928150060a00c03040c1e140306000084c000e601c09001d1040380350200111422005007246080b54003103420b2034442043c4d400101075044c0e240c4150403001101188242681c1c1d616455448a03181c1c10821aa459401d10b0501084450780705410840d9a011035140c802d0254101d5030b4084860480f400e41c0036000b44c404444089031502c4802c404407030300d0b52088010001d2080c00501c83e07800000c110082d1400c400c13a5100a542c1e1711840c0e03440d52a9040102c0c003e52190020b0000c01580e9420881490740d80e203008601 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 985194442 1250 985193192 985193221
    0x501020d0c26130311060708010f080601030b061012060e061915030c1106010b0403060506030309010c030f0c0206030c0c07080a0c092d0f0b010302120a051e 69
    0x5540081d4402c00407072249820714910080344404007055028a03203c2810928003006102429800e1003030f60601012080030404ca540d1060f4500c0d0b07160019541400308840d0305915661011019074040c0f00107102094050309883e4200c04206d849200c03000e598402a030b016114442d280c168180f0b45000040d0300040442140e1140c0000c031820000e80c0208070400404600d2800b9824540c910503e000b1800750080c6e12881d2071640701e040c1480c031210b0202660340340c982d09070041e000c090303800b0408208000c0d181c0900c07500040f08802841c01d021980f80002c001c1c1e003490700050100501003140c2c0070070380d00400c0c0351621903030080d260569034a8803501e254040d500c030440082051180f800c000606403000314010750341a0b404003843c40800c0c40c1c06040d10290101c0805406a803908800b101c020420240b003240c0c0d40d00c90701c0c1e0003140480314012100c00300e0384001c1c00241818010000301e0103440b2a20310741d81d8040b80d4090001aa92103049000043c0c1c13a6550210481d41e603080103100306119030900 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 985195692 1250 985194442 985194461
    0x12010c020a0b06011b113010020403120e19030318050307030f06051017010902090f0114040e07050306090f0d0203040501090608070e060a0c02030c060f07020607030c0501020d 77
    0xa9082c1983c50703280044840b6980468180590a640c3c03404400081e44203c5004840000412032580f48040c020b0078040c0180c4401400040380c1e00240112030508184032400c0c1920098008500305490741e00c440901e410641007030020080600345502c10340d91040b20728010b41802c0d80c0e80382815030b102d18024101c1c81c6540000340903080010b5001500345000135200041d40d41c040c2d4580d2801a0035650800501005005001d000c1c042d40e0b008154542003046000088070510000728142c000b50040c80058003020f000100b0044920300107220b105c3d0051441c0c0c144010a50300002c20084000d83c050410103640c0060741c0c0b50140c10148064802c001481150380b503099000d80e0700c00c0c550080300340d90303d10403803041601144010a040050901030580d15a00080c80e092005840400f40c0015030103510514101020071000f03501d402c19410100142c03c5505030507500c02c1e00e400020385a01a180c0070715007000780b0400740001e05a04252045040c1b5004590200096494850600d0983d000d44113001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 985196942 1250 985195692 985195703
    0x6100306080f300f03040c120b0703050a0b010e0d050a06060b0c0d21020309010b09040501150f0311090c16050718140a1508070306050604061a0301060e12010c020a 72
    0x8064410440e450b42018401c1c00f018105034500300400142c0b050a40000784203036007440107a6400a165410700044502d954406c42d08145075150401010302150805048418943d20301001c8545590b0040381d02480884203e50b0321003c00014a445d600c2c06d01c113a07c00038000c1e4288840000c50009031000f41103107141c10400d44581c403542d600103d4185c4d140107c4404140139408100c00c6442e0b480d40110b03040000c00001203804248100480c0300c0300c0d003d5404680a0b90340e29050a54a052081908080c00d91100d000342d80501e95144c016014294568051080c2d943d400820b210040355022111940000700b22590039000700e0410a403501d042d8441d6901c0750800722502c00044a0b98820300002d1104444030a00030744071032001c04000c0c82c0140039140319240000b00070900800800242001b1840780a0209043c5000e00501042d6001580106500b41645603003c0a96045505590546025140826101440200003080d194900f50740400e42d52a00350030074045580400c0d095546030240 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 985198192 1250 985196942 985196983
    0x1506030c0102060405030403080706180308090d03090506060405150d030903030f0504030822180504110d0b1506090604060c0302060114100e0d05031201030b0109050f06100306080f 79
    0x300041e62240340c102d500030400d1304100310602c005101c03a0090900140a4000050b403420107280445203d98031800035004507503440100140c2c41d90401207402d6402da10714040c000c05050b43c1e41c456548401a0a00f88100e0302c501c000b4282c164058001c4207021002000365403146c06506015244520a0000f500000c0464880b4a0308030301601c12501184c0e480542149451091a4604e0030012030304849114500d000c00c0001e01030400c43c100a0b043c040c0d1031000280c40c20b00d450b001c40d01140c00c420071401000c0303080c1d003030020800280c03400b0b61080b840091640d001e910030000481621030883c07215800040420045919940081031b500c056209400311581640c81e000c0407111341d040c42070021780c0704140701c3c00c0750b000324414410440080e4001e004880c001400e550b0f11425038102803610703010030050741700410900c461041c4040c01001f60303600400003410001c0da0001c22a10080405000c0c1da41e511120314014800e03402480104070610a030342031502da204090380c036948000d00c20140076225 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 985199442 1250 985198192 985198213
    0x15052809150f080106050703120c090503010b030703050d080a09020a061d030c0a180f020c010c1e0516030c0b040507290a0f1101020d020a170702250305150603 70
    0x5207240e03003403006883c1c4606440740c0c42c01004a64a900482044003000303c0506484800000c0303008800200600c1d0f1203581c2c055003414241401c5408928105100b680304205c02c102003030001c24601010342403131034200c03000d40c0da0b0b5400c240078086820001f5040402d44030300152180d440036144030f900341b2218141d40404044c0702055545c1601c0d8001c0c40e44680c0d03000f020016042c8002415001c0707521214082001d1a4039461601240c0000b0107441c030b01c1e5105c04441800070f600520b940100c04007007448084500b01070400501500a0301e0916100c440340080c41018035001d1040500c401da0301c0070b4224230501d484d24040c0c3d200c0d00c06102c3d41d07805100e90040340c5608010300e0309900782c3e0789601039050b05102c2882000c843d103e01d40070345101448440603408480b04020700041c46450407202000d070351000c510000a018500d1a60000d2001074254140325072030b540413540c2c00315100e06090503030501c029404c038441981040c0d800103140e0b100f442081070f9102a119051846400304a06841d0010740 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 985200692 1250 985199442 985199447
    0x210f03090b010e0a06050301020d0e071a04090b040b0d0507050102010c0c0305070b0705070507140a060309020d02091f060801050f030a0b07140f03090312101505280915 74
    0x114031000303024901d600014000000000e0710300754072140e00300700410f01d5952140447e089078000541c22201b01d4868884d266400b404104020080040059400325002c601e00c20070428016070007816901c03a03c47d045011555541d4010104444001384102211705191a0599442049105280c09542005110641a4015203680c3c088035019201c6918001c0e09139122580c00d81d00600010900c5014019000401c00402200300681013040008648940d10000c0050300f401d039074850070425061004140041c0c44031984102c0305981560b821056440d426144464070b540305680302d21050401c40000780c40c56104c02c03102d04076541aa403241804284000b0701d522550500000b030505c1c0e528030080344802d441030070b140c01c01903158079956007420b0100c892540340da8801e130340c461806c1c0e0010440341200a03507081425045651a01034054242c540404c00a40362800c07142a014800045800f0031151544000740f420f0f561031805600c4002824000902240b00a0040062105600402c060000e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 985201942 1250 985200692 985200701
    0xf05190e1209031507170603030306010912151107150b0619140403030906030b0d11040b060403050304090c0807030c020637062925210f03 61
    0x804003000e8071020540344032001459010000c829094400c1d0340c45101c03100d103000c1d003040c0a030f01e0f076a82d03542401380091120700004d240a071400d40300742c00400c140001c0d0381c0c00c956100c08580c5000015030000c261414640c016042142c0320011a50920b1802c1240c140340300002d00301710344a000f1300039803172045480740012100c603500419000742040141c1c20030720481c0d22034200c2580d5603143c00c1e481c42a102074803d28540040d0f004901240c0140c80a0000079094010215071070010744012400301c2c6030f501c50081020428503440d01543c2d4450302e4280d00e0722000c00300c2d4065078014040326600d5545d500601d005041c964882c0780000d142001081d440d502c640150f0000c00f01c560b006100356151a007500d050114100123815031320084940c0301d1031440502c504640c09500307010b40062001c3c039140d5040000d07020401d406408074074800b0000c0440c002c440640d511034074012521444e4162a003107003da50400c15074003a0079408000d5100c3e0407680ea030100f40c4407030140e59841030000b050168094041c3d6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 985203192 1250 985201942 985201961
    0x61e14091e120c1806060f0d091101020f0d050913110304030212031504050c1c05061014040b09042403021c03080601080c040f1811090a1205100f0519 66
    0xc84d114510080703c00440001c40d08440000d01d0103207480410500c184d11a8071001e81c01402c04c0d16000c95400703222004521420300320083c0050000b41600c20481500c40410301e107200306029010403403c0d03864441800c2c01c0c00c0d02d0846c0310100a50030080022195941045034118014400d04881030301143c0c0d10002e5074040d01007008589103622081c2c08110107820000d000001620043c0316402c1c1d02d1a403200110000c0b0090b0f0f40000703150a280050002c8003a11640541c18003d44504010081602c07d046404a80d4502203d5440c3c160800024000c0c0210b0301840300020a144900940d50303160040140c1164421290551004000c0c0c81ca06400740911002034085560680081c40a50107160304030380c0b00240c84e87c3c692030152503403140302e4039502c90b070080180b0b0441044034022440440c40b446200700d09103c0c0003420304129000080c003406460194545c40c4086040c40400c020041010042101c02c5180c10300070415102c8500c4000d00b0100c0c1c42e030701c48141c0c50031700708280703851071150030500b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 985204442 1250 985203192 985203199
    0xa0302071511160501020f1b011109060909060d0b010b190e0d060c090b03130b060d05060c0a020304030503122a2d03010905060a061e14091e120c 64
    0x10140b140100302d407401c56900044da00c55408110b0446151851002807803040c1d14004451112410000841c2c00c40798400100f00a01ca802c021a9400c0c1d5144d0b415510400c0041341c41a249a550b40045103c0c0005030030000c1103980301d58004030700f6205c3d680141c0132030f07a6041c1d100f0408140c241c00848500c1c46401005400c0b01d1008071010100b00b8982201070440c0040c1400c00c160f680e07441650280f03610445690442e260b005445008100700800c02c0c0fa00034104031002490f5900c00c4d2244d5844040103030020350b002c000010b00c0c01440e4028802d0350001c5802c070041c0c07515084201301e9a6001c14044900900000c03a070221980888184065442c6016500580a00b05012500100c1c00500c5401d01c80350b54142001d8100d04154100c80154042c00155802244500f040740900a890b0002d8008000b0320488141070780d04d88009803007040d0313000f8140c034200e8088800380003404410300c244a44140c00800c284510b82c00c6040d8000c0580c0c0f40d18050307940f50324a0120780c1140d5101c0104202042e032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 985205692 1250 985204442 985204447
    0x524030c030903071406010503240105061b0d1808012d060e0a0c180312050a0c050604052104050102100902060913140f16030e120a0302071511 63
    0xe0800200051a441281c1c0e4007200d141c80d00e40d4540b42140c2c940142e0b882840e0f80704400622142c1000d018030300c000e102030b00c1c03000c0c8140b0040086009000d4140151b03400b585003c030340d5410325416001070003104c018030003d841d42245c61282c010017031545409a083d400030303011300009800c2014441c10444402c1520001c40c280341506a103c00035410490300d408680d116403011030341d400c028180030b0181707080030380c0001c0e600d0850314080c0520b84400500c0c464540c1da000c1c10000725441001d16421841a458100d81c0c6400102c010382e4094204840034005120300390400003001800100a02c0882411214401034001500100b07100d10076401000e005800008041400c600d0304e03048480382910080c141070910b40000082b403030f854241101c000c60651903103030320a401d035200f14049030481100050310482c1c0c90007400440008038070080076000c250340c400c0d000000107014801e011249942908150340c400e4801401030181d0407202040d91a64800105c90041900d20310800c00e454482040050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 985206942 1250 985205692 985205701
    0xb0402270117243c100c1205040308120a110c0a0f021311030a0c030603080703050304050709021605010b0315010323030a1d0315010504230a0501052403 67
    0x8104888884a050b0041d2080318030407904c0c080c00c003d50b0750816074505000c107100d00320b404200a4404002550340600c0c4440035103440386502118244644c0d400c00902003040030b171070004071403070311856001070541c40c00850986911602040c20b58080c102d400d009200303240c800682c6400710710507580d010109910816107440020382031404076840500041c004290b891048034100f0503160004503c40d0414800010000031010030720441160000501d020060700741546d40d62446071007205070150a010010000134204a0f0030031010000d0402268255210070100411b200e2311501844116119403c0000c0340103682800a01c0c001468100d402001550f4a0754944000104c0080203906e00244500d00900b40b00300200000d081c40b042e184d890a800358010980704002c0414a40242c1c865004011042d5103403100c1030480e4190340e411a000100e114000003130222136601d120320003600d004004d00300000d0821690245040300c4080e14160180d00c1c402c541c08096980c0c0407101c580800080c000309 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 985208192 1250 985206942 985206991
    0x601030c020307051006030b0108010207030f1b02030d02060613090b040b0c0717070b1501080403030f0212100f080303040b07081302030a2001030218040b0402270117 73
    0x940e140418015245010701644034241000c0300244107004c0152242c004008004010484500411400d802103080c940c850764024014a440302044082000b207182c0b69500c7c041d2158404d948a5000703045880fa0882003e000e5180c4d542222560711540d4019a00c014400340b80c061000655402000e00d18260754607074411410890250031f0460002d07050080c040000e54484c41001507144400c0000e446409524016120300c000030980900303420b0f0300e81d401c652030760400078007500b0030350600340800c561120640a4009000d401044034100c0f4941c8140300b9250240e04040c81030b142c07116401070740d207a2200c00d00daa981c4001e581c014100e5028400142400d84103c58880c1c20420380420318460300e203e6000a4a0260043d40075200100c050106100c3c226130420540c00d4080c0a003010f40c24080740304040f07068080c1c0300001d01d01039601c444050300710360388a0341121040d08482200e1303c043c5044001c041804013100f500e03180070424071147d011501c1c40620047e442070382e1801b41103a43c0c40b0540e841 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 985209442 1250 985208192 985208201
    0x1b010b010e04060b0d230c0324010e10030e1203060a0605030108120d060f090b010f020d050405040218040903110f010506150c0c1c1a0c03220206190806040b0603060103 74
    0x22500b02c110040640200f0307620110240c0d00071707071003a410981c581c00c040c207275646102e0300d11515200040040c0d950441c00c2e600300c1d00740303126800119201054038604550070342c090a00c83c0d49485040c000c06506048511003800510300882d0b007502e000e01281c0e181c1c0400d8950348402c0c0070350070307246e8012605062580c2018000300807031001c941021403000c0da96080300c47d46103555000b082c0b0703190b1a02503801d0b195030b0201542403da50913200400002c02d850b80041d20b00c0c4076900416003c0c1c1d40002d030220320501010b51120040c240940104840392160800a000d002440c000044500404d09000082c0354140107030340c090540142000b20103e230b42c0f43c0800c810b42c00350743d50049500841508025070740d6080040c03075078a44010716507814141e10380350600c803c0c5010a050130081d00500d0a2041c41180b0b01c0642f03601c40301500b0580482c1d041d2301c50200182c03002c3c01c0003d6120000240090300c8036088103440b0300004042d2981c41540e1245410407041c7c0c0c105190140c2c00000c14170004003d0341c4240c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 985210692 1250 985209442 985209461
    0x9060e0c04320607030804060b0a06080a0b030a12020d140f040b071b03030e03010c030204030b040602161415180a0b0c12131e03080411061b010b010e04060b0d 70
    0xc1d202882ca08086209038210560075808180384c14200001e000c101d0085004a24080303800d01d007254204000903148003c003414401440781d44541d040c03942d8070f0811034910141e0f0000604120410b440c0f030000d40d980c0203103420b0b100140140c0010003e10003a01c0c02d96640d240e8403080f9906042c02e01020000310340000d0425141e65600d03600d03144944d04000f4905d00514081d030b65040141d01940305042c01c0d11010340000d81054410070040000c0307410341c0251034000b60300204c00740e83c62405e080160b0921002e40c802a0a0071104001c0079500900003039800408190200000132541e51868007085144e0304002c8480550020010701002803225000c1c1035001c454108000d08002c10341c2c070f05154001c0c0484480110304a010744900912030940c0f0000324458121030040c5804c401941d00500d107440103071000b0304c00341222030842d0040d680c1ca010380d81c96064210042e4410088502c000f8044c02c0140013440c003049081c00000043c2c140b07400798905031a081d140302c0b4038003002c0b0880341e0000c1074240d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 985211942 1250 985210692 985210769
    0x1401020708120706110c06100f08030f0d02040506030108150105010e06071202011d010221100b0f040e04060207110108100b0306060f04060c1e240f020409060e0c04 72
    0x25004e41509110801b0b0a588010440281460324220214403c3c000f80742c2c000c0c2c3c203a075241000400040d94000201c41402000c1c0398210b44901180300000e0290040d5044594044004000486d1030034000502d0110002c50f40301541550740c0c3c510041d1001000c20001c907400450402070040447c4880c902da03680750846100004050320a501e01182d21a6601e50300011650000b40310700d0100d41d0600c52900402c0003065030340a40c01c12011280340171980748500c10300801c020607018089031840044da0000e00386081010281d01d41880e0040095101100407242e001031220039080d59403090b105103200f0b00606444e42042800d1180b019515000108429400700c0b04000112501543d84041d100522144d00c44680e5807045280c4402ea1603840001c03da00d85407200303402e00104101c02d52118155000414041c0451805410007026140c03a00050000d58000100007c042c2c0c0705a215100325010407040081c1d03910344101c2100b10b48030301d11594920840c2e40b4014150b01d81208142c802104450 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 985213192 1250 985211942 985211951
    0x1e0606070803060f01360e010503070312020307020301020d0203041203061a070c1226090d020f0f0414071b05070e06060d09031e030c0f08150901030c1401020708120706 74
    0x486d1780c290083c250304c1194050080e811444a90010303645003840c043c015442c8014101d6042102203596140c0a1001400b180d0060780352091450080c03046031300d440d801074001e650302c4d6080405d500280d801034804483d03004101c502018224464400e850540d17030680c40f1014200b442462650807034016100c282c1c2c060f2013480780040c44504400c103a20240307200d0584003212602c440c04000c0c08200c0200b5408804008014429456803020603840c2c6241d030440d554145034054901060450b007103a0041e5400920742003041d100c00210b081140c2c0300700229070700c150390810885400b40005c0c40b00c000080180d40170710000d000e407505114401c0e034040d2018000138200120301002005547d40c88070300741d02144201000d42c81000302c0c41c030300c040c100080d820284007102211100510300310f0090505410000080045411420329210b0034081c076500801c001e107956103908002100107035500c52002140e8852180312000d50000c180402251140f1010742025480101c54103250350000204544003982d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 985214442 1250 985213192 985213217
    0xf030c0804110301110d050718060905150d020c0c030f1f0e0f03070b0a39030608070609080706080115050315090406090b060604141302040e1e0606070803060f01 71
    0x1030074060852506c9007100031500e400c00100162402481e2140c1102624a00b03074144866500300703004004031b5034190f03032002020400720b0403000c09014040c20324414500020703024031004000203075a03040007c110b056071009007440032200e50300c1d0501c040e0314540c803018071403011164405074042c41000d140e010548211404800070301d8195404503a08403540050001404a90328031403007114100030b04c1b00351144d00070703201c0860b500c070466501002d0149451110b18040907284241c11110042c000700084030303c05070f00c82401800f002001e0040600b40d1113400b078001381480c850b4110300d0494620000d02e020401300e02c807044034980e000920600e0f04001d00007154890f07440b051501486140110000218800e4514004002e1507010305190304c04c520901c0b081c8201d0401d1408030541420440c0c82d040040740b00320b1820040d00440c2e00c4581c10721403110403c080c6181c500303a480004e0400404421032076480d07208014142c003501001401c40e05044c00000c14038106210341304003180c014180040440305 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 985215692 1250 985214442 985214471
    0x309150c07090c090807060806331309050a020a051b0114280c05180a051f14070c0506090402280e010e0319030512160f030c0804110301 60
    0x3d50503046000128036030704c2084664024026540038003540c1c942525170382050800078444050000e1210148400340203018000d1003131001405806c5160030005031200504103070048008814489c111031107003007000041c81e8011030710854110031125250b42e41000c0142400300248120b201c201c9260750360303071500000d0031040c10f001d061040d0420140d2107000745254140c004041c8003166100c035181c2c02c0c0400c00104030303040750503165425501a1008114140e11002880740c0140e54010307a0000501e600c00c100804071070398048c496074859102d100340b65100001102040c031070b481d0042d02e005801d0000313009600c3c042005040c1a0001000541030910410090883c01c0c028001c403002c0f0703ca03001866121a42001001e04841d00900342000031000c14800310352107180c20b90400c0714010341c05101c1c50800d4021029109201101480c640e40f915102e4549002001303040942c00203d01c0082c65a00d08030b20a000342c20458102d992409069155956040e520840c0643d002c0d6040d502d88419034402d08 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 985216942 1250 985215692 985215701
    0x90703021e040b0d0c1d0402030a02070b0f06010e0d0b070e061b0a0506180c0d0219030c0807170d0c0302120d140108160e070c020a08030a0f020309150c0709 69
    0xf4404501c50fa00c541d41c54448044540d1450300d5024801c072000080812480005009258207060340e0250340c2c1d990b113501240c0288030b40307800100300c0741c0b541c400d1107a00c04445220368800d25013a20740400b1503001314208030039000e0744500140817140742130015003800d105114001140303502501040c1040641c10030905140904207812041c0c2c0d104c1c0140506124003006016001007000e00001c50100d04601019110061540c02c03c0c0940c020032040310841d252804104840c030f240c14484042c6507103d01d0320106160240c41180290706c1003510220301d00c1c00d0200030385442080c06005280e03109030fa010960385041400026000e41c0119101804048604030082c283c001c41c001c0000751140d0114132546803c0e4040e048a084c0c4d80c002052400000d110084001c152043c2000b030110982e1060320448008621030310094200c03c0c600400200c050b40000600440c00766510b03240281c8406480403070b0369008606400ea07114644154464407009480020f114250300c0d00103136030615031200038103030944 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 985218192 1250 985216942 985216949
    0xd0905150708041106092107030c0308030a050603161202010e100f14070b04030c08091003090203100911060d02130b1e12270109050606130902090703021e04 69
    0x18400b40d041104010800d0700194106908890759810f08903100c002c907030b154100a0707420700c0d500e15000d080c083c0c11808114a13001075910000e441c241c9a00d03441c10342d0040d0401c0c0c92010442c2c0c02e080200b0030b1807601045280d1000d4003190424441c0e07161400c0c0440404e481101070341481054070101072151a460301082541e080c54441814082d40400010514003201814440e0758000f44030306000505000803a40d005509032600d50103003007490074844180d00ca110603050384280101040001b41e50541c021315541c1d070003103080c2e030541d51550103000c0130303524602d000500c2030300001042d91061804002614104041200040c1001e241924124039584590012024074502094402090034030512122009000c02031150810760b0f00d60240910880c044c03c0100740451410701c0b40d10030342841c0c421000d8032035500d00a2181c02c80905040c0d456000c151111405010007140369407490304a80201d0050700e50182c0030440a6492944c00c0b8000c1d013108101c852a0b280c08080502113400200190015 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 985219442 1250 985218192 985218197
    0x50f1c0c020105150324100803070f02040c052a030913091e0b07050715140106091401021509030415020c040606030b030607030b0a080a0c0e0609010b0d09051507 71
    0x80c4c0c10050103096100c04842402d03403080d40072075200a02900c425418550070070440716082180d85521817510301d20602030700f0404aa101c042841800d0111131045010058001c1d00c00304681810104115810b00c19441d40201e01111101c0e203409600c44160003070901c5501e00160381c205041c2600003031131150542d20840440f03403144000e0042c483e503903081900c40340002016400900c619982c1d00394803e0014140c400740b2401280701c90a0010301d00110003610758500c41000300c0302145003d01c20844080c0190740000d01c1e80d58004c18001c2031510350306003180c4160010f000340d8212a40d001c4407007000a2003603d0500091000040511070b080302c0100302d03480c1d50007a14504182c0000d00c0116880380d8460000c02d800d0101c085600c0e00e0114299410140a150106101c68500040340401d201e035400011244a000c003408207000c1400011020744200c0d4110790040c2e160b82013002000e0340d080c01041a0580d08110040c9030300c0e455032100450340e110742e01343d07215a0741c10f12190700c841108075030318000f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 985220692 1250 985219442 985219451
    0x503030f030a0f0621030e0d06050a0b191e0504060806090c190b0904020c060c0703020c01031503030e0301090b0c0d1401030317100503070b030603010c030504080412061d0f1c050f1c0c0201 83
    0x421030040c011124888410740301c0c0c082c370b94034550048600700b010344506a200f41203210028000c0d030070304080101502028000340700742c0c0d580c0d25005540b048111128905400f42a10043c1a03140c4290030012801403680b45401b8541044040042540600040ca60081c0d0800c18503102c41c000f40b080074031511131109020b84807409403c01130305084181150314100351810280f0b03011b4402d22a0580c05994142c50001003042c2c1002c04640103103071700e80c3c0180960103200200201440b416004240091141205102d00414001d10155404080c000103010400e081d0a001d0320420040381c0f00d40c0912424900f81181c1d540703001180c1801c2c101c0c0c010b1602000000100302c842d0800340034002155080740380400c20351410703449503992406980a085084001c05280c072040c44015046041138241e01c02c1c0c8003000750250b10f00b142d560345200340210024041d4640082100c0744210007582d400f10320303840321890414500d03425012548041080c0ba88400702c3e98118100f42c04900c0f404920191030703000001c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 985221942 1250 985220692 985220701
    0x120703060b190e07050a03140a05090c040519090f0f03030b01080f06032112102c0105040c271701090201050f070204060503030f030a0f0621030e0d0605 67
    0x11515034030300000002c034254400401c5065003c1000c2035005002d40351064071680102c0045029006c00301602c61891075030303003d020752140366074816405141d48c03500320b0b40009651014403082c1d0b802118a0540b250781d1094000d0f0608098001c4181144254482d030303050801d5980380407024246440650019560f0350b008202075802c0300b41690000c0c5142e1000303840c2e15145000a681d06180680e1141c000c240300c0550012110240c00e41e21240c020f0700b100522031a041d91a104245907034403900884134600841902034020001011403450315030034030156a40e09100c18000684507007000c5800300080b04014006030f08014201041c10304959041d00051481d00c42880d444c868248039000c0264035011401d00142e800c00c0c116403160702c94000e401e40b42e214038000500200f40ca64442c5401d4000050400340f480c4400004521800322548200315441840c4103000c01c5640700d00030f45030042200582640412007480515a100b407103841c00881814017100031460502e00c4a004032070b500d45550070b10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 985223192 1250 985221942 985221949
    0x60903030f06060405061c020f0406030506100305100b030c04030605071e020303130b06033a0305070f1d060c07140d0c03150608031b0d02060420120703060b 69
    0xa801035412030341e441c10035040c6000076045115280025600e2a01220207c10ba0f40303030350301a43d030b0355011013050359101c541d03800307004e00034010031603115100d0b2045511b40d014190081c410b02d401080c04850402801d410644420520752020740450401c02c41444000006045030117014860038a81d9101b500e02c50b2a203c10ba00d40c00d00b44540c0c1020354005000700711001c058007081160303460700001c4100054030380602180c201000c3c4412400000400300507100700e5089883e04040baa08910045a440d07401c100c811002c4901c141c44600001d044c250480101a00c50003500c4a00c150140030b00304000712050008400e1b900800c24103440f50041c10040203072402c4081c00c000d00c0300302038034a600000d6080c1d07581c400c3d00040f03000060118441048081280403140d00120181c8481e0b0101c0769610112803080c2c002550b404503281d007600c02c901059101e28030110f001ca011725445501417840344031000b0403c80e218012182d00782c02c60348080016a68541c00c11008001794040d40b030000c0e02801420a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 985224442 1250 985223192 985223221
    0x603060e06240d1103010f06030b101202090402181f06020f030405041d15341d03070906211212061e050135150306090303 54
    0x80031094140326a00040c90601e00300b070001c00c203401c85840700040c141d8546240010078041180f80c041d031810944011403000c40e44000180c9000b1803103201566900e06d40805907648900407100480802d181007401800c0c103181851f00580300420b015408440d0a03003417001c8a43c106d40c0301001c0641c1e00c3d10900d00c4040805803e010384050f00c0035081c03a10038590003907524401c038450603000342da446450303442ca101590300500608005a064031554403040340b03444043c20b03040d605400e40240c0c01014009422000324070040c14a0b9881803801700300352080d416a40c08203034120030328a410342e6040c00626940c00f4004c60700908000500000e03510705112100c582443c0240d02280b05035980c00200d0701050400c5d5007d41203041c00d1809021300720001d807408010b40004d0388035108682034a00712200000d82c00610700e095910a07602e4040c07543c2c40280600101a8070301921007101000c9410f6507070038140c5071180d079114140e641c0341c0015640c0400440c2c80c1443c00c9922162540000c03045c8000812a840d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 985225692 1250 985224442 985224451
    0xd0305061002101a030604030c110a0e2215020702010e040e0a0f05011b0c1a0405060f07090b0f0705060c0f0d0203101703040f08070317030a1e0b0306010b070b0601050d0f0603060e06 80
    0x44400c40c043c10002d0002c0c1142014084003e40610006021142041c41c480c0070dd80c1c95200c10720f0090b404451000601941044c10201d000c21071182c040703480b5080c18801c3c0c40251a00000402038000b0a03242e5018028800303000382d425540342c5410340000105540d144401c00129901c140480005080a048c5e0f04222664011074820139010703c00803074000100942c0010f20400e010b01c0c00e441304a0142d07041c1015510169080c240490390042804081010740030f0903000b03d040d00c41c251740e100c407164541e10502030400600401408543c84121150707014541c860040320214401c0c80d1544c0552007103003592081040c05030700010301406010300ca00704420050801c00000c000050665035840d80b1206461030200d030306803000c0000380355031078aa003004110b4603138214409513000c00d005d812009028800d031118000d106038400001d02d84510012100e8154007c64204440d444190045174140e000700da00c0c84c0d803a910341c4070b40050701c8054880c0c2001940f20b05000112151100703001420b0040040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 985226942 1250 985225692 985225699
    0x60810140106140307020f07120303231b07020312030402120309010e01050a03090b0907151b0f02030a0611090a0b03040b01090c090b0c0d0305061002101a030604030c11 74
    0x40100d181c220460107600d01450303440b56281e036205c6004030b19202d0080b008110a1003407801c0040c0d4000d000d580704004902035074060100d9004055580100100d03000241307002009400010610322140c044820f445140128852a100e10b41e0002440c0c684100c0c0740103c3d48030004148800c49ca04010404007001c04071001d9420b02d00c400d4000b0302456500440030303051010010300003542c2e40c0300c0c1c0e01880d0030581c0914080c4080c1080350041e5542c130340f180154400c0250462405040f58080c20080301d90591003001c055688841e0755540d0b00044800c10200c1e00340c0700d00c844007000039000b4040c0b84002e00c2c00300f040c02e440740e9031b03038041084000e9036a1014860200400900000c00c0c0001c03d514196134404001140181d21601d0480700c4008503072100b0300b580c00c0400c00b441490b401050901c0b07001c41d244e07805d0100e500c80000700102541d8180601015a003c601d294810b507140303410a1103e0f480742035036031040c0841c3ca0042410441d013103d045000840401400c001c11034028000d030031070207056 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 985228192 1250 985226942 985226981
    0xa0e010e06010c06020f0a030c0320090613081209090c040b1209241006090e0f070203040b04080f0607090f031e0210080412210b030709060810 63
    0x35110080302240984100d04024886940c0000c0c89866011180850b1494021039a640c0309450000c009090f1094500c5c0002c1c10b141d0500c6801e64000301c0030364a61120440e0b54946215142089941e6210981d5180540c003900310004402c0c105000380024480802c980300c2c2c0c3c0d01a4007081100c1844002e00000d000d54007840180592034201080e26038000003568409103d48035904c2c01464070000d00b000c01c01c0350030004440d05062464642c0e49006031060038406102d140c699100380ea0519850003a2541c10301260f0029210290030038020b900b007252030040d40e1900d81c0300d41c030180c0c13150301542042507158009040c00c40c40c0c00081140c164800b4083c83d101c0c03806414901c0e006080580f1b4407015140d843d05032849000c0b08162991101e130a640106003041d00001080040c105100c100e0b02900c40295445560707040a00811441402d045443d4072171141481c0c034103408000f050b1404455402d0b01ca080301c040f5050846120b06409011400c00404900381840b041c10f06032a0704800400d1148101c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 985229442 1250 985228192 985228199
    0x804260405010c1502030c0c0c06250309050a0f1e0b04090e010212102c01170a060903120f060506090d020112091101080906090604141509010b0a0e01 66
    0x506032000c1e00c00c00d103442c001070309050034203248070076100c0030012200d0300c00003c0c01003840180009000301100601a2262400c5810400401e4040c2119200d809030040320003448030100f01c0340c40e41040344030313040100c0800e813a40013080c3d040d042e07604202820306034041e062007642d90300d50340c00e190800d0031045032101c42c0c1804100352490080303102d040e005903100e040100390f1030320039016503902c0c2140d4042102c0c20301d0803a40c00354800c1c00502c02d900e203003d007011522210b101414814840c80f201d1031000b50243e440d0003074000764114801002d12990003070780c052000042c000c2c0504401d1034065920082e0040150812030100c0d00142801503180d46018010021070f100c00c001d80c1c03504401202e00790035580d110300040c1e901b240d10200040616241c0074005013009072120800035040020390710501d0f42d07914484030542e00d4009440c804a95802900001c000900d00b007191480303100000195070068092a106056000302920403022994481079660038a0800351956401403101c0f44a03428113515 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 985230692 1250 985229442 985229513
    0x605060d0c03030f09051e041512021909020304060e060c130b130b07240207051903020309040c0e10021f0f1116020a080c03070b070c150804 62
    0x1051000409201c0314400c40e050450086000c44018031028040c100c511fa0344110030f403141520051140d201c0d91a01080a03500705c4030103109400d9809581940118030350540070031103a540c10304000c205c403032b16002001c87d010125002860140b84500c2c408150555602001800c1c00030017403407200d02050900030105074010041421080b200d209200594840e0580307108849040e8907001600007d00004e001c10420070030003040034042d400140800c150030055203124040e4858241c000d082540a503440303207c0c008501c00080c2107940300f80116450311481001140c1a242c0c2e00d140600401c0385807a103803115040140710700186004910250181c00801c0000800c030540101042108030fa854503803052026013580960f0021018408458035407a2a0449200d980e40d0b04070b003280580318030880081e20000002d9140e922a85c000c0107040c0035030604002d101d8130f400400042d20043c4456400080210074182d05160056080e911a40039140038204000a4190a40c0c503001e03440f20700d0780c510b542c5031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 985231942 1250 985230692 985230713
    0x12020414090c0111010e0a030c03030b0303040506070201030b031f0903020105161b030c0204110a0e0a080c150f070609051603020d081b07090618090f02010302071a07030203040605060d 81
    0x41c000d080240d01c00041d81c1c201340c01401d440e504900d081c0701e429442020b00d038000a020381c00c140300f581e00f405288015030605449000b18411650454002d00c8050b00540c025007204482e10000f0b0121182510702c2e9002031050b0100f205010b840f25500c0c1205000e043e42800303260362043c00c0703151100c503200d04510020f017040710b61031880c1160000c80d099002090712507441c92440d075400510500c8007044c40002d80e00140e00c0590010049034a0800740d861506110445000300d464400c0030f084600280c40900c030f807444c488058419150820465400282840805840c005000e6000015140c805242440c40c00c403a90501e69200e43c2003032030400c010781e00c05402a441c1e07a4002e090705d460f40140058440081001e600e032044500078080003041c140b066034031002c1111414144e8001440506500c0401c4825410014007000c446840540140d4000c0c1c00508009106601107441c1c1c0d0328010f0201802217081e206540001c2e0004140b0080c408980601d94000170216500611454941c0c2c030b040e1001d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 985233192 1250 985231942 985231963
    0x9013c030c080c221e170604020108010612061211191802090607060509211e0703090b0301140108010b1903092f10020622050c06041202041409 63
    0x2441321504941c2492400036518018280540c01c846a01c2c01ca01c031100c031082d1a405500d801000c01d9081c1d49491030001130050080c0d8060311006007036400c200040324070300e065100b51040251507440c0010401c82d02d848034205680078402c2e0400c0e0000d10010816501118182c0040300003481c1c0e002c0c000384407000d1480c1d034644054000140d51b0001800410854007482034041c0100d0710300007c2220718240801c940d0380d004c2e03101700501c40052000c541c49405000b414022540c0c2e08102c83c41c0030b4060b01240c000c0414038003a04214030740c2d540d220b50b54200b55109800ca0143c00d00c80c1f21019003156000815a0301514039501d940d8101f0304820510501e0410032000f0310f0801d61241101c500f80440d1503182d0582540c000030031210050040ca52007415885240b540f4000c0c54519480b0a85a20108069002c1c190f9082004041054042400c80c900c64181c01582c90740284440c1213003d80d40c0340018401814448500034880c80d103030040104882e4a032141c80032a103204020040485004074408640303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 985234442 1250 985233192 985233217
    0x501140411120405010b04090818060307020705120a080319050c07031403060114180306130201020613031404060f020c04200c0a06020703020307050f0705030309013c030c080c 77
    0x41c3c0d940c0d05003180036000301e20440b40c000d49095900c009000704100146400d90806480c5095130042106101e0030f03120468006005070400c1e9414000c51070208100480b000b5148129203000c1030301c2e1541540d5500a40d25003800d210741480d90321000c0001d00030700f980480000718a500344119610013a1003e500000340c642c42c1036000000449030382c012581114105500303900582c56002c0e0001c20062002c40610242c071912032400014004040800020103199040c1d000d4081601c0e4804420440e40103d50105c1c10300060801c1c0d00c6e00022203401400080200c0e81c0c0b90400050840000f0b410311005200250250703041c041c90f910240810b032020141c405040034480d0f5690402140681041070501c0300424840c00003603428241a80000a05000b502030b03400d40741450220a501ca0342c41200e0300c24145c05400502170f20045600444078607246040050b0600c0710040c0035104180d080e800c4070107403984030501c01ca2078410f803540352040820604590411144d50308024500440358050144141074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 985235692 1250 985234442 985234477
    0xc0706080c13060807090509090c0d03050f03070e0f10080f070302090406030c1a0403170a090e040506250207170109020d06060305061006320a02010501140411 70
    0x10307911860120355601248882c028040368480400408444060314039500246c0c80741d00104441c0380023844a80aa4001c6e402016201c4502050002c1c01c2502c45081c2c06000f020b0041d544202850002140300d0316241d81d6101c000d000007010000c00075482215130b80140c22040c0650300142d04070035459007110036540c12102ea55038910044010344990480349800070309100c2c0c004200031411012106a42100b4a9402921904903038200740f170080348809031071106d0001c00080d14100100c0101569035440c50300e0708034291145440b4072004400d8030121000c1c1c4c014000c020000c4c500c800403504003180109959810015000002d58503040350040c90842c691031010100c0c0341e08254081200c4c00d501502103412040d003424920024242848181d40d103000d500002810140041510b4040d00e6680d00c4405030155654480300d0000d0705030350750800e00103000700640c681d41380b1030024003000205540041610340c100071440302c829681c664018010341c2060b6111010f00300160546210416580e5841ca = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 985236942 1250 985235692 985235701
    0x270b07022e09110607050102040e01050103021201150507240c09050d30091706040b070507050a020604140307170307151e060905341e1709030c070608 66
    0x22403c02d221100c5039010b000041c0c05010007034107401030f04c211400501c520b10982e82c0c940054040e8411010180880c201a80043c0b000380025103003207c1d178040510f0418207200c1d01d1340d00e15981c840100c00740d00b211403c035200380c0d00140d9107002c4e08500ca8007038681215001d02e4540031400380000b40100600c031070010302610912040d0007155080800c2d94510711800c0000b40040902111203a0141301a54540c004102c428884d002a445018a6114000b4502c9a40c0c00208450716042250121201d015100400f8090303614900034001401d01418000820003061040628001e0642d000390381e10154401c401d600801d0110554101e10740002000c0341d03000780081854020602110446c181d21180020303100c900100c0c0d8003403c15124101802c004caa2a101c0307820100c4003000d002d445032010509a1b0102d1425200741103006000203003003508050419140c181484003400042c00c0004880c00e030f0030a03484480e0f0004581108241004e50328081001e02066100c0b0340034000c0c4001e0200e502d0105 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 985238192 1250 985236942 985236953
    0x101106071422030201121104140f03070b040f090603021014070605040320011b05090f040203010e1005220c14031015030b060904270b07022e09 63
    0x461540d4031100400460302824515120070b403455001c2a030000b0804120a140c1a00511506804001000c3e00300c1c00c0c80d20b00001074a003076030a01c8819030069809040340e502c0752000c000101c0601840c1d640e09480700d082003507103030060b107007644008143c80c04c1400c200b015807542c0581c1e12a00c0e4540c6010914080040d10507081031185400041180b03150400300028941e004505000b00c3c91011040c984000300e108240d17090710200201110307590220354400403036502400080045880140494030070210400c0000d04980090703105d8006000840700700038402c10781008210103814101e400c1a41881091010b031842114408024034169555060944c0e1034051b807081c0070a009003c4c0f815a4a04d82900301d41b4410003503203c1d040d200000d02c41c03031010030790282c0030340340b403114014181342d00f800b94034001c200c0602200901a0001411000020f40c00c0c40c0900c1a00e4645026030f1100070607061440c0024900200420081e9189007041d80311a50303041910240b50318001a00b0001c10000b4142c10213 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 985239442 1250 985238192 985238197
    0x121050a0b15180f090a1b1e080a15060206160c050a110f09130204200f0d2c0606060a0e0915040e1b10080106050d1e09021011060714 59
    0x90703500a110f0010850b41d01d03031a03004110300580b543e405110340f0001c280300350b9149845004810802009000d08c07a0b829100c5c2c61202e900840004001c0b503040328601c10308030781484d1074001d000180c100000b0004490607122041041c03024a01c4c0070034401ca6952501c544607220400000e00c0b50120341e54584007070351070000821103031800500c903090a043c4000e1544042c501003038200c5c0541d081203d44459208a0402c05e00440000c40c100c40c41d200e8000c071401b03030b907512001011041da83d8400c010b0064500084040c0b040800e420985d4100c3c00c991401d1b585040c00080c203040c424941009000c041c0359206c04681c41c010b8040e190402d1a4440341d40d20880c0d100b000c9c95285e0810311b02107003a4024040029840d407100c105040d85206414143c0c18000300d06103800010b004244a5030040051520072401003140a10320000020054080c025101d110888819810082521200880217620f018142802d0a00e800e0401c030140c0c06004400f0f50319030070010711420620043c0e0900c2808c0d40001d104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 985240692 1250 985239442 985239469
    0x11a030d14030a090b16180311011103042d08010615050c0c10031d0304030f0b090a0b040c06090b07050c01050a0203070807060e06090f1b0121050a0b1518 68
    0x5c6051180381c041c1119001c03010341d1444d500040e0386500c01034141e034505c140490549030010905030003002420015145042c456400c0910341c40100000a40030402402c106010503582c0d450f100c1851150b9070024411040340c1040c0543c1c1d24014041120b0b400d540c00654054000d800c000d43c660000b58034403070821101504a54008515130250031250390305511402514902e90585107030720030311000c400c0c0d80303004d14000100804030b9055a400030800078004107601600b01022181003516030364900b440c0d040181c400704c4046e0103412051020b00c0e0418182406015007549140c1000104d0b203d169840407500b0106040c0310001502010642c820700440383c0450708200100d80c1e6820700d18080d030003801c00c0380c161001d5002d00c0d40400c403000c07000b01b40d0031f030b81c0c0905800030225882415072100d000020700c2c20141c14005451070000c20440b40050341d40300b200441e400022a4688551308400b928040707240103100c0c071494124120704804000540746422724030f900628030800d5290114015850061 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 985241942 1250 985240692 985240703
    0x309100815150f19030608190602090301090c090519050c16260702040b0d020a091104090c0206090f0d05040308030a060305030c0607020d030b06040302060a12050108011a030d14030a09 81
    0x58000c1908006001514141060b030345d041099950b0ba038145074489542408050b40b00f100b01070001d001c141d80d0f4010700404000140000b502d00303859620340c00d00702001c0c0c0c40214140d480700104a44a80406c070f0500e8000d403e05c20620861400d8180c5945030b05c61600c1d1903418105c4104514240100f0a262460032200240c4140e4465142011101c1c1c940207080b08901c03c0b414500ca0101c02c0c1403070100d00511903409400801c18504260440c800b82a60300c000e40d041c0c207824000000c0b880c0c00d600800491500d280c000e8202420074804c0c02c1e0900131010700801250380040d090380d01e019807000c00c9908507078024440f0b540707a07101d41d0840c001170006603002404912010400318101704c40441c00780c2c0a540b40d902241d01104280d141a401e96120350740c1b5a330301400921040001d07041c150020003200a69281900c145e2150075000812910207810180441c1e541d40d520740c500d03d0803040130116002086000707040074081d050000380071440c01040400c0c0c4c05801300c08a6002d41c056044000720a6112 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 985243192 1250 985241942 985241947
    0x161b08070f09050c250b1005122b0201020d0501060309061803020c01030c1b050d08180c09190e0102030901240909021f02060f1608060906130501080309100815150f 72
    0x260024070b1304c128940211486102703a4810b4404901c0001451070310071440b00c082a480499256008441004e83d1142c0307030945d50200704800d0f000c3c007a0f00c600b40c040c2020380c500084800160a140703045407801c004810715420b0105e144000300c0d40016852030600c03030910340418502e00b010070840c1c0e020300005e02002d02c140d90b6120807003004004191180f805401d50769004082da1510390b150415803c0f40c3c2120b6440d0840780c008103c0d03003042007040d6400030241c0f2107204110a405494003c455241c1f00d00c2c5102c0e5404024024240310a015030b071036038944c081030b0b08403e8500e912002c40c2a69a0301c1614541507440c41500119214009003001c21003018450380b640c085011800f80d200ca004132101a030400c0358400143e12030f44041440c00e9180029592038005544000c144a000100a407049600c912241c41100403400b890280c0d03401781140d500519102c001e07141c140721500306031785598001d110313015007086606e050400c071400d00c050048484030659800030940302c5440c4504082c5d02c4150200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 985244442 1250 985243192 985243201
    0xf150305060702160e070302031b070c08060a0911131409010203040c0e0f04060c02030f0c0106030b010b042103030b31050c161b08070f09050c250b 65
    0x441c400d84240c809400307071510602801d4400007500b00038094a441c0e60350351004141c40d1407182c2d0196500807840303046480905007030b180303011854200e5007007183d01710030303100043c01950018025183c00195004040c410050a0703610101d4200103007120764000c00003040c1c41c1996491580040150750708040c1c00ca10141845030345039000c3d5101300c0781500c10980040e40082c080b0849054140f1402d6021240342843c0c80c0c49d91001b001e00191419002148410b1244804400d012001089402c045c80000030300d0600d14600860085d405030720016600740140030400030764510107130301110140d42090005090031a40380541c0140800e40c5019002108845250307868040303000030749040410113a002c481941c3e0400540c060710300455404100e10428003840c0c514609140846009030f10600c20340e000304901e98000c3c1605003850784004490344c4010000c0055009800d1400040c0c000d452050003946014076040499204019400311110300600f000d08440c2c04441a04110503804160380c081401d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 985245692 1250 985244442 985244453
    0x190b03160b180303250f0819020c06070203071505040e0c03152e05041e0e13030804081804110c0f030903060f100806070305040c080d0905040f1503 65
    0x1041c05000807202021086003501c0c43e001082d603021104080702e40d40f40e54070340c0c50b0408000c90765002c111a90111403200d14005142c03030000e4620904d1100a0031190101d04100a143c08023100c00305001d11820090240035807400720f20501500c090900010f14440e1802085540c0d118541c4525440640e039070a00c02807004c070100450040640d81c0b6120700c0004c2540422041c2e0240c00d03003055100140e40c00d040e02288020200c05069034003810201e04044d030b994200140710400c8408902c1c010ba03049028080361100380456600070704480300e200c002020300e40d000703480030b40040d02c06001c2c400045001e001040c8200811108144050014071090302125003c0b0b00a410a00154646024040c40b0a0100500105449040c540100241990340742c1800a140700140a854001030469183c0007040d560402c02440b805550540e5000426150509050640c0d0784135401000705600180d400500030341e4400701c02d00640364201c900262299003042554001c14800400c3d13216400010400400d002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 985246942 1250 985245692 985245697
    0x19030e0705060a021608150906070818150906010e011208040905130206070309051e03071404110a020607200c040509030d06060804020901050d0308011e0f030b09100203190b03160b 79
    0x2d1147c40603003015112110800c0d107400040300c0c410000b0789a03900042c0070381d20131b002c80030ad070920081c10764450120490341c005a401c41180e80d9005c950011004000310481d180e0464010300f84e2040c00b100b1909241e5904515200d144158241c0c1900e80c070108100e0100307010007800d0302c7e038003c1000381d560743c1d0303443d019010341d00920429100702800245c2030305900f01103d24180e102c800030080c1c005642019104e05400342c03254503182d013081c2d5031501d00b0f4110303201400500c11700340160010121440c000000070200400b01403041003021051210810702c0c08009051709403d002198049125640d110b245440c50154000b00c0311814109040050010703003040c861402103000b943d1001190b07032114180003200d08010b40050014161200400c0420000103400a1500710300035840c07840b03980c07041740c2d01d007860954005446c0810540103008134603c0130031400004400c0c020055041d0701c4c0120707070b21101c14039810342c0c10307110380d00c6095951702560140310301c0c03800040c01205d07940e50545078a5045040d8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 985248192 1250 985246942 985246963
    0x140f1015030e0105010902030702280c0b070c050d1a070c0c0611010e0c03060c0a03021e040603050a2a020109080c0105090d050705030304020d060e0a060219030e0705060a021608 78
    0x41d444c010022514940c980204c0744110500d40040c100d4040000c0c100c00c3d00719214102c0d414080980c04003200080311416158010070942d5955500c0c1c0030181400c86500d400d82c2d00c01880780c0180721240001584102103240d11850b1001c0780000c540d601c0c3d006075911004c801c0300421a404555010511980000111480c41c0d010030003000004248118266135110030300d0010390640c40440010841a610001803600e080103250140c00c008808880be008207404c03d030034042ca8000400c050212a5051007100d501140c60790091000201d4150260000c1c8100c142042e8400081210ac40019000f50094410154022081543c944049030001d0091a090382c40118034080c600f8000400c41c460820340e5065a0000007840c6583c45036402c0000c0d400b48180c080398003d03120b025040707110038288540394840e03020703030700260340e07042140e03c030004801e141c4030300d4010325250450030240080d001501c0400c2d96030030b851040d03407914000c2d4140d240ca8826440504950400007002c165050081001c4008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 985249442 1250 985248192 985248221
    0x5010e070f0519170f1902040c05160204051e040b010e0106091a0904060819020f03010e1903030b0a1403070f060c02010c080d060b04150201140f101503 67
    0x803940c490040140101840318240f050031203145050100340407550030702003411014002c98140f1402d01d101141070101c08000300f1140c20400707444e1020f609180c0101c00a02e0103d181c642c1c45c5c40c40c602440194841d91139006802030b03a0381c031700203040d020395200d00c4020a00387c0b00da01d050780d1400f4035100c51100e2090248008050002c000003d00c14021401001a42e4000790580c9400300079040c401c41c40d80208101c5035000fa2940c10000300b0b4242030103820042240910b0386002da65185c0144450810780e08402c0e03010381e1508440f03a8088102103080041110750281c0c100100301c5c0703420210064240414155070005070700000054450741c582e4001005002541501c40669684400c603490005900c229404100c4034120310300158812180c0d12100e1b449041c81500b80710040700030600301ea801e5080312020410000b014081c1140c8040c000d02d0040c2140300038045101124031540c401c0f1006032420f4004107010003c0384403004443c1108001d490243c03005140c40178907010003400ba00264180c40036 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 985250692 1250 985249442 985249469
    0x1e0403022d0708060402030607180b0f090a050f010f0302130b0a090305010b040209090106052d130506130b0f19050a1b030212071103161d010612051305010e07 70
    0x320f402020a880d4860340d0001d015110540e602001070780c400128070801d0708299203290010501d040003802402010b0036000300140c88980c1101401003507506600036500c01c6006850360a0940e07886401012003005518015031121091160320301d244d0511340040c0030b071040101d09102d4440c0d0241e21401140d0264000740031410700c07072050100301d20441c0a120303008280040148001e40c0100000c00c2b1003104806400103401140c40b680d40210408120355103245000600c0c16004409080042e01820b411181030f45008015000d0158555440c07003011001000814441c039144c10540c2921207486085120300c0442070106402080c6034496080038000c07400710900f10303c0c4032075000c5402c0300e681e0b81600100500c40c0b41d03840f65141c0345c000103803c580010010a0311002d0341c40c02d108000f0109240d902c83d4000c1e50802075002400045e40300c1483d502c07003141004000040d40305000b1000201a1440042c042d22030310b0b00b03007030010704a04000d040c2c0c0d82003002080101c00001041002caa48860b070508 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 985251798 1106 985250692 985250699
    0x12070c050f010b13140a11210601030f05090d03020c0a020415030c06020f0316021203070c0f0b0c03220f0f0306141e0403022d07 57
    0x4100740d4440103c034001d404c2c1107001d09110b64070b1500c1808018003d156450084000500c0c160000351036958182d55418001e084501085a0500d801019a118114403041c1c620a40d03000d80000e244c040c030504502c00620509004025580141c40840511401140a900a42d03104a140c0c01602c0d852001a5540d03c50313851401d4220b101440111700e9400c0400541000703034812002c1d0740042180c222a50004000c55948040380c10940503500141c0c0003282107180034a03082003040c4400500c950620001603d18400c6621540c05004010307203a1a503807200c1d00900d40081e4140c1e105220038100202400f81008504210040c1c1c09000340d66141292400b00155112850010b0003140a000b4007605008a0031031407220101d421103814240400c14100c454407120081001414010408052080c481c000010944002118248a03250078070712082000d0751610300ba1b840b0702c10000 = true := by decide +kernel

theorem cover : BRFrame.Cov 985071942 985251798 := by
  have h0 := BRFrame.cov_init 985071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 985071942 ≤ n) (h2 : n < 985251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
