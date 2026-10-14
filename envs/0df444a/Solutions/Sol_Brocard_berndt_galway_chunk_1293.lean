-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1293
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:12:51.651713+00:00
-- url     : https://prove2.me/submissions/4e07b5d2-3833-4b5e-8516-e0cb35acfddf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 232374100 ≤ n < 232553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 232375350 1250 232374100 232374127
    0x1110703080601020d031802220c02150703110901080405010908030c070b0112051f060f030308090d0e0307060c03090918050f06070509040b0d0c03060e25051005 71
    0x5550194071036400d107082c5407000a2030000e80c94940c504246c5404883e03001c82e01100900c2c000150116003c09644003881c1014001d00c0b8022071742148a4504200c0820320368000c0b03646110784551031a40400744da1803610540a9590b121100c46c650402000904c040d0340c041c0000c260054000e100008a40c14180d031004420384c030581d0500100880072074401d00b04140c1e000400e026140c1841e00340c01e440060f94a840d61429020a021003c05800c071103030030100c105900c48401403224081d20301509540342009491100e0030b4031200c0c01c50144180342d40040e0b001707603800401d00e54040c0084c4005460040111181120360380c045081201c1c55030001880a2540074904000c03c2c3c00d11400000d0040d441c2203480c280302c01c0c00c01c0c0c0c4c55802403020002e000d0b4202b0159002d0f400c0a0310b010444030382d48400680d80c15000440204404481040032040c40490307400f5a4203030144108417426005203a48807a40091101c0d524002d0b03108104003841715003004804400318071315500703105080c10107102c23009 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 232376600 1250 232375350 232375357
    0x3090108010e04240501081b0303040306110d1401030201120902030a020f0406090e16060f080c160f0302060718030206072a120203070609031a070219030503040b0606030f0103060b030111 82
    0x84d403080c0e2110014042000240030b904012000046100074661406010036200e01980c8400742001d0b03503942c04120200c001004544d09a14071403000c00c44681992080c00455000303000681c00196501005c02c2d22030302c01d1150310361058009000305160b40c3c0540c00c02803d07210703c000c20360b000b948486e00010014540d0140c8505454940050008000c4681035018800800e6201e0020041c1c00d0302c9840d820741c2c20417031244d0401c070181c10440d56403038100c110341c610004007440148071030110a160700c18140e000c0b88450103600c044d5540068200082105c4030b401e0620b0101a5002c0410840130001030209020851030342840041038064070307410149120460700351f1384080e00110107824134100f140750502c030700f40282800d8203000c01d44608548407900e8441c0a420308a4100486c5800300c0e844500820136036001841c1c440740d00d0600c10740d500d40203009800039501100c94500e07080c049a001c0c6418010740c0e1107002002801000c0c2e0313185407034010240c040a040035405560f02c014103524005108003c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 232377850 1250 232376600 232376663
    0x18040f0b0333010e070804110a060507030e0328020a1205070306150b0a0c03020708030307030e060a0605011707231801030608030d0e07090207050d09060203090108010e04 75
    0x3104200110340b002d41070003141c00c010b080c0780031060340c00600c21808030801c42070f0000c035203192410b069070302d501e1f10300c0a600c40300c402c096104c035510740c00040c21079001f0000c010180c403a43c0c520784a80c49000a01d65a6034599198026051050b401018103103014080c102440780010070009001d0f544070807208060f2482c0b002512503030800d107018000d004580c01384054080503190558155441d01610003468040d07003109104002f41e0342994014540308104c0d406c090300e2004181c90b940c3c248060090000c0c01c005401c0c0456010701000100381d00d156201e100200c440684400c072507003048580200890400411940920810503a407003d9284c0e417100010713007440c0c66404d06590340a591000031030b103006408060b0400d8200710040c05041c5000c400c1d6280d4081c0c190300400c030801003410307e60a24120f83c20080344d05102040f020b0901c840054041017400f2203850303240c5400c0e200e00040780c580c403030189100d02146002c00104461805009c1050f40103000e480e04c0d10541d0b00c101c03030b80120503540504 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 232379100 1250 232377850 232377883
    0x1f0e0409110d26120709050306130204020d060806150f090109020309030f0d150806190c030b030f1b0a060c0807020604031b052107030b0709030206040902030a0b040218040f0b03 78
    0x1901102c1d240c11507021340c0c010b0000d041c02c10b03202c3d00e84030000b5038580d00203044114055840c6142821915141c0640d1414100320409028081d00e410940381c1c1d07440f048440c0d541a02d0b03d485010402d040c40000c2101f00303240079003041d00c0790382007004820203540701070040c00c25848204810503081c9100c00c060240c0124400c0042240128070307ca00960703010903040a10141c102e40c00344445040b5100d80c41c420412458004941801e0350481900203100c11401c107509406105206640c00901040286140c0c01c608d25000c55113802606014644030301d030040c1004103c1b04500b82000ca80c450002d081043e20003040c0a152070380303907a01c1441c460000065004020050002071025140c40854905c0c180015982c43c04032561030350055030354203054072000d02070110000c045843c5501c035403000c10155402030101c2d9079965813040140e00039803045401e1f0052910704406405903242a0003244c9200548040a40008509600b080010081c803629032684c1d507a614041c00c15a1000d1024844151501a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 232380350 1250 232379100 232379107
    0x16030c0807081c020307021902010306051008010905070f09060c0204020d060303080a050106080c0901050c0c0904080403030f21020a031409010b090604090201050403120e1f0e0409110d26 82
    0x81010942c0d043c0600c600d011a401882005121036000900405010000016440740c164500041e001031000d508810740210051840504240d000600707107048a0815404000640e51000210351040e0501d9405001a00681d401c004861142182c24202800248010b14046d10a8421401c4500c1603000b03c000c175851034100044041544201d900620b002d040602107490405e180d0034103446a800e1060600c4000716a40140050030414074143c0400985001d02d9820542042e04c59500503101c100e00144c4441d03241d4000c0d512030500000f08441d1302d1852091401d003002020b01a401c0200c51100300350b65001118110003c1c801c0442c000c901413800012548110024801413200c0180520300860924610a0050342e021048804883d0811241012001140d000700e680030040e03030031540d10484903c0340111031001104011a0b0400d10f07150b071107144081005000981e48000d401614030895100c0c10880d6003030400c41c00c07882c68031404011509150040301071001480c0c003a5103d03089640807 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 232381600 1250 232380350 232380367
    0x916090509150702060a1104050303030a2a02071205010f1d07060905090a0209030a30020a05070b09040902040e1b09011503090204020d02070b060901050402070816030c080708 77
    0x2032000207100c5100c2d80c9010701525100300007a540d41d10117084074900c130b503545061006242550301507801400300103041e265242026a5a5000380909081218080d004101b001c5440341c14015030401141d441e40103030590700c5c40c0c03112644804161980544040d501d50700821140c82052281c42d061045000780349490884a903580303841c15410f0b4000340c0a1261100048c01036549403890651b010901c4075008d0b90320440300d0042400d0168003000180480424500e016480b00701c40114900c8154070340300900c034540c18503002c030394405003414050a160003003141032104808000080c503030050050404540c108265001c0740807502c0154001e151074100048541d0a07988448460810000031a03004880b5410301d5598030045007016000740505640300701c1c1d070f42103444a0301a64554152114110349a01a41c01c144101e00310071100c05118402c4400045603e1034140b0990320400d410111080c24034191803452014890704031030903814410340910000000300031500038002d0328441d08032580c0f2a20340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 232382850 1250 232381600 232381603
    0x1a040212150a06060201111603180b120714070f061b020312060a06050d020a0210090609050d020f031206191d070306050105190908060a06050316030512030916090509 73
    0xd4004c2c80440e410710180b00c1d000d07007215003942c0c4040c0c0400382002c1d10140510302900d0f40b01c2e40081040080c4c0d0000c4000509075401e002520188500c10441105540c0e9044203d904109803441e920200314240440b0002c42c401d03902c2d0b260030078466200022003a07a07003076601e0001020000c00b5001a4030004008044148545c640b03a086202a12514003c1c0e0a000000d48940954121010819800705499240e2442000701e4142203240c40400c110f03603d02c0303042200180076402c01c280c0d030b240702c1c150f030b1990194030000b180c20442ea13081d0f015606000e11921207440c0c2000141c50158001c00c00150091303108003034201400100720303003954006403109101030f00000000050484051500c2c201d410030260340c125007107849104420008101100e000d0300d0940b114551604a03030082d01c04c90040112141546c0d02020540e00c040b011110b0740c428400d2600300714038103404000c0c81500100e04440030414014040d40e00420400c050304c0c030780e0510640000c02003900d40d120581c89505c40050240d403100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 232384100 1250 232382850 232382861
    0x40f12240b0f0f090721050c0405091006081303051b01201309021c1109041a180615030f07080c07030801061409030a0602040f050d1a040212150a 64
    0x42d03501c1c003405003c1000041815000410080c00d02401c07801ca00b600c01410450a90045c045a0302000541004001140a500540034440c000c00d1100045800c0300303e5610264201c528640d108550750361a01d4030b8145200404604406008080c0b200c0340c03d980e0703e500070b08010004400006003142005c264180b66900080c800111040100010820f121000e119001540c00c1c244000d03990b0702c0714031032505480b110b01c8442c5a00602d800310703240c04410080c0081210b140119400c4c49282c404600e0703c500c4100d40c1c0101540000c0005566045611451145030300107001090381c1e20980d0801d60011099208840c0070248144d000708001449402144d103641001c0c04400342814900390723a070302a0030204103000c0c423400d00520020f103418141600b011104868006000d136140501d003480c103100a0b400500584c41c031703003050b075401180a08040c610a10840c1c0c0042d00810303001d1a100c03081000e0b0402410580c2c002d00c0141c0c18009128003080150b010f4400880c20410b01d10b030980312441100c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 232385350 1250 232384100 232384129
    0x103060b03161409040314031303080114060d0504081605070f0e0702060f0411030f0c0f0303070308040605040303060f0b07060c05030921040e0106020a0512040f12240b 74
    0x1c04101c1c240080c80c0b03409044102c3c01002c0c1c44201c441c0e256801d040c0c8003015028415140c1140000c2040b422044d24000306044505c280c440c40a140d0300c070a500c90648105a83c0203401510600504065842d2a048540c02601503000c0b18035085915400121680d03955405882381d61000710101308290340361558500504030a012502c17a0f081c0172500a4803849d01401d480d0004a005020605115034000006440840142202c0025805125464403a244840c031248241d90410301c00c030703940c14040102d451942d816500d00c8081c0c0d8a5503074100c0100b102803c280e04065407580c0200f600220200800d018154101d181e54840b1054581141500e05144204040141c1441400048140025120249040c8a814078014500c141d5010341d0b0b800f0310380c40442075a1403840000368007500401d05a0302c443c0250140c0d40034500c1d0031052541480755110311118103000c21000c00050036440480d2030003611514110000c24550510b20440e8030080341c0803104641d50744e070354600c246400b403921000354 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 232386600 1250 232385350 232385383
    0xf0b0a120c08160b18030d020c040b09011511160e0a2f1e0d1e0207121101090b0103060515030109080f070302100e071d0f04020f06070204050103060b03 67
    0x20b00d4902c034050041d490320320504c5000c080204000e0b242191500d0150544034010f000c41d02000c040103c02903940044142d9140683d2501c8900074440c1403400c00c0c14143c90b00161881d165041c1c20a04030340385207044980c143c850081501c1c8a04024040003050001c022032003a52541d8108111510201c40072103000c103a07015400403190081500502e0032109120500c0c882035154007441e001e80c01c1030300c00250b000c4184080042c40014508095215002c4151522403460350641294034000c100c0c820a10b0280c8089180d8240805440c410380e8015000c20f12100042445c210303a503103441c41c1e08420f070400c40d00c00e510382c4200141d203001c06060702d220000c224028444014940c1b9580445d101e100c9020020301d000040c1070040c58020080e103210000804010800d005103404a1511801940281e495079080a07000d4610402d440c00d01a0050100013544941500c541e402c0014100301c1c00d882e244c00c1441400075102583c1c03640b040e18000d60250001158a8012608041c20944c07007201c1013051 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 232387850 1250 232386600 232386613
    0x10605040303090909020d020919020304080310081203010e130b0712050a02130b070c0e13020f040506031b12031602040f15091a04021903060807050f040f0b0a120c08 73
    0x6da50307020071100040d501526059030b5902c030754200c440c164034890040800c0500000500041091440081d840f0300780c2c015010b0030887d00d8080d000c0d140c220b0b803404510380c0746040c0010b00520300d04d400f413660002c0800307020b05040581c56607280880c450440b20304c0c012079088481445016200c2c09602c0d809803040508500d0214000d8035210312991034021a007074140c0119014003041403030b004543c050308200c0075140303042c6810009150640c405440072070040020642e180e206003401c1c000d95024000c0240030740107c0c041001d010550418a904460740b0000113110000e140b2814002000f070000742da0400340e40a4410700601c8103171986c000d5112101480d02c004290f00d01d800300c00314819a000301c8d0f0085140a10506000740500e0503400c031690062000424020100d035000e074103010940c803500c003484940e030754100041c0c440901e4032403d0b401c40d0580c4201042441d0a03841150312022681c0c1c0051b4000514000c2410170545410183c1d2078008191224144040480b02000030400e08004010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 232389100 1250 232387850 232387853
    0x10b010e0a0b03060307081e01060902030408272119170a0c02060d020417010b01120e030403060507020604050714030d0c0204140a0b101425050303010605040303090909 74
    0xc07001d89501c101000380d200400070a201e65014829100103028000450b1803120151800058101c00d2180e104019071030a04006901a0300e070003600e2107250000c82490819004080c092054000d542003c001064910048500c1d41e580340b040160740c0d20000f4000d5444e00e00307031035020b03e0084416030390100d9410402029001843c40602c000030b104030b1100f05601c4810350304007030340c1010203140c0081d406500030a1000700311032550f000e001221410f40c003d201410080700c1860886052182849c0082c40ca544d0000c004000d07a0802484c80e0f580400701c0c0d01c1c10395a5110320003265016a2001b0058010380d0511090003c20489400078040000f10f6001b042220302c00a42e54920004001c024414400400c00c15940c0303543c862080111101820380140ca05071540303a000307015000c00c2a101d800504800341115101b008024a85130317103003000c58500001d0124080c0010301c0003580000422801a6134030005400380091802412603072199500c490452401426440c4242c1090012500d015240130 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 232390350 1250 232389100 232389109
    0x1080f1905102406020d09120f02010503060613080102180a1d06130e010902150702090402091003020a0905090601050d051c05040f080f0c012d0201090204090803040203010b010e 78
    0x2180e207802c1e041e0020b034400e06103a043c042c0c82d8000981c005000c620050000b032080d00480c81c43d00ca103580750707103062045885031414200680c080c50007501031070082210341c0041d40220010341d04074100901d040d040124030340000052175041d4000000503500801c845006068001800f03003021317021900d01c210070382041540d045000c0d005000c210170148070340110b4030546039074510707907101102c4103000e10079010180301180c041c2180345401c80c041d2510380000100c2c01d1815056404c070341da0040603180355803a16002c11a081700090071000071100520350020050382c440d01d14a004051a072000f04252070404001d50511005a01213400b5220001c201c1d40001c5c400304040904400380704140f09000d0029030111303103900990308411940c0000000201c1c640c500019605444400310007122110f007016001100d00c80055001001171f2440c003c0000040751861900900180c0240f00001e40043d4540000c2c0030303580940302c2a1452403000040c030095003020301618415402c2070819241813000b820118 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 232391600 1250 232390350 232390363
    0x90506010c02031b0d0c0608091002030709180212040b010e15060403020d0501140709030c0b092d06070b01090e011109040e0a17031806060307031101031401080f1905 73
    0x702d02000c2c2d100c0b44d20314070f039102041726108507004500300300220307100c0303001811102050f20502c5480c0300d10008504000d08034002c40c1c0c0700308500c0e0303a902e0000d07261081101c1c1c0c0107003100a114195401b0310500141283c209080740c880d9018007038464081d490050302080840001d411484480d0481381c9144140d29030800301c404599049e41e082040c9040c0d0f0504a00400504e68030407800081c00007804015540224840c1c180e03401a44201040c42da0358035020740710710441c01c0068110f0702203000008241e030074442d503c0c62645200320326441400b40304001419a0b01854040315000c13a903100502c4005900d10030040920200d000070050103a0003c911100390007140020f501c625100c08241e05000d5043c8a14009030b60300045190036120307210b5004907150411100e00f60000710848504882640c0012030b64001c14024019100f42030840d200e65207602140c0656605058445034442c00090719102e899000b000701c640581f5a41808a03116420851040040c221510016003840003045004c6040e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 232392850 1250 232391600 232391623
    0xa0818090109140c0a20010b040c030b030601140a080d210507080c0912070e060103180c05041505032b050702060306060a030e03070305030609130b0f0c0d06030804090506010c0203 79
    0x300c0b505d4002d41101100c0030001a2402d282e0ba03901075078102100141504002d415010403142070001b00e601c01c00442c2150140050f803230b4145c0c80200101f00b0445105c410030b0740c0560180078041090388620507149414490100c2c03e000580c10700c085034880c40c0d2a041c4480840c00d404e01401181031685d4014000000034140010620000851460780d5503051100c0301244405400d0741c88541d950b40c5251051201116038501081c105000304a6010901070040e00c841e0f1320050b8030030b07270509000901008002021508080340c148840129040e40c0810160504482081d03203451071040c0000c42c000e000d01c0701d0340d403c2c0501c9014890000140d9a00090302d078441c000f03071103035620b6090713403030044010700f0942c011144070b80800a441000e0503800b00c0210310a03801039071041e149031507903104c04000030b242e10001703059114401d001c90002c07920021280e400011000f4068184503076440d960f0200c4c0c04a83c4100c44640001904101001460103115444402420100004038080d00800c1e100e000101c1c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 232394100 1250 232392850 232392871
    0xd031109010f1206032009040201020a0b09151501020f0723030a06060b0c1203070c0201050310030c06120b040b010203070f06240302090a110a0e030a081809010914 72
    0x11022010f1003403940f4031100c01207150900a00340d59050280a80d85109521000060504280390981c14500f40031402154182e0080030134100c40d8035408204c100182a06c41d0074044d011410502c10301c890161405076a441046801111040d0700180c0340502070000d4a01d207410440d42007101200c112100c88400210003070720903894031014006401c0c20b6481100500f5103140c2207002c19601460005804c0c440740200c00c80c0c25894a03051250244d000480d10000003800208102d001944034074003442d0050011100c040b840c50322656168040c1c903868001000044030b034140b00188004074040c0d5070b00e0750025642040140ca03110300007510f074811414003904607883c6600250410559030b0102c541d402c1541c01342142e04141c4410280b80003458401030388518901d90100d050401e4900c0750050000142071a2491302c080c80305c054070f040c1016202c20f41d0600480ca030754004613881800a140190040190821080440c010000030b00c20603040040d150703240c203034500100784402c01810340280c12041c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 232395350 1250 232394100 232394117
    0x150601050a02010221061002060105030604030507241b1403010531060e060103050f010e0c120412020106081603060b2b02010f170610051612020d03110901 68
    0xa4050780a446200c108501705c6030620445890410010b01480c01400300b2580c2201a00c00164100d03500e0340280540d69260b005030000c41e0029005000822940d4030440301c005107505408801004052100307407004a007074860401088510000f407601d5542802400d041003a1400c10b00d805d8481d01050003240c1c010424490107180c00784c0000e40020001250b16980d90884594041c402c000d800580704254951814030080341243d8000d000f214403603810b5a4080105d80e00e0201d201c0306070361000e0107192401904008140103068903c180d20b208a0081c1600c0c00384003028080207003187c6403503100d085190407410391400040300e08030501d402c480d0020b0020540548100000d582e410508440142915030400000d0480c2c801c1058048181e000340c0301c80c1042036036000f040d181e501c000e40810b441d01c1081400264245801804410a10890b03d08a42080300b001920200e10104000c1036420106940c403d0318500e504106041107100c86240512464000b40d500e03800320b000d81e0083c0b505006440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 232396600 1250 232395350 232395367
    0x130e070207031205070b010f08062e06030603020901050a0e1321031407020c150706140414011a06030f060d0503130503011b021f06030203060c091215060105 69
    0x3008000042c68000021000410415802510683c8160022aa005040800011048140c0714400c00f1108000c024194554a4400315040300c2e400101005c0e00641071b50b01c02443d800c0c2c6d99120b101900007134a00040e05411801004142c0c0b505920052142032116824003ca6403a018400c4d0015000d00e414104240c1e2440c12103110100101440c400f102100d0f0700d140d42d03a50581224800104507014110251501d042c12030b1140003c40f02140c004d80f003044100d00918044000300b56a6015041c0025a50608500d10146940645040da521910980103000c808003c0c420201059200000801c0404101020440a000080000e501101c0b0035000038401c0e111071010b070031090781c0070040d03965804070400c032200342050500401d40203601e00810200450b20581c80c1d14200101c640081281c00c0c0300300040480780c1624403004101545980c000401a101041f01c0c5000303190780007110b80c8a01a440500c01f01f03030341569000a6550140081e00c10003206090380c82e070080c06c20329040d6503139801d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 232397850 1250 232396600 232396603
    0xa080604170f041203030504060b01090506161a010303030204061707080105060702040b04110318030f0f0c07090c0305151c0210050c160806090a050c0616060e0d090b130e0702 77
    0x115444180d0003028a0350030005c250307056100300e00c2503108000401485039040d00444548050b405029009402045102d00c0c0d580213259810700b881c03242102d06540001642004060780c0c0a0340201c0200b5000300e418007a9035001a09400d107090b02165613503d601c1c1814004100e55410300c1514040c8034006044402c1d520389800c0014110006482408030a4183e001c41826600841d0b41310007400b01c080304287c15090100495800d03400c000b00490404070003070001000d80d8806000600c251188500004d01480a409202c50032107980d18000ba0f43d00e81880604d070390404141c1410b01c00d1450715100105050700f45601d145054041c1c40130044102c43c0d0741c06807814450350300c24180a01c101100c401100c070644001d03809990070f0800f501c800380c072640e40c000e82e25802017500400641019500c0a99810a2006480707083c2e0740c4148803241d021607484071400c50f4a0101030501c5c036004a40038081098000200c04018981102a60314041700c640d090032400215010b00c560902602c008543c0c024030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 232399100 1250 232397850 232397857
    0x60504140607090e060a031403090a0b0f09130f090c0e010909020f0f01020c03060108060109060b07050d032c0709110c0703030e01140309030c0c12030904050a0f020417060705040e0403050a1103030106030b0a080604170f 96
    0xc444000b080041c0c0030b820074079a00d900034f1241d6824040c0310400405d41207980d02030000210b03800f9002106072048201082680d515541d201c034110b00c0b44400720615aa0100310440c020110312014003d21b504200a120984a00e42c014442100003041007000145e400281209044160318000580600185078007d00fe0031558084460359072080c40c0070740c05240441c59100326843c142c001c011107810000c04902c02d00a181e0001800c0d00b044400300302103401a641c00b89402c0051420f40b0850340d03402002e451640003030b0340c82c043c603900104000075a800100681400c0660403200d0764018804030f481c1c26078920071900c040c0d00894581c0089118001d03507821034424000200425507e0f0b90322040f40303041c9100c2051b2025918420400803400f02c070f02420172901564001161800b140c3d40e581ca094400394807030b030105c2c400c0001d24800a610350400f4009140030301600c0d0340c08504082180c0070895410060b4002000a42001e01844001030804101552081c06020782548480303a0780c0d9440303076900 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 232400350 1250 232399100 232399121
    0x70302220602010b010306380408010207031d030c06030c0f0f0f12071706010c0206280f090b04060f0c0c03060504140607090e060a031403090a0b0f0913 67
    0xd40301900810701a07010b41100712455000c5e0380800101e903545107200c076407400400052035090303040150b4107042c5a0380c01d0303800511041c0040061070b055541e00000d089a0080e401070300003906645d00c3e011000250006942000001c070028003a80442c80c0016005202c0501000c00050000030210b04c02e0070002c0c1598804070601c00302030303290040c00703400035113503800b03c40340ea00410b56400010300550300654041010080d43c41c2500c1c19030752020010340e0100e0300d20300180d91003107051101c5180c003200302805250380405c107108800b841140c074402401001a5015035001d1082c440c0050009045403800d440c122007503441c00015120050b20242c503440750349440a80340c1c014080c0d020040c480c0d41d8004c03500a038818492040310381a0468015140c90040c2d441000003086040c08008980c804885150000d00007170581e0002d903540d1751b4210f0305816105084101c5e40020801080c1c52070495101c0300180402a402450320881040c58096480f68a048501c01c00045503400c502c146035a00200021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 232401600 1250 232400350 232400407
    0xf0603020307080d1b030507020d06110706090201030b0f1f111b03070f0303020c0d022b06141003080a120e0c030d051305060702030a02030604140c03010c0503070302 73
    0x458648030b15030740741d41c9801304100c041000345112502c440840031001381d0158041e81c4190910000750b0070010000142c0005440d0315448101011480010000402c941c51144c03100180035841ea100160a44000c951018440c020702100c51100d03031145d000604410309011b001c8010071034141d5055031201d207005c2e151082481004803c00c5065000e00403d40d43c4d072000c0b8200d410207a5101c60504940301c49000050050704103502c1454641030007105140400e07c0102002d2181c15441703c102c0b41651b00c0c0e066520380c40108100b850a01600d031150341403108208614a807140b602180c00a1001124400188008000141c0061840c8180c5041550702c140040a0100510f40d80741c0a54800700010710340d10078011a2080c2c0700d103d00070011240100004528141c10500e40700801c041c42d04090002e80e0540649015400140d4051280301e104501c01c40d58485049903644040746441c0d40494a58007903854100e00e020816046400e0702e03844038003483d02607910341c48420030b81c401810810395030760031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 232402850 1250 232401600 232401613
    0x20601060810030f02040f0207031d090105012c030f1f0509030901110a08030f160f02062a0c0106031505070c120e09040c08121e09010c0b010f14060c100f06030203 72
    0x41590010b19110240000c401d540bca0603403038420010108001e100307090100e4840414441b0015080302a0040511503000742c80c4121070007000300b820b00b050360f0040c000d80d4011000c009854207800305803403103001423a00c0802c010b2a1072403203565244181c40b09070381404800c044118240700b0030401400880e80c03206503191203041024070407940c00c030280d51961410320170740300700c02109104041819500815500504141e00c848003886070304c68014603c0c0e40217000c0194018203408901c002010b00c08030b40000000c8541c510b050050700d0180380d81c001c2c4103580c01c29041c400080c1c0e02811658506401c04403200000a01e2101690724400081c0a181c20000d26020802804240401c110440d11480140c0d40380c0030101c10424118841c075112084a9445900440340c040700074009008030103418100780820340810344888180110076400316002400f0040c081c002061040b1461a4403442940c440d820030100c0c14845456007a041c0003180a903540b9510007800c15883d4012070002e68020341610a03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 232404100 1250 232402850 232402853
    0x1d0c151309020406081509060103151d01210c03170706090b01030209100e18010915020903010606050403030c0f15090503120f07050f03090709020c01090201020601060810030f02040f0207 82
    0x690094403459021170440300025808405010b031029007004020001d5105948100040d0010002c5076940b00506488070300100d0703039061041000c0c1076550034104022041d07150070810080c0d4520703192452200344604148100003440207518006907a40040704aa2541600c0e21455150007520000b82c891030825a002c81800760325065941aa4020360f035902d542d5446926942055410748030b000302001200000a002c80c440c090440c4541071070800110f081d810300e4940303a0000750321010890340b0300c2d40050035680ea0b26092042d0b074010040340c248141000c1c40c545002e421110150303c041d000c0c0d00080c0c480c00400a4204040311620406902040f840009061066036074000e2201e0413100050751010400c00c03282c030303e1007a111b10441d541d602e00c0d2604440c1c42c964560005040840d007882030920100f0300d01150700243c40103e520000005640803640002441d000040e800702d418000b007602400710038280601c00c0300581341c00c00885019624144041002801500402032096102044100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 232405350 1250 232404100 232404119
    0x6030102070819140301120303180f121211090f0d0b010f14030a0503040b0f0412151b0e0d0302120304080705100b130e19050d031d0c1513 61
    0x540d048613a515a40000c3c2c007549046140d100c20b0042c0030010f00b4244000300000e2103a0000c0d401d4087d00c50100b959016642d451a141000c04002111541d255003400848640d10440b00007210340008030078441d5980521100c142d82c46442281030089620010380b101d03580740c050861001d142d001c41c0448040d0381d1079070518a1402a80190072a9101a802120703d07132030f000810482ea5a023000107149440c0c80c08501da182d0f0303400b0104208140701d05200005044211408a58015010301944004130001c0782d110012560791410392090400f2131030240d800141d211000c4404824190f41810b01c01600d0300307042e898440480220301c0c07000400410030080200803c00341c0305042c410345c111190109684480016038001c03076019a0000c25158140a04040d00c2c0c0080000c2d240700410786200c0c2000307482c1103520212440c0140d50991010034058107041c8c1c184500107202100089400c145031810300441e40f070300c1042503030510501f00b207540341c0300742d080c054116240a43d03181800c01d400c554030b15245 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 232406600 1250 232405350 232405387
    0x2150a050603010f09020306010b1e0f0715091109090a0803150a05030601030f0227040506061905010c300c1a01030f0f210201290a0e060301020708 65
    0x5078000c3d420311046141688050103030703000c1d00d6401405803001e603007040890007454202c1540d002034565600c11010406144c64004c01c0d40c480002000e40d602c59041c10142d094105500095071070f94540410b00d404944c4410460705c400c5012106044030703440b00c18070b0902c0c0c10444000a0602100002840401c1e81a030480c0846800151101c00f082079540c0b0405444041c24400030700a500c8011103031005150074000350220b044111b407510030342501c240c0380c0c0d0b00c3c0b010119002c440b130347e000c44c081c0f20051a02c0c0880b41520084100b080e00310b46e0401e00005c00c603050703982c0c0040c031101e10001c4000d1540b0303c01c90703000c140c48100c0043c16103040c200c01009040e48410b820607581d50b0f10010354812011600f004e07190580350846140c0541040e03e5890190180150b04140d4420341c08900201004003542c4007040407001c00c0c2c1c0003046010071807840b80a910482c200c0004081e200d40d80591003600d8080e01a0203c41c0c075844442d0555a412012a0280c450040010041c010008143c000c108219004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 232407850 1250 232406600 232406611
    0x6110a03050405070e0f0c091908010f11180402090a12210e0a0506130801061205100513020d1a01121a0c16031701030803161e0c0302150a05 62
    0x22242c072250313560140003c5c1e050655003640d90503540c40c000b404240f4000f00400342414007030002e11291401c00e02884601c00700350080d04559440d4217a0010445440c02054074820082032a01d03d010385000c00024020f8032240142d004940100d19880c03e5907603060900004c1903041d0b0607282500daa460848110b021042017403036101140d8032110b0510384600e100740310090b4040d201c04802030800d4200516a0040110b060507070500711004540201c0a0042c24014244084140c800014907e02142056a03281020305a680341504001c03c0da00c0e03405109040cae40d011744003081c8000300d078144a82c442071a074080749030000c45d140c000120161000d034902d039450f025542e078480b01460250003801807602555004071036013043c400d00c0e00c140903810395001d41c1d82c400e00f800b0500a440f074006000c00c80d404d90094582283c0801081080031080040b806a080b207132824441c440390f616070003400600e10181043c2040609642d2008040c000c010311200450800e51580d042d00d4222032500203040211003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 232409100 1250 232407850 232407853
    0xa02030a080f0603060f06190f060201140c1602120703030e040f0e0d120608060a0e0105090d12050705120901060f080724022a041811010c06110a03050405 68
    0x59500c611000b082c6020f040c00902920b081d894105000301c1304e803009800c1e154404041542e514100c8a0550b40c0c40c020b20720b0028100c842890064084d00f1902c0000700070604203000800c2180b03551060003150310140c0c0d50341b814040c952446c004140e01d001c103a02404054030581c0004005d15411440048401c0c00c1120144403c02308008141c0984181040310281da0b0b20600080480c9802000e400c102007122400000d5500d81d281246407070107005903a8200c80a540300241c03500c00304203004203031784109810020600300c3e02e070480040c160a60480000b0443d6a07803000716510912502c02c41d0403000c0c2102d00711046003080c0410070300030131030303840340782ea010400750340c0020724410119900c001c6070f0480034040581c0c50080180103401030450030759030850092000c408841890450400e18041c042e0580c0b03201644085e00b48021212111400442c800902001d00c0008400c2e00741406695408c0c41d001252928138607065002d09072045e41c07080c2c110310218902e03034915032660100c1c0c81280101d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 232410350 1250 232409100 232409117
    0x801050a051b07030806010e1011070f060518010306090603210f02030901110c10020f0624060702010201060302040608010212010b0a0504171204090218040b01050a1805060a02030a 79
    0x1940024418207168100040801803000c000400c5c0075000c421780c40700042c104840d0b414240790009134420700d148458004101c1514401c040880100000000f0300140d14101076864244030001d0b2050140b00c103900240841b510002405074803d403c480c00410001d002401407039160b28040c90303203141851480c070350703000415a4060380a110f140d400c0e400c010745401442c82c2514840044400240481a2071214400e0420030503041c0c603841c02d010504091a80917011040001078024107101001e401081b480010b0081640741151080700c0c40030940c8104d5030729075501c18920050340076081c20342c406540245080c40000c1c0116064000b448140c150200d2400f46a032249503001e41806964002c800150041c00203002030000080d070042c0c8098804202d8007c0455112040b0007680f08e6004221040e8001c0758a4101d070394004420101000110380c02c6c02458003003c00200701740140d080807010406584000141d0035400a0340c2d0011b4280038003e103659210416020355a40d0100910703400140024 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 232411600 1250 232410350 232410361
    0x7031119180302060405010c050c181f030b011715040602040810020717030405070b030a02040e07052b020706090c0510090f0302040507110604050606030c060708030a02070311070801050a05 83
    0x70718454040e01d500403c0d4078209400c0100464580a0140741203038244221031100b07460707039604000700d20300b0620680b909085d071610165240d0035024501c80781c0d202c6a11074000b8800144950241410b641c640502881d54901482000c1d1505211070300425120305000284000d10070142c00174000e40b180001203520700703c40340920500300e114a0320003800481e42000840644a0858000d40e00076024a04645803151148420380065000381d0301c00e9045503001804000c4000e9000c500e5907c513000b0f0900c582055054140c100384240c2c2201d0115908400d43e940114810055040d5003c0c2500180c04200d518006e24042d101c4001d0b9000300c5100b0034030f0004852242d4417886d0002d0907254007400c1d00326414a0762b400d020140c00c01804072800c1c841c0300104a0b2002c04c04102c00751107640100000c02c62410800d00340f508016000c007441d401910100411000710340c2c0c00342140e4024844440c010b81c2c2d40c03081d0a08480030010f4810418441c0078080d030004106005400c454020303829243c4c1080540c464 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 232412850 1250 232411600 232411637
    0x206100f080303061201020403081b070609240311040b04030c09020319050907121a0f10032301050106050a0815010905040b01031b020a0302300307031119 68
    0x303101d0035803694020400215a4282400c200c3c00c03010039038002605054890317880c0c0d0066044000701c0301d05414038154034888200100180402026942410000e4500b0900390602c03a0034850013080304070300240c0d603050810b0b01c00e40c4460105c80304281c481d40c0380d50b1290702045855000f403000352a880c0030484086004000c0384201c1340581103040030400158020072800000d480700600001c03490141c680c0c001040300140350010446845150902086039248030344280c2c82d00c010780400c81c1084010700704418610202c043c0416a50080c22034040d50694208090020500603445942d039424107000060040d00710014121441d8076860300500c80e903440d91340c09442180c0c10b12040c00210b00c114104240e00b895407200407162418540811641c0380c00001100c20740c03440000303d005a000700300359014960b0521031541c4201d40a41c00030020707110300c1000c02c004050501282c0304102d0000c045040309001e42c0c804101d9440c2221640e031110410310f495507000803442a40400302d40702205180f150460b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 232414100 1250 232412850 232412879
    0xb0307150c0204060905012d050301020310050414011a090a120506061e030703060506060c0d0f140702030309010f1704050c0a06051207080a09080d020304111504180f0c020610 77
    0x244604200c8804480c0c90000d23400d41e1001c0b480e01e001e10040040030440751401c0c0019442445514064140540b0303100910044400c0c0d4a405480740c0c9403400180000c20002e0280c15000d900100416116140c0a0004190140550140c212000c03080c4c2c03c0f40802102081d8030380709242c00c94212610112007030010348160840c1c5031240e4540c004000900001391254032142d040034003c3c08035030a001c640141c00389400d00340e0040d100444d030100c1c054038002d6441040a2103404110b0b0600d42030006541c007081c1e0303e004808000381884070700455084500d100d20095000903c03800108030003418141403454840340d88920403400792107880000b0a80318018412205c109100c50300c2004a90703200d4004a40300c0782c0c05010110700350f84480b0207402080c04000a080400c402d0728006a0301e09051905c5010805c4000da40e9004001e80481d24201450350b60030b640c122900540319960034207103c0c1100300205010304031008070f5490207001e503603100c0c0d00080d1944500701c6c20040400d8a07840f4150070241d8030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 232415350 1250 232414100 232414109
    0x20d0b2101060e01031203020a0c020303070b090c040b012c0d0c030302070515030403030e0c1008010509090a080301030f1703070503040b07090f141f0c0309270b0307150c020406090501 81
    0x1075400d81b0400da210358003c01d5603000a19002e0010070141e0300280c11540003502c280e440c07100d107005000030b010081c8180d84454400300c808006501032440041e02468440221200300403030064034030380350440403401e141c1e0131800070303d4000a0704c201e25006441160501003a0018400c000c03012601c8d04048403100c2ca0340759003c1c0c205082d40d8078ac5c0e07011006044850303603090060040c1c905142c15619070301d60743c0b120f82d0540d48a465a170b40c1040c0034481e00c05d40c000d04d102856030002280310b01040d14102128156600420100501031071400c10406c0298070000d221440c060000411186561000123107000e50300c11040c03a0440d44800c01c1c115052070160050078003602e2180f804015800007245800e411280107041044122082c100750400c12411540440224502602a03030030180c1c003030038480c05044150000407100c10b07000140c0450809607540424540c1c0d481822200656040144000402041d4103a040d12440344000422030a01640101c7c081c41c02c100f4080b840281c0c500896044c0c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 232416600 1250 232415350 232415363
    0x210c0702010903020d0c21060e0c0105040e0702030c0d0815040b09060d03110f0706140c0d0c240c11030f0703030c0908060f040309060f12020d0b2101060e0103 70
    0x70ba0075502042003d0403001c500300c03041600b041d4005035108100d4515030b1a062904e00100b012005420302c0d00688440c84201c00c4c880e00b10384048685c607030f00402502c00752608a102184655240641130b49548680c4070307840080c2c807880310350507145940700f4201c42c420155030143d00d15507049101800251042da0200ca94007000c2c80300007486034202000c1108503203000e460301c584004454000f0609145400c40c4121050b008081e060002c7c0e07411030002610403518032040745c6007907403206140b6100c04102803910308200311110308401388081e1180803000f03d0404c5541003503403183c100401c40180002841c00c0041400503100e00040d00c00841035403074200c81181c40905d401e48a80d021402003585008000c1404011000031411281c10000d541c031512119540c3c400710f08003400c000d890145154000c104203c034a800c1408500c0d8000011a20344446203000b6071141503000c4504041d00702c142c0595000030510000580c140d00f100d03503035108400d194008220403030f11440d000141c01e00900000e08034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 232417850 1250 232416600 232416617
    0xf1c02010507020a120309060e010b040b0d0503090405070c1a070306210b1003080c0d030f0c0e09060a08030c010209130203040c060c060207060905030a02010b03061504020706060b210c070201 84
    0x1045610080601700b04031442c0001e0814000d0351204120b9a2211603104540e6540550f0b5459050504c0ba586005400f194940415003240d070355207039203200c0d03518150b01454443c004108014003c416038502c05901071003103181e200e03142040a05a010444001c2c0000b410400002501e11061000d036885e443c4003c0003100e045801d031910011404003030711030400f4925400700040403543c4140940a11001c04001e0410300b124010005c0503151750802d0401028a00203d01c00615000300070f550507040150b4a41c1001e594500009207007010543c0003442c00d000004c1d40001c9241e0640c0206000e5408581c424440b4001d42c3d8a941280400c035002803020780000c2081c8402d9006e07815401843c0c0c42008003601d4003a2a58900c01941c4029904864544c000708419280b1a028003c1c5500c85c14240e004243d40d10340a010721410724a4031078018001e9078005038000a20003140c000c44050a01f116525a0761864000420261101c80c1103002e9400d0061003c40c06103c40c0704101e40c0b1454050351941407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 232419100 1250 232417850 232417853
    0x162603070c050c012124170601061e1b060f140c120105090408040b04090507080f0f070509060c060f04050d02010606020a080c03070c290c0a0803060109080f1c02010507020a 76
    0x20040c0d006e20100c64281c0d959021080092400c019000d410643c803040d1000f0b600c2d0001a1403c181a0030490a000000e05641203008001e86425400403642c0741c0075804224108025204040b0a44040c0010b030802426440c03081194101080d541441c0c403440d403c9590300358141800c0c0c020949a03960300422100104000e10b400c00c0d071142c02c9030048404a10305940c86600001c00e52041d80080c62098803442000841600302d02d11540c004644002e008440c640040a00b000000041c261f0303042c0840440e82c0c4406803500d4041d01d04c8803031004100c80c03260030201924424001c084408607110b114491058210703500c10300a00045502c07a40007062043c000303076034080d1941c104401031b00745880148500404100070794119002403102c52281035040c0409000f0400411100071251a91082001201d44d08400000c14088058002c1d060540307a0300c078880120344e00c080c154802c482038850300495090101d8003084400101c0411180300544580c00035082e42a034004459400142c0c00c010000030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 232420350 1250 232419100 232419167
    0x415080c0f09070e030f0a0605060f1c060c030b1306032306040b06011101051015020c13020304020d080f130510050a03050c041203020c0405070203162603070c050c01 73
    0x4640300c2c1c000b426a0144020485150301c1c10500e40381c203031040790315203050260382e0400b4440bc622280d0700380c0d0007948091881c0c110010038294100d0041a45a8851564041e00d00c03960207003a01e0341000f00310000c00903181400d4006840320b4001038419401d000c050780b040c0b41442e4100c080b42d0948101a144942d15603d806e4402000200894148003e0080c0c01d02d4403442882a45e10954001804540807810310450325110400800c89400f594009000d002543c0d03189100781c2404462402e025949544620105d00111400f00c401011001c01003621004140d0b10f802900002c0c2c1d4107000e60700a2079a64040008030390201c100742010420401c40b182e0894443c0e00400e50043c10740707241900d4240d036840078032000c081c503540c00d40042e0081c2600380304a00d0680201d580040c8248002e5080500e1982c1c502c0910741c007004014003000c1c80c03c00c180515803103200b40e05001c000c5190320584904e4800c2010748103044400040762680900d05041000e0743c042c40e01c1d070043c0240c04c00e1041c14400b080d00e014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 232421600 1250 232420350 232420367
    0x51009080703080f280e1e0904020a03020a0803031b1201030201050d090506090c0316050603070c0f230c0d03020319030617010e101a09150415080c0f0907 68
    0x1040c0214100117048084400700c060100c0940341000010000c42001030040c43c1050003100700e03100f50324030340700240a42c3c1c03078001045c0c1d091021502c051071030311980b001880210072944002d40068801000107100700c00880614441d07415510419080c40c0c4103048a06184030300055540104050301c014005540b05101a244588481d800024001100e465461401030216516000d9a00211906030141818081112030113035485a060245090a00050b028000109040100800741e58408144100103110210044d001481c1d44800311103200901d0501c0c04508030103a052145040c52038803820310f44000b00311345405602031400c100707440d003408000c0040500304008054071a107012400990304028210b080381610000541803d05c07025242c100720303044640601c038615240d4020030f120812000400c41c00000c0724081210780d500ca100342d900c018002002c0d5002803418001d0036a000c0c404c03413500c055412003001c45900014180401c099410801c010031340022001011480090045d40d01c0e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 232422850 1250 232421600 232421617
    0x1c030b031c050c01110d1415190e07050a0306050105090a0905150306010b0a030e0a0305090402030c0412030c030315060512060d14010603120801031a0907180605100908070308 77
    0xb40b0b141203490714005081d281c2816540d000402c000402c0084403410784543d00e2105000030300c0c150646001d41c540c03245003c440b8101c0e40141d000c1992036544500d0f84440c28080c0846400c9144c02d0304150303000030410f40011910801203881c180700420729601540903100c2c44040145a026003a082000c2e400c040e24000e00035080e80001c0b5180c3c561180d07001e00c05207004c4c0000480702904c0b9400d0550040541d0000303048842603070446801d00c0c0100ea449411915042001d60340960703a82c40b442e1140c400c1d4402c075808200d0400c0b0036440d8408040c1d22140041c1d103203000e5038050210781c90742d8801c4180c4698074820907000c2641004000c1e03c11800e40381441e400100100440580c407016200d40c600d010003c645030343d25035074030042030080012103074101d420000146480c031120b40c1107589104403180c1c024060b21140940c0302c00141803610410076038015100c10320190303d042003082e074108007400250040612071051500200d604a00c01d014010072590104c005042003469078035440c00070f43c0321150 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 232424100 1250 232422850 232422857
    0x2010204051206066703091a04060c02030102130b04030b070203040b090405090f0f0d020f0a0809090c12010f0303021516030b030c0a03051c030b031c 66
    0x140556a10b41007903a550765400c0504440d2804808002d9403001a095004c02034032500c0d001484810b9014000320000101d401a68031541c1c2d842013203401d03051510740000c5a0303402c249100c40c00d0b24100002c05110780f080d00c500e0390301521204008041140401513401d030110078401004154440d000518480f030015000604c0c0002d103c0320000020307202c1c2c2190340190380020341041004807000b54681c0c02030310740c170240d410141041e8131039080e4440c40d000711388119110700101d8446d400501107800803c0910007101c0803021030158194849409811200260151808101700620b010482803001540301d0000c61400001d8000c01003800b4020708241003078801804101014001402074601a1062071186400c2c2c520f1854000c0c90720104100007102c11016805001d090740281c1e10149001c400d80c2404610f0070388400119207813000405c2d04a43c441540c20000007417040c0482c0d2111080e00e80d0500086155513981c0503008d4442151700700d5003650081042c40d6466018580b9450004464039 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 232425350 1250 232424100 232424107
    0xa0210230c0d12060b070b093904060b03040b040312060303020c090106051303110310090b010e0c0406022a04090308100515070807031106180705040203090c01030c020102 75
    0x8900344455002120112800d41c03205800030a4182c0000016040104842050100a082a4000c02c0600441c18003c1202ca003e5002c501615030511102e04184840009034210380085500070310200b032500118072081c281401c01c1d41650500e40515420ba441d940982c0d40380da220795441811040b00100300350100040c85489491840c2c080c000c01c00154082d60040001c41444070400c401007038103901020612908215036201400c1440390310b41142d8112080c0d8a100c01c90101103401d104954005c900491314010750a010405940d20780c905940b80416161580d41d1a0702248115100e1801082c0240c1c1c0259050704244061400c81800f00d81006080184c460040020070141d50315141e00b1408998410104513807189a806031034018582140c0036950a2207149505000b8810b030300000e0021940026030304245401003041210098100e001c0342c40518103c88415500da10110440001d030041d40b81c0001c040c60140240c9001c0c92600300585048000d0300019002041d00c2c09203642955000d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 232426600 1250 232425350 232425407
    0x3010b0313050601030507080d110606011d031006090c0e0102100b1906020109110307060906050306040207080f0408010b06091f0e22110414100c320a0210 68
    0x6110701c5001710312480091403814103020409003051088444030003009201c0081040e86000000c90755000ba40c203081603c241068100072601490314070110b40d406208145024a40900c540d0102c41150102c1004000500f04507004648504000038500d005a1001042942c910400d42c4200c4510394010a416819102510303404001c0743e0551200025075501c002d0081406162424218142c4084003d8122903080c010701406100150081e001040008000540785482d290b04940303070aa046a0026100d14020032440c60962080c014210345500740300030418035042900544500c10740080100103407500c00000800120401e41408c030411064404100c6641c5524010035140b1003114107501042c0f642840541c1940c0990b600c0c10561a0108004c0252046102c891404804111491310812402c0b1100b151501c4030014081d2207280342443e09071990034078204c194440f06000c07803010000c40140c0000c540321840a0f101079001071031150311210541c8a034819404d80303e80317201d0b00710b0502c0d2803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 232427850 1250 232426600 232426603
    0xa05040b210112050f0a05120a030f180302100209010509040b01030914030a030b010c0209010b13180203070f0c050c0f1201021303020931080d0f0c0305090102090603010b031305 78
    0xe83c000c4801402c580142070511200f8001002500c0303080005044c10a155550580e51380c402180500c80034a002c103402c22a03c0c4260008050344008080a02120b030210311035400405034001c007200544200a14040d116183e40281e44540405840300e608100e0403070240401341c044e288400b810175581d00f842030001045100b60150444840c0029521540040e4014085540b500800c90500080d07406000c0165185403100c0c0c10340b804020002c1c1c480500d0340c041803810185400c2100010040100f1f001440c0c9035501a43c4240340310f80e12106180700d005001d40d000010350002401a41002100781031500f412207d480d99880040c160340703664000c822a050898200221700350100b40369240c20010f600e0504115500100604800c029035407558840601d8440c43d030740160744010319100140c007800013440c1514030b4805902c0c0144203003040e2850071002010020383c51008a8036103c0400c8981505100f03841ca103500c05440d1510356400d0000840054000429111000284e80c3c0c0d10b90004c0c10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 232429100 1250 232427850 232427917
    0x61e0f0e04050f040506070306030506180114010303020a050d09051e0102100608060114090f0f1504051f09020910051c060305030309060f0f190609050112050c060a05040b 75
    0x11041c460f4059414a480c0a505048024080c82c0405041a500344041072021440a4000c0c10701c0360400071550380c03d041c0c54050503050090190101002c00000305160300070882c0a5160b1282c82580c258100308242076a1103551400b47c5170b080807800e24803945070f00c40d0014a0142c407030140102e40b103510030852030801b9075071190891a850741002c001000703030302c6840c9010440e0030750883c0d00200c5403825120f0541c0c0e00c0001001c0c81c8013140c10b200414140c0d0100d0101c00300a0001420912162904034209984081e02036114016005001c0002888031445e20980e005001b00814054442d40c128400315030780e030000c1c844410b0801400107400c40d031003040d215280007503228001650302c920f0503c3d01c1c5810204000c01803406800c0b00300c1003044145107401420b904c8034403090509200e001d030310030310002481107410000c0418548000071400440c03044080a00f03a202c1c00481c0d503040030150910940c0d001d40342d078850104500f44014402c0541c0b0030007404031f120040380365041c120580400100d0f40103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 232430350 1250 232429100 232429111
    0x5090702101a0a050301060e1b16030e030c0d050318040609020a090e071103040e18100b1005041401200d03090b0c0a080601050f0405041d07061e0f0e0405 68
    0x94000444041d06041d20540004e280840c001c01c15549003c00c800b0710b508000740584528400c40e10b04200c0e01280005a614036400c08000d01c00303110813490046e0800c042030039a94400e100e10301c1115034625140322055541c0c1e50110145081401d01c41c034020320007000042c255072081e182d420124030340c0a00c0c03015100c40c070702503500e0381c041e40d1800d030003000f050001030300305070401006009401c8641c0f0004100c40c1242d4600e82d02402650700d410b0056542e51b01d000781414039008100d1a1f00c4030500e203800c222038950b801c485150034004041c4c01a01c0a00c41ca201d4070b48170300b40080800d8415170150f0045910481402c80700c01c2c6d4000b0f001261400c000c2c510b501c0c10041f039550848002130100e510b51517680401e810300c1440c909080008003501c0614020b019504100d80010046441840b00040e14000c00d0003030070030301c44c00c091445804140c40b03d203554100d1a208800d40054040c1c4601610381a0040c08001100a1940710070200e4480d21074401e60420300c14092000c003116141c034441e252180 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 232431600 1250 232430350 232430381
    0xc090a0f060b040602120d0603021f03060617160c050312091002040815100b0706140a0605010c1415090109060e010e07170a080703080907050a030c0509070210 70
    0x191504010308200c0d000394000d80704900c0c00740028800c0540000b00700c20110800999162116a000e8413034000c6d02407500000d4004004e60740220f10301900d158482021b0189450502500c0c0d20340700c00704d8114404003c16204100010302003403203203904003951150f129441c542044040d4594407440d10f076500006020b40e9004040c4c080003040c480038040f60300500b01401040d4902440c10071150f40c0c4801c0e141c0c4144441903104049608412161440340082c40c0d02030307101e034981045051030001044445510b0901e0300c1c0b0030b0300003000c3c801d030b0b882042c0c1541c80584544544c1c01c84c07600c0d1a80214404500f0071164802c0c03031070456031203204100561240c0042400400c6103030081c03034940d05840c01b926200c06030380c2c105441101d801c43c001c1008800c0e14a8a846c18440c5014804030b10b140000041e0040c1c0710040000703050b01810b0384040418800c0c00841e08481c2c569686200384103c0192a12010b8000626820140418501840d089800624600c1219400c1e4185170f0140211014050903001a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 232432850 1250 232431600 232431611
    0x50a2c0f0d110607051303113c0405060a030f0f0c0e010303020c01020d05030a0b01050d020403121d030304060e06090a080f150c18010504090f05010512010c1e020c090a 74
    0x2480c0704000d0f46038094440d1406070704001103003c1d81004079a0b10700000703156046c00105260540c46140d82100e814207481050304200300101c01d00500c004a074450898000c007900240c440908060054601a184c09401d24650302d2a645410100c10a215000c450030622017081d0400704ea0340380c1d01c3c030b400303406d038445d45048552441c6806850802070700c8140307040d50071041c0340c41c01162300f02003941d80c071405448010416100040c0121010320506402107006480840c0110600c4038100071042038425a4a440301024103102d081c1c0030b00707200241c49aa066108220500280f44200884002d14002030a0346007001045c100007410100d0342d821541940c0c2c8a060007601c030920030090f484401e1400c028407075a42c1418a01024144a00c0105248640859428003c6039200380700300c0b001892084010001c403803008800401421007841000d03c5554800283da80c580e40600c503a480c4207507a40c030346020704003403118030b00c1c0c83d803030158004001d5006403002880d55444a40880b441000b0711500000c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 232434100 1250 232432850 232432877
    0x1201150305100611071205030c0d110703030311120403030b0114130e040c0b0a0305012301020c0f19080c03010e06070c06020322030201090501050a2c0f0d 68
    0x468045160242054109824048100341070024803040e00d15a1078110300b40c1d007030030356200d01c0e0181d1765020055071001d0062031000d0040100103004141501c1081c1e03040944034480458807044035180c44036240d0048101080000d000e940301c4d591522100d42c1181c1425000301e29841c031020121026004a1346802100c440d070b42e440307510300390380c2101c0fa030385039007840d0f049081040040d142d4000c0074a035007000c0000c07900780302241d42002d0082614038045596000e115400070003900c828801d064200b070b200640d28101a512110040b02c081c01a03004245507400502002481032a60442d140c0207500f01c8121310700b00b01c001a044010708000c0b801045505245424142111400c805000403a08100203101400da80503c148500a400200140c1c0306d403140410031500c94801156600f55515030003400007010b80640004030340c2402200204950b550b1001e0010030b64543c5400c0b51803070149802100c040c08500800800075407800c50490b41500740c00884940303001070b2981084041541c1886800e07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 232435350 1250 232434100 232434119
    0x905010c121104060e030c04022109010903141809101806030305120a0b1c0b0f0903030c1615020417010902030a021c0b071806260601141201 62
    0x1000c40070050003085040520b40a00700b4901440c010030003007104910711080d4a6804110f46140100001e004541d500004425081d4003010a03c12202507a104c200141c1d10800c1071080096254141d1103410180104c04150303030311580400640c070303080f00261025807a242c44503c0c0311449444010900c6001c0781c10158181d954000701003664484500f08207007400001ea1003010f40d1018980c0319520b1482d5196205c1030310190075520a910b4020320b0003c02e140c200c44074071441d200040d01a840a840503112048025891181210007440c694810004150499001002002c0e07012400311724011043d0b032691414050120b140000c46555000b00c1c05221310040030507551103c5c1e0b1080000c01c41c500042e80400d4a405090724043c0c03052280d49400040820540c5042d040c1d194070443c03101c0c0518060002030039200c44540080b01a04a00c0d2003c109240a4420040340c00440000c2d664500751003416240d9504000344824100644040c00391000c40101d000f410782e95a03543c2d03d00c0184c1d0304010700304 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 232436600 1250 232435350 232435367
    0x601120603080d0f020405150702060403051f0b0102010e150601170a05040516151d0d1b1203080103020613080307030302120708040f0f08041707050907140a030c0905040905010c 78
    0x104e40c1e91040004004560341d5211002c011180c020740940c96038243d00006401e802140e101600b14014425451506030100b080111802e01d41d0b0400c000c50540d09004a00721460500c0c1541d031a40b050080c0541c40e0341d440c41c440e034000c00525200c2e0071082c00b441612001d4030181d86440c401394561062004000051000107103200140b0003440ca410715044591140c1d8140710001014050440010b05450f42c2c0305041c0071040d4000740c014a6000030f6450701601050945601001100c608000425804c40c121034004039035030543d80d10805a400d6800f04201c1ea03006c04030141041282c91400240c0680600243c88122301903200161030b00581c4119403252000281040104203c82003004002401200e103c0c10031608034242c03516040c8030f0700d8a00004d02c503a4010701500380f0b05c0f0400c44810f22000802d80f050b41d5050702c10b40301ca516140e00c08d0b644481c1802c00c1a2408c0401c2c45000340030751095100d688103014620308001c61680c0d4001003030840d9078403081035880e030b511407075568001904803101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 232437850 1250 232436600 232436621
    0xc10091101020609030d0e0118050a020f06030105030a080309010b0a32130c030e100603050f010209090f040501060b0f180a03020102070b070602210919030909050601120603080d 78
    0x90400ba141c001040c0c1c3d142e20406d0703200d081c0a56070300c01c41c2038072140035071045206d0307141d006d22501882c065003001d40c0c2d103404c0f41104910500c0204ca9544036414110141c034126000a002005040c3c400d990360388854100a041c40001d41d130742c460300c203132039501c200c0108024503a25140300d12903001220075a04410044c0000640ca051510540c4215100e030040000c20141020000580821007a0200c0c06000d010359850881e01c0f4401d0f007010a09981c0d405041102d10680458110a9540d84950701745e002e1130413041e501044000c001041600c40f9000c05505c1840b450000900342e0f280da44295241d0071202c1d0ba660550350114995050005a811030700a070241211542c50740c1e85107500007076440b403c5000d0514200c8000ca0000d0811071950161050103e100110680200455148000c0c0600407668110f00384a08500320031080700b00100160301c95059550b4445c56400c02030b21b0b6000d84400340c4402e04004011030061108641d0b4862007000c4d5124041417a980c1b901d00d9404420f88213106030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 232439100 1250 232437850 232437853
    0x109200406080f0604090c0f050a060305010f12050a0b09030a080f06030c041a031b0301180c09020307050702060c07030b010f1d090c1e0a0b03040b040213020c1009110102 75
    0x107000300e9401c0030301a540407140c80600f10055a603600401d02401300385100410700e5103000d0011030100c580e030042d14107451096401503505076950004a0540d0310030300c100000b02840b88400d10900c406c1c00b645814450003181141c3c060a07195849000b05403044034680b0413600007203000301c5080e42c041d60b040c0c1c00600d913003442344c82c605080000907282c0000014003446150b864500f218542400c0c01110440710008003a10207618004900c200c21114007055144603502c3c241f0030f00302640d4070b00c605624440e0008001c0800505115002d4000d40c03014001c2001d110042c041c080060f40d030600200a001d412001410b0031744d01d549450309041c001a0001901050b00260512940150421724400040d40100d400e001340c9a031216282000100350281da000503500480c5040c1200c20030315000e50340c5c400d4a402000b1a13a038669030402c0d01054800400244418000c54094900010090034901a150b0300525004d05120000c1c41c1a00c00c80c40d2280054855801c44c061002031030b6070b003901407800e00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 232440350 1250 232439100 232439107
    0x6060f0e01180504051009081b01020307050304030c020f13140130021207060f0210020304030f050306042414030c010e011808060f1609061d040f05010920 68
    0xa403100e0b07101640d01d00c0030300c2c0d0f80d5000501400020403040e105914080820480a81542810036095126466030103200c510a000710031204014801c43e44a030500d80d80311411600d60350760440340d040c4913030400c0e81d0207208210121034658035038038000442101c4044c002003c0149409170800c409050388580007020b0490790380c99010710100e5984516844014410503d809540300181c055030035031aa0600c0ca01c101b020200345140c11003120b40029506800300c400030080501e20310140c0c0310855004000807080c5c182c814102c4d02540240d47c100340c00800c00710b0500c01c1070016003000c456205445010300004034080103c070391038285240842c1400d8015018817a60540040d01e40420410010b0411a00c0c01101d8030480c87d00c0d5801e4054011001510914240304c0c0040903681000d85413143c0b000c0551152001040c0038502c1c040480d038080d00d0310100034100302c000b00101c51030350f0380194005448a0040c030b84030506114007400f030708030b0010000e00010503014050440d1b0b40d038070410070250000c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 232441600 1250 232440350 232440359
    0x303020606040b03010e0d05030919050307060e01020c0d05090a080c0f0d031202031608061804080a180e15090907091a060d0b01020f030414060c0c030a06060f0e01 72
    0x1003061075220340141d0300410790044450100340105800c0e10309040c01d00030406042c0c12158081d0045001c1c00f90001210510280460800350351960200c2c020059842040528002178090300002000c140300c42c00141000b10050f202800d10407103a403401c000890000700b003600c91400700e240c000074168840c001d14803091801e02058042d4a005503141c40340c0c0c101510b400402d449144401500d140c149029034503824107400d13801292986521030004110001c000034140d0030111458110718400d845600480c1c3c42c0c640750800f882d07100728042010440b400070704030100314007005220003c0c005091056000e103400d48803803c480d00b07135a01040c8031300d05205c24049a1840025060b0589092120014100442c1c40001e01d0304481e1507a40341d080000410111880d074845d60200c801e00743c00b07030203545030390519483d800d44901c01d034001d00300c542480d8081601c50703052a101400d200003110f41111002001c00c000246000301c0041d007282c030642c459005105284503203d0f810000d12020301410440e5050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 232442850 1250 232441600 232441603
    0x8071d0114060c03130e011508061002011b090801051005030307030e0109240f030b011b170415021006030b0c0315060313021806010f140c1507030c09030302 69
    0x61059000004001210381507903650038044440000c00038040740d6032032610001c00100301c0300178400c00301001104400020f20284c1c1c0035501000845c00e070307511902c0f5030340d200c00c0120100301042584219035842d90701d40c20901ca9107031803084d00d105503100e00400d01d240407942829964010007000d84401f90680c100300ca62000020384890507811300703105240004d0715004070381d098010b500c0145481024840700c5528100f0080c515031b5209181d0b10501d1940d04020142c0075200240c96260029000986680448000200c40c18203a44250100c51030490f8180d5144800e801581001c3c17184665441c540e604e16404126615007003003118400c3c03190b40e1460700c41811582004100203800380300040000c200c0c04c40c0c00c00341508000000c0500d9180d00380b42407800f03600011084100d0103041d0341003007410011082c0382003e226200580d40c0c1001034641c2e000445aaa22801c1c2e0300c0784840303060041e0203804400780000405010b03031728040c06162400010080503a8403030701158060017010301c02807001c66030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 232444100 1250 232442850 232442909
    0xa05070303050a110a030518030c1507141005010509010e06091918060b01020d180501050a110703031e0314070e030a020402071b0b040e06010810120302070807 70
    0x4242c00c2054980444050640700032486400c0c1c2d811501409000908264000000d8102072546588141c81c0700c104006150b07564400040c01a40000d60421010b0014441401411641c4c800e603030125030002010441450206001d44c2d17144000e0702d4200622480c02e021080500402c00741c00612054200300001c240b036074501804000101a50107031408070000701c0d0b04103c0501c120380c100010704101a04280008000f00207041d40103009000b002e1113414441d149400c0c6882140441400079840c000040d261940407038101c0c0c090004806045001c0c3e9800d228410055010f91146042c5c1c0810031148000c1030b10b8030b60b03040c0c00e1500d0701034182036a00d003c41d0003550007c040d0a014100301e914500083c03400000c1e40b40254002e000051200411400e68104240380c403102c85042441c980ba162a003010f0f01590140c0c582c0d8441080018015608ca100c020360080c07a042e0040702d5181d15a01000a0030f109400150003580c42010100401e60f02003001c01c008101c503225810010302c0c100e00501d0481c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 232445350 1250 232444100 232444103
    0xa060503150f0d050a060b1207050409060b090a05010e0a0207080304060c050c0109051c090503030f0315040606030c0e010806010c0b04080f03010e0406140c04030b1f060509030606030a050703 84
    0x2070144510741d00e075444054404019000c0181000003001042c40c00584d0303020385a20840d8000e0502e50541c00c94213000700190700340d204000181502d02d040c102030200030f01c000324041e90000c0d02c600321660640c591411311402401400b601064642c100129103882803000391517401d9403441084918007041031182a250025408000070842c2031903148115070902900f40000f0302c2e54070301075092040000c000350001c0000303588105c151011514040c19244091548034154250300100b00c2c008190030034000560b4406240304216404040201c007040848907aa04800082a950144010900d82051402610010910340207415191140008000d0b00301204010705030705422003c2010030882e80e098a5560800b18851a00d0f0340e51004280b02c0a54252800d0344d685144c800013840b914810003ca41c4210242d402c400d241510f960784003c0301c90402800581ca000c40e60200039019210200c10000400041e6143d40e241d1802004140c2881c502510f12482940029000c000003070000c201070003242e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 232446600 1250 232445350 232445371
    0xc02041d0313061d0d0b190204060c020910031101030e0309060c0d0809010515210d020c0406080303010311040507122d0b131a09010f0e060a060503 65
    0x90001014614040a0103603031442500002c02c2d800e8901c50035150610031a11140d9452808034148642c00b0090a00a400d0344d400141858051000c914580c404540144082519000104a52500104070b0300181c200000240175000f504055203806000c107600414100c0b46055030791301d16500d4801c907106441a050603d03848203604c0310a0417082c4240d40b207403c009400e169550480c004c401d81c8855180c105000030903c95000308070002414403401f44101099003d4095200400040280c81403200c40221805801c0501d82550000180304514001519400504003690301c04100003e50351140c20005540c0d00601c01000403901001c0c1c0701d0041c607400d50307000541d5100d1070002c407001c04030540d02007440c5003070581500c2018440c0d032001d500b1140030304041c0b0000512800000a5402c031881581d8170100c03050b100c61600b006507000e180000301c1b103480c03410303000e5001c400700720342c85000d0340004a03445c4003560401041c060040c8042d80050104e07015030f101c4c1c0c28581c3c06445130001801d02500f9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 232447850 1250 232446600 232446611
    0x9091a010c02240409060911030702030d1109030a12080105030307030e0402090402090907020a051b09040b0613060806010510050f0307030b06070f05030d0c0801062c060403050a031b030c0204 84
    0x70b40c03e4010080e5640c80150100c56035594584048802810b0f41c2d02c02d00103007900c0c004024941c0030f20802034a018144540c040c5140c245241c190001400306003210501c0d003070302002006000c4c0c0c0c08012601041e881500052045220024040c01c0c040e0140d20980c06500100800000654040740030b01b203030304007140c0068035200b884012030028003a40c410036400044000a202c8c03842c2e00080c2a0103d6841401203460008907031019101e80d40e142c401460f0040c00100c0400d000410804610307034000d030064040c4880c000401f800006462055001d15241d030460f40050041e8103202202d82044607090414924100c1040e0b4030b0005884020425010580c1d1520101d8142e5503880c00c840b0510381010f0321000d000c400c1c0c109180c499004000d5200c245190140c0411102e00451095049503510f4648084c1e1220009150b00003007044d00e800c3c0c80307203002d2201d144459503904000d480a9406000100001c00044c900070701742490b518031a002007488298440d0000e07600c0503400c140d466054030b02060 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 232449100 1250 232447850 232447879
    0xa08030f0f160512030109060b070b040f0203100513030905090403021908071a0109050a0c08070c030c06140106020d03020306060a0f0c0501050a240e04030309170a09091a010c02 78
    0x54050a141005003e8042c1c1075400c81078909040117107040c1c0d415117000700121036071400302640e14844e8020041c500c440340400500030404100a10341424000b80c103845504043d211a04103c03035048401074230003061940c24a09043d030008208019240941d4000000d051544001c1c0d51503130141e5104000201030303d180c0e010030001f1307030960b84c03d19481440220000003988224a08400900404040c0c500d414009142c40e81c030740c0a010009a400d0b01c8442daa034036801400c0384d160f0845072090301400205031001b00064100c3c4145071080fa40c04842040315410410000c2c100140c4008040801d40107006001190b90717910b044815100f1a4200740d00b205401c09800e503864034081a019002e94680800c1011486881e00103070400e59812981c03901000c603200c503c08088006008000c0621282d4001400190203a40102e10a40c0195416034150a031006091016400040b0b10800a2002c50080102a125005c1c6c0c6104c4241e2001a03075400c3c0a02000030302d22001a50b01a100e07440889900ca07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 232450350 1250 232449100 232449127
    0x1120503040f090c080a090b04060b0103091b0303020c010c03021213031e110402041202060d0b220c08091914100e0c0603040f060f020405060a0804020a08030f0f 71
    0x81c01400d101c500420b0b910b50362140c4000408401d220500030034841d0f0005580d164581c800d500100d5801400c15000b5152510b4200081112204a0381030503665101c00010030b811020100007100c201a118602500794600282065034110f0b440c0e0602c860640340600080d00410440303911328000302d07066100c070000c8032882404802544003405039510406140c4245034590950580240078401e2690046800f81c20311049100d588201e00da00500b5910610051a029000300300150711800c0114022013010700190091400707010506002e10000303504014080240103041c01e030950742c1011400c030f103821401c064444960f02d010f03142032b12007458100e080100f003000d0080c9811400b022a501c2041003511880104400151070485100d04c1343c07602074a203020300c21a8482c645c04007043c44080380560700c450162002e80d8440450a401740404a00b588882c0c026200a42d45c030790381c0c1c01d1242002e006100061095403c51400350304100080003031004004102c80098142c1181142e03118400300300f60 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 232451600 1250 232450350 232450357
    0x4140103151409091204050103022113060608060403170a06091503021207050f010c2d060509010606050a11010e0d050a12020403030e04020f070209010f06030e030304080301120503 79
    0x80440440c010000700b880b0b44520300c289070405003901c0c002069140c501d8400e91380d821144032000014010002441103521a4028181740000301240c4209516042c050440c401022036980d0561819180c91000b480701c60f002e040700030211400a04084d08164500a0005401c030f0043c001039250140841c5075550150702160080c034055000308080c8031902d40c02d801868051109030f01c00c281e054402c910242c0040365000450700024420940307030007400019500130004200541b842e0418a0340c2044959000d02039098000c881880502c2180742450010211003014018092981c0b615602b031064540103000c48001d16203d0801c44100a200d8a049004d0103c00c0d000f02154001c1011245a003600840a0a900f0019803a003046032078518209904a01030707031002134000303025422202c0391070401c2d038000c10300034014941061a2201d56004540411000c0e0b002c4506a2002c4008000003a4144206110510240c01035407860a0680701c4001c03501040c050344001000e0758009404010080049 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 232452850 1250 232451600 232451621
    0x207050312130b04020f0112110417030408061602030706060609050a1202090402040f020c0102190906020a080708072d0501060b04031110110a120914130b0a0f0b070615080304140103 80
    0x50200178444211b02009401a00c00d50a918be030206092203211030110a40d000d40d01c0380c500a010b640c3c0c2e864226040400c0310004201035010402c00100401d000c0c1c0190701c054075460b01d400c0d0003149000c050101040d566880910746042441f180e4006954007000240c100380c04840c0482d117890710768030000082c4540c01c1054115071000031606c00d020001104c1a2115503241ca40800140c0d84aa05a0f15501c418074000c040d02c4041004a00040502018110b514002c0034406901032680315980c080f0400303a083c408410100d540400c080050902802c5c01a0541503c62420a03140d903907400b030350003030200304244103003250f618440a591081001418840bd0101100d45003692070800c02060125a011503001a03105040454050228015011103040c0034011541c5440703042c0f00280200190010a90300011b80280003484442c9618984080c1119004081e0344050130f1418404440490b04d04045a9108200c10001c9500100039201101e420014034400080e001d40100c004081c140b05 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 232454100 1250 232452850 232452887
    0x7030504053c0a2402070204060303020a0b2401051b070f080d020604020d030c060b1005040e011e18020906040b04080d1103180a05040207050312130b04020f01 70
    0x707090300000c5202e41038201080e491452018220b070b00110841c2c40d02c5240b580a00705034118003c141191454078040b014246541800504010b0154005015543c1540c015030040c0d01003074180040c000c448040ca600200c1d1701c10300400c125542800b02c401c1981251019044c0000070901c40304020452852540500307009094649054132080451801c914038010b41c41140708018003601079900005506000d16001000c0c600c8140b000d075404c94100300200c02c11600b4a482d0340e101c1e6060b0310b403200c0410b103441003030300e0f80d6490710704048038840040c0c0c0580c009041200c0d02070b042d45616250102c8102600c1d03880380e900c0600160012004040d00ca10400c05821150002e00042c03511000c502070b10555030384100740e4a60340d039891012110083c42c1003101c5580d800810840c2401c2c006202c030111003060140c1207242d45942c441c002812a003200405a680e50000281686030270352440081c1d51100c1c05400c646940106511031881054005000034096400c0f03da20082e941e01034040b01c90001882c41 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 232455350 1250 232454100 232454143
    0x160605090a0315020a021b0607140a05060a0c0f020118080705070f090609060509060a09051e1006090608070f051b0f0a03030f110f09040b06040806040302061605030703050405 77
    0x81c00f00001394090080c000042c003500c4041030150031030b50070004445000034156410b111302c645440714030042510304001d83e4412001e04500203413080c000b1510580c0114000114020014400341c100c440400c501411a45001c00126050141c40344200b00c80380c1141403181c5a80c0d40746409854408603070460f80b141190000c0019000001780c08c0001540c0c00b5140a102c040c0e540c40034802c12a100f0359070070764407040c484024043c000b100e5001c5640118a0441d251724484500003880707000c0e005035007007003c0c0300940d9000c0c00ba094200103544024503040c40c1c59400c030302c1c00490082c0f035100e0040800042002c001907141519801000900c408064070041d5110701c01801256542c4000d580c4080b0003090401110443c1130340d443c030030305010601c0540400d1401a00707940c1c1a0040d841300300842c0d441031b0744d071401d240036458a40c0540b028102c200010072080c101130801929106000b01074500141399042c1c984d6015601005072504030201e41004515a21145002803c0c81002100d5589404810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 232456600 1250 232455350 232455383
    0x60c090d170a0201060906080a120306120303020903010c02030a02060c031026070503030306060a030905100e0703110405061e0a0504050a0c11030909010e04060204050301110301030204050603160605090a03 90
    0x81d80104400d082c0c540081100a9603540344405032002c130311401c3c0964201175400d6011802c15140b8015441c0700d031800080b15500c5001109844c1c401910a900103580824000140e0070b00744110500644a80001c1d170900c00b901900a56a2900030300744201c0107000700100c0c0c412041540c074140640850003000139842a587c46085402003c0da42c145000d01c19400c0010300c034200071040720300071040541014505280c0000580c0078000c0107008484520800c1d03092003805160348200000501a40b01030035506165003014085c001a0309800d91085103030001784182613450240445500400c241c50151b0104244005509540951700168101c1d041c0030801480130055403040134084200c1d29143e445810700100c3d10703a00d008580369036400150030001406000d004004282d4854420030340940390030307140c030b011a0a542a0030b80164000c0303008001442149401c0c0540d55108005400604070000403a0740e58003451807611921050100004580c0c0c41a110004608091904084904182000c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 232457850 1250 232456600 232456643
    0x1201020d090602091003090305091e03010603031e0216030b0402040f0e061605070b0c131d01150305061509030a082101060c080406031e05041a1305060c090d 69
    0x40201d03110703098852503040c0035800ba20448071604c2c0c08d55911410150500280304c1d42d0a070203281c1a0f100c2d42d02026803222580d090007043c000e14420303a00c0103800315040c014014201019440c80d015508403c01011114294425500403a0341040929003e0b450f00e0000c1002094003192183c1034508010f0407016a4000041ca540600c600e03800408800d845a1002c07516402850350080403800104041200340c04800080c0c08208405034081942e1940c0d0050b02c401c2010084043c5211a4440300421600c454010516040c0c0540e040030305c15132504100240011180702c841c80c41282d400b00d5409400d03242000100d9030241c0c070881c4650341340f28015450b144140020b45180420a600002242940c85062031100c003d512526141c105410058145c02400b541102a65030031691142c51240100078080c460186009003469403800070f500702e003020743c21001422107403884d40742c0d00c03208006000042c03443d501007052410b098651440c01c0015a2064050201034849024441c40d40d050001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 232459100 1250 232457850 232457857
    0xc0309081b07082d0f0601061d0a0510080912070f110d0b0406110f040b1b0102040510080a020c030c0d020609070311060702011206091a040501030b01051201020d090602 74
    0xc40c1c0c812a8256035032054000e83c0c50300701d603815080042015122400c00c1c00c90890024401c90385100342c42c0c1e480c40400c2d081e4503203203007603000740f000039142466202150890074203418641340941d1a040c40500381008074140c900000c150320100b1842200040a541043c0b1076250210192148150307246001d0070190010201c84100341c480746002e150b10003151401d19040802c555000c00c00701c038036642c1c030745a54004210000084800603401c001e035410750750b1444001c1000e0880b2240e41d42d1aa41c0c40c0c4003061404000b559800750700d03841000107000540e50b0708000e0b0600003032880d01548954804c103609029000b00007680701c031440042284110410081008008021141c1c2220001c1e611101c0c103541e0b0364010701c006000b0703820a10040c815410504014a4007a0040c1850201203206403412001c0700d07a654000c10800741c0e03c0a90080d441400c859544681404070b07421303c42d40d410360b02c85448001d01072182c80d10800b000c08001e085803000b9010303079142d001d445c8010400c203045410098060360 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 232460350 1250 232459100 232459147
    0x50114031605011e09030f1211070501022a030a050309030d05030c042c0708061201020c0c01180306050405011401090c020714010302072102150c0d0c030908 69
    0xa080254a2034581c62607500c0100c0b14160750f41103000f080c4012140340134811081d10030410840007804404101500504200507200c0c400306484525002c000501e040c01c160b41a002070b0f08201c108000980e4001554a10351800b04024221100345251030b40a5450340070106415000389419078082c04404006402014000d0301551003e50740c0c442e044072148001c40305041040022300c805e1041540340200d00e00405503070f1000d9000015200102e01030610108c90103000226014100141820720a0080340c0484100c03009508000040f611a0307220b80181040f5030406c0080100c02c948400e0009880b0300075908030404005500b0309040007070280c051041880e503070340440ca000140c00c070002d1146180300116507001d402e08909086d0b500c5103094030b0440c082e040680030f11000c0080740c0760351b21042204188032811800c80c000c0840c06403c0501c41e000312000020700c43d0070401784185010460b840c0100300d207070004007240300d40800d030700901050354040c01c1140c0c0801d0f54072405070a80100b14180c0b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 232461600 1250 232460350 232460353
    0x10603030206090d120507090321021207030c0f02010c170a020c10020a02040b0a05040c09150c020916020106210201020c0a1d0a0b060c15151012060905011403 70
    0x503943c8003d403a0ba20b03103094042c00000313089064039071762141c41580481d402286c980f4122201700d5481e120500031600c00d2026040b08144a034a1141144c0c04121501d511107045034140e003400b1181d20050051000c0714005040c2880c400f014204680c442c1c1840e44a141c0d001400641c404043e4000c0804e9812031005407015115410385480c403458102c110048948550b8014203c049a1fa42840090240d02a056801c44601040802c059489015000b0050742603941e40000c070f850165044070420003042d51030280802000311801580303982000c1d50303020400c10010401e486c00188106d006010795072042d242010103550398003016410f1103003400e40600076030032941140c02d030b07000708006003519225500c011104c4403850b0741d210b1014030f412035025100140005282140130085005039006081404841d0490749811014200820585801c07241c102e0050f8042c1035544041803d00259400f22400d0014441403644039100f07a400030805040e110b8003c0c0034559558030b500765645109102140b19 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 232462850 1250 232461600 232461613
    0x10b130b03010e1c0f050405090a0b0f030d03090b060901051f021903031b03110307030b04020906030a06030311120f090f04060303080a0c110c0f06040b03041505060108060d060e0a0b090106030302 86
    0x10541701c2c02c00d40d81070380c2303000f481e18140d91540320084000f815241901d40c0c00c0360f120000180c803036800348020306900c182600c01240c50001894050101100100818421050400144450703107460041c002e14800d034401100405420100176868841c580c003040d01c1410f40625804105941904110000012080001d5101041650507002d079140c003004400c03890000d000181030540b10b5002007013005005800107152480c03007800b0a00c0d40d1700031203003001d10a803200c004100301035101240d01c80d803c52a41c040c241d19182103800200303074411140340c03221542c5c0124a0b42429034484070040349603200100200300141d500d280143c000d020444007008850715201e01201a28022071403002070a21104c09800b41056400400200c80320325003d5035003101d420b010200eaa45183d400441c016806070000c510306100c1120610709489000388818100b026800601c0712680390349003442441d035440a00410007800e800d00c0d0515202660fa0060009203110040c40305080d4198064400e0b2406a402e960f070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 232464100 1250 232462850 232462877
    0xb070c09020a0c061d0a0605100b0708030103031d032d0c0102250b1c0c03110901110c041d070e010501050a030507021603110f03010b130b03010e1c 65
    0x49001d02ca05030030105a04103600400610958049000007203d01c02e012004c00c3e00815440c60b00301040303c100c403d00e0307561003400181109913a2100003000900ba00e24506441640e9050450006101c010203101c0c0c007020900c00d40c08000c81c1070f0a4000d0240844803c48565084429802e0442d0000c0c01014030142000410b041c010484444244040c1c00810900741c21942d00c1c04230000b410900d5280301c2d0403950220380e001100004007221a034809111203450b09042d0345108507420000d5400c180341c030380148030710030414600a5914401c42400c10f42c0d00f10f5a011021070a10281d9012075600c0351400e50414408402c45c241c1c46020480300046404060b01c0e04412a0700d10700c280181030102d8030600c203103620503110782c1045501c8542c1d0310690780541084610752101c91041d8104440c14141000c40c0310440c2071420414002c0c05084000384654009080490386030f41c0002400740c1516202e50b8801101e8509404c03100300961404101c0f026040e20856058058a07151208000210004007580703 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 232465350 1250 232464100 232464119
    0xd05010b0301210203011401030507170106060e0919181a07080610021603030806011d0616020409020d140d02010b130209041e05160201090f06090515010b070c 70
    0xb81601c680c0c1150000c0242031084055400b00c00d01d404a034590f489000d6461000480701d140d40c02140f02d8001000180d007404010382c40c40e4074070b00814905a00d0f008080243e2035012003091402c9100f035621020a84070070002484105c1d01d40041c43c2c1c1031b42041441003422409003012035050703000d4081050400140c0514a03001c800a442c4000056039640114900d443c1c100310406180140b801107440c1142125841c0c058000744d944180c011641000c00c11030700796008204c0e030ba1080203031901110340d02d50b1003000a116014400c900024605c44100003030840d11954410070013a034004100e60f2200b21640703000c4c441000c90300b4515007a030149075113a407100d9005014001414000400350500c088a00d80c5c030000030b40013070681c01c0d0300c40c0c1c490600c0060b100350300344951040005032101040901e0042c5400b0304402c2c8010340003045a00d04920000444c1403203444800140e84414040b0304941070703040080c50600310340240456140b140000244075074640000300850b6204032041c19405503101c1c0c00300b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 232466600 1250 232465350 232465357
    0x90f050a2102010b0328050d050307030e0610030b0601140c0304150801080c010c020a180903030c0f05160c0b03090703060b010c11130216110418051e010219050d05010b 74
    0x4e941540c0034000b6070848201d02c1503181018813055110020000443d29041e18040440050324081100002444403182d41400f6806100c804180100b072a410300300a0010101028031004e4901e21840700805c20036845080d031004441324071900d9684920813250266200d91040c03050040c0000181d0300c000000c1d014500c2107040ba0790700806040d11030312180040d00c55204003074042380e100740c2040300420300409030301c0211aa11151240043d055809240140841e0103569050051004041090a0719035219040311100782d4000d0811a07003214a1a140c000503155030000060440084100225070700b00090034001c5a000d00e505000385180c0300019503184d1001e0601510300320900d68552081d042c2282000b0310386800c1c602c014542140c2c001c040c0b1031807814100842d400000864001042e1030301e0b000d2200060b101502c448205800c40e500c1c1e907941c00350101080c00c1c58030514400080980c0c00e6058950760202ca01980340c511024440040c142d0340708101a004261400b8004030b981d101c0700003034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 232467850 1250 232466600 232466621
    0x408010e0609011e02130506070b1e010503030702060f07051c0f0e060f07051c0c0b0109050106080f1b0a030c11061b07080706060b040303092106090f050a210201 71
    0x24a465003103400d58100030751301240704050342d0b00c2c0606d40007806440742d0b00182001030040c40004c2c0d440c208018800c00d403412000010220f40c5c030000040c40250340200407903c2050381240ca90f030762402551040d07152400f1307420000e0400d0064428049007100e050341100d40d44000780c4d5680124a580444c02d032034400b190405c2c1904640240180303074608000000030100907000710112800720140c1d00c4410588802d503090380002403200041d030400c20450300b061074054008403d00b8803041d818003034018809030000f808204c04100c1040420f41040f020074408106030203036a0b681e55100a40302004e4003502c3d00e0042e40700064075400140303011400200740c5501413a20b5045a8032500500310305201c49070132505d003e0700c043c08104013103800a40310388501d8000b400a84a2036859500d1400c002d400001654808a1440081c8117480d0030902e003540260701c00c2c0d610220010b83c10141c1c2c108981070058550000b421071196040301c40c1030141350a18808400c0000104413865403480c00104d00341c0c0e1a0184 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 232469100 1250 232467850 232467881
    0x60e180106090509091f0c1808100207210512010806040b0109050907050415050405070203031009090c0518040204110c1e161d010506040b070321020408010e060901 72
    0x10601061410900140d044030388103003111110099017803400600708065003006c1e4129510702e0700003503103038001209412102d006042207001c80d03d000c1d48661110301c4003000100319036000400c1c0e01040441ea5082065101e001c40410514910315406001030b40500400030062110900001d07908000040541c49940e1120080e04642d00c0d00c090000500000351110720103016424011600391558454803400140b050101803103c3e25060038482115005001d580c1103420420402c0740c0d03440080039400440310210400100d81c1110f0030080813058550b046154005907804484405164600c0150301540c000c0703c0410101f00e248403031141e07a100340b1003075524641105000500f094451290052240e2861042d55802e456044029858080c2c542204e00a0252401c1800d000d40b8001c1c82c450140c070003920704034681030402c03001d102580038842000b42041086101000c0c0000501c0742040b150701e40c040259107441e1200c20380b5028009500d03001405110b0480000e14400050003000100c112602 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 232470350 1250 232469100 232469117
    0x12020d030f0905190e090609061303052a010b060c0a1e05030f07060606050403020607060c0e060c0a0203060f070f1b150c0e0114030a02160804060e180106 68
    0x15019a4409189002141405001400001da54036103503407402010740000342c005009410041440076030217010340100c0d190380c82501040ba4070390b400140e0035001074074101080e40003070b03892504940c07611a400c2c140d0b5000050980000b1030b01c040f0402d2001c4405c0304002072012034807040900041d03008204c04d0221a40c030091020020031660044910280247c2d9a50b044840498503520303d19402404d2a00c17040d80c0000e0000d0a0000301d1050300050a41ca14003945064510380014a5a008400c1e0183c480e03990b61114170070f207a0142554107042c460141626440f00140724540e9110741d541d180c04d038024003482e00000d010345a6000414441c0450303844808a0800d01c0d04229000c688103a041400394544480140c082103c0e2614540c0f0b0050411000c221898041002032003603402c1c000990500501c0031109087c10180307070680383d01a410703250058641c0d1450304000002c2d480417801500c10f150004012414560102101340c1c0c40741c06581c0d094851102d0b4a1003001107109100364000900e000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 232471600 1250 232470350 232470353
    0xe090d0c03090626010b091e03100c0201020d0518150c07080c1e070501140c060415200903060117030313020d0212161a04170102040b03090c0a12020d 66
    0x501004446184c29940c0b0001080700701d03211031580c0c50070b030840800c030340380840c0754145403808602d4081810140802800d00b020b0b00008603550303000000480c58842c1d107070030551001d50320035410f07654448600d400030f100e2800d100314408100c900164000c0c02d036014504a56081510b80344400d4040e400d1114120318140103034413041c0054110b50110b0415000d1508035161a03048071110300d102c44d00860281540500d0b20001506040040b56a842c1d0500180980c0e25049d10105249074425000000840030040301031103200100540c030341c101603a50003c03030044030901da400040c0c100110181c0c02c6031600c0e40c030b5881c44160001d18540007100c0d64020400200c1140640c0084004144041c00c81c90782400c059000a4118a45200c3d376041ca92248001c50050703105083c0090003841039150303400020350b0300e182c03600040c4a41e01868000000220b12030031120300941c101c80041a14180f029182e00740b004290352a100c0140c40e0900c500b6603101d0114042c081e25862040490b8000d00900461405 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 232472850 1250 232471600 232471607
    0x90d020d05030f0a08190c0e04050402120a0614010f030f03050a02121c11090a090e030d091b05031222050a06110105090105040b010501051e040e090d0c030906 70
    0x2801c803842d00050150881448241c03010f840000e26540702c0b0f06541c41d10121622021001d0f02d82c00410382d09203003400200c00e030003044020a480064801252039601d90001c1020000c3c030800380e00252003161800424400c0a038441117101411f48100d01480e40d8802a8105503000d600026003010301c40058140040d004d0801000110b026005031840504032003503c2e00300c0d1b0841408040300000c0103c10350071a030120311550b0201d80001c40c1c91070500d10298046407a544940c01180c58130f07643c403807043c0c481190820a032000e044c0c0076542070006203124070b0240c4011820350b041948902085001155514010440000381300c591980127081c0810304107050045180b604003c180f880040c040800c6d240c4452404038040d0802c1d884032130000c00100b5003503003184c0c00181a136404d42d242c50107000028810171185070441e4000d01c0d0030b40d1070b001d204c0d40c106400098103149504440c00000d00140d440c0610700014410190340056801300b220700103050b6500c40c4c2c0d20b103006000032100302081c007004c0e00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 232474100 1250 232472850 232472869
    0x504080901050d1b0509030c03010614190302040515120c030a1101031b020f190f060903140703090e06060c0706081807030f0204110f0403060f141005090705090d02 72
    0x1d0000c1074142281070960b04c030140343d07182000000e900043c00e10303080c00c04110b16041c80c2001c2d0002c0005038640a060000184002d20b2144034400350b00d43c240104003100000805150002c0c8100840c1c01d0120240d15803004040b1303c280201d0741400102101900421481143c8c0000b5001c3c00c21040c17241d44504860081081d9141410380e142c0b0240c110764001c51101c10f001040e9002004421031907012a486e10100200c0b107544546000039031400a02030310403c0b41d100380c0c0450086203051080c0f900351000b140356035181003207480205401090507409042001211104080c01c5030545607801072007c58440c401c0d000502d40d011301810490a440762030754035880f43c0c0300e0581b404601461980c0c60b0038213070240d1040d11200700e03514901c0190300c2c0070702c00c40710241070030017207107181c4191010a44003c0c0918131020705481d5541c40d002485601c0d84e007140211070000141c1c0441440c0c81c1c1e810a000581a0244d640503141540c0001c04c014001c400310b582c510801030003140030140342d41c02c1082d4100d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 232475350 1250 232474100 232474117
    0x5011808030c070f0b040609030206010f14040209041404050d0e0904020306040308041e1515030f0605060d0209010608070f0e01170a0603120c050f120304060510260f01050408090105 80
    0x24404c0c03030382c5012518440d0541d001da4805c1802065035646d6050003443c3c58010f03003009242c0c800f000c00420030307e0307000a0000103e10741907601580b104200c3c00042e00400e4914078032440b880b4400208270400402060401621030592590f02c10041c00c5c1082c409501d070304580080d010303808500402d02190242260683c09403140e01c82c640413104800c450040c0c0c1c20b50500c100da10080845c80320780d5401c958001d204c201d031007589400110340d1858985284144c071010b000b810143d0f80b400415001c1c0c8402250007007264001d4160001569589400ae0048504070b405c00c00007100a82c042460703d2080c041d14545100503542d681480c0030341041d2035140d01d1301403c0c5118503640c410001001548050300111150b20700e444004025201c2e0402500b0140c00c7d1001018507044041601c0c41140c01c00c0640340c00540084000515a4469030b80030081a040d070040341c03464586c481c5604141044050100f00d01c00d030241034880c01c100d5500c115090340d00c10340b002003500c0d4044c0701403409075225201808000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 232476600 1250 232475350 232475363
    0x305011a070f02031b09010b030402031e03040503031303030206070305040804090c020322031a010e0127090b071d0904020121090b250f1412010e0405011808030c07 72
    0x1400b07a640041e00c0c2c10b0807504e0034110030380507010743c0c001032400c205581d00400100352014550b00c3e0690000c1e440d14295510700110510140d100e5100b144100250f0b4043c3c400139007143e644001d50045031101c01c03294030040700140700340400140507a10038050280650f40c440340c49801c10382008050800b0306445481c1c101140b105000414110410342e101c0002c04900d0450f1094083c1142007211041340e1303031280d41800017003500040215503002ca101c1411138400105442c071103011090342d04a0422150340107000349041050003403d0040d90452240102801d071190100c844000182d02103c401d8007100a80c07243e4650006005540200040782c0c0c03201c0508044814a51a04c0c240b02c1200c0c500c401c29603d1040c59410092903001c0684212001c600e20111007804640c030742c2e0300030020f50b108000e174810480c44115603408000e41000f6500d0040510b030070742d295580c540c01844402441140c09841070340c02c020516000c030324524000d001c02c9800c84419403540d5581c0c20300100d5544400700c11601c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 232477850 1250 232476600 232476623
    0x1a04050604140a240906020d02030105040e032d0d140106081b0d02160206040b0a1803021e12070b07060c08012d090c08060f0405060a030b04080c07030305070308070305011a07 77
    0x1c6c195100900448645010068413941085c0034030080300c01010b141440e5520070012103030740707642c15944d10121100320940b001e04c034841d0310304002c2c0d1409030300b544c44041400e0041050b084140801c1d0b440c180e0301036658000950b0350b1444414000304518034004803100c2d042000000d5251032b03400801448800300c6a1a862171210303408a02550302c9540b01c110440300101d000c40c2c03102d0b8080c3c8044c43d08030510042044ca103066030005212005540c402c400d0b00860f85070301c020707191600d01051500c2011607060790003282c9c0d900111034103980000300c03c4402c14074000c180098180075113902c906072003a81400010071703405000321060300d44a001d0341c110030a1446100090030300c100d00a40d240703c1c01c00c0c0d6542c2d00508007142448404100040c4261150707042004004194480d81d0b940c0007100c0c0c01410944058481c0d0230150000e206074400c2d90683e00404c1404421300d60000014495203200755220342c4156a02ca100314200e07542070003a240d40c4603a0382c007500705021500b8040c03d0500c0c0656071a018 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 232479100 1250 232477850 232477853
    0x20f0102190803100f03031e18050f030a02040606030b12010603050c1219121704050607050a0e10080103170301050603040f06020c1f0e060609070c1a04050604140a2409 74
    0x686005c158012400a0b4282c41c00c41c243c45802c2900880c1007009042080000c103a82915074450441402614000d080810343c2c1d000c284d8081001c208810b4024000308a001d031110b030b0040c0584900108a80502410b00c0217000300403051249108072074001002d081441825801c001101c401001201c072280328020880c1d61100610f00314030a2540f0480e031041c0e115040355005010b5100c841012000d041c03002080002003000400c009034007411914001d9a9001011420ba0b001c03401021869007040d03200740c02c40159500640b0300c81c141c80c0a1911030032000180440301c00184024081d507030b045013003880030600065044102c810910720403100503003440038900744203103001840d1800030000503001d190500e03221040d00c5200848641d0390082c2c40035242c01d0002c1070b026400540840100441503440000f407190076826140070445409608101341024101165214015582500c00d004000c0401410f001c00181404039242e10100f0350f0708031640410030580c0d840e4416040c4101c1c603201d0083c43c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 232480350 1250 232479100 232479119
    0xb09092706150109050103020a02300c0106060e030610121a0a1d03070201020304180b06030403020102030901180201020d0c060f020c01020d0b0303040506033c04020f010219080310 79
    0x40c0b155054801d01409140401c000410421080c0d0000381454410404c28080645c04101030040c1026420106030f50b1a2482c41d030480f40c0000380748584c200030003161890310b06106400060071560b4a0b80c41c480d009078050700f019220b14080e120028038000e1110f04100d03101941105d640518000c3e009201f03102100e0f0300e0780403540004c6a0b070034034040c5c0d9411140440002c01c4168500c4d5075454000b582005410760002c1d42d030744194050101486062124549030b0301803074000c181e9103030006e80310760b0302ca003414a0f000e400b0b504140c0d0301200650034800c400765840010501c0d0900c0030b4050f070082040c03030003d09090b21600401603080c0c0d4a0740c2c49298501d0030440500003012185480b000069442d0301c0c001c00d66084540301c600451180c1c0003007000700a01da40310419a6003101030036884480301c0401520440311558000f1000d603030368400c03079401d41c1d1310b510f20a4400e21480c02601d00c0720a6559201c01281c84200c00c01130400107003103400002c00443d620402860b40000d1080310402d20548680041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 232481600 1250 232480350 232480363
    0x7030902040e010506100f0212031b041206060509041a0a06050312041707060503071b020d0b06040f0c120e070b03180f0604020a0e040206220603060b090927 69
    0x2e070103c1c2c0d151801d110799402c0480d00b40f000b00c002458481140c044030b2400035224001c040615159203800310218066844002000c0d40d034a041c010b100f80d507260b41c1d0f0500100c1c0c002980c020780e0b03034a07e00a0005018140804030038461984250b8030041020400c0e07500b004d07403201600c4964510358464021419071401c0004034440c1810262040e2118600700400c40c10002500070681799801256003003191a4006081d00d403c2507a9040c00d0007040b0712601083d080004200011350b2106020300d003481400000c0e41018010241550700b071050025100102c0c096809020000c0006609255010581e56a580c802008080b2000945a080c0d41c0c4091000083c2c0068510003000046008008400c1c1c0c020000e600c4418032200162801c0c0c03409400045202401d07110303080154088070001000c642c4e81c0d030115071011a07090260886591140b0504a021310280580d40101c2d203004c00c04580c00e90850f00380c514801004000422035510100c909a00c055006004c401e0b00460310801c0d00030b0f0b681170042 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 232482850 1250 232481600 232481621
    0x5070801020c0c01020102041202120a0c09020d0e03032701200d180f0303053c060f0619090302090f040c0b0403050d20030406081614120703090204 65
    0x750716284040c078441e0412040711101d9055a204000070042540da0074400d80d240303601119040217824049414038200341c40301000600860308104041005100e030780c0980b1038202d4081c0100921121230001036038901c410380b0206912005c81c40f401c09003c1c05980c1c0407141c1440a000801c0c1c103040c85440d40c41c07021603880c00e825800c5021a0a59200440d8881c00d82c00849041003010042c41640300e10b549050400d0002d803c260326040050403664901c3c2100035011320382c2454603441d041000742d25110000164181c20b8903458480071502030710704145881c2c1c0e81e0800500e0103180042020b00d00004030b181150200c00d0106030781001002d0382c1c0b20600c0900c07a0b0844413080e02e041c9400e280c51043c8181d07540000d066507405003c00d03c0401c80006050004007034500300034a00540d546075110441045074580c80301803000180101d20142c1c04a0389034001d4160350310f01ba10400da840c8064801c40c80f0742e6150544010305008e032004030002950490380083c4a41400110304a80e600454183c8084100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 232484100 1250 232482850 232482853
    0x20309040c020c0f04110304060b03280209010915091a09010303120c0804120804030908031902060604060311090a0b0a0b07140c09062205091509010b090103031b050708 74
    0x740f0000d0f414101c00700c3d54400000c0f54100040168450b00c04c60701c0c00040c1c07014140a94800724995591007c0204101d4100450b15041030404c01a4202c0007600078420300701d02810400000040c841010b019815504031001e403100c00c201d04080e050b0340104070385255002502207444038a00b00d501d5000d000d80c085c500a54604050104e0420110705898124100c142002444d80800c00464000000710510500382d03d440b00b440c0c2c8035030600721548002c0b030b00700d00c4083c0070001c1c0c000c04030280d2012907080c0174072540a8864656407c42080200c5004d4400900700b1a050f0185813014a04550107550200d0801c500056034003299001c50001915600300d41000d1100003040b00620426140d18646011020010100000650041007554401030003290007500240f9100180d2440d0001012450340c05080410181c54485200c0d6500d4005560071182035240340042429480103003e509840240074080034a564a15030742290001203110885002030921104030001070b50a00204008010000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 232485350 1250 232484100 232484113
    0x31c0924110705010203070807050109060c050a2003070209190510030201030f0203040213021b060c07110114030f0c0c0a0515011707030f06150611100e10050601020309040c02 77
    0x100050512a01c01404040d641c0c480c410800042e03a000003101c1403da8403112043c0c940c1402e151140c00b5140c54503001380314500707100c100c03800705034030001074080c003030f15961790500314000500300c04820014412031082c0d03600100b1088016041407203159401c1415110604445120400c5180c1101c4041d900001d42100c0032404100f50760741030240b03142c21580410214510308055000826001001c08460141600450281829a954a14000041081e0058804524100b003e91080d81d0203e40200c51030000d0700b000b91659449040a1341c4a002003602e51442d40c3c40d03a400040e180d54009000c00091702040110004401c0144410b1204900c28402412030880216613560f0112050300130901c0b44108841e502000c4c03c002450b1411640c01c14100e0b20307070f00c1c0c4a081c80c0e006454242190030300201003140004070300d070b404031440400503401d00503220310381c55aa01400030380f1030082030807001341c1c13110508040e4003010307501031500300740305004580c5012101c81c0400d0076154185103a102580055 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 232486600 1250 232485350 232485419
    0x302041a031203042f01110c0a0915090204080607110a0c150f031109041802060f070512160b0601090e0106021e190b0c0904142202031c09 61
    0x180c107101c03061110b171103600ca20460424040015440690a070304020780740c401d412040c1001d000034101c1a101408000d08191910088006004060440e0b58508107402000030b0aa0342442900d040e21803c00c00350010762503079035088034800c50340e040d034406900940d02280c00180121200100602141c154800c40317441d84c29010b800c0304010b8243c0c1e401d140c109403684000202d00c4040f12000c500807100002c40d64210b00795201c9a80e00e400d03000750402000a10745814440210160039890f1140040b58050203051901d001e450041d5440c3c1080b071044017401c040041c2100c810f840e840003041c07402008041d80c406101c1c0c0002d82c282d100c0401742c0c1210740000f800740c98200703c606641100c00300400c0803000c0714103240d0b0001a01e00000d044c42c4900c1d008228000843c000300d0702274980090040c400c0c1249080c0402100e2800d541c15541052000344802034040581620342e1103e03001000f520403885d080039001c090660341c1020404000000c0e2000c01c1c41390a809001c140c40e01801d0417008015102d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 232487850 1250 232486600 232486613
    0x714090418120201090809040c03020d020d1d19060507210204140102240612070602060717102c010e0103020a0f1a0f0f030703200a08010302041a03120304 68
    0x90b003501011641440c00240c0441c07a00b03400c484a0070029140081c8145100c01c2c214028022541c081c2c00700b0f8000181e0f05118513554000b0720000c011103e40010800c01e035100165079816580c55083c010780064460408201160700003a030120084c1003010f03e010402c5180d00c40203c6103000d8000d07581d03000c00e05100c03007074005000c58816482070005044100303284888450b080300c640e007080b02c0d400c40da100007640b03030710741341170b02051181080c080320002500e4010203512032070100c034440c00055031000301012186003801c045002c0e2032004094484075040020500032010181e40460b6104c441801072004880c601d0380c900c0c02071000c0280c8088079411403040094585181c0e000c5941030302486070034096100d140440002480003002c641e682e48a810401a40034043e800c16506920310210800803184e4140d0410882c6005483d15511900e9001d1150085809201d40600018800c64018801410301c0d50020641b10150707213503441c50300c42d80000240741031f002001201ca02d0b04040180702c01c0140c1c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 232489100 1250 232487850 232487873
    0x9041407090b010806190b03070201020c0d03060501270b18030607020a051c2303100524030a0b04060315110304030f05030403110f0703020109050603040305030714090418 75
    0x20040c0090000c2c2c003078000002c0034440040c0900b407080140c0c0811440100e0204111030017413055251068907843c0c40d2602900035040514020050f00a004070030036003034428130500d0240c50050715844041440c06034100405010340400b10040c1803001400f240340c0400c8009010b034201d1203002d5040f03940300d000600d400c0150141c11041554820b42000300000c10109440f081d92424a800050003402c492084903603082c01243c200c100207008400a1110042030003c41c4102500682c8071602130307486040c081d51180c0c006003542480e900d13100940d21401c0040013944c1003402c16001180074146940042c040702c001d40e00860705d12110311001800c0302418054170041c0191500e44034114030381610003030300101c078060304403003080320010015040501405808840c10340500c100e900542e41520556511444d44c001a40403900d071001c0001d1500c0d00780220391040350305030350f218110b41b40d949080c0d07410142d05400c01090b00f014800c1107a02d40701d500c01c095074801e0055000c0c0142c6901e042c00c41d080c50 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 232490350 1250 232489100 232489109
    0x901091e020906120a06111b0a020105030a0e010609060801140703020c1e0307050d02060915010b040501031509140711030a0806010f020106030c0803040815070c02150909041407 78
    0x5100000d100c0566550319446500c990107483d03101105142e0403200d418070720b0f1540c005008611b800f100c0c1142c501004003a1003034078107180e5482030744c03c001d01040d80d490038440c0c030084c0021170800006c2e04861050b000034aa00ba84100003290301919400700906584581e040142c490703548004014094081400085d00300c00c0c0c9003821458018114001d948031004a000b440075914500c58444c4104410011100e5080e00718040e100241118400213480703e00580c5c51400301e10811001400300d01d21881114100c40180b10300c1850030785010010341c041c100040301d181303d241560700001500e4203d4081c2080b805a1101c0c00005e0f4945004042c00c005050250a0203541c002c4c0041c07110f00382c21200310754100800b401c0c0b40d06540031001c0100c1c094400e41d0402062361a500740d00040440740000030b80f064031765010582d54401c0b01000c003141c148000b00c0d06c0c6400250016940300140c01c140c0080300d142d11080c9409403412a030744001c00c06541d0181c42c04c48494910348824007003950140300140140 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 232491600 1250 232490350 232490393
    0x121d0d0912030504150504050402030f0109110c031e04030b0906100f050607030c0602160305040311060c0a151b11010b0306100911070f0813060c02013203090109 71
    0x41c50369850052643c0030703d0044034000c1c1088145441d10601031003c0d0fa0003404000d10566483c42c0000d080003500b0002e214001703030141025a0700032002c403c6015145080c020000450912140501d2034180c0008512200c42800e0104000f1001c202d0302c01407a0300c00c2c0c01c2c000081c02141444c07410b103119200d495001644c043c1040800b030160755035500c2124100e81d007500d480000e82c552410b0030750085c824503284081e21001c00c0780050816821901900490303014503826421001ea840510101d4032a014100321035030808c0b41c450b8001940001da100d11000c246000080d194014a03a28140140800628000c1550b0039040b01d0854001d000348a1008000d5002d000b10b400d10444854021a2500880210356190596040032585480136a08040d40240c0300004450483c184941e655022200c0d20b40303404c008140200310103000302404540c0b5541a5628000011440031010b0104460050b07445c1071400700c0ea280180d11040310155009009040c00021000300340d103010151b00c46c403d201e20001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 232492850 1250 232491600 232491629
    0xf0e06100e040c06120608010c18050f09160203090301020706050121241e14100f03200406030803060307090e03030c0a12020703080402040605040e060403121d0d09 72
    0x5200f4100030720031144181800c4858445c40000240905425001b080d101d604e00a01d091a25a00c009070250b032507080a040e03403200d51203600b801242c029882c180ca41011600b80414003046100701d0360007540c1c28520559041004240c00203082e82e102140c2078441030f07103400041c489001c030384105181c2c00301201c0707010424800c55030350031048140aa1a26108924010010403680050381100303117000c107185618128401000c44000c0180000c40400d440d10b2031311300010714030003491000c4000342c0ba00516a83c80c071030710f10b6079000910000000e072881101c0f010190314a09403194001c4402640c490b00c801910392a040c0c040c50700e00380c80307607001d408014140000e82500c180302000303ea80000c40b0a08495035150b42c004280c94030031583c506003d85910000782c102c04c3c141e101e4001406503108880a0114980d50350401040d0b44412090050740c3d080030010400190107000700d0701a40c15070030004680364048250080130950f135000c0c2090079801200300194441d5100350f180300944040075250b00e4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 232494100 1250 232492850 232492853
    0x703170403121110150e01080115050102031e03070509060a0e030606041802121213090f0c0210052205030c0114011a031f09020a022118040f0e06100e04 67
    0x2070307450042c1e070460707010340c0da88582800c0d001c4e005290a02421b46125030000755650703007200900a00c03010800340c0518000410101b401e43c400b2003111100c0320280741c0c3c0c01c000c103880111503025500240001c42444010854030416880d040050310580b5407940390409007000c03040a060501c103000300301c5072080c1d1800c4410361004072400c580d440c1050701503074940a1b04180012540c6008982120130038892400704054039084000440b842c10b94505900a0006003020031072101070311001030105016810401e8001c80a0130a40c0c0250f41c4034401c9100c840400748400406403203a0000c80c0d00781c405d9000000c0510210600b4015912010a10b800190042d0300d000c041c113055208010a4038504031001001c601d01c07002c02c03840040080c64000741072a0391952a03800200a41c4441002400740c014001d03041c00000011681001020184444c9464101c80e0400400c00c55030030241d10307074025521440c00403207501d01e00c282103040c9190f100600c072906101d90781600b51030950b8024065805500d08020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 232495350 1250 232494100 232494103
    0x100b031504050109050f1605101d03070504060602030a08060a030b040314220302120708030301090c0512151207051302030403030912030519090c0308070507031704031211 75
    0x154003140d40e0800286989562030594098084004040d0092158005140004070b001c0780e15448545e08161150741c0d15929070500030f40c00d4403d120769001c00c4e011507810031207440003158403d08140c010281c1c0e00319a140c0c0001422107165800100040c2c2c00850b8020b20207410000b0726801c00c004854140c105483c0d941d98812800008000a0400040340c0c3c00f9001d42c1c20a400f50742440580358111042100d8003c0c1c0c2d0700c40c01d00c043c80203030300c00c1440303000c8910448004a480400c8d00c0750071014500d50f81c00c01c180c210103044007040d000e0030032000f0014404034050724540c190144040261841c5042064810419032500104c16004660003807041001184d440c080b00480a290840c0d001da101c4e51203040c01d50080c0910800506600c0d00d072800040d402c0d501d903000510441c044000794070518a902c0c0c0210446500365001484804084d9003880801d50200203031280511501c11900d000307440e0380d9500c4801c1084400d81050302d41c08603050040180c0c1c0043c1800009080c50040b084820520455 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 232496600 1250 232495350 232495363
    0x30c060e12120f190e09061e0603100801020d0902210a030c02060c01051807080a022d0307080307030201051b0306040903031b020609010c020f07091a0a03080705100b03 74
    0xc060044009074010f00c0c0303940041542e0340f8041014541192100b400030182180c458040b20600c40c1c102c110004142c1e117803118101c03039100d240801742d44d018200c142c00e22140e6032000e040300c0348440d070f2040001480c203024001400074011810010802580c2403050166400400c2400451500310b00c2220120610014140e54070316054039080d44140d43d64000701e0480d100d83e4400c0c541950034101044004505400c2055034814140210f8003041c0d40c0c4c020f0346842d001c40410081d0304c8108103500e201d461006c28550100342c0d4a0030b640d0300307002e09200c00082c80c0c850b00740e1022176107030404580e14007410b070213216095100301042c06103c2100e480600c1c241b00c1e844001c1106203da41e440d030a000501d8801e900c503030f43e1840c01c000c03000f54003540d81102070740d144011030394480550300340200461010310110740790303e00c810058010040c1d2801d20080318046d0402d0048c00080c0411007020003115038540c1c04410083d4011400e080d0341d5812403c145007401c80200d2169040c500f04102685103490002e40b2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 232497850 1250 232496600 232496623
    0x60a020703140a05040b031f051e010e0f041401090c021b2103030a02040e010503070b1c200403120315060509010c02091008061f0e04020d0c030c060e12 67
    0x80c1d40c44043c00425900c9016075003100c3c402c0f0101004015074048002e05906055150110038001e40359181d040140f18106500c40407108075000241842d00d5009032122040c02200500c1c442103075402d80007207000c80740702e500d907000203030000d4004012030b600c4c901c942d062411461019260b503031042140041c070040d4800300c0c0e5000d8407443c081e00360700340c82009140c00041504400d03a5601d0500c2010310340a90024001c1d0315a1a200e54000150b5103000501a01216420703a1241c0c1000070903241460512400c189140c24503403580424888000340303010790300310b4a02040c4070075115800c50400e641e82c44020395806007411300d00103420042c0302d80707022800b08880003442c0c141d543e0010200129014800840002d40082d41e0100784201d08040101102c1550982000c444613036850011a060005003421341d400704110140080c00101c403481180c950080c005440c038034200700213a81c0c7c820110031980c01518500c5403101c040c000150b2207441041e254900700c0742d0403d062109440103440d80c084018 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 232499100 1250 232497850 232497887
    0x14030306150f0c010e030307020d02071503020c030c01020327160513020f040f0e0f010b040e0c190206150105131509081e010605011b200d03030905060a020703 70
    0x1c1c0368509640b00002c07103000703c1d41c44000307102c0389080c492516030300d81094405070054000c1e940075405a80c40001c04900f100c417600088440300b203030345005038002c0d40002151121400b042080440d01c0409000443c0034580e0742240250b403251081800480081c040881405500075052a281e07284101c00e0200075114102c400002c07500d88400440001e118101c041d0780c0d000b2021a000070068000f108600465080d450681030360b64995005010350302090060491810041c0814407440c40340e002c02c00c1d40322015a000629005800080702101c001e014104001644121308114076000c00407141c4401310001e09080d0b040400d5031044041c92009801230010400d0f00c5010140072a11509910000b424001c00380c134540d0402068407142c00d90700b440340501035828414005025446140948100c100d084698407042a00d40d035010b46030192201103600b501078040700c6c104940c2d03407000034011607842a203002a01e002c031840c1040c2040350007003625101e05e205000440c04a0742090782494040400704 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 232500350 1250 232499100 232499107
    0xd0f03080603070911070212121818010306021803060c0f0d060509070203030a050619060e0d1b050909030c0c0d050a15050f090c130207020a0914041403030615 70
    0x1c021a00d45105036200c01c0c0107505064400644440440082c20301038001c1e00d0b0f03000314851304035105549058680e014010300408002e84110318103070350090840e2800080c400c505049250a042d14040b0081c2c0040e6100c0d540003c2c0c102c460103820305035254038035042e405040c040c40d103030311000303124003850840b84421000040e41e001c013106542e11610181100401040c403904015000079503a40048074146002483e020100f00c591034503c0040c1c3c04c0030240800190340301d00f003040490300c0780100100340790030256041d900400544c0400ca0416441128200119150b140c5010001400009840e0004582040010900e603141c04a0661440b09040e110392014203210b141407450103a11940142c2001141c44d26000c03018141d4114501440c07085203e503101d500c0d12064503407184501d00020b580030000d404d500d440c03441a9005031004600041084104a5560626806442c0b070039a1f40329596410104000c10408980b14881580c402d54004506618201e40841e0701d018240742d00701c00608021 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 232501600 1250 232500350 232500361
    0x40f080c0a0612020c0106031428020f040e0f1c1403060d2306040318270c0c1a0405011808040302131d0a030210090b0a0507020c0307060f0305060d0f0308 68
    0x75003204008543c00a249c00c62906922281911030200607a44d13801195940ca0380050604088550044242c0040507903510700c402d20200001400c0d0748241107035038001e2000420011a0611242440c1c1d070340700c00ca85260400d40c100c0148807403d11044481000024000e00070f240d03c829400d16030f03890344160f0b04a10110701e400380b296814000041001d9520800040004061703005c41c031200320409229070b20909a03218550100304050002d00800046c040f000700180c060070031b4129004081990070100e280c1c02c1540c4501d480c00c56503520a4005e803c2103414481000409d21446038503243c402010780d0101d40d10b40c0c0d0241580702c1c51002034440d01d00d083e000030740c080750b6600107000d030f1100c04121400e00b0300001c50740e515001c40200c2a07001d80960540c10821824900442003c154040212200b9642e9480b19000600015003484114031840100001a8908000c80f2018080d280c0b01d600e4071003005a002001d40b0001802c0314041d0200070300c1d02e0700041000c4000145180e06051052465454 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 232502850 1250 232501600 232501603
    0x6090605090f19030309050414060108061e0d051f0506010512040602040b12160201020f071704030503040609090612020d06090312020a050c19050a081c02040f080c0a0612020c 77
    0x4140100d0f4049180580001c10940c00c0b01003542204d4061b00c0034032101c89402c00d5501d440c40100c035070324081404280003502c2890b001c00803a8000304c0c22048140e5000c8400c0c00b05078074480e8000200c0b120b13032000c0806a86820180142000c40c81c01040511071440e1250001b8514000e043d01d8130340151101c1c7c0441c0c100b04a030f40546000d8164008195190b584902004170144416101c4a007603240503031544074618818000c0f11102419440c1031803404d10329640328035143d900b08015840300c60040c00040000b80c030500081008145c290b880b03040300c50410170705c0d030110b950560001725030b80d00e200c909400580310411520350151f0011400a0f0103000c60800307540c105880400d41620a1000404d02c800c1d80d01f1a0140c640c012109003141c6181c00314218520200180d0500034000f540a912400001281c071002040d80314001203c6207a0303a6620f400b20002d03a000b60304155034404080744280110107040000008140b022208014003502d010406031190303003c0240310251a0b0000b40902c1d00381c90 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 232504100 1250 232502850 232502869
    0x70b1809070c0209060d0b01050d0c1815080a210c0f060519060305100b15070f151406120c0d080d0e07060e1009091803020706090605090f 61
    0x40c001080900c0c0c14a4010500208203400728400e10944000c1126404c0c04003070200125032020b84040242d00302030030440014440801162110041e00c000b00342401c450a2441030b10b20214004908492110f02e540d40020041c1c10183d15644002021400300f03c0e1642d1010340c040035021035920300050800304407541181100c020340080d0001210f08108280c5038000c1c0d2140c5468030740b501400382c803010031100383c40552001401c141d110f1900f6640ca60099880103000d0300009101c03540100b891800d85015401007102070340c801c02101120380600c4070040f07c0e2440c801d0749000802c100f0400c00c45095600d40d0280c5490300980100100680e08402045101c061160003890b07338000c51540d24096240d6800690592001410700141d21840c01d400104141500c02c44d4482400d24600745007400086030443e18164104184404001032192181c82900c80034188007a800b51003117142c0c04d0181c585000e070380c062410041114010840350354000f040d40c01c0b07131204840f00100701200742e0020300ca505 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 232505350 1250 232504100 232504147
    0x30c0702190b13080601150212160213050601020c0105032e0801111305040209030a030503041b141806010212070203030d021201090605030102070b0103140703080a0e0a1502070b 78
    0x2d000510000c030f1075078040d551011a0800030440d0356982e01d420280c19642e00360a00b02015904c0740f1440d080380620712000e06000c01081c4019500c6c0d402503000681501084403244c80955a1001403001c0b0f56410700500c28100000e00b4038914600f480d0380c1c160740e40341444038a048402c0c02503080e140e2030035951080c1402441d0060091082002c2c4c2d490380f000300e0303104140020740d140c9209030004890800e4000e40d1010080100070340542c1c51141c4068a141e0f0005000301d851100100100005980a2070f8000240c06070030b4124140090b400c05026003030310036104001e82d060b088004c020090313900141164811920805a0f501c940052000c41e00c0c0d809424000c001039400456004c03440c0100d1182641286d040203414000c0e90366070010306080384200b10703000d00030145a0300140082084200300520010301c0380110307903515a681e1a008100c0c2c01288440300003402c1145070703503481d00c0d2885018015040201048031410308000002e50b558185220f1080f054202007800c825107a03144510341c0880 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 232506600 1250 232505350 232505369
    0x30f02010c301d03130e060114280c12090e060d060b122b050f071104062c10050f0d12091a031006030e07090f060305060606030c070219 60
    0x2641d600071025100c1e00700e1741c0010f009064142000400e031030560100c0e4002d0300183c6640c03d0050300380c25200c42551000e008035880c1c0b40364030305800d07190201802409541c04140e03911840b0289a2402c071041445140b01c8408020424400f0b12a0314a03ea2000b504404125100c03020851585880c1e805811005505070b070164040c1616025a1030224507100341a50541d002c602c0d00c040046a480410403100952001074814050a5843e00008005001080c040c030324401080c54924000b60903520f094220022055600100500c4a0b4912480210340d0003005c0320050a46000d0134254003091940c89154400d546441030306180391581c0c00c41001c500d42050240b41010f007034190245c0041007610039200c0164444d0540540100300e00e0949000303100d84000c0c2810949050422005800240c840c1c400c14014034000044500e624807800c42c4800b001d14000c501145141000b0782015401461640038010801c00c2140a40c030b0003040b1004158104c940c2403000c2e0700882c04009401240e0030031a2813 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 232507850 1250 232506600 232506641
    0x90a06030b0411040e010906060507050d080c070212010618060b030f0a15120b0604020a0f0e04021b01050907120308040303050a110f0c1c1b1a04030f02010c30 70
    0xe005d00081da10381a2130203610203201c4260b031010100d885104440d005001504215159601c0600c100030300d5400480c0b50205900b8075015800252180c20140d8140c031903030303541e0042040700c11507640000c0012500c41008001c200d00e45600c08800d07101c0205241c00c2107a08a000400c8102561310040e0300040340120700076a1510780c2c040c4001c01e0503880095525990081c0040d04520703045c02114400d0445564112031194000801c0d1040003200320a01c0d4441c0d0203208042c00481800754a1601010071000419281803e40c1400c1c00d0080d16009803541d4801080c3c0e00b40441e80200c01e40c1e8015034145000903090f80c5090700c0301c008141590002c04400000108100825032440c09007030b0700c01e000f40a441841c10460716213061216040340c0b1201180082e0882101c9003080c03d4800c15143c002c500d02c424850604962403c110300848044000c80c1c1d02204040001c3d030709105400c40750707a41d07040084450150030940880c81d44090070140a0502c0105000c00e07001c030030b402c071114443e100240000e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 232509100 1250 232507850 232507859
    0x18030f010c021b1e04020307140c010603150608061b121009050a0e100e03040801110a120e07170c03060103060501090c0504260f12071502090a06030b041104 69
    0x440e19076000351181c00141d6152039a8040c0b0b0001c00c50204241d0401a2807010b40c84c0c401400040d40008120205000c4810305960b0034000c040c004008490401000203200781c1075182400c07103100c401a00c050743c1c918044042c00301d0140096255002070003d034013200840c62414082d1074078490300031b502a04110307c10901420140c024010000c3d12014142405990b9620702c0010032a0820141028240d200d82a14070498a860b440b108094455800b66454280c80c0c8808509489040d1070b1640143c000080001a945c1e202c183c440d507400010f481070100f00c0c104100166901c0e4580108110944851108101701d02c1c1044083d130030240203001d40c1e030b240d0394038101440100000d01c6800c50040c100111076034a00c0c803481c11a4144d8034084401c5500c410050031054024134104a011403610403807502c001c11346c00401c48484500312803601280c2e10151413910b040140400140010540e005101d41c038465030392661a04141c1c4c1c500d10380010a9600000090050402407140004100300020f0106 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 232510350 1250 232509100 232509103
    0x70303090501140c1c1403090a02030618060c03060109031202010501060201150326090a0308030402040c030501120b28090b060109060518040209040e0a03030b0306070518030f010c02 80
    0x201c5200341c0310864a901d20f15114070180c8910142c80c009034202d44040310035820713001e110300001c50742c500c2d04610304240e5204001d8181d005607980000340d400400c600c421807800b0800c055010400e0904e940000c0c5640403015a540c10244c080004c10318044000790103039101e6500c40c401503802c1142e0308002906074001034001c200130f02400b40154280460081d0b07001e00803410100b01c90348500038107000a4084101200d11038000401401c01000700900c6003260b8440c0526000366028800c4607a5030b08061041108640d4543e811005260608004100038003e004242002d65040894080f80d565061000000b52a211840d82000103108241c1e0b801103005501c403840052181d0354903102c0e501c030302c001540c41c0c204600c1042c00290080010b070500d4409003015034001d0f05c0260002d818101010000f505492000600710147c1d80841c41e15003d1580c140a1000485c60681c042c0c2840c2c1001c52000306144102d84404844181c00c00008400d0788080000c2c80d0b0200025000b00318654481c41c2c0207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 232511600 1250 232510350 232510367
    0x15050c090d030c02010909020a05041a04030807081b0d05030a0b030a050f030a03140609070c0f0b0a050402130b03061f0806040606030b150303121e09061009020903060109150305070303 81
    0x3a030014406c2c80001c240a24a0320840741d12619640740c00e03040c649040a5548492207194052400c40018013000000802c40005004002c1c843c1b2207181c0c0b40d07940014280e8501c0110300900c14182c0c1701030304151446800034200c0b90018148440851962420302c0401e16006100100824501c210070003c011080301001034041103030241d505002e400d040f0440c0c01e0006400b43c0f03810f41e000c071008001c59901030146244c041c2c20b91203800c0c01d000204181e1901c1d004031808841c000081503c4404203c00c47c64060307174121000e40c08071010410500e0f40c502081c0e032410018201c84460703211109e03161000228030b08410040c070040f4200d03a8185402d1801d14080c1c142403100b10b5281c60710340d02180720004410801d44130714101034001c60801c0316608524001f500b0241c408909040c500c92980d104000c0030b403002c1d114102d03100051804d801c0841c894016a40030f075101507143c9106020008255030045040d0b03046034500d41c0e0102d8114000c2d10140a69125a44028001d200e1804d0020030980c128006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 232512850 1250 232511600 232511603
    0x71113060602100b0f2e02070501090806091f09020d05030901081e160e060a1d03030a0c080c0c030607030b0102120f0a03110f040314061315050c090d030c 68
    0x941d5540040b0031045015642001c200700d80c000040c00e01030701c0710300b032440403503805a1149007100c1b1904c200d807080500024201c106207005070007040081c815540c20210034401400100d0041603c0d1500e0030000c1d45400144500442c004403044582c030340c0004a0300f00303602a41d00200400b40350107c1e0320700b456803540004800c50109200500054a80082030803440d490040503072280392550b00d1020400c080b5129a003007000380304940b1703645000d9455001c050300748001c03192592141d030250042e00041807452a101c1c1c610a50041102075404c80d07015a815008660020145484021101c085030403c0d004400043e0588107007420440b807a0340c981c0025a01140030780070780d0710b66107681210b00d03403a02c545049181700840400ca07907003400340300340e203e13030a1007910080c003900b043e01c640300540040d845540b0940e100384d403840a001c400042440aa9040b90700c0020402c081480c6d540ea181040c8004601300600e940da52000500c2400d400c0119101c0140c0200340d80020780e89458090112001c0540 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 232514100 1250 232512850 232512853
    0x1107060801230607030e060d111b01060812160b070513080a1a06040902061303050f010b0a050907020a06020301030f140c0f0409080403080309030319060e0606071113060602 76
    0x2800c180016002e0038045121602030182c5207801070986050b2102c8002c40d00f0b40341c2141e010080c03106a0b2500d80700741d00880400ca1600c41d9030300215102c02001d4032424004200c130f171345062001c01c420040003030101b00d9184d5450207592240d03013b030001c410900c19035102800f06640e441c1000045988800149a10b1088048250502e900c94451a40c0d61008140c0144116150b0040e24000d29040b2005681700c14020300220b101d210075408600b190700030601e000080e052485060003004801d000c1c0f8890040608020031821050780005007404010340708a40c055044603010850300c6200740044035619070001c506650301e5039645000302c400070140e10265000a507620220420315000705e40301c14000c100521902d00707800342c0d00400c4020018501e0845101d02c1c20000040000c41e048044c510425840d0090354403860280080040e039a00d424104502e01d00c0e09005001080d085140c094125000307540341038a40d84140f4100e001c81610390101984002c24003007403c0c0740d4059422500c2500e02c3d960 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 232515350 1250 232514100 232514129
    0xd020c03040317040305070b180a08060a06051c06090512041509080d0909050915100302011106010806010e06041e0c0e0607050309060d021908060f01110607030c1107060801 76
    0x140b03c0040d900650000503e190000701c401c110809194028020348200824404004007008000402007011030380b042a00f0341180707040200000591146000801c0e00303445540c091090421664030410703411000900050b6603002e28018481c040185202c0800002c1a83d543d6070703100c03a5407820024a803903110b000a0025080070807026004a40800c6014954455000c49814030300200044c103c01040c0c0d856601ca25031900c005124401c414600400070300040710151400c6000040010743c5031071070b0962540c07040d001082040c0c00040c0b00c6d41190410903041c4016198000002c0240c181b8402042054a102901502001981d031102c943c0400984905580c00c2444090247c01e0140036006481c5403c14803504810341442c200800300920030603401468005d6240813041501c40c0c1d000554000741c810700030885c45080c0218003c1e4a02c8003401c1075002c400d6218041659500300078459070806440308030381e0b03101034040e4031200c2a0081c1c40046d900d00e0b54540da0001d0000f00240f003503808440545 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 232516600 1250 232515350 232515383
    0x170306130605090610050d020d021902010c020a0b060103140421030b060a08060607020603010807090e15070e0a0b0a031a040c05041a070501050414010e0705100c0501020d020c030403 80
    0x78400c44045607009441480b1942d00c01c01046559400c3c5001c002c2407020411070040510920f00c01480e910500e2600107070bc40d1707005221950891074401c001020b680c0740c40000608190000342c0c2c1c1c1903540c0c0c0004424041d039204001200900480103202207014040024402004004112125148104d282150310301030044001c03003c0d55210103102d900020208540c10300203201d00060782e4801406450140703001c4003540410301607482603004150315000201e051207200054007680500110300700040101c0b28002200703040500d07018000d00c040c000d200b40a42610780b180544d01c80100004041d9544403800d200340900504a80e0003030841840150101c2000b0b03107001d10582c1e0340009156200e03405c01d81400d00300d4049115440c0f010710307080024000100028001d00840384142c2c40f601d04002903542601d080360940358006c00c402e0f8581c000002c20b01c61911080e4109454888a00d00364420740d003039080c4140288502c0303203009000c40c00080d0107031000313074004020400c4074442d1183c0c4183c1e8495 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 232517850 1250 232516600 232516639
    0x816030215160c08090d03020106031713090c0e09040b070216030c0605160602041e060e0d02060d0906020304050601031103060907052205090a0b160e120109170306 72
    0x4842010b0400400c0b1522030425100d103240115103031107401064a0581c1050000e1600c0d2142d41c01100184e441d080c0074020050036241c41d1442d90803889841e810003a00030b29424103140740d4011503000c0b598800c4044c021510440124419801c00360201c1c1141c2418200f440c4200000c442110261050855411000e201c500b180c008403904001108a40d80c01c02388125801d40c0620440b030700360301c4104100307800b040140c03006000525150b4a5800d01c8c180d00240107a445541350b111200740055800341a0b140d4070f54240c007451003a07048841030340c2c5001d103c00d604014100c0b0b031000350130700e8808401c01042000007d109810799000d1300c102c005200d0840c00705943e410040310f2000c150340202104006500b04147c410341c1d50b000032035181c0a100b4140c1c0c1d8820032038508840080b00ca80c0880091418010107000d05500050005000d02113078082440140c0011888440603000d0500900c3d10010b59000b0341c4400c29403a40b20622484601001451140b20b40059412030301c940c40140c0d007900600780 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 232519100 1250 232517850 232517893
    0x90309010c0809030705120102040f0506030402010c020f19090f0f0213170a02060a02030a0305060a0f03021e0306190c090e01120f0c090e0712050c090a0908160302 72
    0x5a481041c584001d81d1100c1c41500003000e1140c05108091000c43d0a6895588075400300d04550b0006844502e064030b02d4100781c8180c0e2025011b004204140000750f644400c4400c0b8040d015a84011104d80c1c0394045440c1c01c08a014010403810f207a040414030341100d4000404605030a07a05200e61002045200c04921502c1002e0100900c2ca800412280c1c0d02c180068110000203c10303204f090f841e039004106103500820601005810002e0f0034010703190184929600610b0a8450000c15420560040312040040c040030740708540d9184000d920f40b4490800c82c9e110303a0302405407105410f100403002e0083d80300c0016840018100904002e24a1040303500c50308540589440784900c0e4039008604c0080680c001c0269010040c17681008003251aa0044500a2101200008100e120300d508142025100c1d000101e400c200b07801e80c4d1010600000e40d00c001c1000c1201e428120b602c480d21040004c0031074400080120718003041103005400c0710b0302891a424025025503280a200810b407040104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 232520350 1250 232519100 232519117
    0x30a050d14010509130503070203011a0915060406050f04050406060503071b080405010e060903010e0601080d140a14070609030e0406080102090d0b150a14121501120c12060906050903 80
    0x4d021900044c9410544092001c90070b004a003620326010664022a0039220003032200d00d032051a030200c0c8402410300035803559022035103095900a00e403000c0001035480c8039500c80c1504101d00440c007070400385030341011034008001c024010010141d4a050281103600101c50355000314680104140c2c050701030086650920b540980c84034a0300781440b0054400844e5042c0c441d070010300501c00c1e440b140d1000d126100030900d400f0002d100c1c562401d0017013807600481c40300080800c4100040155440600010789070072400e1820285a094440d044401403030048600142070790b400c00904000b0f15422454102c1c200b00c0c00e031001e002261305e03128085d00341d1182c5940f080c1c2100c524001480890300190034a0303003069150800f1081643c000c3e0000c0c800b6041608000c035000c400309902e603a1480c0c240c3c00c0205030a41d24001e491030000d07000031504860014445c00c4001e4508004080800041c0c1d8841005003c51049549000c042c50074490000d000700d0b42c0440d0b04034980000306d240e0b403d00005684200 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 232521600 1250 232520350 232520359
    0xb0109080c010333030b070e03070311010c120801090c0f080f060109050d0302010f0e15010608131a0a06060908030409110d05070c0510140a09050f030a050d140105 72
    0x20714401004400a0100034074004103400c100c5003e560804041c200c03050300e01407242c0c040020b84e081d0b040554100502074605c50502400240c500103c1e100030a0410890f42c01c140109040c43d82ca40050b1141c0c00900002060700c0900c031400c0d22000c0c0c000790038a06880c2480001c10515145540036982590941c60100c0401d4413030300010f42c1607811090751980703c4010700d4400350141d03640300031520042d1805400c0780940d45074010300c00b1018191180300800075030000209541090b20f101c03103201c2d81040c001e880420001e040000c01120300034030f420085540c03216041005050301460702809036403d440c0740020f241444800500d01340318001400039189008040e5160030b241500c040000c1c490360a4010103981e0a010064004c003562051502c92601626400903815161901608010061412021780d0385002c1c80c414503c80540700196101c038994074002402d00f075904020340780c104400040002e900c000074000700c081d83d020002e000e444c0110003060048002810806696400034054a41c21 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 232522850 1250 232521600 232521613
    0x708070e0c07150f020d1413020d02010c110303040e011508160309110a090b012307030f050c1f0c230703051210030b0717062704050708010b010908 65
    0x840d45010302c143c3d404607062000649184100c00c810103a070002031400c03504956901c20300c012820001c01d4158808400d64500f10f10383d0301d44d40045c0d1611003187d00681044030b1340c6900f00030840c07a48000d5020312001030840761a56508d00442c1d006200900400e90004010101039008a00808200340100070043d408648000e480600710000d12000506807055141081c001c69141c0701e1240c80000f43c200d5a80c0460700c02d0b01000090b0000301c0b0741c2c1c81015041403031404950380a242800b43d4440326403500c0d14000c51000d228040301d032030044c03024100e154081c00044004090011003001c1e41c40d204400c007400400300040003a038403d1268142030721207000744024107001d00071071002000c2c0d0f50b00c0fa0806038107095001c021900300712021519001d1042d044107044c000d0100340321920f81d02074a90f26100d080344054051074206018050401c42c02810740502ca4007412840c030084400a07140c00a5200d068038060410aa48807164402d00d1915441c05c0300b401082e511450b4001c040d41c0d40740c0e005208 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 232524100 1250 232522850 232522853
    0x50304020928020403080909060d0f12030204180504060b03030901090510170f010828060506030c0607050619060305030a11100906020d0606080106140c010b0907020708070e0c07 78
    0xb2581ca65202d00c0c404420304046000550200344042c03c040d43c01060259250011201403100080b40501380910840041400e4400106202101003869602000719018170ba44480150041d0182c1e4005142e58040d100b40d180d00c502c5580d0000d0b00c618000e80c41400f06600610501da103070b200c0c5407045400201e1071142171001c1d0070000c44640c1003550901d44450078140c1c49130704c3c01811109541004900b0000401003291400820810000303a4174440303c007250100c100da800b00303a01c0e21944010325003611000010201d5405101d0400215009005145e41e007100345480d41d00c9041c100c41c02040720306000b0901d42403000d10b10032541a40d502000030f610748500c05500381d0b40075000410f540382c540319010320041c40d269a40943c0320340318440c0d0320258035074055503c10400e84203190401010462000010403c25030f010501e51810211780c400f0315030b0341080c1040c56000d070003e00400381c1c06c510500e050001c030950001d403107400c642c110001c1e141d82e19161000130a061a00303840000c04054240011720 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 232525350 1250 232524100 232524121
    0x6050616021c050604051c0e101e030b0a08011a010507061b050c100c02060604090512030f0f01060e06030f09190b1605130e040215040b07060c0503040209 68
    0x5000d90004240340daa4440b01000c480c5003803816403040302e80b41c000b4420701040000811a03000c0312485d003103140d40c02c402c3c9181300a090b480461b2110340f00d8800c00044241d0103004100b040c0b030007500c3c60ba6015001c01c0c3e9000180244c011501e509000c2d00758400c001441040621621007036040ca42204240064045c0044074142c104009c10f903806503407054a03000300081c100340c90340c4010b00c0ea120342e5120013505103480c1c04c0a2050381c400c2c104601708800701c5a040c1d40841c00e03071350090b000c9500155402c038030304000d440d0921000c641004504000244881d200d42042024400c0705c492074000f520343c4c1c075641d048030a0b0003405100c0307400103818804106404848240180e00141180841d016440300520040308040803480175a125644075080c84500c51210044846418031801c0651601d01d0710365120340da02440d4071034036104868850101c0c1c00c550724a02041000d000c40c50419840d03c0c1c076840d01100950004c0030444050f8a0800c3e0410854010300a0307903c101d030010710840c40760f586c282114 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 232526600 1250 232525350 232525387
    0x30a0e0609031903051b0604061415061b07231c0221010f0f0b0109050d0803091f0605010e0405010617060102010204090906020904051323032502090a060506 69
    0x1318248030742880b402050b0140e0034082e030825845400145081d0410b41071803806c442200034164403440000040000200c0001c00c641d464030415039000b070b524480300001d50080c003012215900e403030046980020710390049054032050482815045280e6400344401c000303000c444200b601550f01d0388444d0501c003501d00380c0b0400c0c00405000e40c7c60001d11000b0304401e402c654001d2301c003110460365142014041c0c06d00348261080c403042070a11110070350418000824038120094020208840080040c003511410302814940b45a1490900c005880d45141c0c40b0241402d0700607540010301c48001b1b807100d40380a0150604840c129201d420501050b00c50071401508020109419907408100009035046c50307100b507402044c040c0380016215502d220030070080d11006061900400d07013080280c40410f1500b050100c8800c1250341c03400b03507906a9105030f400c0d03001e42490b0050b110400300b210446250011058400a0301c00c0300c5000055a03104524070444400b40690b64004105006145002002c0c4042 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 232527850 1250 232526600 232526603
    0x10b070201090b0403030c0c080d2309030105040804090f0501180902030106051c0c0f140628080403030507080c090103090507120614010803030610030b060d0c02030a0e06090319 78
    0x4507400742d110142c1118a40c442c1d84101c0000300c0087c0c00c50309200d08200d01e034026040200203044886560400100400d00800504461604030032001d0004120442242d0080c1d901a00034001490b10341003841e81e54106101c6c0d240050300b004212000800e00f0b228082c140c8074070040c004d41c408004a80e00001f0440c0d42c03000c0380c2640d40e52001080940d074400c050f03801c1420108405100113030a00e01a0b08202d01540403060120300080d05120384403d00b0b840c032043e900d055a22a031625001c04448040c010044100b81d0b410408000e1904403580c043c4620703101d80d0080d00d00307000d1a15103090482c0c143d40c0c00c0300c644419010604c031584c1298440d402901c0a103008401311001e281c0c40780540c00c200348100c1400c9629559452000150003540f1010038010800500650f081d41760400c049103402580001c0321003015510f80e4540e400e580d0f042c1c291045c50b001280f0030010014031880203580c9502c45210302011421285100200e89402d000b184c001c001c0107405400b292442c8204903640d54041e440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 232529100 1250 232527850 232527857
    0x303070215042909010c0302030f01030b25030b01031a0a0911120c0406080f040b011e03060f0b030c121203090304080d050405011223090c0a06030e16030b010b070201 73
    0x24002d0740f1120003c800c240582411403004581d08007943e440e401c656908000c01c0c141801801000000542240c9050442e60070a04440c4690381d440146000c25507410a1000060200d61350b0046103a072603888400c0a20081c0c03001c200e01c422400c401400c041902858580c4611181801c1c40480c8450b08030168401200d40b4050400031481e18005906408580c0c03050615004941040040d601c08546504207004d00c3d1000c0c26418681c031ba02c01210814003a0480c0020b441545030b59102079440280700568010034100000021030290034054924240344030303c0303807141081c40c1c503840c03910001c8c40c1071000c0c3d540024903d80d41c1802c02d00340d6070341004000404600003484002000b8000784607850b0809a00d65030306659504103000500741c03551905c49202c05501d0440a0b6040e047c0b03014110f800d0400c00044008540d5420100a250119001d0241d800c5400000c1c0015030360381681209007400030000c150b40c014920510900c9400d0013600c80035180800d6800100b10090038500200b04c07060043c903 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 232530350 1250 232529100 232529123
    0x1d0307140f0d050d0f05240f090114030706110c1e0907050301030501050106020102180d02041508070f171c020a0c031203181115070203010c02010914030307021504 72
    0x100114100485026040049a000103201483e04c3c51032164418840c00d8180800071ba042a40742d10424807517056060112a1603602c40c40c07031940e164942d204008100070840603084d0b0b1215104a9801c0d80c2420b218040d01c80c1000c00b00e0b0141c0108820b45200c0c42c84030041c00850302001c20050801d2514610741da0354115982c00c0911520758440c144d12070219601d03490707070b2540f6600c3c2803800c4460583c0310034110391040c044904581007102803513096800c00c40d6030303401300070342c17800040e00a004481c0483c1426042c00c40010b0640000700d801401c544c2c0b115405402c542d0b44900481c003c1c0900c81c104003641e08402e80c54000c44c148040e0184980c0c502d8411a50201d5250307039401c5100300107030019215500e090b116001c11503410f00400318400d030381c0100401408920b55a0b0034464402c400c805202c3e0707030496100e01c0d000445600b030b102074580050090024201c0f00030003034001c00f213003001920060102c0342c5542003900004222070080f19036134010010a08415005a04190090000c550544815 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 232531600 1250 232530350 232530373
    0x201140705091e060316020613020901030b0403053c040e0105041e090f0c05010f0f05030901091a010501080c03010b0a03020d0e1c082404050403050f0a0c02041d030714 74
    0x54040c62040d900d0440e1b107000044820000392525800500011101a00540844c0142c0303501c0030981c11213034400130100e0a5141c0b0b14007900e0a010340340e0001e034041c22500d9542c24045000a148510018035500340340414031a070003450480c42580259102900141c0041001e4206503005907178507010504c41031514081c0c10b580f01c098a0941e54182ca841140340c0e0120140004411200d000700024205036040078601d01006d025022400f10342c009025000c400141002030030f4000d4000590310994500c1c0000450314131501e0300400b03019007400203140c0c10015103a0f586800031281030b5460f200c2920704043c44004110083d60115190408407615140c00c0c99044101308544c40a00043e4070028243c440c42c400000c01500307000300f601810398403401c4942c941180c2c1030320303000d0f52500c00d5401040d1a43d440c20251460b1090803039881d1418000070f0610201075203d45143c050b248200c40601c18421440c4503402142d0800c100900e460300200300c58400211103802d0065507401000c151485140403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 232532850 1250 232531600 232531609
    0x105070806040f0c09052e030608010501051e1018080303150102010b011b050c040e0c0907031b0e0604080a0c0618030305040e060120070305120703080402010c0510110a0201140705091e 81
    0x200907d004641c0f5941c0030b0000040a008082c09401c040c0c4859001d40030100442c41890303030418806000305450b0080001a520402d444c100e440341c4901c805941583d2449860b41d03d6004036000200307440544140c030150762041c090b14820800594a80c03581c240081e00c1c204081c0d86603d403c84091150301c81800d8207803250b01030903100c001d85002034140c00e080c0c40240100e038400108803108052816003000b00031005401c964032210241e140102c900d00c1072001080092240ba004662144282451a010451818804004d898140d0f5a03049040c4021501c0406144075001c002e012400030b10090015080c4941002d40c000030500d4100d5481d10300c0c0d0384280000950304c90344031060700498001c1c02405420005c1110b040c80d142ca2051926190b924014203140b8044c0c8000e04012140051009000c0200156001070080010400820720621a034151030f40c451259240554244000c10001510724861300c1d20510b400d454032460401d003001008100e00792035030010300310340203c0074148040d00c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 232534100 1250 232532850 232532929
    0x405042609040c11010c0e060f1608030a060f060f0203030c092805150306030703021c06060905060906090405070e06040e1903030509030403031b080c0105070806040f0c0905 76
    0x441e0b11444080f80101003294207441269150400380090f5820410b280d8a9481c21108d4914018650310740f92000861030548141d941c1c2009060b109010051020302014ee5200720202c030075800f482c0810542c1d501094550b00d0140c1c05400c00740c0c006000050a28081000401021400520210300c091030010391510740c8484180995407840c91101c14406400c1581d62501c44241200086056181c19030000e50b4489450000034000c007049201080c40240c0000c030010065400f01081c01426282c6207520010a411a8407a1080d904080070815909142405600548d04100a0041d241c00d1056041602501401e42500035a1b2814000c0030050140040b40420f0441150021600303d64200201030724000381040e1202d8100700310410000348c00408030300203c071001518034240c510900301050f50b4010185801e149500f010300f0051460f6000c00d61600c04e6000703e40420440d4401e05400086940d0400c03154003044a880c02842755203810300d450034480240c2041e00c0d100c400c104598002208 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 232535350 1250 232534100 232534121
    0xe0d05030c060108100e1b0a0f080d0806040207211206030605060a0501020c03030406141e070308070806010c02010e030307080c1b01020c0a0303030e010b06030108031206040504260904 81
    0x100b0210040c00300800600450b0750f845040c51040c00050910010340384c4501d242c4103819140e25140314a00f10135140d985010008084208101c950359a5420703440c1c2d100c480c000e42a0340010402c00029410b482c007442618881504100c07511082002e4100341d10000c20a500981b0500991505075280c2882e240900340c059480303654085400c0c06c06e41c081c4002c04aa0303400090654110740e40340001c58a002081ea0102e030003614120a40f904600440d081a03c11442034040c001c42511107084140d03c41401410040c2c440e940780d1101780d80d414070441d0440429034080307001840070044e41001d5032080040714040c007002070a0f80e04c1c1c004950380d000003a41c0110541001c41c2c0210382000604c001801c9402d030011801c1c00900b0640500d8000504030709085d000003001d0581e00ca00e10200c07500b00350301148520b08040c21103135803561207400440d501d4010030864802c4001200000f00c45043c14042c2c513010725800340000021515061040d50035402d5458051007116040c407010035983e0f5940a03902c03641 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 232536600 1250 232535350 232535353
    0x11707050706050108030f03040b070e2110090c0b0f0c010f0903170f0109020c16060210060b0408061b0d05040309050112140103060209060c01150806011a09010e0d05030c 75
    0x402480c6001000e40f481680b1058880d0418482d940840000e0381c00c8a601c65800b0a10100f0f50b40d0340d4401342d0310210541503a9810804440e902c43c41c0c1c1d445902c080741d078029614201c0d4100d141d80390074841601c400c118000c0200c05a010100240701c400d202a048680004449904000c030200f1120708550303146c094104081e40300c1c001c0c14145600f12210744401500c0040c0824286014914000c0802041c030403400800d40c002901c1c1c10420017070041240c4102054184900580c0d50ba0000350f86042580e9515480d03850900001450300a8070219002c4030307640f0300075003482d981d5400d480224030340d01110b1041c4100100031140c2080303218440c1e58410f0b4400d0b00c91402450800e4001403040034441c0601061614026030320080014805426044a074003d07809a51800030602181d02401a001d005000d5800c180340c600c0e0034080031b0320000c1611400f40c2201c002d60b9a418801400303075880150255010020020b000740c0d03501c94003601003040f201604500c003041c1c041c2d844514580c40900c0f240d405 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 232537850 1250 232536600 232536607
    0xd0f050c070b06060304120e1f02010b0a0603200d0e1e0610061706030f0f0a1205030c160606050604030f0219060210020706060b0307110c1801050f01170705 69
    0x30080c02140d00d94003c0415190581180340c1a0351300001d95490356080d50503c0341a101140c410b55400c403001c1840582801007140359440940d0103800b07000340500c0c4070321800f4103400c0880c100e8840c1c4900d1040601c860003030107001e0b60a000c5250960b01c401c00c041038440d281c0c2410f1101c00010014a6542c20f00c503282c041900845213001818900060014100c4550303022082107525070041c1090f06041d202e040c65200d82d00e9010000e4076103031000c5e48072885402141c01c109030042c4049441781101c1e000d40f205060030420104119014401102c1c404075401040c0304009a0403001c07a084055940702d8040041d81d180c4a4000079800d402a0384100c070303464510421401182424840042c204040140035040c10707051081c003a4551010070b6111145a9001c40c0c01014048160030103002088801e1036155a8103094000603c0c51400140846043c4034603d022405c2d800c240c0d404d00442d4072049000140b51f404e01d01080004091100749504019072080030350000f0040c00c640a0284204d5142c0503034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 232539100 1250 232537850 232537853
    0xf060a060f03150f0b040e07050a0e10060c0507050a0b0a030b0a060801090c051e090117071e020a02030d110c01050414060901090819150c0c080d0f050c07 68
    0x560358160050300c0701c0d00c0829000c20014007044251a00c03090303140c40c0420002800b182180013806420841580310381800c4100e4850031000c5250400e984041e80c954000548600589040700c60a44a995020001c4d40c401c020061140c0078804000b84a0703820340760840d039204c1c00590b443c40305821418103088001800d540311501440b841400060654030070311a281b0700900031349464014440e010740c090302e0754161007003a40308208841d070411001d59814105880300c040d134034141c2c011625150200f51070a9503240340380b00c0312031410b00c68440e0741d8407041e010010320a401001280d41d891441548a12400c0000580d0280300c401985140380e034540c06054262400a40f500901112b014148581040240b10349040044500c0c20800191040c2e5595081040102d6000c00719502c03080d01400fa40c18001c00c4101003640100e1410301406c014604007110200741c204880341c2000720300105102280c0d1900203510600604008005c0143c00211007141c540c0280c2903d108903013001c000d610004d032000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 232540350 1250 232539100 232539121
    0x1118010912080a0806030a170306010e0d0b010509220f0f1208040c0f060203070204021b15090105070e18040602090d030306150306050604031b0b0d020702091605040b0306030309030f06 81
    0x15170100d4101c00402c8060095154842d5541c2c40c0c04840c615a030300000003a441e41d0180c2c1400c51403900280000f2546000c60502e41c208540c280211407240482d04041440742414500070510746e60f610111036056802503441120188840e071044034540200501e0602181000c00c0380001182d043d10b0b4406c4914040c51302681716002600251441c00c281501400708603400001c0e5141c0560540300182e50304001081c12038204c54500340b2461034071840311445d40f0325441e00946170048441c1c1000b0301040d03c59820a503050400b087c040ba401c0303400d0f941099240060700340c000d90018040c0e0f41c01450302c50a20b02142c00d082103104c1c21b5000c240c80e10001c1102c0d14811f401012040c0c1903240420169040400184140c492480050042818802003201c140901c0103040005c01d24080ca0940c1c404000300000043c0d040a98240c0c4200a40400a003020241c1058503d404416a17111860181012101a84c54201a000300d800d48400c0c000f6207001d4a0030442c0c04a0007401b40028111481c1204201 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 232541600 1250 232540350 232540367
    0x10b0906040e030d020f04030503370503060118031b06142a010b061b2b050a030b060d050405070b09010512040302010213180e011118010912080a 64
    0x40d8040da24014001d0035110740030050704d8019008800140c1e65407900310800c01c040c020354001800c540000200864582040030445211008002d124040c3c0c41c2200100710480250700d149001280003040004c0c150362003514000182c19803444011201c5850782c170351040c141810042e4204411840c0c01c24445990850010b07107403902c1c4103040310319001c449080d0074045410880541040020b40454550780d190a40246200307100143c000c944a40700d103012050b070a00c4142c201c8659028058083c41d80d01e40c0c0e0315084000300b09600210a00d02418482140c2652000c044081013680d10f8031380c40015a14440103100f078094071715001c54242024100b09081181e079500c101c805910400000c84144d030803505031f6019502c030004400143c1d949040c141c0c00381c0f2881c8203011403014a03080c0403884503011428501402030b804810401d41c03c210074118200c8852109240000b107080c04441901d4007041c00c4440d1529040c90081121952005800b0b003050b00800101c850310800300318100e00a40c8020356 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 232542850 1250 232541600 232541611
    0x302030324150304050f01020d0207110105030702060f0c0f04090516080702070312030b030d0c03080702010603020f0d0204091a061c2613060206060f04020c150702120705010b09 78
    0x100855280d035000090300d07507101c001d190000e5000400090240301707007400b80000100b5000005e544d00c0c40f03074445070b00080d406150708550035400141c035010702d540b00c2c3c1c0503244104c2068001303000c151030f4924410108030780240404808803080200e07030442010a0060b200030300070307440080b80c5400d00e4220074026144401d0224100000c010421403c0ea07400074500040701e40012000e02c414890b4038085018110050810fa05071090016103002c80398040381d000d881c03c0c02552413002607228500101d0a03146039100103540080342c99070720005803800c130300c410403100d10003000081e070b041096451881c8500c0100f070558401440c80300b00419420075009100400301910030405541c03420365204298601044884031220010948220402000200703c500902011607120b02030f43d56403c000b5940ca10803902d203030003403015100c1c000303c509250003270b0341c0c110781001c0151841c1c0c0c0326005195601c440081c9071104520400074060051600040100f404a02820000c100d01c1c0d1800700340090300344003910 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 232544100 1250 232542850 232542901
    0x60615130315050c031b09030c040903080604060b04050109170c0301061d09010203060d0b070c02030709091b03030507030503040c0e040b0a05060d0b011a0d0e0606030d020a0c18090b010303020303 86
    0x2000b0701d001c40203d900c1d0146c0c00300502c4540b10030f000c20100e490701c82080a001c0d0400e1400c080d04040c9904041144c0c49068115001d001503621608000d2043c09284203041c04102c2400c024003240a0180d0300c1800044050200d03600714004100003429101540d00a05000d00c241c00360058000d80c840e4915807003000e82d00294074608000001c80d140211505002d00700c5154040421341c081c2c400e21100042c0c1760028100c40200303031504c040a00401d210401101c030001031050034102d84005000440440c3c0c0c240e110182000446d0301e068856510042044669078411b090100d40e01c1480c01c002400755000d00344108841c0742c191000422507178040d010768442e940814001000030f142240785419106500b00c0072008070050b10340781c1740078041c0800c11800d00d420010048100000050b00350b2183c4400c41c00c4400b42d00d440320782a6158a640e01002e85031030446c007030600002d240c1c50721856200600c80c20001c3e01a8164451480e0b0060a0304118010b80002041c0300310110b0312000f02404268498 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 232545350 1250 232544100 232544107
    0x7050d0c2607140f060a050a0b1912081b011a180105040b0f060304080a0311040e010312050f180108060402090d0b0408090d0c1a0c060615130315050c 66
    0x1c07103060314010690010500d0406802c0d0782e203040780600912504802c2c0f8030448001d410811310b0000580f40c22541c800641e4075003102c1c00141c4c582140d40b117103a04841b624101c14103050180170f40c00256113030815555006c0800441c01f1043e1035284100452046c40c000080214030040f0304a07440350181401c51061481d405981421100d03884c0b4a8115101104d00203100300c001008540100300b41584c6550003000030080209020800004000c4c0c7c010700d0750100058500b03652444158002c50066840b0a03a400b001400043c0c030030907005200c0b60850a04c5418040b0000d4030341c2441d4080030615501444c50850b258240d6046034456812000440b402d50924185a0220349076046000700034140c50030700c80c045418800090101c0c0c0c4c0300b40c0040c2510401d0072180c01c1c400d486501c00d106a40014a8070b480014008000e2015a40400a4000900b09136121441044075115201c50490130b0400200b00075042c800000310701307400461044c081c017400c90301d03200c0700e500c21500c008211180410040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 232546600 1250 232545350 232545413
    0x20f070b0415030b1f0810091103040609050703020a120510050915040c0314070f0905060612100b030106020d020c030703112101090807140f0d050a0507050d0c 70
    0x428803038007240054540000c3c1c138015000040d0070207481e084a05034000c04a107005e61401c0d84002524850402c0c42d19044440c3c0c0c1d40c81208003220041180022a01d0041c404031b800224a0307086600c40f54002e00031103801c15100c0e00001d180f44016804070b4020f00000c801b00d0f007009801d0107550503c0d0780340b003c104514645003884035264001e610f185c00c1041030401c00102007200703092800c8041c64101265602e548144009a640ca0a0f10b0050494001c140800091004c0660041ea482074002134490380c00c0070784440340440c039124050020702034034441c140081180414140694020f0101d507005140ca41c00704e0f48040d003441c9040c400b8074000c7c1c200000502c04515000300c284000f1300c0589101006003091212031101c4511805461495424445908107111590018102c0c59008400d071402c8820303400301003039803042106580109900700a407440291350086015001155950512510b4502150380e400d0074645003500d0880454000b045038000e029400383c42421455060b01240d0b01076070b03172 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 232547850 1250 232546600 232546619
    0xc2a0904031b05070e010b2715030403030f090305031f030b1503120d0c030b1e0108070e0a030b090d08191d0a060b1e01050301090506041803020f070b04 67
    0x50501080c002d202c002c000410803a0410000f00140801100d9000701d507122035989419038401d0240390301e10740c0e200c3c410300c90111406410308070700c01005203456420204044a141d2a8000410907000d0503a1136540d2940b4481c580034a01c0d500d442581c40e03540e213180908040c0b2000d0124040c080c40c0c28003001e000d10014034462403a40e040b2071100442030540300030100191821890b12a00a0209000b0404201700341c01604141100301c41c949061001e1a1b00100380401e140a000c50fa00c02240d020710101101d500451190b60092070610b0820342001c3e09070049244280360364811a210040401005a041018085003521030858a0859034070f040043d440500b140016040480c12503648210440b002000344044400045040c156200c100f5541010b0005151040310031380a04104541060341e20605814941601016142c07070341940d0074820716074010440180444d41040e0340790f00901206000070242c2040a101f40c3c01403102c2c400280000f8101000c0d9800035025031014401881007410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 232549100 1250 232547850 232547867
    0x1816020304060806090907031b06140a120c0e120601050901120302031918080609120901021908070609150c0801120803040201031401140102010608030a05030408030c0c2a090403 78
    0x10f08a82041264950542c468202034003944001c2142c60500e54000c09c49251034140001c59985481300040007440303000084291041c01c0015000550707282c4c516440550552080c5505500c0b0301e071102039440002c010958a015100003040340343d119100401051410350b203c180035190040241013408450b1794082d50301d008042c0744e00d84241f400312030200c0c81849074880c1c01803081d02d1054400d1450f45d507601c040c1c564509031001d0b00c8900a4052885208802034203d4481c91410780c0105252990300030641004100075a0498880303400b00710100114505020700c1508a02a03d0394080c500d021003040c20459140802003014458144010441e0801a1800007001c640026025940380d47d680700403001850741000622030542d0341c1c4008510011100340038400c4170401e8000b040000e8507010519901d004000317800e80051010000540003680319030181d0303007040040e8492070400c14203400d1031f414520030744112202503a52070007040403440c20090780070120000380c2d680040380c181a02e00910424 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 232550350 1250 232549100 232549111
    0x13060e1e06090c19050711030f1209031c0504060f11030304120215011e0e040803130c09020331050a031d0301060305060601230706091118160203040608 67
    0x2c80781001441d030324101c1c411030386140d01501454080c2080080007410700e800c400b40a840d10740c2d13079030b00da00e12606000500b1440c03000544024250b1101038a004101f69020340e0403107805008188244104001e45800094034803102e4940c941c0302e42c1040d400814980c42601d60108019200e9011400314501004403600250043c0048800c0060752800307910700900104180c00e142c00d0381b800041c00c03080e4018141b03100c0b4000c2c3e0f40c0025282e90703100200c1584034152009000320500300081040341500e40d44291000e8070450504402ca13944520340c5049810840301038424841c400009600c00740898459481603064603d040b603074130300b1911156501c0c80000b0b40101880200081c030004110701d00301e00e42e600d16000f0001e020b80f68991a00c542c6510042d69018081910079403550101c100e480c01c0031064810490031103041c00f60a40754940604005041a1803001d5480c8810100d0707162042101009a0701010384415400d1544146a81540500420045400a000c14000b240c0e2104000307800a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 232551600 1250 232550350 232550359
    0x10060e09061b0f04030f1101080a0c0206060f0a05030a060b010906090b0d0c030e010906090203010c020d0c030c080d0c050714061605030603010b04060312020c01080103030c030f0e13060e1e06 84
    0x840c1a0041c83d800c5208039080913110f5140300380140c0401c14080c132001305250080c1d0702d1164a4850102d920240ca1003c6040c00c0541c110800080d000e00344039031100f0807544001d01a0415594a501081c24050a0041569896100d0340144d80c196040010640104410f01d020031029140420b5800c0f640140e81301030080741d40303840c400b08003503200350000c0915581d120000c21685400c0d01e0312030018845001704034041d50800412030102800824803038144000c07a242e08880c070f80155800c40f502401c404044403001400c1c00b508284840904c42c05110b1051511141d90b070303402e6410450249080003410210580c4560100161a11900d5680b807460f0030b00d040070f1380c60781c5034003000902522040c40a10b4100e403402c0c400200f40051104442540c07800c40d000d03105209402c0c070044402c0701090101401044100e0b1318440040e04c03031554455982c070140f170f01c1c50041c840e0b030f0000f8000000c0225400c28482e00e0798014404040d80c1c0c400550000000c15005082d504200b8001100b55402130045218 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 232552850 1250 232551600 232551607
    0x30a020901090302040e0a0204110c030307050c0109050a03080915071407051212060109090b0f0d06020c06010b0d0e010203130311190f0b06091302040c030b0310060e09061b 76
    0x103590240e0081000f0315401070092041756421800030341e03103804501e0188e00c01c0c1c1c00d05110a0000d40640c040f942c4100a40300034614503541e24000380e881d40d00407007a00c0300d42d42d030741c202c0303e80071a106209100c205442540d42422508008201510f020302ca4004445110104014040d000b504600c6051181040d0009281c80c0c041600344030f814059110400e8054080010b22a10f8441c0403001442c80395100342c807580040754489094604581c04540a1504481c162044590f01d2400c6224461302a2040c1c102501d000c0c080125903087c0034081c0d005543c011030128003c20391141c01d0007580380c6010001c008504500e0074507440524001150301c06802c1c070018140001c03041c0418404881118640360b01e4940c0022a803401c0604180c1890701541d4440d072190204101d8544504554020b00c11160300c4452403020f0707000c01000b0300119440070207155450a00e2b9056482c00c4c800c0d2240b86c00c01442c000381d2540f9000d02003030481d000400f06405900b003a410094580d42c1d1a1b0044502d40310002c6460302c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 232553956 1106 232552850 232552867
    0xc0605190516050d15031407051c050717070305060907080c0a050d0b1801230f0405030403080304060f0f1d0c0f2e020604030f050906030a02 62
    0x2030420403541e0350182154104c0e5024064030740810b001c4036581d56401f4003a00b240c12060312070342c002c180104924500740c084094101c4003500c44021080181d90f51030f48400203402002490031440441199050041180c00059580401101e0607428030791041641d4840711700c685c1d0041d01c03401c01c0c4414079081c001c008008030f810151607203a45242c10360358400b6102c1d0007456042895440301000010b00800d010740702c2d200da0707000307900300548420081201312350400900c10160418600c05100014070000211401c60f60071154650b265203407407074080040d014031151984030b1400c00821501540717460344013040b542c14160391000c605280340c0b8840c0d00c03041c5240c0020351003240103800c90500e043c0f000c0380541d15410b01611921440345164951441502001c02d400107a100d030080104046e041140d00c1c408548508245007014201400200f035403000400c10148035401182d0b811 = true := by decide +kernel

theorem cover : BRFrame.Cov 232374100 232553956 := by
  have h0 := BRFrame.cov_init 232374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 232374100 ≤ n) (h2 : n < 232553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
