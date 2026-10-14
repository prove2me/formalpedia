-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1272
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:06:06.740792+00:00
-- url     : https://prove2.me/submissions/4e3e3e4e-20a2-4eb5-a120-da3863db96a9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 228597122 ≤ n < 228776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 228598372 1250 228597122 228597157
    0xb1908030a0809011e090206040306060b03090105010b07030f0302130902300601020717160f05030c100e060f1e030601090806040507180f051611010504081602010909020c030d06060203 81
    0x1240c0c913400900c00e0350f00280c03c8c00d291a03103940f641301c280da07a0b9400c0342011507000810300c140d540702449002d00400001d8400b0781090359690300104502403001c00e02c0b01301a004034440d04520300924504004007009802190b4501c00c01c01040d120722100080300124040440d03604000a04500040e880b65805078003500060381170003140c0703594950090950300140b050b0010302c8000015050808090f06200019402551500742014603017003c1103905070081c03e812544c101340a80200c1403c0a401040303c856459050010318031400d4003581041c1280f01107000307000004452200c0081d40200c500b81c1e2000107194072030040c00d54030319003030318010003aa200c03200400030782103000c01e914600d040c0d80402144503460300c030300340081c3d95068511a101202a081030015180c004071100b0300002c6420003070000703103000d40315030940780108040440500c00580b0318508581c800c80b40c01000d0300152108544805041e003a09035030b43c0003a1404003c1c41e180507030124815000005442501c60414141c04d03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 228599622 1250 228598372 228598421
    0x207060201060b032217070605180318060901030b0913060e070815062e18050918010207020a0608010305160509070f020c030a1a070c080406030b1908030a080901 71
    0x40c08407503950400e5800080854903600586c09403802059014010107000c645410201c529503c2c51700c00c1d030540c560550003000910f00184054801d07400d0200200d0340140c580300c5440042e000fa10103e8240c0340e01480a0f030810848040048103000540e01500c001c10041c0000e1050f00c0c0c6d586220f01a202040d40281d28001200765042c0a1903030001001c0c0c2079600f4440164000c50781480d0081504c91400042c0d90743c00c03003655104500c0b098a03080305c10010405454140440c4516001420f00365285544560030400c000e02501207941050703001d0300d0101c1e00e0b6610280104054400c2c041200c43c0d00420601d088048043d148000684000400340d03481503c0b9014140d84101c0b0752440e803030940c0038860160f0350659050016031100e50180710143d1221906900481503100014114803c0c0a040b0303a829001c03c8040e0142e505a80d483e05001450b0130300d00000034190184201820301042050502141000700030018244007a041e407900d8049450361405d6034240c2d100b8000c082d00009844c08c500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 228600872 1250 228599622 228599671
    0x140106030b0d110f0405090303191a06030c070506190f020f250204180201180b0f070501020f1c0e0106230d021503070f0813111f0207060201060b03 65
    0x803282500070100080d13103030108003140c1a214110350445c0d45070800f100300501400d01003581a200d0240100c03c0040d1081c0081e44440c201c1c08440d4039024040100020329855190402c842c1800c0c0c20904071000c81c0340a12981c55185540400708480301c0c1019410405411640243c0e08580c907040c900c1424114001a00440103001e06080402d4034842100c11000da103a621030800348a0345070844c1240c4550394000541900c04000d9007050000e0101000c001080a4405a400401710401165a070f000981403181c06800f581c1c0980a10500004445002d0319003007200d003400707070000001882000900901c82e8200d61013481500c10640c608600c00000385540740f202038041c90018101c0f80b0508507900400c2c0c0c880d4104010501824000042c4080160031103d8040104c1c16484e103044e161601c2b43d05030380c480e4041b25004211074038100e1000000d90301c8040000130050400b4407010303c4901c03a40020343d1542e5a116241c00f6500e80303d40420003281d40f0301101d1240703101c1d0035540c200641c0302046 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 228602122 1250 228600872 228600893
    0x801061707061b0510060b04170a0803010b0319060f0e0903130911160f051903020d030506010c080703020105100b0a020705090403030617010b03100b0108070f2001140106030b0d 78
    0x22255401080c0b2007951303081c05842010b0180c22110011500d0300d00707100782c149c843d0b00040060009580040d42e46030000e110b4400f10f074103481d40301010030303140c1c0c0f555112051800c0031034045000f4141044c00210740c003501400001c00710703001100450384daa2510803038680c4a12814064441600d109002404030001e50b8005144504c00d05860358500140f0300002ca009644c012401c8420000b2004c1c0742050200c00c1000e80c0e242521603da1007188000c9030382c0a540c0c0d1000c80c0401060589640010b20f40d68016509114115000050b00703641740190700d00240200411034a42c1511080000e0104a00706074000b07550f8401425001491003600f000100220303c14010811001c0507103400340802d05260102c02c12403013540e03c0e40045801400102010f0501c420102a8401d43d4a4400301c0c10b0381c0d81e07000c46c0140d0400c1c07880c10130780c020040c5084100c0d1196141c8480c0304c8400107100004441030415409100000082c103420002642c9644044081d078402080c0c00c0da1184c04c040280c000310705490103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 228603372 1250 228602122 228602177
    0x6040b0603060f2a13080a060f061203030e0106050d05060a06080d0f0c05030c030f040303090e060604090906110f04060311041d0a02210402090604060e01090903020c0406080106170706 81
    0x904126440502c078081c4e180c0746e081854107400c20100c90b02040380b0b901802040741d07030040302403101d02d041106010300e4940c2c8040250400d500e4000c0450f182c5000c1d1302013001317090054454903001015041c007950350f00080d96050661840d013030000855100128035841c41003203641d186041c036519140c048403024101d1300b0944007400100460b0500e004104014540302ea0b01c141010b4540d840c0d800c02525081c081c0d0300020150003070008106040e65000d080354180c0d4541d60b0000b0760000c031410000c004141c00751250040700c03000a8803580001042d0050421030360366581c2400f00a000c0c4c42d81c002c46000303a1003145861503a9203070303091903850101100d5a010b41050801810320507401610095010350802900c5884000d00501c0b0642c100012010380c0710398150b074140511403910101070343d05a0148501d08035180e56069403003c242c400d10451049000040c402e00819480b0280c0d5402480c0620030b0005008052019400e01e007804103d0700100c0c0c0a039110310280c0030030304268820340326200f070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 228604622 1250 228603372 228603451
    0x11d1005130605040903020a0201080c2d16030503100f05030c01081b0708030403080f090a030e0303070209100608011d0a0911040c030c08010506161101090806040b0603060f 76
    0x1000f04640d102e521801051034000e900503d09581e080c000500b00100290624a410104001000300c1c40151582100c0c52030513098441e0802404e0361280605015820700540c0c6c508829400505041d030140185001c0c4400c075192400b41541c1d03483c40075044a8520606130035400c4a410080d440d07000ea10920b81c00102880c00c141e40d031001c042c100740180e100d00c0f81280c20702d101005100605500c04000c40c1c0c412902c0300905510f080140d50650340b41030f20351000b42004107640582031280c50600944040980c041e01081c40c90800b0f841c1d011204800e0f01806000400440000400c4444c40b03100c040c02e1209440450040d40311030a505024080c0580c3c152980042c1c400d44007955200c500c503003003103c1610f60740080c41c4078144c1c000804921069114511555045c081e80307001d40c10b94094500c03241c1c5d0000c0c081e440e1080210040e41d420140c3c1c1d014000c03e0003120100308c140b082a41c2c01d41d22503003048043da95195102e02d1040b0f81c50400f030f207000b400c0c61100d00318605000c0c01204d0340c4072000c007081c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 228605872 1250 228604622 228604631
    0xc0e120c01080f0402060c0709090302070905070503131b0f1802070818060403021314070f20071a070309051e04090609020901080a0209100b091c0b010905011d100513 73
    0x2c03200300d18100b07030349d44070082e103644e18001030003416414440c41c00500b4145600744418101300e00001d09500001c2c100107009403120204508000040c003000355055000444111803595881014458480500c21614010341c00d513240c01035002c05108480c0680d5000141e5800d001c1300c0e1049008014a41c60015000f07207040002001581d9441500c06d00007400c901c010a84100400404501c0765002c0c203040c06006070080700d600c9568000d1003a406012a10b948901224521a03030a89814407076403207040c11f81402c655000c10802444003c10b0064006d44a00709119a15000d0001207070082402002800c1d05080301c070702600d0a0340184040345c0c051440440e0130005500001c11121003070f03100c1b120551142c6000b1707085003000843c02c3d0b0301034140c0c4118070b0303524988490049640716042c1154841c80192421520401030a024403881c5030304034007098055a101c008844c001e0030280104071308025440d0240811503100410507100c0c06d108003c1040706032914041c019601c0c20b1032103441e00300e07440d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 228607122 1250 228605872 228605887
    0x24090a1502040519080c01020c06031501020a0803041b0f050307090504030e130c0201240e07231305041e0c030f0207050c01030c02030711010e010507060c0e120c01080f040206 77
    0x1561500c40400f034062110101340c601d020011441e0100d00c0d030b4aa41590809100c0c007040361343d59402e0381d90000d4454a4503000315601d01c0101d0a00441100c01003074954003000380018021207c0c13076a150298500c4000c50410340300d40111903c0e10700c130f2154550550202c042800182010b0300148d81140c401d0914801000c841c40000b0f4111501101006200f9030f55407003242169424001c020802c194000507044c024241040914080071134000c0c0129910f5000c00f181e0703800e105040032540c2e07110550400c031030311044a185d00144c1d4400080405603514090021442c2d207024440c181e10420041400d961184280c1c00c510080c181060100092568403c0c80d00b0505c2e503280010200140b00b00040c1440007994130016088414540342041154424450100003804a0000040b569002d0030084090900c0d500100c5040c881c1450042800b810105001a441e4002c00b203024500b40c2150520001d03485000d981e03569003407016219001401480119040124081d01c01c1c0d001b0b800684a03c2c034000c0c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 228608372 1250 228607122 228607129
    0xc1101030c030f0c030c031107031b11031e06010b041d0736060e03120313120815040c02150606040509010f0e09010605010905120f0f24090a15020405 66
    0x1640c13003001c2c02090721540b945040070782c94800e803028034045411071401d01010f601d00922a50100005d100c103000c1000300503040c0800100a04041031001341120820704c00700d241c4084001c2902111052441808000f15450180100365401da03101004000030b403011543e000306020602603d0201072086007044407140c41c80080b0400d8080c1c101001c0d000c08a007076501030ba0101d8602c0c2d03103c0320400858051181c125035000c00e405d400d00e0085640e040c0c40751111001400c161081e50001014403d0014031130700415000950188540d845441d10b03131a050300d590910042d01c1128810303a0058000c911154044821015159004540a0541d40c00c041c0c503074011800c0d000080c0c0103064a180c00c68070030490b172851900e0044c0d001000e04c0082c07101501d80350010301803003d2406450701c200d400c803500d2420100100000520b01141800700e40c4070406a100d60350300c03000089012194900100d0f078001c441010180d09138042c09140001f0110940300c0e8560742100551705150412141d02044001107503607 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 228609622 1250 228608372 228608381
    0x6040c0e06030a0606110a02010f051c090f030206090114070309030e090f06030f030a0221090d0b0601030b03070f0302010e0a03120503010f05010e0f04020d0e010203130b070c1101030c030f 83
    0x80f21100002000e6003011005042d0f1440b45048009a03030024581c0001030364004200506803042d401e005480c0d503544142d21501d10191282040c0232441e1410340780a1040c400b0300d00200350701035001e8a045071030712031199090358401e20342d03d03c1c00c213000d10114652521a90184801c03a0080c03400000290000d07000800322201070b03450350201c01010341400843c2c903080c0010701418840e003005614005488001030345641c0c191085000440b24081e44d500c0c0070000e182103e04201c0010051440c681886c07506124210090325007a0000b40f8240b03400a540c1400103400e400da89400d80a040d503070307103160700440300701d40300f12009034208000d4400040080d00f0051072920008081e01d6060720b07507042c500d9000501800d0b5218904120205c0322050aa0b1604c502400d107010041d10003503520400245843e0103081c203145051925032000041101108207424081040352141c031402c44543c484041c1242d40704000d034405003004110310703a800419800380d0f00c5200003080508021030746000d180720000468 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 228610872 1250 228609622 228609631
    0x1e1201110d09111906030f09081c050105010c020a03080904020f070c0302090a061d100b040f090b0607052a091515040b22080d17060607030806040c0e0603 68
    0xe0b4442d1551420005200f2410000c803c0546290202c42d040c10014a69514a03120741d80a140c1d81e240003d17150146500a44001604000d50b241e0350603030b85d250b00062810030f148154426140c0740000c64150f00c80c035030303540c0d2454006000d0305107281192140042c6500c01124158042d9080002c4144003041c0c40103000707070a00520880c50061301d14014800c20351002410400c4061070074405000c00b400d46daa8480004205801e03182059a40c07103440d4606c503050b90007421141c1720200d000982d880c003819007003054904210060082450f0601801010f02400b9030041c2940c10181c2d88501050360583c072000c02041c01da519001c00140c500c0820003229040e2250498444840d1480c9014180a13400d0903102c0c01090f40d60b0300d011319103070401516014803c081c00801401c0d811700d280b0200c1004004d4083e0070400c0503140c014210410150501e01070004001c070110b288000180c49141c0b41341074a003d01e4241c3c5500d18155100000c00c001492010948001c0c0031020308007400c1030301c3d42400355114 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 228612122 1250 228610872 228610897
    0x50613030f0830010e0721020c010f0e031210030204050c09010807022107020411040902031006090303050d0f0e0706021b03010603020d02060f16080a0e1e120111 71
    0x5880e03036040729010052207032107550b24011100c8040700350b000c0b03043c040e10b04540420825410035102d5080841e004110340c0c040100c801c0a200780c25000f807483c3c0d401460441120030082103005070500c3c50005a80c0f050341094580c2d002841003248000d081d040d0b0301e40c0500c0d07404000008a03201d60020f021100103485d14440f1400220702c48055507046242c8540010042c0014030003200408682c104491201d400f04415003c045561404c54990750008030240201d80c41d0340f41c82e40d840d0030500000b9042241c030101c1d1591581800900c49010341c480e4410b803a016501c05241c00d03810401d00015001131001600c0180d036601c0a0b80c80b6000a2280d01c010386007580c080c14030a141d500380c0e11194149410b625100303074500403081005940d4240031480003070303042e00c07559199017104400481c07034000c1080c8645111100300043c410045440001d01c8107014540381c403014907040500740108807581401c034510124036100243c880386803c9a0003041030300c0d040c0c0082003a101d030b9003144100350030016030303a40b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 228613372 1250 228612122 228612127
    0x9120a060204030c06110a0201030b150412050c0607081e270909120d230408070201080a2705010f09081207140a230a051201050108070504050613030f08 67
    0x204541c1c60110300007017425245c00c08043c0c03020480c884c1c6031901a031009050541c2c6940c090600d440d21030701c00001500b810011615241e441c11004411006540201d031030b070244118880305031400a064900310b13900a19210f09020085424490301b20150450703500c509000e2101000c4528082041e1464030902620302038034140c18028404000f02c06442e2a0f03040d0000204c25503080088003c0c1c1d00c000411510214041030300d2030720360f24800011050400e40c02c0305181040240074910004020441c0300313a8a107850f40d550f4a000f00f041b985038141050002c3d0246d003185040180308155440102d0090000040c1c0d112005401c0e001c03903214030001ca0302441c0c0864150341807101c052880d644440d413030604000039640303d078800d0010311441c0c240409108122412803013103550b403540049442e0350b96205a66070b428101700905030f0780141410480024901e0000710f06544180e1016020354215200c40f41004d04110420841da00071100301c034400c0704182c20000100e03141d00d01d5a91824024295580d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 228614622 1250 228613372 228613379
    0x30f0724051f0b16030c0c08030301060f11070e0103020d033006051819020c10020903061f0603020a1403103f03030e0105241507030509120a060204 65
    0xc202c0581903110203030110081c007820541906844c40400c0c8a5414600b02c007904034940340040c081c005903000b0400310320010001086498200f942c07145804141e440d420030240040a4aa07030318481c3d4010810280c405500400c014107003c0e22202c5501d100b410404d40c0d880070358049400c08050510481d0340b0f100140160b0241d07284078440c4101818080e941240c0348405048100c3c0306802c00340c402d08413801c40c60602c840b00e98040d4152170194007050207075900915a41c3d403140103900201c0001e48280078100c04280a2040523010104040e00c8000180d0540c0c40c0c0a0160001d4201842e00428000071180010f5803c0c00ca000640c4640219a1a2000d160900000c0442c2c81003500c030159100c12024414030454040e027030800b40c030000c018402c681a40081c9011405007500d54901d411a6081070140880c0e00d0361031070081c400c0b959000300c02d0801d118039410420f0102e2166a8000703501c104002e9800407c3c400c400901d0050800340c00350f01101e84070784081b40b900b64100b04c2641c2043d400318051 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 228615872 1250 228614622 228614671
    0x50c040f140f16020a11010f0c080408010203062704020108070504030f0b0a0c050a021c120207030309050d0f0503060d060b0d0b1f0305031207120603080301080d02030f072405 77
    0x19442c078039903480103025170100ca558100c0c001080c80000c1c0e06000034240e0490400f8407922058000d1a4004405e584403640e0700c1046010750020344446221b50980410010100e0000010241b6201650496040340d01c454006423036012010306000100001003001201107190b41c1c0440c000c45105140e02491454100310140450308002c40300341c20040c0400c1000d40700b5900241400d000612002c101000c00169030003601e41c54448a0900d41c901d0000c00d8101c18941c150340a5200f40b405501641c1201c1000c503011617212202d201e150000c940203001003a001d06111000c160018481d1000007512501000000c4289030b101c5002c9508407541c004000208000412600d02e000744688800c4149003142d031882d481e4080d8010000146564900180d185c0c0e1150502040c40074500b80104615600d900b050b1029601c24018505140b0940c2402001c3e148008216019008984513140c2080039607520540c0410407100b4411101c010150104841c43c601d110f06806055441080b070140354011681d03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 228617122 1250 228615872 228615901
    0xb0105040510060f050901050d110309070816140301141311030106050108040b0907151701050a03030c0f03050715090b07090602120d0915020a12020403050c040f140f 73
    0xc454020342c08010803085401c49042c400031145030401a80b00c61240300101d510b070044085500d4140d040520b80c0c1c140c0700600700114000c0c4400025110419110440c10340c0d10309884000a007004032000d030030040c0c11300b0301400245586005001140c000641500314410365025079451584402040d042c40401481c840105141d0030260000d1190501c0d00001800c170000007000600500038620005810800c28001c0e40d0150000304280c1c00400c0d1001c20040111583d01118001401000d001140d1450b04501040c112903060782e230414181c0079643c0307039044c400d0111001c4007805428040c1c40c00050300e45010600c50110002c0003d030340c0040d800e1444000390050608410b1007107c030410320210f079001c15521421000c034203420750b540080440d908014010000050966840601e04c0e5982c580e02d034000300408501540c030f00e12103601d998160422803281d4440140f29600c602d030010002d04064209060b0074611160000d42444001030506010900702e805840d000d04480800c40c00c1200d1102 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 228618372 1250 228617122 228617131
    0xc0c120703150c12110d0c08060307090e0a0803191a0904030305180609150f100501180504091b062109080730030c0e0114160b01050405 60
    0x4121691a544401c01c000c20400100b109281d182c0803000000381c003070101d0304005041c1c03140400201581d440488429044103c00484d254108140c203c030080c890807030103001e0345004020341403da14241d0160002e0070100e04d0440140501e22030304000c141804080d6100e41c005842c00c4603009101c40d00e44045a940c0f210703e80104460102a0242c0c0d2500c10009a10550504002400384c403129011500318a440804107040c4c0b080c0800c0040c11000868080c034020254001103009445403040c40c80109401c440340901c4004140080200d50300c1032034522541c544640804801c80d854201103002e858071b002080ea404000e404501000707004071804e18008080b1890264401c44840c102d40e45600105000c0281c040d4a4850300c10600441100301e841e056807003c40303a00e480b449070b0b98408001403548040918406440317500c048560080c0a821080c0310555030704104000d08400650380300303820f00c070100a076500510811741294824000480407a0250560710519803410307040100342c030700080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 228619622 1250 228618372 228618409
    0xc060412030e06040b0a03090c06111515040203010801090b0f07140d020f0c0709050106180303050c0f0106090f0609061a0721030515240c07030501020c0c 68
    0x820000548800404069140e0500d0200512100b400008820b809107401401003034a00250700600c0d503406510400c0083e109a00032a14180c1c1c50100b560b240034105601010f980000001d065030b4804410420b512503a001c03540204014218045422a0002d0b000409240c4d5111049414005807544041d40b1540c1d0f0746110486260040c00240300e242c412103070800b800001303e1515442031b00740d0180c4501001f07140390240c4513511000c3c101d40c2c404a901c100500c1034078000000c107c09202e1010009401c000e0306220680034034555048803a9404568103503402c0c0200c000342c1c0304202c1d00f801008010b158121010031106240808a0115003d99000c4441c80c0d14002003008843c0d0701c2401c1400c00c0e91510754a945400150500c01201080701c411150381050b17840b40c0070b2407603400d0b90109000e4105440b030390100c00520700130701501141841c5410034480c1e031b550303089500300030910040880c061f50405680d030b4160740303545160990b003100e90039103a41e8010740b03030188103810a01800080040110b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 228620872 1250 228619622 228619627
    0xb07170f07050405011b020402181003020703050a050c010b030f07060e060403020d0209041a040606031a0402010905040c0507170316051806030402012015060307061b050a080c0d020c06 81
    0x1580060710b14400da104103818071001c0c2102442d1000d039040d45400c4d10b6000f40c010b658943d80e03001480c05540382400304a1080304942100c50116100c0d00c01c2d03540f4260305448070b501c1c1c02440c0f84162031b01d4003c03a81038615176403a4086014170751000d0241e001891240c070010180d1606005014252804a00327541307005243c01c0c4004c001613621418080f49641e01a05e44371490b071202e0a04154007407041031408a02c620b40002d2204015044e4400300c2128056501c1081c60381034074030b44038001707202914040d0009101600c00d111601c3d041e440344c0c08020950a08914085a5690b0180405103c003101d003d100008010031000361180d00c00c00341d800b03e5a103030192a1202a1254021014154038031a0084402000150840e40909221821020b0540b0100c490300c08052100ba5504078110601c401c122004c0301207020740c01c000500c2c00540c0ea45898180c03200f44012201d0701c1d19486240140d1301e61044110135008510b00100419011120401070b0440c0e140f000300203803406011a80d62401340004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 228622122 1250 228620872 228620881
    0x50f0a180e01180519050705031e0c0105270f030f010b09060303031009020901091d090706030506031506060f12090d020a1205030a0f1e1b090b030907030b07170f 71
    0x30070000b1385c400603001c5802c0c10806034144507203030050303641129815228407208004150400c202140b2034441941c200c800b40403c03100112a607011b0300f5500000200245001070b20036135a2200301500c014068004050300c220032000030701d040089030b9207808503507490301c6405080c1480019a54409001c2c0c00640c99810004241200790040d0700c5840b000381e034007290501003a03200d0b0b4651001448284010201000d00c2c3c47c0400b80620b06441c1d464440c480c00100080c00c0380030780a07441c414030008019003100008003711040c409001004954040030800101408540d400090007500f4800700500340d0728604070710340d0303860540c05a640c50b0655101c6401c000c001440904101d0070501d8618103d607d030b032203219100d0054001054032040150030040c2c590520340e603105220052003074075413052008403002c240c0c190400c509a030326400041d80d242c00500c148607500c00250b4100d41a0340c22104803a40c1d84d10351011403141074a40030700262100104c400f0480140c01105d4000ca02071a00742c002d400e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 228623372 1250 228622122 228622133
    0x90726070203270604060f03050603010603030e04020a02030d050406061d0609040f030c02131a06090a0b13080f0c1503250908030408030a020f0610050f0a180e0118 72
    0x3801502c1d40c42404074443c55203001c10500401201c8901c003a000f07580752038950101804581d0740801b80e40000b031508001420380c2c0f60500074201100d401d42c840c600c10000071800c0c400a0f51206640c881980f00421803400c0d480e00520401d0710440c02000d000070a181010140b4814950b0130360321009200c20001804041c0d03607500045a005a0701441c5400041407900c4c080d0fa01c480d50502c06076104540315140c441001150b000070801c159050218100000801c00700416800f0f4903030381caa007154000d041440b500c50382c04000c000b00c41078440f1402603e82e50f071a00c180342080d280110000c80d00b10100a0f1000d040a0b103250782201000300c00141145000310500114a40c108003840c0d060030b0005120b000303079005016803000740581800340caa0725600d8592656980e404541200014418403505041344c1c0004103a0b54059040c0025460280c0d00e007800308404c24100b900030315800300a40200007486850b00101c070070303003404007040030424811102d2201c4c211441e8004c02c04000300c0641e90707400080c6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 228624622 1250 228623372 228623377
    0x90a150503010e1b0a1206082406010c080406090e100803072a12021207080d030c02030d02030106020105060427080c01150608180d0824090726070203 66
    0x8000c01c001d60b03c1035540c0c20180d0040107414030b0034401a0400519450290f9000d00c01d03d111401e40301040c130507241d44a09196484844005141d8189075410340100040c40c001c140b81e8000702e051510b00141901da45840c106a400380c1e0058002c42e0005004005104100c40c1d9290302c02541c03035a1001e13951411608644a10481c036004200e102c20383d4800c00c40003850075440c024050349066800c05161558541400c00342050000c5c1c0c0304801a141e0201080c500240d02c005517200701000d07190103525240294064103d2380000e40550209000c2c120303060b1214800b55008000a41c004101400c000041c001160304d41c4122041e030b0f04103542050111184401c21030102c640c040b658076560040410b8060051418141415102c4407a0b8030001d1195170206c001c2e0b002e0341600d0f1044d8140c030514240a03640d4180d406084022542d0480011040300c600321400c000000308685408181001d00005121110700711110380101d4164810740b84078020014002900500385078014141c2e00f06403002030754130f0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 228625872 1250 228624622 228624629
    0x6070c09020a140309030406021c09050d0507090504080d0e010c0219110402030f01180903090b070503071704090f060305060f0919230c0d08030702010212010902090a15050301 77
    0x65000221071007a00d22030b44403c88559101000940c803404d2210704240c80c0e80c07061048400500c25080f044922840c0c174890b007050f1141c01c0d01c964045c140b4110521008c06d00860080da880d0140681c0002d407401203004080c420340c85000b58566501034010f48408a03441c0c5003000c1c4c1640c1c505900c00c0c80040e000135801e030f003642c0140c15901c00c0400707600d0301c0040304e02a402c20b180c00c03500100c00d110a0942c1c030a181c0381a980d0500101e120714038500c065070b0403221200350140015030302e4507013000320400070030090102900800583e440c00703545841e0078031440012451220300900002d0104020452f901c40e05000c3c4074800c00c1842594950f4540a546000c06444e48152540b001d001c50380f0103c0130881201d544110050034884c2c28040d00700310782c1c0a81a0303d00c103079103000c10306030940c51000e0100701d1035401400103044040040103902d030900c190304014003801c150f65003000820030203403a01000c103009011002c0c0c00341c0d9a0040c0014010703402c402e0351100b5420511850b0403a2280e400c5020350381035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 228627122 1250 228625872 228625889
    0x10050c070902090307050406030609030e01051806090d0618110301200d0608060703020301051305011d0403023d0204050303070f0203031606050a0509060105010f051303081603080606070c 82
    0x2940d60040010317007044510340c00181d101e440c2c481e00104100d016040004543e0281c1c403416100040c540054505226905403802403007500440b80c0aa0325101c0080c00183c03102038981806400c090365070400722501c8e40100e840c0000707506803080c10000c048803002c20112060f40284070062410100c80800c0c0040900702220310004074100801d8a81c542c402c2d0000c250420403540d407030405840c050002d5001303003c0c5602840003c1c40c0110f020013140a950b0403580840220700b50403030015594107020074081c00032004c5002d01515a52810014400c88141c2c01d2800189100340c1410215184820010340d8075544081c01804104182d42d40801525811f40e0030800c0300c49041c036903200190a5100b40180708071a000c4a05162050180e960300442c0705001d445400c0081d51100c00070719503168424440d441c00070b041c001c00205004d11034030242c0090b000c0802d004030001d840790360780074054020069460509542c4c0a0000915070b22600c09a00081c0554155141c141645c48402d01c0c130b079442c0101d04a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 228628372 1250 228627122 228627127
    0x601021605090c131508060102120d05070905030708071805090a02090c0c0312010501170103170d02040504090f05190f030503070210050103031d0a0b070b0c0c010c030b10050c070902 80
    0x401094003c1102c2c441e600b100c203540c401546441c11420a91062000000050784d0f54000030360550000130784004a0610801803800d1140900118000d0b010062850042010381c0c0710020303050310100543c8000d40701117009082d00500303190200716041c0081c07114540340c50411051060720f171000f042c420b80d070540540d22f0094a9403040032500303c070f2080c0641008148000140c218000710762410135410307030308240e907400d02c4910f24841c01181c610302804068050b03684985003200040400c80105684140c4040150a107940d40d0002003c60308000ca040d90091610040c08041100901000d49132440704103152000040300d8580c0040704036465002400c0c468000f000c9110140200701d01310903081141c0d0f050003550384a150051100030030240c0c0039a144d441d42684c405601d0a029003c040e503500650716801c0100c00d40322a0780082c1d015000540d4100104500c1e441c48501b030040c10b03001003180c1c40c04102c0300d455106002040302101006810004280907442c01c40e80e02080060803941210b00141c5c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 228629622 1250 228628372 228628381
    0x140f01032a06030b130c08010e06040f0603060605211518160501020106060509030c04110903060f040b0703050f06010e0102010b03070e040c0b0403020112090501060306090812060102160509 83
    0x8070070340010321500c90480d48501d0004007a0f03415004840c015030142c510b803007511408403070740c81a550003108807808629240c0041c00310042c07080d24540d000c40020400b14100c941800d1000c104d54040c4c1080e60b003140c441c401800309040150b0848411042002d80102c5034141c2d020300350311038000f00c3c240d0007000000310118500003410413006e03c11280c130764142d41408a500040080d074810b54402c0d41d015509100d0b0001d555400b44040d41c0744000301801600440b0241030400008100d600e055401c00c40040c0314289668038204045c61140010b0f8903140c1c040d08042c00d0a822101b0028007481c00c01d400c6c0400c100c2c0740f0b02c0b1803080b00e400c070740b0a0910f0b07c200d5081c1c2c001030303000d051500c6190f41c051159100c0010004d10034402113004a014061107800561030748900e124901c43d5005c040d010036048a4400046002d9502141ca0030340540000194035850355203410588081c06000e84409502107a11501d40880002d0241c120000340020301204072807501401c010400351181070301c02c66240c000075 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 228630872 1250 228629622 228629663
    0x803030f25050f040b04060309110604060e060304020d0501050f04110d020a06030506150a0c0308060307060207030b19060f0501020c0f010806040b010302071208090d050c1203090309030a15140f0103 87
    0x65001c5e080480295841d15210b0200a0043c0b21410301501d401484084200544c241001100c0c1551880d50724900b0000c04441409096440600102e070001d100d894070b00042790080c8901e0703004036540f1881c0707150f40c24681400c0c0d8109040c8000c0740d20600a83d40d280005170f0722001c00320100c0c0c000b420085465602d1800040c4c810911011080d0301000019401c0155640320384a025014802c1d1101e102c907444030701c203050ba50481401804003591107940c080c0003169a01c88100d501c040203071404034506c0d070340a0b410300640d40a071384580400040341d0000d200345e41c0c0600094890302800d403040c428000210000800581c009412140100c1e40c405503007030356034481d804460700103402044800655905040c005c2c11f242e0304580803121030141002c1c0090b6644a8400c4954410043c00100014480c00340c6480071540050290341882c0300410030050103441c184100304006001d00c1041d540c1c0c03240110000107403249039244400720342c0100208640040340c81c543d241520b402ca22080100c0c0d001c08080c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 228632122 1250 228630872 228630877
    0xf06041a090a020301090e07030c0303050304050304090e0c0103050f130311121612081e0a0b090f04060c03060602070b0f0f070507081e060417090a0803030f25050f 72
    0x440d0001c00403401c104803503200c1d400a50407580601c4003002201318565480d511040b440c080208410302e070b11020004280b0030000780d60414060002d0340d00c0c155a900c10f0004542d24001d01c1d80041d0800c40b500b19503580c040c421140e2003402600e09031568681080314404240e032500c0c006040c40101082e40c4070300c01381000201041030406018544d41d05d130400c40500c100320316107402c90340d207500001e0001d0308030b210780c00547c042e0842160b1880001c1025101c1003034500c0060a00191607a207400c0340a0b20741c0c1d0031030400d00500300035000d0011800e043c2841801ea0b110f22113180700341070524404110807940050030408880310030044c1500d03910b2000228246214115410f0314284012600409204011070320130225000c0d44115041401280e041c1c1100500313048442c0b03219041707000001c0c04124030380c000b06441d0031034501c41032400e01b032207001810350000354003c180710754408410880300401c166005074106188041d440c1801d2142c0311032100d00480030044204100001ca0500d40b8020a03005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 228633372 1250 228632122 228632171
    0x1807090b04090509010c02010b092802030a0902030f0c010e13061a18010f05190e041505030601050d082b020d02070b0709080c0d050f010606030501030308010603050f0604 75
    0x280c8941c0c0795079aa00710780140500f600d01c076259520b4400d100700118014030440301c1c00d02c1c025020703a00d950340e000c4081c0600000c22031240081e4800d09040c41380c00801d44000c601c1103003c0070001402186c1d1703005062a20040f01d80841c80755004080f010626038000c50240c9240c41c0480b00032080071840c0e8905030103000281d0114443c5941d12056070000c0c1400006031078651076607840c178074560b10b10b42c0046601c88236911125011a10030810a103864240e2462907000c0c44550800ca03000034035400c08130301111001206203440c1034075550107201601c2c1c00d104190052000f02c07220180c441942e103078007050744030351002111110040311062a040c1c841c0e007011498424000400c648031040e01c80c21402a40c07181e0800c660b1144800001545640100404000d4030710000003490109000014883e100381e4030901502d25101d000526000c1300002d009180182c4121360300072a0030351540c50054010740e010f030841d0041c981400c0800042c80082103986034000000c44006c03070081c80107403144070b8a02e000003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 228634622 1250 228633372 228633389
    0x3010906050702031e180103110c120408070501090803030c03060319050105190203072007030204091b080a080307031d030c01060e0a1404080a050f07050a050c0609180709 75
    0x20704000c5403d4000c030240186100c1150542c48a0020052503801440f90111000c0e0058124017000d119510980c490720009401404039480c01c40c94840aa10745042040800307401d40700094107000a400a00141004050a0078440f0700385041c010416101c0c00010990701101002000046056404001c41074502c40c5005280c58124000d0500c1806407a040f2186120f121150f610b08030140d989208482c421207040d9204070001e4041206c04403005401440c13450244601d0300c0110142e0794600c110318401d4070405000ca0451035600c1501c0103840036a000c1c00b5103070018042000828051811603602040e2464006041d4160064868030038607143e06428051101181d003040c6000e05620000940c5c00031168100c1940d1100b40382015180e800300f45000030854080480c000400b12005807000e2002d608005003004401321140d00c0c190402e0b1001c2d134150f4003a41c41d002c1031190910540c00b504000369411441c180400c4041161100d0304030317803014138468a02c0051806445195808040c00129 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 228635872 1250 228634622 228634631
    0x30c031401090212030a030b0109030206070b04210302120708040b0c0d02070602030a2906040b0c0f0f10181707030c0209010f06020f0a030e01080c090a030b010303031b090504090203010906 83
    0x21135103550381e08013582540120303180074504134542d03005100d0a41240c2c0d00403c40f500d0210b41d03944060030a00c0150044a840428610501159102640c0c1400d002c4003a074005807130301b100b501c040b03600f0034001e07088030b0a00c005a0103210124203142402ca034800d440e030089541d24030128510400900c81c07004040d15851020041c030070050705a4102c2004486084406401050507003148884520f0b6520b40690000c1e04000030000541500b0180000350b40100c25900305050400c252801e00e1000c00314500990805805086d00c446581320f1028820a01c004000f0000e0140e5100495251309000036000c43c407000c00c40788101441b81740340150035a4041c100340d00c0395940d00f149003d41c1c6250300990b405401003001c0c6040140000886100f4650103503501031103400104015200d074000500010036200003009401241c0d217030403c03a040214440d11507500c8644c51800c0080c2215412080206488070001d07588030130070b070b00040b08402c0d070b8411500014a2a502d00c0003078010010071000400c8079080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 228637122 1250 228635872 228635899
    0x6070c0902070c18060510031508070305010c020f07030c0e060d02040911030c15040306150305030a1e0e0109090c0507050604080703080c031303231603030b0a030c0314010902 77
    0x4545140d0403203c82800010a13202480203002c2510f49074010290010701e400c01300d00c8451f21035008060180d028903054080c1e95254030000d81051401e802c1642c03aa9190703400c40c4c6103030f6810000c0c513004007134000140140c1c50540d034510b440c4103c036120b170b600d4483e1284c01042e0641d590103a014111580108100b1003e820384c604120755040d400159446400341010402181c242010182e0098a403920301c00e11306030031030360384400610030a441c08900b014a2440840061030030002403006407615101c692240020025130301016480e41c124100300510551481a540d0b0010004d0040d1500e6007c0480c0000106008403058040c5032006840c1e403055005000038082000020148103010b03a840ca40b1a68030342c1c00d50704152206603404c2100052079886100403030301c105100b280a01c5907503c3d00c030100024040300417642c3c1081c0703401d0203a00e80c1802d8a40425400d4440e03406104000d0300d548400526503121700103800140d10003d0709135404501803816658083d4402d01d4107a5004280e2000880e6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 228638372 1250 228637122 228637133
    0x150f05090c04060501050703090b07060905100209041a1f0e19140603040506070e01050910020c01121e0213120308040605060607080307050901090f0605210603060606070c090207 78
    0xc1d601c0d10039004038a0701e580070540f948103800b112950394164645825561900d08400402d80c4000700c143ca266a03036a6101c40003607001c0c45004e80f45400b0b000c02680781d0542104010885d8002c9404a45e01524055034605c05c0d01e5106525900401d450300000e0f00c3c440718501a12942c40101205070320070241c2d03000014078a00440c12806a0344030f00407022075411500140a6a0300c02039501400642c04180052001881a41710705424907040c0350450a01c4010720200c0c041c0e071f60941200c40980c01c100f018001d03a507406100060300e85413886090002004c5c01800c025105801050010303001c1c0c000401248184a07900c00c00700520a00055140b20821403c000b0301c00c2000350703802c4500c1c6080c0000f003041c0d07180c800280e400c0d15400c00c12492654895200c04d0700c480d4008400d1905200007220001040640c00701d24034024a02a00c0303066039041c100c40c4000048009d0322a0b00340d82c2c40d280c001d00c02c543d1000151940e00c00001d441281d0750340d031982060700440940d80d000500c65400081c0d00c504012 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 228639622 1250 228638372 228638383
    0x13020705070e0c220b1c20030412030507120b030f0a030305010608100305060105010e041b091d0f010605030907080d0e0a050306070c06020915160b01050108010b0403150f0509 77
    0x44c108880c00c0310881c808540c3c8218280035104180b040403060000120b52500003880d2600c104004c0b000082c20044011340c0760080300810800400d031400401008180038900b00c80312a8142186000c110380d103040200501020011060500e05c26a01c3c81d55409a840400003a260702041d001103030000381306841d000707005e05000d002701d42c0092074030360204134041580d1000380d05595002028052aa083c8401140c141c000480b040c2d51190301c9070200340113900d08401d000320704c907007959812107610b06007960908070f074440c0200c0c40130351400c01303040000740c549003151503056070302d00d01e4642d50369119404140d2818440e50030411a070300034045101c00c410b400000f1282c603800261600c04126646408060715480e04491140c0410b0b49400000c0009449a009180d15600103020354046100e501554410f60408a809030034990140411418001000140c50050000b482e2542c095810710a034210360f400b440c48000d141d10b034000f01042420f0070340e0300301c1d8008280314042002186000c01c10b00381d950 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 228640872 1250 228639622 228639637
    0x215160905090f010308030703020d0e0a0b060a080a020f040207080a02012c0c0d05100c020c0f04020708160c030b2706010b0a0c080c01021209100b13020705070e0c 72
    0x24089080081d060424196551140c0c1d0400810000c43c2c2c41e6864903d01544000c0128040683c20400d40c2c01117180c620a0449422005000341035241d4603140200c08242c0190180c1e103e50480c60042204481c002030300d41302e4a41c16905d41c02c8504100020401034050702c1c0004100050126844100caa4150b00401500d14010310141407032441d18000e014504801d00c40b50601c0d04034495030310030f9044c007141d2028154403420440300340a0303482c80318170304480c10840d450b4016041701e06500c099290030140f54003d8a400c507400c40c98092203644002c2c0300d1007411101c101286000c100c030414002420b00400046403c116081030746d18141d40c4c92030052041c13624070300c41503100300350b61001484009140350584030035602c12460f10001800035034050071500011609518104849401c2080c203002503e41c1c04000c80e0784c2465800c140012a0405490109840c629481d0661540065403015100d0074402d540c403000694840060922500f040c03083c1d041020360717102c05024002444095801417005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 228642122 1250 228640872 228640877
    0x20f04170606010509010e0103090507230108160206070f2102040303030e01060501081801110f0301050111030a0e0402030c0d09030e0310050f06040222230105070b0109020a021516 79
    0x5942d0300c000560b4540035090340c190002d20741d402619150f50003075000d40c401d03038015401c80300056640e07044150302100341680d95442c0116101c00000c1035800c180b000d500400e09000854035140c50740b20003942c42000030f2015003082100804200c0d5103006c0c000c1d00b240e0300750880d8012034181c040034080f006544240710480010746444440c914004040c480c2d0300035184165170740584c5458407051110707600981303503019845558444000546220b008001d00a1011111940e40c0b00d40c1740c00c00140ca01c0050019038030b02c0340c00400ca040d0b0b110750720049890303207020b0072940140c0b07030349814103210341034025001680c151a24207580b4130141070300000c090201060803021181004802052001501c1c0160707402c3c40c81c100c611010618502e0541c01a0819600c07000000043d040190114a040c1c1c1c4107a1006400580e68460000083d12a40b00c6800f411000e003881c518001d1565a940b20a040501c50103040b10742c0402d20411291091101d05591070621200c04101e040000b82d40700601980b0054502 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 228643372 1250 228642122 228642133
    0x606090703020c15070e04060320030303070206071803020402030906041b0807030204090206070f0804051509310c122d0b0a0f031208060316050d0204020f0417 70
    0x250144030b8002c9070301000045004e400714101c0c2d501c0c41081c2410240c031002c280950180090b01a44462180500450180c0e49a0784010007090101c100c40d000880a2030283c1c00810410011130340004100380c0003809481c000210000c08981c409829041d034000070742c0280000144141d040000503c50301a900540c00300e44000c2041c444402181258481c0d203285c1d4200c07460070005450141d1219a901d4006042680760200301e9540a04100b441071003240e4648001c01d050296062004a0380c48031907500080a10385414840014007000302c40d202d143d990040405510102d1a405d600b01030b020b000c414080c8a00e400300358015003101c90f4070141104891078001c204d00303551100e000b2500707090550303041ca00744c0a021146c03150103440d035504000d0f045182c2c5000042c43c082c031840407030010b5004440c02400007080c42c8000300f80707080241100741f11345d12005640302a5000e96000008403442103c001512044510205001c3d0080d406035181c62880440c0010b080f41542c410001e0840c2e0385000d03a603 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 228644622 1250 228643372 228643381
    0xd06080115050a050a051c050a0305120709030b15130e0a061103100b0c07030206070614070309051e07080d021c0207120204022a07061815140d0608060609 68
    0x11200c24403401780d108000307003401c00003401c0c0385400c011203118010804c0030b1616191074030341c904122440110700080300041c0710641c52030820300ca40d402244500c1c145c0d900340d00d10b03111a000b410004d0101c4181105120403541991f884d01000f683e07500503e1010f100c640f516191450b201c90543e0800e0310020704220042000e42d0a0b4002c481c4600002a60280c03164104140b80d100d07604040c121100380d1041c00008070140e660b480181c4a0180307d80c41c0829008101404001130b0a806000d01c0f0031b1509046608000600100e200302c0b0070405020741000440040b41224a41105648812070300d00440300000d9030241d0100c4c1206401041030f1411041d9100c00c04105d94a018600ca41051010990260360052805400810304102d007600c200c044000c50700882800c80009041107210f03540401c1c0e040111581220041c1c2d40e40ca241e003130310f01841d0300c4c20480e114400180b0740b0300020405801030000000301160280c880c180d029000070006143c441c0d1a660fa00d89043d54800c2c483d514420001d0b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 228645872 1250 228644622 228644629
    0x70603020c060c03060310020708030a0e0c130b03280b07080702060103030e0103090203060709050301060f061d0109180203101a0d050405072112140304030804080d0608011505 77
    0x19511941010010321a698030f00203c074903281c0010f0225985809405046078480d541070000c0c000c0e0b940501501c0f9501e05002100d8411100d180c08201100d40225001445942e07902c0300a500b1385140c00c0c0003040d00e07003030344000a081010081104a21100051a0b03103181da01c120741c0e04038190302c034400e46101c5403507401c001d4502030811074204c0b005038403903c01400007038490301c142401e04006040128220409034006070800604440c000e0004000020400c03083c40c2c00d01480e00202041001412000e00b0480c000307062220341c600246808103d01942c145c1079205811034001490b440540301e407140b6881c0c0f0010b0280d48252307480c14800091100109480700b46c11003511540c16070520703491409030750700006d4000e424001e01c207a44034040c411000520752440c1d40402c403002d411000813002c040340d92034418508514049088208400f15488803c003040c4401100d8000303030141085c2d1a641e68524200c910351080c0004000ca15080041c0082c0480054000b07060003040442000076054852061 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 228647122 1250 228645872 228645877
    0xc011a030c0909061803130608040611031302040e03250309090b1011010f020f070510050105060909180d090303081302090a110702060a0f090906051516050a060b0307060302 76
    0x4280e004000030034002081c0d030361180030062085c000d0300c0c203000002e4008609140c40c0c2d8000004519844200400c01c0058401c104455010703801540c20b50800018490042ca00820001d001b2a954950070701f50f040c0401c10341c1d50350fa488240c08051100d510031025004006100c2c02c802080040d8404640c090710b81c01000708080740035114140f42c2d404541c048a100010340382e0006503568500c0305054580300741c001000d8181001000b07035a0380003e440e046103001c07116126224072502e80030040c0202c1c3d41d00f4084403404041120024082c4c0c840c0e0910081110000d20800c05d42e00c0b41c100c8500c81560042e0f52801103a002c4d4644514581e60010600c46c90340100320000d40c41040140051614602e0b80e209071340d01c0c0f550795003150030211131b030f400309020f43d102502c5280030030b660b03074030152680b0b0380144190f006e0700710380e0b405004003072800d00030401001c039020718140707c5640481c21080c40c0e00000101c03060542c000341111055540c07410b00c10001c020100c1d200e07000b03018860b808508140203008 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 228648372 1250 228647122 228647131
    0xa0609061e0b010c0605041b03030206010501180510030c09080304120b010602011814010905060a050f010f0b2d1308010e0102070b0105120a02090106030b0a050f0310110c011a030c09 80
    0x44105030350381961758240003040e00034011100b480d07200000d100c0c10f140400800003c1d6109800411582d418000050003000c400990703054000403402e020302540e2240c40b8601c009104e02c1c14003013501c40411070b054801514640159902e84008500040d80d200d080d0124000c40e8001c00c0e503012140d0700e6075001c074240c50703c107202040b00300001d410b00800201305445c40c02610058a00024001401e81d8816041c85001e5810304001d40d1540c00340480c61260b41304190060001004540b4124a0145c14114a001c0c100a00a03144c00800040c0e0000c421404407220060134a04801e94034200700c04804070310442405140c0d401d41c600008601c0c007540510840d02002d030001d01255950307207060308011101060038843c1d403803409403d08080050300c0c1c10b841b041c082c01640d10082a0b2480860502044000552200c0e2040c00e14104018031518003107045480b41d0411400403800309003900c3e80741f910f8420084030101e90340c40d00f120b8400603c03240711100c1c10848114103456130602003004200c03595000342c0703 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 228649622 1250 228648372 228648377
    0xd05030307020a0309050a3206180a080f120f0405040612140607051204060605030102030f0a0c0918020a11070602030c010f0b060406110a081b06060405010e01050d050a0609061e0b01 80
    0xc00140140a4441c001c03084d241141d1144a42460303200108050350841102c0d9184c001d04020100310514110042f00068807501004160041c480700105948560441450200038000107401c52034041d6134044901816011300103208066031f495801a803d04001425516000402e03041d064080e00030035141e01513021540c03502d0030407020100d21007215201030030840f1425655000010b00d9102800030714426034003040001c0461034103c80000580e29054a00020000e40c50310030701480c0c01034201d0ba401402e0144c00161030780c00300d050649402c00d1018480388148070b90640020070950010040494800a000920480d00424075650030f98941e0800550300c10390a000a211551242e50041c6952001c2000c039400d05030b0700e8880207420340c01900381088000c08081c28100061040103041c0d0000000d4800300a1580340944e07030090b0810602800e44a03440c01e849407403c0c024104454244c1d0794118004001080b40c0b490600d00130089800044904100d03d40d0341d407198042403007080b0b146030041c0c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 228650872 1250 228649622 228649649
    0x61501050319020c160f0b0a050f071a0c03010609170c150f070b060f120601090b06090315010806011517070302040e0a060305010f09200d05030307020a0309050a 71
    0xb01e0240140d00c0400b14400d12496081c0845002c41d00108081c1282180c0280340443c0b40d814200300400c1003882d5000550b403000c04028815003168810222031140c0a4580750a40300c2e401c4d80b425a048149405c903000880050314103100c0c90268040003141240c400d03443d1042000d50310005c3c00c119005d18400f03952207401c00014000075090028508406248100c9603a107481d08507200642c268014010a50361000c1a030100310003414102164201c010048540d07000e001d040d07101c440da58203014020700c110f07680c07980c001c2c00b403940360f040544041800007000c0e0b8200720030b22200e00c0d000103800d10904980d4403428000161001034038085520a00071076403400400e0003da40200100345015200f42c0800d0b07401c1000040900301d5846103802071400c410f0129035146103003001401d40b003c4880c1064024030701000400082c90312180341c0e10211041080c90802548000021640001403a025140d03010000801462550200344044201d100313486034a021350311041401a400824000c0c0c2d5181e002c42d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 228652122 1250 228650872 228650881
    0x9023c10090e0907180603050d08010509060d0204060b0a0e210d0509010903140d080a050907060c050c0301061d1303090509061302130e0c030408031f03050106170615010503 76
    0x2140b9502c0c0c2d000b003030001224280e5548204840525100e00050000183e03504401d0003006418003c2c088040410701e0a8680341d418400000c1049101500891107010079504140454455402120052060560003a2910110b00029025424200801d8400d000d04100c2a0f40714484850324410040d1140051840940720070041e5510350108440c0c40c1484520380c0c0000000c1d010300000021619440c01901c130300500320380098110bd40203040a000c0c0c03414001000703040d000c00100c0c0403c03a09a480c140c00078805a04065050514501101307426508003103010646507140c03041a80000b568000708012543c0c0e00b01d6000707480c10801001000612002410410b42c500400355030740051004045946c0917612083c0c1d8801c903407195100e451b0000c1125000c00c00c1e0010340820991091604041da07165240541c0d42c40e1440c4070060581c03104d44d6034420540c0c40d01041660000c00b80d54060300030480d054981d001680d12801e42c8460112920400300000e00714031025040000070791040e152141591503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 228653372 1250 228652122 228652139
    0xa0e1206040b040f1406430f0306030803040c0303020607050906030a0507110607120b0102011503080325030b0f06090f0f03030f04120314040e0a09023c1009 69
    0x1300594255440115103845c501250820b001c1d0b140104e085e07000746c0185000755200d02d45003108048405810640ea40d1401c60140e50081c00031070728070304c14a02400581282c11043d801040180c00150403503e001c002c010400c03035020411800d490083c1c0854507581ea60b03a03400c0395548101c00c4080c1e0040001d00219080d1b02d0300d81c021940001660a00a1041084059141c648001160018000341c030300500d11840140503c94458500d500388002d004640000c00b125004c03103031030b1000900100c030006c006541c04c115290400c0695980580300c0a284881c130b0401006042035003010303071043c0001078000c603103458050201c0f0301503c03000d842c00b41c480d0180010041900c0d1440701c903540500007040450081d42d0407000400150a8450503d07001a4080c10010703c80c4030881d418810300c03a0104402d01c1194003d1940d2070f44a01071500100c1c00329058800302d900f1284840c0e042c1c2e600940490b030b8410032401d1051b42507101c07000c81d420b070300002280020041d01c1c08082c0c40c0c03040422000c803814480c070744 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 228654622 1250 228653372 228653393
    0x1209190f051c1e2a0b0f0c03120a14010518070516050f0c0108190e0a080708030402040506030c010c06020c21070311010c0504090b030c0301020a0e1206040b04 70
    0x100386114403110740e0a5502c456450780c029040b0100c12081c5106210f04005498035015030014105407103034141c1c1d40d81002143d009955000c0d00c001080702050300320078044850200c50a0051803030903207440d0051201c110101400640754404491700707210741519100030b10030195040b108000c004072903240c000742a90000b000c005d8000d0742003201c100101004000f00c0c003000e41c92a882200241268524407061904200000400d58100807442c014052600c0d4940408815541606000102e00d10741100c1180340802000d4002c00c3d0000c007240308000d200000024602c9a0300a0750f00780f00d50341e610820192203200c0714180e5030205140030002c502054a5074081c119100d01d000496060340d0610000c2c0b200d0740b10540312103a480300005504010194480d8808a0b1543c40f0b070000d001760803902d42c000d0440d006501803025215500d0b0415803d42d5410803040d150840050021580c810382204c000340103e5922148501441d00c1e00b0140c010b81b540002c4452040382c0281d0900c1e17080e11240e0341d000405 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 228655872 1250 228654622 228654649
    0x70b0402030c0a18060515070308090a1b05030d02070e1b0403060e07150219020907170901052a030604050c0409111812060406020c030c1209190f05 65
    0x140b180c01105212074444900d0030001d490842000709401050101394000ea0b100340c0c10150003082d06601e20541e50080c1001e41301482e915040000d02a03507007514040c50b07d440703840040c015000845100f014806240d20503001d0314000d4003602e0760702600300b400f82e07900c002c1c601c075103c140b030300c4880001c1804000700030000c070300c051491259180545c2d0b42c44400c02d07160000d1490f800c80d001100200105030fa4008401002c80c41350000cac01030603104030100c06011681101c0a4081c60444000071440c2e44910700001071002e42e0843c01d1883e00b44202e0783ca000305021a0f4910014410012600f00c0855000841010040a00210346584c0e1103009001c06000003900018252105010118484a86010b0000c156107050940d61302d03101d184444d42854000d0b2400180200c5907803844050090010501c42ea02941100002d079980101d403080038554840c9160284039409009803c00602c1400c000074003040204603545523215030104600315002d20300e1320541d42c620008600c104041e04040101d907004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 228657122 1250 228655872 228655879
    0x10b0705070303031d160503071205190f06240816230a03030806131e1109030a0c0e09030301080703110613140405090f0d050c210c150c070b0402 64
    0x8076940745d0405441d016840386540400810044140b02a0030200000741c0100082e051080d0f000d00c540d100c650b22403249114bc1c640301e402d400d44120a12841440a40107a58080d904100007441c1000380b054503607400070b07030340300450003c0d100196140d00000c01204404c1005105200e0904c1c01c0c01c956844401181480d040112195003041c0d0307030b550405220015400398031906101d20303201042201e698020403841c0280323490560111141000201104a812801500020344c02d0000b14a400705000300d060f41070340b40c402e2215102c10803d50725009011510143d02c48452500c0c0d110404d516030109007e1419146c1c4010800c0020810b1046038065100000d40600d28040303140002c030a142c0c07404d41000c142d4281341203064400f401d044c0304e0190721400140241482c5801048100c0d156840c0300c111104110703010030720004400b02407280c41d142c0607200c02c41580030018024022125048200043c64600418201a6440c0380032481c052098403020021450003d00f546ca0111104005c0d0040e82c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 228658372 1250 228657122 228657161
    0xb0609040e0a060e0304060810030321090213020c010e010e06040206030c040f0f03020f0301140a0e030d14100f14010507050f0a150e0a020f040209010c0b1905010b070507030303 78
    0x308465110358826544c00f40051507807241000800741c14102c0142605560075150407080010075804a040c0032440903054003401c05180000d03030a40a4140104065845582c4c1c940303140f81122a40c0c0145041d071404c0b4001e0018041e4101100d00720b0701c0e136444a08690304800009401407a000c4021740d0b200b842141264103080c0c959031003041054035a00305906a5500103024005e51409600650004e0701c00c038000d116015072200d084411110151000c001d090320fa01c40031200352814426a4020a9514000c1110712004000320b802e00038240c8085c80a101c1d91080401c1c4c01d02c1c6404010240c0f113104280344100020038004541c0e61f84444c20550300c1c0d0003001801c00111109002061455005500c44001284004460400c503040c20034032221580c00341008100685a41153703640c2460121001070303c0307541000060703a02041d6440d005113103404007010007036202002c140040c80d20307003445002c11142e030f00c0340d40d50241c5105070240944181d21503041000005d00c00e820a809512801d96802d9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 228659622 1250 228658372 228658393
    0x2a0d180f05090f2d0f010503030a09050f130e010b09010e04120f11012d061208071106030a0501080727150f09020c0c040b010507030f0201091a040b01090b0609040e 72
    0x220039403070504000400e581148184985c60350651001c034054034044010b146005c1d26044007400c45400c500c01d1602070b215040036114541d88202030507111000c1d0f8803050140342030402c0e2560007440301406141c03040c03008000100f0750507003440c6c006109c0c580c000458a4240b0414070300b80c030302c100181166810003032001c011240302c0c41d0a001d400002d881c02e021000c58440410041d24010b040c42e001a0246860301000b00008426402c03450346203504101c005544607851f00f04a10701449801510360030120020612101380540d0717020504a941110560b6001c9403102200c0e511096950300a07090f03000b680c06c40480c041c11a40c0070205042c82c9841c032804255960b0b03565840d400e019403040f106c0035808648040c0034041849000002c400845082106a58210011781680181c0c40c024080001108100c49964000d5205d07a07002031b0044403d40ba0b1242e5649030043c2408129802c0700c07603661480000510400c00d004042d00d002c1e0042c003460800411200380801020700200c0d40c0e002d48a84410b82c2d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 228660872 1250 228659622 228659671
    0x1140a050108070305123910022b02040911130905010b0403020913020a060309060e0c030304030b0a022502041406090a15120803060a1205032a0d180f05090f 69
    0x1c008004140c03180c80c52040b10700d41e400c02e03483c0018100220f0041107164144548134403848078a18040d00325144800c480c452b803000a0046800200d100381c60420441c4c1c45182d11030182000b0a0050b2079250425100d05030902500c1003841500520081800144014903001c540c1503840240c00c003018282c0c040580004038050b05507402303000441e55a403140824031007180124079007030440000520764110340a021076500c3c4264031000c0c0c622402c640c0071400c4082e01d03404440e4401201500082d440700715440e0320070040070380b8004910942c0b4180d0325000b54407900c00f420303102e14030043ca040000c0d6181700310107010b40541030904041c1c01c1c02d4040800c0c01040440c0c03002c8481d01480030162a45030000620800040c0e40d0059602928054002c02c00030350000100d42c522694020b00215440c1441070311514410403014140303540c015060801c40c125030103070b0501c0001030b45500c09880d041c2d540c482e1310482c58190150310741040140700010b080c0055403003566004813403001c10182072031810851 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 228662122 1250 228660872 228660937
    0x40e010902030a03230304050709020901020f0d12050a140408090f0901030b060a0e010311130608030304060c0e040c170c040b0304080706050c0c06042301140a05010807030512 77
    0xc401107044e0030313182c203201e118848014181e10350070401e85e859820142c8900d0381d5600207100c0e4240c91034000802c15001c0c0d100b03001c010700030400c000071103001c0c16620001800f80030300c0c1018061030350b1134000090035240543c0610341c0c000e64201400c076000c5d12140c1b51108194018003009400c2243c5080071203258880d40000b9000390b002e40304203a641c1c1050310410001a0b10355100001f903440a00060002c1900e4030340807460017904032600001c80700f1192907400942030382e6100e250b00c1d0001004000a018854000ba4205010342c0ea0b02d1080d0302441c0f041200300d64100400c03d00203082000c00340c0640910026854202d40c41c40805414582e0314501d40242b0b6104903401c46805001140440400c80035000c0c80b6048103561019604203100801629a90107009001401c42c0d0592240c0c40c0d90a02046044040e0000141c001c0c04850138021071001c4901017a650540254a80000000c0401e8085010700c145c0e948034018142204107041da10304030350002502554400a651101c0c5a52000b4441 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 228663372 1250 228662122 228662143
    0x1d04020f041403010606050301062111040611100c051204080f070c060e010503011406031302040c05090f060f07150b060711010324180f0903080f01060f020705040e01090203 76
    0x302c50720140341106160941c5d51035800b0909126041c001806013a801038414001110245078401c030604c00100380c0e50241c20003004400c2441400940480e609034004000040034501000319411388422698003400c41e041024498001030303091103014881242415002e4000d8001c0401a081c03c0d1081e4442e603c5600101e0f00319500010044204065a0092000c4142140900380a415980b410034104006507000400f544641070000005441d190000301300310303035182c0151082048021104014103180d011a442078400d0b83d884640a5a51070214100e40b010103d00d46154180141641c43c40c2ea500140012a0b105d40e0301d41c413a03105140c0fa408064803080d405904050360f0720100300001750444100c24551809101003078000d40d07641030700f8645a42228002c1e50064070f444c00341e81c454401800720310841000c460030700d10f42100345a4811426800b40303c201040550304c2e6a2040180c0c0c0e9002e15404500250304801410002e6140039070140701413803403003800030511540c550b00080c1000e40040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 228664622 1250 228663372 228663389
    0x705030718170606010f02030901082706010f0807050301060b090405061503090a03090b0c15100e010305010603021008090607230d0c0815011704060908070c060206161d04020f04 78
    0x40810610790381c00400042d1b410303103e0010390b00c2c200c0d9803c0000c0140000070007110355a0034030300110f4501030707403140c441d888000a202995415611500c0b9540c000303401d84941395a43c411100b003c1940d00c1c1c1807140034100e030b032801c08851420306181c05200103404010450760740700881d0a00c1501d202601c00080d480342032038402401c800e03907240c5406030642106400002c5004014481074814a50000311000c0c0700300c0d191103000b9141c1e11072101d1408400c4236001140791005100c000030401905400180940f8400c5403ca264010245070403551404121041a981d40c010f0001c504094056184002c0902c054031b5085030b2100090350319401a4444043c50450955548840c10001e40c0a1710a80c0c000c0c5600082100340210070b00000d01c01b0066800c5040504000000b103030802400e603002d2428164000c030003d440e0140c03418001b841105a02c282e0b00503000307600009540b0314100ca0004070340881c5845415680115a03400c2e0042e03034500080d5074006900300700c80e45080b80e524010b00001c10300b04e03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 228665872 1250 228664622 228664633
    0x315010801060c0506071d0a06020a110603190b0f060a020c01030c0e0d11040b0a0b0c12070f08160209090a231c0306030b01030809010314070503071817 67
    0x14001030280005910100800c03180340000b600240b0b020660300d401000c40c0c5003200d02600c2105551101e00031202001da449180c9280c000340c16500459042c000c11300681041014000c1c400900125100072543c20781003040300ac0d4171241540103a40151080c1001424250155242c180441c25950003a0009405a4000380300c80c0340c0781d82c0c10b018203012a4107626007070100c5407410b40414404100044002c250b035640411000560300d46500100c810b03000144600c84071a640c500a5140354004170409003240242d16800a0030780e94003084586e001d41c03260202195032010b0b200d040300d581050519101011709655403101603a50410264002c459083c0034162006403890001d070070441d1700d2b181c0301104642c81c42e030449110010403101504440d040011046080300c2d00118020145504010a0a5010070011061108040140039041c03000c1e217040054404288c02d5959003c001c0310010001001000040e902a10902c0c1008007044011080310145407101c0071901c401d0a0421a5005940b00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 228667122 1250 228665872 228665911
    0x20403021c050d030e0c04020c0f0303010308070311030702030a06020708130f09060503010506060a0305060a0909120806330d051303030c0f0c0b04081902010510050109050a052403 79
    0x18003054000800301e0404216480790468150b40360742103400c0700d607c501d071b0101e51008064000d020054024001c06c0c141e07582da60316850440c10640200e02d05400150a5003540d41038403c001045401035a001001869280d21f41c2d80c0c1d58010398880c0f0011190748000b801035249840301480d05c0d00240482c5854003a0aa041088540413107901e40c1c4140c0c440d03810002400200e4a88500302c4201000364640407905695000201700542c00b039600802c10031380f41143e030f1024000761542c52500c46840d59606080c6458110070002c50303041812201f592906813002d0f2440c542c10000b9140324042c030f00400c030790600240110070f900701c4078212100703883c000c0c1d02141c1d201011762503c40c80100503030781c2c24251140500c00800a02d40500d080d40100349080c8032000c541440500005d82d8034642d400c00d0100c0c181c0d000140003d01901c42a01c6204210031018130206256004d5074104083c0d0701e0203441c201c1c07041d281c401004044074030500c3e01e10403008450306146041ca109001035210b6141040e4a8014004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 228668372 1250 228667122 228667133
    0x9041a040e03090913060b03030705030409060e2701110418140f0103030c0201020102070209070e01020c1e040f0207060213060816140901020f1902040614030706050a0201020403021c 80
    0x20760031000c09140d00304025000d00c0366196103070b80d50046504018009001c03091b1405a00600807007861070707031500c4049003403000c02c80000002e000707035648c017002480201d40da403140c04502507050754404405203014489006040b91201b000050880d03103400401c0031217004c030491510b40d02c10b41081e21000020600c040c10130038940200c0d00c12180c00c03070b0081814a03041128500111040c0030040804c072081507480d0540e8400d40580301d000d50001e08050243c20112409403521030a0105035025004141c10a103651411081510611184250424131092031000304001030030602d2080310b61541c24002c4101082061000c0c24040346d440c00031a050505000001d420f05800401c0601d4406000c110f50192540c040303450f064450143c4c050750307114440040140d04002c00320940d000c0900c80c210740145484100d42a08028074000d860802000c5c0e00d13004260400309000e42c1da280c265002c1c54041000c0351080004086c0800a44001130038075480e5400070f52043d4800400802c121410743ea180148803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 228669622 1250 228668372 228668381
    0x20304090510050d0201260109050603190c060c020d142a030304060503070e130b011101090c170f01050c032e14040608010509160e07090b0d0209041a04 67
    0x20b503199849181c0903e0100001c0e40a608000004e04102012941e8080303143c3c980030200201e0f990701c580b89080d6844d010040002c00c8100e6001e8424410100fa0b001e0799400800d1403404180c1000006004904101003581d8842d003000382203821205200b640d20100d000d82e491508001c0000c00500303403001c800c0e144865a504100b0810310400007000d00205155030020448045030994103145840b696000401d40e2807501000615820a881c090145c00b01e40b4540e01204c810741e803d0b2601e480060580c1d42881c00c0360082140240300702d003000300a000151405419258a850500480b10048084580d46080d03c200382c4500c00900c00100c140602000e104800817001304402401516455490140302820406480fa5000d205900e48103904c040d01c60b504480041c00034007009000718209512155550b0f0302c94840c450061001e8003003c40c400084880e03640c00381c50656140c0349194284260030030142c0c08528440c140d10390821284174951a42c0c0240005024080310846903704050140000e84 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 228670872 1250 228669622 228669631
    0xa0606090b060a080406050c0403021309020135060f0d06050106020d080403080a0c2c130c0c0809130c020606040e070f090b06070f0c1502060403121a0604060203040905 74
    0xa003400c0c41009107282d88030328807640c0f1a412072000300d41908c403d54005150300c1f903504041c5d0450800c2105010701c3d4007540001140030310070317a1307214000e59407010000d108150741c0c0c43c4080c0f500e1040101040e5903c20b45241600f11000518071400d20050b0800210101401e540c200d80460310b4400410059405002c9410300346aa801c01e15901d01d032540d001081002c00800d03c035500b9940740c1504408601c0390300715a01d80144c0700d0303022481c601600d002c0722041c170b100c5461034807594260707105e907540b46c1d1540070300703403034024180c5520304000d429564907803031600b00045107038010409601c1881241042c1c059103c01c55425000b40082e0f0625000b440140d4505041c98840b5611241b0200410700c08890368408855800b00005281d0320b03a40e0012709244900308000e0200c02201c1d054a00344540301001d681180c1c20706d02000c0a072160b6100913625150111070241c049061811a8884e55042c3d400205111a98481440042ca4104001289900103800c20801a800401c0a100150440c82540c0d000b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 228672122 1250 228670872 228670879
    0xa0f060f020109020108070c0c0b0406020304080c04060e060105030c09060d020a1205040215070204060b0a020124030309050f12010e0309030114060607061508060a0c08060103050f0f0601110a0606090b 88
    0xd1654002800d98800940580204214102d0200070311901c211100080c240792079207155128cc1e01e040003507a070f4006000d02c0c9c4c101d001d10800030301145070038400c200403155802440308181d51200010f40796900001c00c00441e070f0f0002c01c01030f2801d03500d4500610380c203a402e050040e01c1d55811600104541500c110b0b0490b440e28260610015a5039040c100e0100014404c120366500c0c030610110b800b4204075403040f05003c0d00464205082070301900010032600350145d10b54840202e1050140700d200e00b41c44082c0c01301c1c01524003131143e82000711544000d00000781c00502c1150103a1507036421140c202800d41140d4201184080187c50280584c000111080c0001a00341c00c0c84800103840b03101d0603000814082d981d06003da4003e01210f80c0000800c2ca00e02500c1e03051510050300d1010f00382221700c2c5000501d020000038020340c003c3c031480380203407069100403416507503011055414400141c42c05042c8603a125071881000010810760001d60301c514404540c1e1490700c0035500030b480300035003223612 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 228673372 1250 228672122 228672131
    0x60b0d020a090209060d0e0c10170c1b0a110108101d0402010908060c09040c080f0a0c14040b0c100902010c0308100f0824010503150a0b0a0f060f0201 66
    0x580d41d01ea14000c00c0c1c2c1c111000069841000b0000070301701e8407030700c003031261054200a102c3c84040800714a540c48241c06480e9190b940e20000c00898220040a42c4400c00c50700c0e0201142c034031404403024211119444610804008600c1049840c200040800b2500c1c038132040360412007075910100b80d42d0000f15111200100b00d08040c1c05015045910511014006c1d2001c00101036a105051280c0200106402c2e83e803141070111814459611250000340070350f05183c10100034610a00c261403142070075000c1801c00d500c0780030505020f081c25031040400c1000320140729030001d074413000900c003c081540d000c40d903c007485010141041c0380d412080800c507180c0031041002d80d030000794829640d40c1c540341c00d4070780c0d0b507605418101d01003103600170060100b503645000c03858400006000701c190304482c40b0250300c03488100c080c0b410303081c090040d5501500311080e030803281c061166640390481ca00f100003159020b0070304046000f1068039030080c0071107947c042080000c960004041c0070116254070081c00b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 228674622 1250 228673372 228673399
    0xc0708030405031207060b0603040b070e0105070209060f0409170a1103040501020a0b0c13090c021c0f0f03180812010803040b160510110c07050d0b041101021f09060b 73
    0x241c84420240700042c141c0c400185c28020802154403014403104000d2410352242454103000700700040c00c60390382c0003007001e10060341050341c0224142c2d0b131680d0303000304445400c1d920541405103100d0004c0c1c0c880c0d00251651151030008900400300ca94842a0b6007091741ca944100c1801890f0440e80c2c1c00604158100b00000d01003641e02203203248800750400c6520b19241c5a416420f0064400e05c411003a20a42c0c0043c00f18101800c2d4010030710b01038141e4215489281c800c601c0c1080b078480c06003941c002c2a00c0e402550340103030103007008490000701401d0006141b100403814040640d071101c0111043c640008003d00f1002c104106e081c0500040d000450030182000200e2388184900725910320018103990002c4100b000030404e40007001c50300101803041510180c011891a0041d020f0b0201c0e43c085e030100401c142c10030105510030741c0e0f08035046844944664036422035a00c0e601c0702035411401030458002d001e00500c000218811031820001852412505290049854107a2081c1c800c0004128030b1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 228675872 1250 228674622 228674629
    0x60e10050619030c0b160c140a05030f06060907020705090c0d0501290d06031506050906030f0c130b100c0302010c08070c060507030605120f010b030f1507051b030c0708030405 77
    0xc00d417a00303810f486540c1c1158401414001c90351100040c07054801100100e224145800c44002c092019910381d9401900c0c1d800301502c032300080e040800c80b6440355002807014030300300030b4003500f111080c0160b4240c50303100e1b004a10040790894043d542c08400180000000c40c292258500502d04203100188461080c0d00070031030303006442810840700c2008220070544600c81c2e1301240040d0740c0b1004003600c1c281e9150040000c2c241d00c1c0306145c4200c4001002681030f00700851080740c07100c50100a030800d241c0c5901048044044611103038451903071420400c1c800e886a814500d01d0609070384482440c01d035145002420358900d480300e442000385c10000d0105050300801c3c0c001c80694070050100c0c09680c0c00f002100101180d0b400a6400f40f4a100310000c0c032a00402d030030220101c0300000b0b01c80d100071542455502c55502101d680590722600c03904880380d01c0d00380c031f0341e403c0200c500d025131520641600205011400101154480c0c10008010785014000c0007654001c0044c01c020710308051515001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 228677122 1250 228675872 228675893
    0x302040303140a05120115030b040b13090f06180b010602010c050306010809150a02090a08010501060903020909030409050408040914010b0414060c0106060233060d060e1005061903 79
    0x61030211500415401c820f540250143c07101c1c24501308460600b981e43e44454840d80d592000310f280440d19020040c507040c1407600078034046d02c401404406174118078421000082c00c0a60701520721040a011450019a450043d01140e5021007085642100c032810041d107601d4041e449101035a1606400e01483c60300541644da06c0f650900f004070b4555500342034a801d0074941c0c000d49407a40182307010000000c8003603010b480c200c0400d54101102c26103901510f802c90b0401e00611002c1800030a081005141c0110110340c001e050000707a82c1081d98803050841070b00c4098904030b0380c0b140042070074000100d0074030605082c1d142060102c00c40c1e514245401c3c0340c610a5000c1d107102950038070803e10403a201c13142111541961134008028040d030312030740251503818001048505400d60049500d00c0b0120b00c2c1e03062034440041c218421f007501d95804018000031004000ca81e020303203a030003880200c0c801740700601c3c591007140da0129031450302800f04200074205100c5400440c469000030720100324442d00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 228678372 1250 228677122 228677147
    0x40c030b0a05280207050a0c18110f09031228022b0908030f0705010c0c0c060e010e0402030f060916080103110102030909040302030c2103070e060c03070c0806070302040303 76
    0x414240d0030510303070801c8000c1e1185d188003900d280f051610700b604008861410600721020200c6c0b00b210098100503603401e0305d0203000c4450b11800305000b1811240c4e14000240600e00c1e004048801824480c29480c00ca60000b01010f00501c2d488c60100c00d4440c880c0251381040c1e11540302801d124050312543c0b10003031a01d408140c20201d01d07482d8507008a4054500e080150030000d084940700d00c000103244455030b12283c41211503508003070140391514050b000004006a01203078944503503040c00c00c100c0360007441600480c100151502c1c0704c1c00076110b61001303501840c0d020341c41503168a000424080304c0d07a40540b20f44403841100c0000300e400d551220b0100c0c15203501c484842e240508400c0101d01d14003888071015409850b4400740020190000003c01000000d60700351007088200da08490842e1040c0301303c0c400074020402c0002c002c2440b03074080124a1500038026811311418011441c84d640044408641085001000303104140d03040049544c84109841d044d89007070b007550340c000c1412a03800b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 228679622 1250 228678372 228678421
    0xd0e030d0e0a0504020d1a0a03080403120e0406121709010504091503060219020d020a020d120c0c0815010e10030210050f030a0c0e0a061b03030603050105040c030b0a05 74
    0x1070a50995900c000140004050040080d51162101615903008203100484080001c441c0421841603042020640007207941000342a401d051030b6071180e5010900000d0000200400c15070750308290b603540e109284c00342212803060318882ca010b20307118542045e03900c40c10741461001e0000d00c0e078680e03111045034190b500030440403640c00040700d0400c00f008183d42004080c5030020403088588111401103010140003903003160000460014181d8440d5030002c40a034020003000080404580342d104001800262440c0c26174408080351544804004981c21490f03a0b5002540b0f11003506030b02e000114090728039038814000a0414100d00b900702d036036503c4000d00034001d03c94031a0480b80a14244d03101c006910050a50340d19140410200600081b07a0500100704130340189810350404084a00a4501b5500d8540300c030034540c49400da0030f200c403807021400c16890f000003200081d03080c0101801148101c14903114107085190428031000000c241c0548145048200020502d14400805d412500350 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 228680872 1250 228679622 228679637
    0xc06180402070512030609010b0301060c060207050a02030607021b0303090310090507030f080904061401200316050115241805090f060405060612160c05060a020c0d0e030d 75
    0x140081000380c01600c0c0050894020811301c180400c1180d401540301d0441116010703c03d03070701c40c040c002032800280500030000b4841c4442c0000111107034010302206005008031003900005e64006031400004494020058000300000203299001035451804a08200c010b07505000001d000700f0f648254240f02c1d258100e0b1105590028450144001c074040c40d000101c0c5403540342941400c0102c3c2e0302019040d0700981c85c00c0310004105001022078240310360140d5400d440f074109082c03412001810f80c054600c05000410004240b85001010038680d85e01c103400209440c1d51000441044460540c016504e101d4035051454405661071003030000402a410301545e0b0b8802c03048805000760071a00041d411254000a000c5286070610503144071380c10032941405669200003c3c0b100d50b015124046200c890039002103002c114006860700c0040c1c0fa1858000440da80c103884091800710f040da2305080e180da0000344540d41c1e020500031600d4843d01c600300b1428043c0e460002c6036850b010904dc440400205 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 228682122 1250 228680872 228680917
    0xc030c02151503030a0302040e010605090f120705031609060e010506030a0c02070b040e0f011e0302040e010b0a0e010e0f1e0402210c040e0a0506010308030405010e160608090c06 78
    0x3601c1d840b05211070050201ca8849284c410041d00035401406065102003c220001038628420411101c1420000e00901c00a40e450320502504242c0c40360745003d2805100350205017510104642008244a1603074840140c1c5000d400d901111001c2c2c0201e02030844100060003e516102d045075008121100c00040021041400301c0c20001d05401c550140c4100140000d115056091254080e0820a444803503e9030b07140c0310000c0b600c07402105285076010150041026103020350250040c541e1800000c030300600e26030000780e552042a00000320442039a00148090301a01c0e0869900480c4a02d844103181412800c0070100c1c1c604002c0c100c040d0b82540e000600719100d04001c0e410040c42010080e00b0281038005003502e80c0c031500245401076160848035a40010300082d00c801c1143c1040103842d060742152520070b0654801401a44c69640320f02504202403001c00c0300d0b001000c4810b2804480c6030910000030035911010700030301c051740e100d07580c45d01c7d41e5590042110740d11070510051083c648030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 228683372 1250 228682122 228682141
    0x70c080a020f12190c0c060509150c0105040b07020307031b080c060705030115020a15051e0705070210020102031510030603060f060306110c030703030b0414190c030c0215 75
    0x70b05800d5070390140140000b10003100402006010141c81d00840503804400e072031011140c0b41c4420101a11450825008000c843c4c00b4100411078000003400c541148072440030303182e805510600035040c550307546000304010f10540300c02d1690400081d03c051407034002d031500c0082070035a07010300c1d900c0b010802041e00810800120f0031600d286010005a620502e00503030082d0031070b0024450f5040d1000c0740800113030350a2001c114404107603030080f0075031221802c0c140000000e0000403c0030f00184182c07148000500b130120300c00d42c4180d07413036071302c0c141d803403c4600c18480c900f00c1100603002568010b206001c0480c5c0b00502a40850100762903150388241c041034102d01034a440d80c0040d02c035515014080d0318040d455080343d0142c82c000c9a040c06101403400e1503265922565103c809140c03c02c3c001d07403001a1203031b008001803407001000450b4000084004859680c400d44001c403115820b91031140c41e4400d01d01a0303c150558500302000642c201c00d2002e91147c10403490075403400e070480c0001e011031a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 228684622 1250 228683372 228683383
    0x30b0c09040c020601080f0705090a0b030f070b07060c0c0b1b220512030705030d02031b0423030111040303051309060e011818020607020a1e0e010e070c080a02 70
    0x200014820300c40c0082005001c4c0d1500e4003800707599442d01030f82e41840c5030100d00085441c1100c0d405041071085550b0266504024003800f15200e41c14010010f101e03280395803c0012501401c03045000d281c5e10300c44d910708201110300c001c0701d44040c8165801c8141c0458958000b00e54032440b2406048640e02042450310003a20a812080c2007920b11034841107070000314009640140c2d40280c6034030b601104584a25540e034092214010007907441001710410b044002c1d006940c11000711003005440400380700e0351003010381150f00000115440703d0fa00b81c0020700100c0c3d103c4e0794883c013a40200034482c8010342040390380c81140070203000d000c0001ba48100d940c56100043c4000c1c032050341d04120140c0c9074a0500c3c1e20610a100d8000c1c141c1c0c1404002c10104494410010104204a04001c002c5011b6081c4409034000c1c02041c0e0348120024070005207680c1501c25500c00e481c9a40110005500b0b1200301c10700c014040c1c2080303603a904401c04011080d500b00003a22503c41e0000c103a5074032082d6251049107403a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 228685872 1250 228684622 228684637
    0xd0f0f06020f0d1416180801050c0a020c04060311041a061602030f0c010903032006010f06020f010908070204050603030d1a0901090c1e02030d0501030f02040e0a0c030b0c 75
    0xa4400900e408107141103201400f405a1105000c2c8003c5503040c00244110000f610800c07000c80079000031007015800390710305903181203003103506030416a0b950500301d0031600215038500307004800080480a5640c18041c4060000d02150108201070a46e118071215032a890151030085581c0c03002030301c07103c034a034210004d04103000341116900d0340310315014a580a110740e4206c2c001c0c4250562a00840c0c0d020801c601c01c0c40040c0c0d6540b410a00c1c0d0f480c00c94001c2c000c09841a500c04100d805201c00e8907051080324043c1188041c1d40c1750017031400d20002d2801c40301c0da10020700e1307916200c1e10b0030015440204484c511501200c01180c0350300c8110010307095202d10302d070680c008c034602020728042108442c211145800200c8280025030f0b80e609401c2c05540daa03c0050700001e4006044e07440d0340707500c0c504148040b440741c8102c1f800c052500c0c440d2011600c0c281c00035500340100120500c110b1501d4000c0140341820f04002d09014540d681e079070704030514103000080481482c031001580030350440041d242d81c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 228687122 1250 228685872 228685883
    0x90705041a04270204020d020910020f0f0a0b0c07020f090103051b06040e0f040606050301090c0321140c03122802030105030a080c010612080d06080105060d0f0f 71
    0x1071600072401080c0c0740d45400100b401107080c0b042c0d40d0000c15121200d80090860710101d0741c41c985055003080020751020190440303580c0d0038001002140c03035202e51402910042c0d0002c141c1c5001500220340b41034100d40881406921181000001561600040e0742040d2940806074035684140b000a0420184c040b1558110601100000504c0340000e214030b200d084050400d2908243c140500120740f0a901500740002c940001155603200d100b188998828000d03040014115182c00000e425134010700002d907041c100c00d403014014425003108014140c404c0d0452600d08450a0710003800e28414000300401c0628049280300450302c0510456000c240075000004030792030b1060130201210103042d810500c40c0320051841120ba0000c2c42105d050712801001400c400f90302d6a00d40685901c00c60f552580c5540300c05000075607010b0615140035441c8118074694460314582c080c1c1d022998164840e0075070303a040c1828884961121043d41d06d815421580e00d480c2450103080032044803a280070020f00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 228688372 1250 228687122 228687131
    0x10050702031206030714010c030c1e0303050603030a080606030405010908041203030c080c0d0b030a050706030203090f0a08070b0405010213080c15040b09101b030c0b0601110a03050309070504 84
    0x40180c0c04002414a0321101d014038240c1d46551080c9035450b01c1c80e0148001185034500b040c1c00b1580280840c5070070500c20700c4c1c442d50344002c40d5100c40c040728004951241d0030104848c500c0405070580a001c0c0c1c0300754150002d60400d8800724004082c118050501c6002d51000000f103020300c402174000340c90464100304c42d42d548594450340c010100d21080c4094000900d84030b25155850711a808503406a80080f003280d08000d0701e4088880101504c450b0301c1d07894030803107488900280080c01030300001e240c603881c0140c407441c00005c4103041c068640b8409034190480746803580051700c14000c0d0f90342907411160b801410b40e124605030740244143d41f418111001045c400003050310703001404038052a0265088a6444d44416902c500e0303005034000d40d1101181403148498605110940c601a18907034600041080c200b1b4590a601c5110950103074002545195113800b440f6014100d5908030102f07181c40082c1c080007601454840d00c0300740c0003c2c04c20500101060942004211100140900410412 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 228689622 1250 228688372 228688381
    0x8060d0b090d0806060a02101d01060801050411120303070e06070204140907090608061306060506070f06050709080d0f0e030d0809070e04030504060f090e0109020714060c04050f031005 81
    0x2c1c0c0d648040850b042c00501c110000842604001040d00c15840d1550000d00200c0030400900300a0001811003c180b00b0352a860710705c2100007402410000c0200300700000f035605190905080940340118950300540c804c85240003c21070010869038042e16a10f0501c070348c810110700040b0180300300c4101940c024104050704c82e1003d8940b1466000c0c150301c400302d480c5650342d07201c20019a40309100300101c940000d000503054882d51300f01e4810b520710030500050856103507030016015401c19081910055800700340703030082003418482d1030b802041c5428002009840d140f5800c2d070f6203030b80ca43c4d04010404008000c41280c0d01683e088411000002c080d18030744e401c0340c01d000b803e019003101d041c6901d02c00c072140000e40c0840404520302954069441924003410704400f590140c484141030700c01c101c00e0280000c5d11aa191078998085e290b0030380c001d603451203c2d040c0820380c421194000819604200306000f118420f00041300c007107407030130348203441c610700b074000083c1c102140354850900c20740c100000c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 228690872 1250 228689622 228689641
    0x510030c1b030201020c060f011a090301060806250e060313050106170115170a02010503040c0e04080705211909150305061005070c06120207020a170d0305090d08060d0b 74
    0xe0110100100850f81c09513550b5464540300075085c82402b06c1c010140c4141e041d90848200180340382000034001040d4155104401440c1a070122a0040005910740c0031031032a400140a40120401e18038054001802d900009036182c403010f4901440142c510007100c04000080d00705400900510456529803400506640c0c0a404181850050300000c0400861420b00001da9003d074200604000c2100d5404c0341d00550702c84e4400351081d5190f0303071281d4000840e84aa911071600c00c6100d14510b2361903c0e86031404070301d4116980c1781505190158401e5010701035516041e9141c010400030b440d511b035100288155400c1545802507842412299210201980c040c2c2180d0700850703003620490710304001100103c5a07409038031001003254206010070070403944992124079203410001001403610119500160081c4100d40c040c2400042a461101901c4000d0000000004240c10140000d01d0030344c110b9916110a0504c9605009102c000700301da40d12250340d0102c1450303102a18960780e0600c00000b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 228692122 1250 228690872 228690877
    0x218010f06090504110a030e0f060103080918090a03030c050f030109050921090904061803021501050a0b041703130e0a0b040c0e09250e1302040510030c1b03020102 72
    0x1c21010402c19040010b06042920517a020200c1580c0020304064001c0e00407800381000c1e41943c6024401d1400d100003060050000398002d62150b03080958807103c070014407806540487c20315240102d4481044403500d00841c2a5080e0b560601e00020010301d120f000742c41070b00445904007140f42c0c004c000070510030001d03030100e802650704200b00d0354141103107601d501d82c0020b0040711442040d42440100400d0410282c001e4110b40300b1240880c1c2d1491500849510040751001580141e100700c00200c150614000784a001d88016205920842e0420849041510845c4900d503a44c42076148400c582c9403090080c1c841400300d40f00313850310241d030b00d9288880151042d82d0b03c42c0114a0081601381500d0203109075440000d880e12400e807580f000c40308028001c00003c000d1047d0710048040c891010304102078003e101d20043d145e08600340d40f400248598007840840c51020320b44104002e2001f0703a1740718807c414461143ca03000c41d00c0c28800500700c8000b26104e00094510b454000c0c00c0d810140c06402 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 228693372 1250 228692122 228692129
    0x40b04031e030f0e0d170304032007030807080d05010b040f1401090905060d170c060609060d12030207120509190e0a0e0a02060a030c0801090e0601120218010f 70
    0x20125403241c080c016500c01e1403410300006000c03031100010030b0000f5000324882d032090a0020003050000c819034a81c1d950700e00b100b40018a001800004000405400c004c0716210025424101c2e1050f41d03c0c2c14401e50390f40118080502504408524042000820411503100c10314900c2c090080b0359580705c3c0c4039181d400c40c0c012034010305d5041e2404207011003050000000d1000c1607490210551822034040c009100280610741c204001086c4100441ca40b82100e10040b10740240d240c2d0f0340c82d0554030b5181481c402070140c500c210441410f000313036551500f212086080e04800203000c0c1c400c0c02d04054000740329810f4020700041518420303520a1b41c00002401a049080d12951504140101d040b00500024001c0d9280303180148003059242515038818070711a9042c1d001c40314160794507000905286c20604003900020b0721131088900700c03036000c3c07032043c010141d065091001580707500000e42c035000140207840240c8000ca0247e4150b43e190540c4003071020400b0b10005030b550b11001c20701002a510302 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 228694622 1250 228693372 228693383
    0x12070501020d0f0509010e1f080114010305091e0a050f06010914040c090203100f180e0a0302060403081e04060b03013e07020603010902031909050d2102040b0403 71
    0x8482d10201030164802d00d107140b410381c0e00c80d841d01030351000654541c03682c00c0541390001400114500700452030440c4407001c001c1510340402a40c0740c000f01e11000e04d0005c5110341094203010a200400100040d0104465241a6031501071059004664545045828042c0c81c1d44034200240c03003140c1c0c0104840d8180e0708440c209000d0700e09485900910320009440042000c000d00c1c804101c5812164059078001d0004a09507403500c1d03441c18107101600d0590820340e1000c42511180000780000c2c8203401001d0050f90290000c51f441e0744019440d41c034003c00182c1400803210008115080806825102064081201d87c1c5410281080c2000b01400080c080c025864103c004110304040c02c0180001200500e104030904440c07e28001d0006080145480240061001e480160354400c05107020b403000b1600141c60340f4005882050036100c1c1d0003141f60552a148446002c160041404554150300c0e08014440562014854044040300c44030044a584049008108403042c0700c020000c80f400351 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 228695872 1250 228694622 228694633
    0xe0406060608060904030c0c0812040e0a11070f03120f0f0e070f1403160b0333010f02120409140a050903161104060902070b0907030305090d02030109021207050102 72
    0x34071003902c1c010800e07a000d41d4081c02110000300081d1003500c800c000305202d9a850481c490740c3d095040c0c500068400740030704200001c60305112402203032002e25800701c00c44d00c1c14402c41d06042054107041c0304405000c0c2c1150484402101414040d02541c2c01140c1041c008009055012804d40028500781d40d180d0021414a20b02a00740c4000007409030a80704200b000d55111464094030314480709a080b825500350080070a0f07120721a00540c1d4040040c5401c500741c03680e030300c0d02440384c44031841d544080703182c2c2d441d803c000724103200201c50003a0a03500080c01e0140211601d10320907403030000c1e031001c02c00600d42c002030046002c1c45039801010511012040ca80c0b41e580b603a00000d025141d04980d180d0681d80203100240400d01c03100302c050342c0715006010181520452a001c9030580302c0c540c01100030076400040140c10051a00c0c1840d522541c004040c186250859a00034003a02c1980034541c80f4100c1c41d515103096660070762200410300c0d4002d00340f600101c0c45070541600c61a0300c2c0324150250140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 228697122 1250 228695872 228695879
    0x306080d110c040930121a040e010213080c040c0c021e0a1701060f0506070f020f0f03030304061a0105030907050d1703090c040f0c050403060e15010e040606 69
    0x8010070030740c1d015103901506041401509010041801c00801c2c0c880c200c5590a203030340e00d00200d42c40800380c18032040035040744800c07400282540b4019001d80c10018580b82d01c40c0a00344c024182c000301040304580202d00816410306a80c060701a0003540f030754104000000003803000c030004860168030700664050140300108070040d9a10000c80c00041e40081010107916074885480c103e041d40c0100050030a03a0007610f89219030401840c000b40e610f25699640418400c465101f00118001c02c0e0840d00316291800c59074030340c18801c0100c44028000c400d0a0154902aa0b2b0b2a0000340d01c4603014084a4803447c043c00c0640160289094040d031215941100001c030f5407240085900c600d001030011b04025280c10280442e20a2040040d1003648a4030400d081411800000314003c5980300000c0900c00b40f043c1c1000100c0301d080441d85141307440c0c200010040c903042001c2d102140d410080c0003803007a0b0068805401c1c0302c280304100c5a0b54144030008160514010045806035020320810012a503c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 228698372 1250 228697122 228697127
    0x10051c030201180b0609060d0b16020106050609130c020304080a0803010e01090b0d200a031a06100f0302030606070b1608010803040b07080702010e09131a060105030103080d0e0a030306080d 83
    0x704910044d00a98000c400030b0b18500300f00e00119040310014190b428030400d180c49644080000ba24070850b202c1e0219038081c001070b42401610058001107441510b00704108000421421810301c071150404d803200261541c8600a02c107580040024009940a100581c540320185a100b4003800440d501c03440000700e010013291080c01c141c250041c08141c0e1810454640b006e1011408c00310703600e444002a0780c44c01d41d45445038614011481400f800c0b42030070f05810300d600d19800040c46140035010b01c43d00044032903844800032130117240900b00103a0341c3c0c456102080c20740c4100350001e450300310050180013481c500220120340c0c0d0120f607900da1813140d0301c40c4841d60301ea01c150311a040000f9070500c100000b0642c0740d070052a8091050600001c141c030700388042a9183c0e400c03141c80c10300409111455090001c0180109040c1d545a503e41e21180b0705100040c01500040c00042c0507034402054100c5038072819400801800210b000319180c440162400a01030145400342461501601580c0c80e01a030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 228699622 1250 228698372 228698411
    0x619020601081c0503040618060e0f0615102c13020403020109060e060c1b031504020d0b0621030a110616030203062e020f07120b10051c030201 63
    0x3680c0c0c2c5200c61082c9100ba8111042d4102500c00e0b1a200e46e288448010501d0803c3c07923640042c45188007140c0d0b5000035603928103000d40d00c0f000104030b8200400b0827511107001000c1d880e403003800b01c907814a0342c101c0900c100c3d02c0017100e030030f40c006007440500380d0b00d0f500481188048290300101c4c1c3d000302026040c403920050b03006a00c002400b02c1d0a4000a001e560301404c0510091840505021305100074200c07040d1600d80140b01d4002e84040d03854042e401c905051040c915100c0807401840c5003418680d010660025690801a10f0702e9071410120b81d035640c0c0c0d03076250600101c103803c218046022061507a510390b4081d00050020030020494105181e00c0890524499078042002d083c01e14441101034010b584001d0982c1d074008161624110101c144c2c442d400e04c0c6400030183c4884540720304101900e0f024058259003242d504c1200c00704100000325290100d002ea1194000202e91151038580160704140e40209a001c0c0c403002c001c0700304444c04000414418000e600912070840313030404807030850 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 228700872 1250 228699622 228699643
    0x21207051c0212120c0720030118080d0203361005010b09090a06051504051507050607030b19060807081803070618080a09030c080303150d02040605061902060108 71
    0x140901049580410080d104d44e4044143d1200900d0001203035201e203032904810040d02c00280500080c0b000300c0c02c0c02d01c80c0940030ba61120708480080070680300c0c60b10078003c60104111103500000043d40305603a40c0d481440760300950700c514469141c4416407011103041902008032a1050903041d9014049a0194904803805003501d1480c0c030360b441c41030100110000340f040300403985a84000070551502c0c81310110b01080b103180e03c1e03110343c10081007103014161004800c1150400f4030181000c26004585140c1060345410000360342803001000c1589280c0c902c801c4503070506044c6001601507000070859200d000907039100613580d6030390411201c42000e0010880e601c0e070310512403100040c0056228901c14054040704020f940015525003200d81c0c03000072548001010020200200406000801d01816800e4007450031851f00c492020002c1541e8810b0620882c061410b620554955178401006050064030460361150381c40d0003039900850740848500188035000001503159000304240440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 228702122 1250 228700872 228700903
    0x70203031021050f07140d03020d080a2004030201030c0c0b071b05030f070c1a3403050310061b030f050c030304030906030c02010b0a0510021207051c02 67
    0x45070500300030b8008100d40201040320b492081d09482c0c007158081010111a84801d00205545818040305580800614174254041c10819100c0382c002038001c1091a200c5a191900440e07660f1400c0041024000b941d0307040100c0303074a035402c50072600010802002940d0017a2014800031184503401c649031141400042c10740e140500c00318116511910f408240110008000000cbc8182c0c0d13201d05045602c100040001044001100000c204410300301c140105850004103225084c00b04407181d0038883e800802e40c24000c0c0400c0c0d403044400b00f41c00010131040c41c2d0801494251545000707045548107482c1d03007000c2d0107812000030b0010301c101782c010300720741d210a0403420960040c0c2c0c093390400814448003040c00070a0100706900241040903601c50760290340d540341e0b81e42c54510043d04555076103050302c0443e41403160721030940e01c4500801c0100d400c266030502c009146807104074185032a01914003031200b0b00103000804d00030700140e191038002c980104100705420b0204282c1e0743d41c200005501c603 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 228703372 1250 228702122 228702151
    0x405010b161103010e010e010e060601230d0219030501180e0a02060706060509040f201f030209030a06051b0306030a0b220305030a050105091e130c030c060807020303 73
    0x26181c120b0000380210060008103004400c51100c0b03096854613403204032169034178500032541e28002c100140e0005400e00745012029800e44030070046030210411806600130000c3c0714100b81c100e0b6411110380c44281340c40d1602d81111260000c000d000c0c288076521448001c0306064800380d980d131180c80d030000011801020083c0441d4240005500104070139241265281070014481c0c0701c41c02040d102e6403054500c1c2400c08031601d040610107040c25080d0114019854200c0100e071610300400c0385800088200d80c1c008900300030124080e110f50680d0355014000c010b05d800c10000d244e0807541c051000c180140c030017081c00d4141c054560000711104c981c1944060414000300b02803401150b0030100d0242e03080300c1e030010b00407400c0407104183c00480000e200081003090706242e0344a80b9001d010101c94410301c1e401c20b110000c05403038943c80061120000140440c08402d40d254801c4074444e4031481429030f003682ca040c10281c030402c0e8424500415095000550105d00c003100b00c92240a18001220 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 228704622 1250 228703372 228703417
    0x16030c0e09100f081c03060e2e0603020406030b030604080a110102070c0b0a08090109050c040c09121b06020102040b07080f0c01050c03010819020607032d09050405010b 74
    0x8010140040b54404034207800410080d140d407403110080c1551800524011000c0300c44981008441700b50b203401c0618115040c00b04005045942c0c5e04889600c503d20500f0076405010b009002032056440000b03c00c0e000b0010319540c05401a100322682038a003002210f007110145500c03030030100ea004280150800403201d06501030004800111101c0300018148030150350b5009000e04c0b00e804c40d20000c030002ca042440503620100203548800d00030000e01000c26159650b0343d54000b0810b50320b1289403038030300d006525481094041c0c0200078100d14524075444c6404d100703004520840d03035030401c0800d682001c15402e00500071201101c001c05032092806101c0d84030f00c07803c0d401409141e408580f0801072032034091000d000701402403502143c2a5a2540340c1b000c0d092a007003a4008103540304070440005009691410292140c058260500f240c0000140c0f06580c1401c7c0c415105000310002c0c0d540a840c8250301c8600f15003590310903582001182d80b110f03c62900c5004100000780d220b64180c0540 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 228705872 1250 228704622 228704629
    0xc10270c0b0a020a05120301090b041e0b01050d090f06050c0a02030901181d01080106060c020d08130b0d050405060a091e08090607240e0304060e13090302010516030c0e 74
    0xc154440003403050304c040072880c0c3d881d42d0401c00102002c01c2c62250200c0140000201b03480740d560080012503003003001407550640740403500545440c604055a039080c1c83e0000ea4082c1c0f0403611394101c1e40e901000032080d00c5c9015500e00c01c440c602030303d00518220008a4958095040b16410ba920350010340c10044187c00468180b5804290210f27203007085140010411031902451300c0d40400c80704180c0003581041803041c00c4a41c6540110100914500d890740940c44900c50111033940000c809076071114000c1c5200c54600480c0d011105800d000034001001c0030490740554045c0d0302c5841a2030b225102c4214a030240d40900c2c0000e0070081008e81e650140701644603010840740c1c070038a80b09091403030600005006400c0020300780c0383c021610000d59039900c07129490b460301407810001000240c1c509008150381c0d0140340904010300c0441007000105607034180c400c507a9071035410010b2006040700c1c03400074042c1800341d0b070307481001404440d445031080c0280a4a03094882954820010458a6040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 228707122 1250 228705872 228705877
    0x40302150c040b1b0d03110a030e0106210b0106020d270503100e0c030d05041205120d0903020105060f01120b1c0308010f0b07020901030602030405030c10270c0b 71
    0x45515900d070401c000190303454a20f024000000d0162400080360300300c07525003802c01e154074a07080300300351403c40302c2a03d5404071810381d0000c1206180001d000c84810003864014091500200c1040c01e100784c21810540d100c0d03144102e081c0c4a400c04284030b036a81d0303500b640d88031702d121100b40100c2c440702a21140290010300400800e001102001040760750381d00441d0503c0c0b2040e130101e40c0c50780c441c40e1024021300d0400420b41c020303030290020300400840d003800030114001c0340180342c801d10508081da01131001c200803068031080c402c0380740c5580b0414112000e0003020b00140c03c40c0954209400030b0032501c1e068880a550740c906866420703802c01a804031b00014044095042c1d4001d103529441a19481c5100031440e016220b0388401c5859410280360040302c0440d80d0201c1c0380362104121310001030321003100590450f50321810150302e9841e07910740305003540502d80c1c825400d4412111103041d0400360341c10942d010ba00c008101d944000d00341c1c840410088217600050301d42410f00e04200156904be100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 228708372 1250 228707122 228707131
    0x409050a0f060303020d0f08090a022107141509090406020a03090c0b250507150e04020c061501020111070b0907030c15080c070b041211151801020304030215 69
    0x14400c0c00440301081201e42c40c0e041030380140d2000c14130601440d0007101c007240b0701541b0f0520071040e00c0e1041c0480c1d0b40e0240340e035009001d060040c2c050704511904031605454194000143c4c0d500700d032130390035810707040c5000000203200780700d81c030340e011040034151045500c24080030b01008041e9407243c5031140030358080d1050708100760b074880c03c84020840c03807800800030342200d0f00c000d56220203406c0710040e401c200c00d003a09016804100c00400049002568034103e40c14282507124060781c44000751007015004100315009400011802c11054002c110a441640c0d1a038810300c07030301408001242240c030483c1d698908000d0070081c0c04081065008200e60100c80d8404807000540c41b95154000341d003c03544000800701140011b031185981149841ea4010001550241032181c20303180c0000313070301d00640040d081101007a0483c03c50380c86104450313101d00c101030844210410541c001c80ca10741040300c5a403941501c1245089940380103000300e900841d05603000344003100c0041c260000130300e0040d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 228709622 1250 228708372 228708391
    0x30b010e10080402150414041a09041209180e071505160c170a031403070c030e04111b060604060b0a05030711061501080906010303080a0b030a080d02041a030c040905 73
    0x20a82c0614440c1e08024005441c03c7e101c01c0b0381d0320011900707020503105000307001d10b40c0c1c1d0300c2014030161a4594a0601d50b0041e081041c003240781c0101d40007a5184403854014240403030360013551150748d10f4a900400c000a1340c980031982d81d1607440500f8420940312941d10000a00204595035540c1031150080c48818000e880c140e40c03250380ca0300703c040c8134207401441503604d402c2142c2500c14541c10950640440d0000c002480c030b107142c103403401416400c414500030144032034401140c8183d00c881c2d0040150b419007490490b0342d500380211448100440d0403a000c014841c603400141c0c581001d010344011030354880100c1f402c012494005480e143c10051000041000126440c2071110040204a000e5541d041d10041d115004c01e00040003e0b50041000030a0343c000001080041e80c81446150b2040050318000381e600c1e00000042e060182c024400b80c2401004203110b480708482d98000d004581d90031620320b0b812602c45503084007070300040303980b100350311000c3c8020031010b411504541d6001e043e04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 228710872 1250 228709622 228709639
    0x30504090c03230402012a0b0426040506070f0201020a06020f040302090a15031202190b10060c03050306040b06090607030e0103050603160302060c030f19030b010e10080402 76
    0x20180c1108461680000701c0c0042d80301d54010f02c190b080c1d090103140301e02030060400b030180f0305a0000f811161040050300290600c400300f03110358588409450100c10343c028501c4255003030509108a00c4204083c244a03c20301c5c80600003010704010088400b140c00180806041c040c00c2c0d01c500040c1060703c3c1d000d034158015038141d48001401e0f8401403030b0070190902c0858460b03046d4014890391603030050425508500c0c0c007103644800520000352800b180d500a02511140c0d6000000b2800c005016200091205241c0e8045080000070b0740611300c00c000006c02c1d14081552000c0881c0c02c0c0e0030011024010540c00c102142c8181082d4000b414910300c0030308544d1a040744400840c280307511041007500003c440c0f000304452503034107020b403a0704581e040b402402144141e041206400176070b80f0000b4401d1030000780c03407485a03100748255210441060301003911466030300b00d120203200d00300ca0080e00180c503001d1107241540c0103440300c81e5160000703000c4400c12501104190344145010b00180d0748100038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 228712122 1250 228710872 228710879
    0x15090f03071a0123090709081605031b060414030109140309040c1d1c0c0807060215010f051c05071214030721091d01150906050306010c030504 63
    0x4000401070103120b44031000202d18a154038001e05041a000580380c0390344141a440c40340f922005030741280f003044410350300d2503c0310b0070161075201c0d00340d00c600040d0145803d004102c03004040150300710740c800d40a42e0300380d0540c02250300f0402100204640e01420601081c040c103046d144481048000c050700014400c1d1254a80b2910107920010344c0c503055100144200290a050103001d56862060170f20f611440740d00841c900b6842c552415050090141b155002001280581c42d2000c0340c0c0c002d40e01060858840e200349444020724020140940b140305812180c01d5207401c10141211b5141d4a2220002d090908226141888c0f54010201034152850f4030302103141440620000c0c40c04040319403458080d0714007141a041074010441c90398000b44a4040803c091485480c10303442010100465101c0128090703400c44100d03085107840070803a200540e104c1a10903101e90581c9c4800e61a941110003402013102c52082074003a03103000074001d00c08260203501030700e00c0c00c181600c2030030000e04050302d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 228713372 1250 228712122 228712153
    0x6141b06040f06181511070c0e2e060c020105130807060f0311030606070212010606030c080a09110f0d080d050114010504081b040615020a020f010f021509 68
    0x6980a6400b02c0901c0c10800810083d0b102d071002c0c0140c1c80c40b102c000702c040c40c0c0360210300c2440e009036800480c1c0c4071442d503034412014404481007654407c2d460344482d51183e01c424401c080440c0c0c6190b00554130241d448540c914030120040038550f654903424104d0810134210b84c643c5c0490812810302005100410202e49003040f0301c4060075500d00181582d41ca0440300800200c60034102405051910079038103007900088040700c2d44040207a601c0341d03884d01ca41c40030418005c0d030109044480c1d40b03010004114036506400c0011001c0c4150b030b074000113440b0350240c4821100003c0006190390140628030f40c0310305000c00300d0102c0010003004101d0540c4182c4603601c0b240e001c812040030007981c420041c002d0f1408040307036040c0070310280307895810681040c0c0c003195140400001003083c0114201c138140203a8070341c0c01c090050428095810560101144065690103200304120302c0340582048007070f800e500c501d40c507030480c130b460b54024148940807050680c0000d034040c0204003240500c03088481040b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 228714622 1250 228713372 228713383
    0xf0206090604030609050c0415050109090b0a03050f030304060c0512060f0102010e01091a0f091f090204020418050f06010212030405161502010501093b1009140706141b 74
    0x140070300040d1101074130347c5040200326582504240d0342c003032455100b48a47e9901c10311450070381c0c410714070001e0366070915000200d080c40c099100502500c50007201d1240e0443c040007550003584200001d10911403504010b81e164010740946000600c51580090303014135220018450b15541030000046e81c507240b404490a65000350001d441089030480d10351380c000300442800b030344112405201422400c1407850143c69201d2075000300c466111202d282007401ca42c80c0d000441c02580240215a5555078000b076443d200301c030401d51080140342c00c00040c44825006c0205200d00b80c140e020b07003a514000e48601019400282c010b030744600c101c56400005590900c88100504101011801150490003000b07082d40c00581240c0c5000d4141313032300100c50780c044480036001c00c4124083c200903240c500c661000a0741c03641c4038080c81881500f0507401d0314180c550058003145d0190801c59182a280c501d01584c6000354070602d40021030420106020700f1422018140fa0080c6195082c64141048401351404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 228715872 1250 228714622 228714641
    0x60f07030f17010b0a0206061203120408040b04170d110303060d0c09020307020105061002030414010c0f060630020a03020405060d151d010b01020c06030a0e03031f120f02060906040306 81
    0x2101c0066180c503006c0c0c0401007a51300c0030044428244090315200da1a0312400784540c030001507104100407030104003041d810b860240950250040d225580e508611049044030001c030340142c01900060600b051082580c41401030390440103514644401701441200c082c813580603994103d107070b1004a40c02c40c041c001035000e43c4141c1d0000c01e06040c141c0c2040045a503035000c0344155403081104210101c50307140300e00346903002400c0c98031000c50b06003403491988100c454018209c41c03070000d010944500c2c2c02070881c00040380c111001b1500c001d400b1191101005e00744065801440c0030420001444c02c1d4000c664800b4000c0c11018500d42c0c0c654401c0d0b580300d0041c51800c0803d0300c9241354001030f001a1042c01c042c00c0e9001c000d2000c450380c100040d458026120940703008810020000b5031104486e0041441200c00381c040f20380e240741c050101807652401c440407043d00a14000c000961580800312070010f290882d1041c1c0211130a80d00704850359001414480c1c00aa003484000003150591084c2c0014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 228717122 1250 228715872 228715889
    0xf06161502090d060204050114070f121710030c0605070323160308040209060f090f07050405120f06072a0c03020a09020d0b040614011b020909031305060f07030f1701 73
    0x1b55070400c4009403d01c12a8408140b15030310500127000402c55001d4044c0403a500100384e07041001d60800200d50701c4110103c1880c80d030b410381d41400040034200c550a4106c030b00840502c400c040d00c0f10f004940504c01d411000c0c00007483c0a1681106088020400340c4405407101c85c1072404001c5140070b1642481450b0903400325078048100400d41c10427210340307584241c04a99000300c034019140010441c440c0034058040e03040c0c800d40010121801a4111005094000c060717840c250558000280c0e00c1046010991440c01600f01084034207001d041d1102d00003500306070f24455912610450400002c06140944180d04083d030b0010142c0c492103041005494007010150742c035905030a48101f5104040061802071349011001c000702c958844050000040918210b180200202c0765400300c4921140b02950154242c800d0010984001004004840c1042c0003c2d000326980d8040182d00d001d42c26000e2401502000443c0000e841810f0000585856050a81031014042c00040c004d04003600175254 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 228718372 1250 228717122 228717127
    0x2030a031a041b0311040e15040603062c07260a061b030b0307030201020c0f1305180d080603030304030f020f1f0609200708040e040b0103020f06161502090d0602 71
    0x503d03c0e414041c0c0d0518010040c0254076042c0f070000c040c00c0040c0028210011091101300010a80da56904000020340d04050144034030507001c04081d8a00740a4218469041c5c120030051000c0035001c1a44022104540c0c000c10305005403d5856100340c501c41c12850840c0505207541000034200d00c030310745c54100762001a00314102041c4000e4202c07103150808511980c0030640420041c0c0c0d0005a814880c041502c0841c2c1151107400459054035650100031040360400b0100040380d0100b410181d25050305204585024500d5441522548e000f40c84140c0c1603041000041c3c0032038019140c004014a55204440e0704000d15000c00d41050110100780f804409034001c9842c50071030502900000c0e0081e048108a01c00311240307040340c0300004140c2d10142c0e250124007602404080c0c0d059a000f400395001148a41c07502c2c1c40c00b607007890000d0000300e20940c680c10f15000d142c10150140c0b1001d2082c1842d0114140030b40d101d10941001140604040c150204809115034407580f043d0b5444078840d00300982c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 228719622 1250 228718372 228718421
    0x120a020d0807030e12091503040f03080f01080304150e09090a200604031403091809120909040308061f03020c0714060f03060a051203070210020d02030a031a04 70
    0x40400401409030010142072001511051101180d0102c0c1c4001e14072000c1ea44240050101e142004110f803030034200180401002706001da500c00d0b0400c058032958503040d41c0c1d0b59402507506070f68028020b5441c5a80280014051407a9117258503d05100c241000420490064006240340030201d40c02d03441c0d6000384000c04100008101100c000487c0010014036549088001c600b140c0510300c4090030341c255280071a0500c8900b441220780f4a4009010909129100001d903c402841500d0401d4580f00352000441c0e000641e4007924049100100100510f41315618101c51641c00682203981c03068144100141c01c1140c0c00100c800c1c05c2e03940e00d0142c3c0311034066404d141008000d42c4401c0c03841302030244c42081541d0718000c80d40c51404000e181c540b41d8440f14089001c07503000703402c200d811901248551010590010191101a2003140d1500e104628804120b8481421001c043c026038400c0c81480c030482d0103a004048522a0140540aa00028000101910041a0080488410780c85c110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 228720872 1250 228719622 228719627
    0x305090a180c02011b0e120d1d04020304030e04020c011b0c20012001020c03210619090c03091a010e1806010603020c0c0d030906030b0d020f0103020c120a020d 70
    0x255038103525000170040991840c1c03a468038061245401c10411981400f00102c039074919840e0850705c0c820108031a05006003000103415100b081c4125003c040300d04c1e000c0c00b01407405000301e031301c16649503961160080100081c04060740103c5c50481741952245a062641d241003c40c06042e07403078036520000036412a0924450350030802c0c074051504c032200c0d01d4800702c0e0b0b604214800122080c42d103011050100114045009004a04d0464440d010004101c5070100025011180d54891002a08440e44590341080603040341d003c0018000000342200700708800495002144000c44c505000c43d10300d90964511580494076403440e19400030b6500140305410350f180209078048520710a0b0028080c80204160303686c9c00506c5214201900040c000d0544132080c00034926101001c0d0040984034003901e80509071030028020400024a481c403200c0c018505000582d540903005800d00500034454401100a544202c00c210354920943d41003041c1029404001c005001099018001840c07203074900 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 228722122 1250 228720872 228720881
    0x3070306050301060b1e16030909060605190302180301050c0d050105090403080406151502010c080a02131202061b0604110108090309010f090906030302010b0405071403130305090a18 80
    0x2c2c000d030b24001050000c44448012910f40c240d50442e0300341070040c00d245445007481113004c071100000080d04040100f6400906640554081000034042e807030f1950400c60f01409840d00850340500d01991101026000b81c0c010260541890004440c4180c508007003170035210191401c017000c8400090080b4150703414071826000d0501101d100c449804c06480050400d04050405081381d070748c5102d0b221a41543e070030070703400a16508010740c940790384c00d034800b0307000744100490b01020824010024100182510894850700542c0031070049840c10b01d20f40c201d9007490f084040b40c00100030001003030401001751250a02c10301030b000420040c038151a0000d050460990350505002a91060101c485804001e8a1440300b00f8a4038110b0300c1d149050440b034880301070b0f001032412450400e000c024980d041d08041003054081c1c5090003182c8400b0421a581001d42d03000031003a14050011940c6011301e08070b0110700d18000d19000b03080c41c0700d20001442c2d6403a194070a003008484100291100c081500a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 228723372 1250 228722122 228722129
    0x1090e0105010b03010314070306050903090405010501031503080d0e0604051c080c1602040906020c0109060b091e0907050a0906091d030316110a030201090b0a09050316022403070306 80
    0x7401a03514049070f4004600060000828001d0794103841d02449000304017540c011508540c0a00460401381d40064072a4072040702c050240f8280400070170194000d0251007041c5600b07011607041e961540d11401c1540d0845054480c1290b22100390780d800740310801c03040703028500420103800e801074441c80002d04107949000390804d201c180f8007080429203150301902d6008400350a016498402c0340f000900030b1111800090180d0300c00304040c140e0303820552006a095205550801803580b2010030002608000c840041d115800c0f4010703804030324480070720b2a8100204204840156448074001400100c1c1904201142d95403010204480e080c540207a5102c100d12010410813050001000e5480b40301c0140700075a1001c104a4007000316100f4002001c1c00b03254203060300c04030091071500a0107080140c0081c0d490244a0010450600280c840c0c1f01045d58007200861400303c690071203101c8410704440a0380e01c454080c038402d041c0440036201d800d50b0782080d0122942c07860000b0015045452682 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 228724622 1250 228723372 228723401
    0x71e06031b05160b070801080c0321160b040f0c0b03042001020c0603090303012409091a030f0708011113230a060201020702010813050a12260109 64
    0x4140000c0c41c050302642a005011864440d58550842c004102480320642004001030001c0b4208500c41e03030b101ca2840d040e10080000c0d82d00b003030300c140c040656034000318503810790030584412181d44401400c001041100c00000c01000038041503182e0500181040f03e003036840c03180d60306101c0108980c404060020344444030b0080d05600702505c82032072082d01011868040c01400d900c0d0400d0768000c004c00240d803140180752a40e43c0c40c28410b4152250021701c0f42d03840240b80d60213071005142c0c1102c0d0b40c90155005d999261b140c94075003001071002d05003520800d0b0b850383d90b00034007241e40e4600b8004622108055002409900d00d0079021a08440c43c41d010403501d084248098414036100c1148002100c0c0120b412180060320140300442c003101d6900030136801042c44d1000119180c040d006018114000d884030145130790303504108800c034107030740000405a8114041c0c110000c0ca00424024030202c082c40c1000c12700b421014981039080700349545034041c2880e0340042040031518020708142d004400c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 228725872 1250 228724622 228724631
    0x3020102031015170705090d060213080606060d02160605040b040c0b0405031b060c010e1c050310050103021605070801091407060519030209040f02310902090102010b03071e0603 78
    0xd40100031340e1010b0810000842c0c12008105101c0c441c0c01540d6001c60b000706200b421481d40d10344040250301030284a0303c00c1c0502880015213507004a000e92250b83c019110619024111012000a5109540a1074001e10340c80c416404101c8500c2003501c00c920903d180d80380da080c01e0a00c4001081079501503031000008104c20b200070345002ca125000f5a100192006824800b5400104d080c090303249007100030b43c60600340b921280b00000312841c50104d2400e0074140901300c50302c12102c42c48111030043e00b0300c207504000c1129512039401040c4100e245115034000c3c2c00e01d80c0d200d50800441e540708003003980d181d04010702840700303100807000c2c420420390081c403a00d8604080902240289200040c145034040d8943d40e40c5030094046802e030300380c014070070450b401d001c2501d01d0080d0488030701c101c00510501c4140b118940f91204210441c1c50f0f501c583d407003103845c3c45d0403038010717500c0310885a045540380c094407001503c04000310740181c00041049095405041c2c10495841c2841e4000340415090 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 228727122 1250 228725872 228725909
    0x8070605041e050d0302130302031603030807050c0d051c1b0207080c090f0711010203090d110d02070b1b0a0602090325030305070303060b0c0d1b0b0117070f03030201020310 76
    0x9024203600303207641170258980b031030190800d1612680b98006500741c011a005141c2640341840b655081da44280c85900180d201c150086070380f405600b00c40100795201980c0030302d180b070190b40901205541d190b2100c02000310003030188240ca0503216070008402c0c002e07641e84400c60701441001e01402c010002000c1c0302201c4800610080e00250100d030311340c86080007040010707108005280010889600955690404c3d06d001c03940c038020740c00340800050703081c0d1041040550128030250407138450b0313004050181c01d00ca4421402e6018969018016015902128441c50b0520440d80000d0140600580780c00000091604082ca8401251071815449101d0322031400d00c1c40100c4141c94140c548070b9182c0c1c2041c036090707005141c41d40106401d55400b140005900500156a01001001c2e6482080b0000344d06106600c0c0d00803100001c00e9807a03001c0052001401103180c6108001e44d54080306e40d50f44d41c0e68641c070a0491260800e0700180d400108009001925005c0e0310020000d0401d0055070040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 228728372 1250 228727122 228727133
    0x3091a07020f040504170a0203070b06061c0e010b0a03030c0611070c0303052203060902010f02030309120306030106170706110705090a0911310513030c05030708070605041e 76
    0x1c4010200f07102d00d0743d0704046014401c015008101d4a0786141581740d95041e5000041d40c0c0c1e03004600308484581003540003c0c070030f040ca481550030300741c10325902c5c0230182c5018842002608544080390351940d0380c4c0300c884244e030317882e599040000c60084d00c50f9000c0c035505003000002c2c0c4000c0341d407009042d0810001c41000452081495084981615140f91a020f03c03019076030006110041380026294035020100500c81540d20200c0c00a2017600c800d44070482c0c040c020380c7c83e400100c2300c8031002d800601d460140203200300c000310703800031000340001101521610b0190200d600c40000c411203a001820500503da00549000c241c40382c504010070a00e445d18000420034070b0003c2c284e005482d10345010300c0400030800901c03401c85030010210602d080d10410403d8041c0f624400c0800c00c89441022a0b40010f0b0320300c11640981e01c0c3c42920601040780e41ca00b698095202d4504581900c42000f40201090384240640102c5204240c0403440b4202420030b04021405298006129074042c4543c01c009003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 228729622 1250 228728372 228728389
    0x316061d0a03030c110d0809011101050708011211060403120f0302120112060902090702060a0c1d0108040206070507080c040b192d0b121b07020918010903091a0702 72
    0x3c0e03151420341e500c3c1040c0c0c81d21452039040040304980000d9458001410451050081c21500703c0a90315000b00e65003400b2841d00313860003501c0c0c0c0c070089540d080040c091040482e6502081601820122031814080c3c1d02243d0f8690107940190352600c2e01d08109071141b039100401c1c100d00c0e59545400c2d4148081905044c01462040c841c1401c2c0b0b00410403040200290b9400c809480390b002000146186850f04001e915644100d645400343c07403421400d0030030a0302580c01c0703040f4070006505035001c0100c02d000541712464058801c0c0d911110601190000490400c0802c000d0140d0783e000c0c2a005201000303010690700c0c0c1140043c407805440810008055200454800302c4050026500181e10005602c43c40350005c00c0340c06004102d40c0a021840d4000d0400400402d540703400544060740d41c034101306840700d01d0000003181c04041000207a015140c00c1d01d0241d081444400c1565030050310703801715400c44045020031804070741c41030400c100b4602040243d41d442c402e5612001e24000041d8002948039 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 228730872 1250 228729622 228729629
    0xa0e0a080f03061203070c03030f0903050a06050718060e0f06030f0f190c02010b0a05100c0b070315151101050c0d09060f150f060c021f020109020316061d0a 69
    0x62404000210590f94150601540200034000c0e03a50380c0515087c0aa20407209010a90209400e8640e47c01a103125241d44d808803500040a01038440c541e42d215005031001800590400003106802200703891010614802022103403190682c4a14010502c0089116540d0492240c60144104007104510041c256448000790186648a5039050184100b00550481e078100311442c001c03000c41159015407010100e40c2086800040c2a42c1d81c804008241c4040400900054251020f032800200746101e01c41e04041503080114170010700c918a94005025a0b10101403441b110010500c01a00002030000c80f03050100240101e240c950442c002078410b10701c5481d00c543d035803100c940c140102c6910406803981040424000c1c06d20130720385100d001640b0b016100c4103117000c58000811502405440541a9010342801d00c0101189021040801004290419952548180300040c0d40611402690340880310300400d0711809c2400050614007080c2d140312074a1050b0314010442c1d41c1d42c0d060030080313 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 228732122 1250 228730872 228730897
    0x103090b010303081305030d06060306080a020d03081e0a06090e071a09011403070e031c0e0f06090a0608150102161502100509010b0411032401021e060a0e0a08 70
    0x205d0b1140c200d1002d60071001c48019000d03020210300d40c2d5504515420290844420f40d45c1844250344410300f11707840c2c10450390000d5000d00650320387c2000a01420610f0f50001f14010b400307001d003400528440c810901182c1ca810f11542c1c4040a2185914901c10014082441402000801d00303100e00504015450076412103910f201054445840c0c0c49200405043d5984038a007a0f00d0f42002513020b00074031181c0e0900d6100340101c4d42d8404100c491003650070340e408825555001e0700000d41c000d002c3c145c000f1545480c0c000d803081080045039140c030f621140060805582b580614503101620401d4001e001e010b50341190442000c40040c19426101d510a45078014682c1101221014060b80741c1040140001c64690411703041140c014410b502c40b0505000075a000e0140324280701c65079000d4402155520450200300500820101c160013400484160600481d80500d08104005844505841221003680d101000b009441030b06401000c0d0b810403130000410b8000050b50f9070700703440c2c007036600d08514 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 228733372 1250 228732122 228732137
    0x7020a0303030b030f0f06060306010e07090509130b090c0901080a030203030a02090d0203070f06140a0f1d0a1701060909031202070323030f07110c040b0409020405011706060103090b010303 83
    0x80c0d544c1842410001c0c00309400f2200c01255401110b602c071641225a81d20030b0203403070300014071122343c040c11a104605c03035940c0b40c00e46800c01d400c0102060000d0407200700007203081440400038060307241d02401a0100701c010602038100004005600340141c104846541004e8103040c00660000140ca4000704840b10250b03d45a01c100070a58408052a0196040c4985000000c465030b28040000a03201c450713031489400d038040900b40341a446a041100002451040103141c16032040d00300100c0101c41c0f520794010303014001c1c001140070382c8070b801801c9040060341003298504001d01c05d020003402096018844407141d618090080c07103c0258400d84103070006600be0400d8407410050001d01080d544901000c019000c10490f00e420480711154500100b1000c43d01c4940150a4030540d20b0391000200004c00066003800050071610981940240e16140c00380016902c5000e9a40a01440703100c1524502007107421620303240c0d01401d03807814507181c400020042844400102d041d650142800007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 228734622 1250 228733372 228733391
    0x80a090b010f06110601051503090a080c1f06060906051b01050103030e01020d02070528090603080a0807050406170601020f01091101091a07140304080a050c041107020a030303 77
    0x10280001440040103144444000b04244809450001c280d9141e07995401c21081c1c3d0003419a0b84082c01e000d80d60b07000c3c000640710410182070710b0045030b20500300d2042e50010318036a0344544458201054a031142e80004070490b0403904c0000d0500b41800603070701d06000711481d2074406020000c25010748000c00c200080e290541206181180038000c0114000300b00560756810003c108034800340700a8018010090340d842c0081c80010f241007540c60003007400f92160071190510a5802c00c0580351a46e0150b80800020f0951403846104002c6000d640c01701e5481ca140d01d0001c04160004201c102444001d2000380496580040244084514800720990b44c2e161040142d2802da1f00d404403040560a00881c21704021402c294002a24020b03222031440e5512090100900030011241d070080b51400d01130400030404d041a2049010035000a4914103a1610182c50404d101c3c18800da84983c00f411400103d130806100d2000b41049101d08681085410740c0007980d03d00e114880a0b0405484043e0b08 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 228735872 1250 228734622 228734641
    0x30050f06091c1706060c150702011505120d080a0f050f06040e0613060902042c07170316020a080d08010f09020a12110d09060b0319050a1b05060f0c0c0604080703020108 74
    0x5071f020000440c40c0001da403810950007406444e9144045c4681000d80e440002c95003090110700b40c049400d41c0c040c001d0031006000880740b00c0e000524107003419032501d0800030300c2041780c41240d0142079074010614051802205000940d024641200100c2c0e0016040110583d4102050440107a00001c04101900c0a000003405002d8030000e12940002c0418500f4510128040d030622142c0140280c80744c3d10343d80d000081c00f0500845003004d0070340040046206900c0e009403121949403005101b20840c075201d09196140c85e10451101012a000c1c60050120650f800b40c00e40c020402c1a03000c0d8501400e1010007003a003180341c00c15030002c03500c50745035499040d4264150340d460b45100c40d0401240700541001c0024241b00040d09000740030b881c03031484100c548816941c0945400100601c0904520b036210000a01800c00b0010740c04504040491960755400081c542c03028081011a154408006100d0816080460b164031902c4108000c00c02550045a400b080380c0e02401c002c0d40656403003121 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 228737122 1250 228735872 228735883
    0x2412182419020f0d110408070509040c030f080a09091b080901140a0207200108060616020301020f09181b0c070b0a0203070c30050f06091c1706060c 65
    0x101c00d10740d002080421401d10080007420b030940100000b031006103013070794094119104e5802542d11030303007250a083c03000d4141624226007180c0300c5c0e030400c591b2075940d0b200c0e4188002c0f070300b804846d10140040c04107413590f4045c04c2d1401910110b0410012012030000c045c0320400026070040600c425400024003000e401c0d40032881c10118000c00c1605886c0815821000703502110b000c5501d000e0031101c26034006000f2407031851200040e1640485612b60b03404115148d00800d545442e1200002d0690b8010b860a0000d083c83c2404101c52584442c103080c10802203200c00080f200d01c20005208110101c1902146202c10340002c40c1d2060741c40c4007129203141005815044800c0d0b0702c200140d00801594004002c00042c1e009120b03aa214680300ea0b82c1c155482200200740c0407806080c0c2d2203036103014030070b41c24090151180e82182c6540800c0b00e1094100001114401c801d41c2004009003005030000b50601103400551070480340004142248048041014100702c1c0598408602502a460b00304003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 228738372 1250 228737122 228737161
    0x140c07090b040e0d02030a02151005060f070503040e0f0a090f061d070e0703110406020a110d0f1a130b0109050405070b040801061e060e24121824 64
    0x3d441030514043c1340030f9500da01c10400d500041c400c8185100b80c150b50b0341c40240c051424548002d8626290004001058000000c56198090104400fa000407810002440103003541c1080c00c41510f0550304094000c43d00800040d1540c1c00c0158040020f000c82e0390359074025901103800200703481140302d000d10318071b401c1c2c00415240c801c2c008041428418240400d1149030300d90b8040c0304050f807404041c1583c0c0601c2c840c0e017015a02040c02d1038001440c014004207015809070689184c0401511000350080c1041801ea45c8540e0000c2102c802d01c00c00d542c4154450010240c0060005450f0b440100002c414810700b440540d60320089410840c06012800003001d11614003500c894651045a0003004d01d845090180500c1140c02d80c54041400002403c51b101610b503002e01c100c1c20400c3c0b0851052010308005c1002c455411030182d0f0042074081e041d404500b0303003448160710380301071031310000b400c3d400840380d661303001c4003c2200c0c4511a11030f100014400d0821031000352aa5400c2d621401c44012 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 228739622 1250 228738372 228738401
    0x3060609050607023105060f150a05070302120a0513080105070e0f0406050306091005071803080c01060b0a1110020903190302160617130b0601050703050f07080703140c07090b04 78
    0x3884280700f05015001b02d40100c80c100c0b2490044404c810400c032080010142003070003d02c09004402503039005d03d002e004118000e0056521486c0d92040e010131b01d40c403540480000c1040819405170a580000b04000070705240d100030030440c00e002002520b0b200c3c12004080c4109491205000b0a80321900680e004020240c21241141002281f55450f01c165074a001c69840c40d1800040c1080d1256a1405041d0b00c0c0d0203040c0f80650460711103071143e40c0300d480211000d42d04c0700c10000b03002c2418801000340704069515602c0360030300904c842c0e040031400d4250601450041c410840199030108a0341c400084151174215400024903040c0e0400d0810485d030301140c07140400c0000c003107801010800040301514842801c1d0703640c6074040c0740028540c12020b0403c100c0d0100180300c0c1d500450003450610b010b4144981402c00490300340c1031a91100100303d0b03a03040d0105034602015088050002007480c60240c180c04c014000c1c10060ba50680c911451681c6900d51a4410040c0c550340e018074a00360202 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 228740872 1250 228739622 228739699
    0x1020706060308030906070311030c03220312150b090d02010c0b010902030711010c0c020f031f0f05090a03020a0f0f08070b0115022b1103040e06010306060905060702 73
    0x3d0801c0d01d81500100c80c2901c403401b518000555180c402e124001e00030013120041b50441e103d042c00d0786419000248607207010168059180c50300080d0020300303035105120f40e07a82c550000d00e0640c4d0406561421942e030455640440003071017150350240c15240b240d8419141c0c0940039100b030004135604104014040c10300840c1d4000400c240c1c6ea20f400440c844e45450b00c034003080c0d01a944409088605140d8513500003170111100400520700f200c00f42800c10402002c5412203441c1d04000c0d407004e06146651409a99100110030081d0803a00074503034410ba101000c0c001c4d210790b40d140a901c440300c04030700514240c0724605000801080e40041d003403140c0c01c84ca040fa2078040c0c0307140201c4400740c2800b07444020060200184c0b8a070f1710000b400c2400b4002202d150760141d144901c0311340c11060201c20441408130409003242014020800391005007152500d0717001908100c0009800c803445c580020041124000080c48292960f070122080d123030781074505c0500d00c502444000440f42041c0300425464010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 228742122 1250 228740872 228740879
    0x90c020303010524070309060f05070f11030c190f0b0c0a030807050706020a0305091002130317070f1b0b030c090d0201120513030311070224130609080607090501051b0102070606 78
    0x40032001f400ea540300d88800000c04044030f41a036250040780c00040289105401c404001040151050081d144c040d007210b440d50340b1440060074020b584858251012091007081000d040c0019000b801003140070002ca2505081c25603264403001c07044400b5040c4078010010490540c0b00703400b110701c0075400c90700c03c644032403101200401030034041e96480e13150301c2088003950408115100321000c5114260400003003500e1683e910012208021b120041001c041c45801c020482440382080b14500c5040711410005008251f460b02540c179412002d5591011b00801090070f2010007100c0318400d04954410f044155880100c0e95180f010315003e42c481d00f488140200100c24443e070145070ba1007078406020036400006d90290303902a800c07020b94020319016080c00c6c5070443c2d1110001c04024601c0607403038514031000d15016041550b10684c005441d1080400c20b030340c5c0a00c00039810030b40d1487c012900a18200009045000d00302460000c1d4036484a0459007000035811075072a107603c0b19003848002e5030b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 228743372 1250 228742122 228742127
    0x70521010e09060a05070f0c0203120708071509020a06030e0a050706020105160e030303270316060e0303060918030d06120203011d030307051b1b0109090c0203030105240703 76
    0xc003a9a446064450350011030300c60140780c02400e00c00c186c01d036141c021041000c001203c0c50f1401031800d80c1c160040740200110101000c0040c50f080340107c1c121503507060540790403002203c69194810074a0300c2c010310040140c2d1003602c00700c1101d07620710b0042128020f00fa0080d00345154100014081e1043c80b0700080c40c4c81d019005288981e10007000c030740110041d202c0540300c07142c40c503004562507042000001c00324001798821198281c0212002020054900d9505146a0001c030400b6030442d6040148010840903000d0002e10011a10140d800e505041e0b01140301208043c2c0401c84030003c1c0501d00b94880420407d940d031201820805028141d914000182454120345c0c05174001c1d424900c0301b801d1092041900361983d1003190085155a590000464964115403001145070003140807001c2c0105081119040c501424074002420200c000c00151844000754810348000c0d050000c622400c0750007105490440e10142d80301d032041103d98000100a1065088202c040840458181c05055 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 228744622 1250 228743372 228743399
    0x6040207020a05120a0605010501050913050a0219113d020f0a0c0506060103020a1d060702090108060a1a0102030702010c050f150907080304050d1b050a060c021f0807052101 76
    0x2405010104070236601ca0300115224840c000281f0740080d101e030304083c810441030307000313079070240220070018244402d0280f1400a8004000301000081e10444880c403811014451110161400c01003603502203400d441c540d075002004070303406502d08540c5403220030a54039501154030542000b2249544d03442ea0803c007406c228000c5406903418072821001501da54002d00c21140305624170340303e0104a044202a48484000103041381ea0046814002c20006032100b50000c0e0103490948040c29003468411091000c4404140d280030702c0c568503144410040e40c000c0116000c10b0f4083c600850030074002e0604520346409600d80f0340c610310907845510000c1144e040d003203008068032000ea41041d6a90701d0440c1da0390240d40540c640c44a400d40880001600310760703070842003988110040046642d15800a1092000e42d408200803800004a800c1180f4001c1d42c40c2c01e00b4104513444000401c41050000d100d1100205608280040018441035a01c84106c00010000d50790303000d21075a68458410030b4801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 228745872 1250 228744622 228744643
    0x309140709060b0a02061308040b0a1d040b06160c08060106030506031b1e0301140126031804020702060f070305070308090607120510090501080703030e010c080306040207020a0512 79
    0x8620b4032002040d2415401c04540031842c103580101219120b008500101c083c001508607000c0a0400c800200303449080c000e040001d4030307510349540c0f0001c80c0004003503040b50200c1c0c0520039840e02e0b00420040c0e07200019200d591840a0500030100705c545426078111205400160452060000014010350b040d040507216020179020b5a280420403074922405400c0404040e07072100f464642251005052003501d07075a000000c0001c21500310400200082c0d01c020b0b04070080741810710401100c0b2504035004580b1f02c1105800551a243d902c081c1c0d40c20040f10016020700c0340c0c4e00001d00c442503581c2e900079100b0051107101181d50f81d0085240251150740449022400b00d0b100000040800f01d02181152090083da00c81c44a04111014098014030b001490007d055481c62400f00c1d05800e50312449010f031018000070000c960031341c100a85120030380801c180c10442a0452940000c0401090b0b940001042e600540c0b00c204910004a043e0520340101d03800030410b42c48000059000110b442c002e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 228747122 1250 228745872 228745889
    0x3150b060726070819050906070308070e01020a05060c0a030603020306010806040605010b030105091f0f0b0304140d020304090b01030b0409150507031a1c050303041203050702010c17060103091407 86
    0x80c0b80b0b50395102c0e014041c0c1d0901030901c44083c40304d10304100400202031000d0b419441d11514161400001841030340041109030700017903500041040c8990801c1103000340940c00d000602c454130040d504d1641e29900200502030f582c00204010205600a070840b1014660050a4400640e12406c030340da035558080764180e45060500000013184142507044a05071103000d8141340a5036162100c144001c6903050020603103d09000c000108445a54807200c050b002600790540d0f03d04240c18020300d4900c20b950240500d4101600b1107419580000448040340c0b00703110301054600a600058009041c41403400c1d80150400844008020380c01d11081c0592600d980c00700840e40358a0011400c41d03501440d00710b5034110701d098007000c0b8a480340000d0080164007882030203099495407078500b140c00c1540e085500210003036180c1c074859010b0042c584c1c0580184000c01601e8190b8200515006101524000004620010584a920a8000d100e075650000004400c024151030407540d90001d502c22602d4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 228748372 1250 228747122 228747173
    0x31505040c0f0f030b01050304020f0d0813030201021b030c1203120a021b120d090606050307080307200a06032c0c010201062306090315040b0610080403080103150b0607 74
    0x3594005e1192004502d41a5074007800d5031b8481d824002c07501186c030009540105210000c1c400280840000c3c0007910315150038000f032170301c0c510000e454420744540e217004a80e010a034890581e00c0004075044542e00480340740c0100c07110031030401d0552052401014070a80d14904000482256800500c401d05604002e6551000b42808003520f40e005000002c0629030104003070040754a0903000818601d0040600140702036907040000d00e0703c1a69441844aa000410303036030b043c00050f0801204019160046c0c04190b0014400078010420300d004980c24595201c4041d00340f6950002c183c0340a465000c2805040c0042000310fa81d0381a0300ca500c0c034015820007501040d440c0880f96201c102c03050300c5070307400192120307401000400c0e00300400041d018841d110720750308444000411030b8042c1d401040585000e081042c10701c0174140c1da48000400f40030891083c040080e40c0041c880d411a50400b03d0118000c2c0740c0140034024140008000b42e01420205080c41489079044181c0301003005488c40e42e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 228749622 1250 228748372 228748397
    0x3060c0807020312010611240103060e19021009120b2a0711010e0307030308010302040501060804030c02012a0c0806101d0907050a030807050c040516031505040c0f 72
    0x80c0d8900c19010307204a00784d542001000040e004080c0c48042d14010416036040351458103400b00c81d640041c03144001070000e140104244845440ba40c03044036400d0001c1d05002c60459000030450400740c070300038003801100850100c0c0c14131841c8a50041c028100003a0320410140c181251110000c1d240038904901d503e90200406400c0c9459040020310b4404440c10b14005442d9464038101c1046902c0c18403200840c076242c40da03000e006401c080c6100c3d0715075141650450040c0310440c3d505801200c01e020001d024000403d401c1340408100960928280202c490341d10000c815180e0100040c0e2440b0b149100884200681c4500300d8040d101136000b11503050340c0d07045403180113425510a42d03001882d280011614004580c41069211083c041202c8a1540c0c0e00049860300703a245d8019190b03c0c101007070030007c1103000d2003082c0c940e503800c48041c0b102e4141150040c4108210080483c02d0555075683d240d01004148180401090b00910401036100c3d242c002274a0120310300910b00c005814410b510 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 228750872 1250 228749622 228749627
    0x1020606011b06020708130f0602060106090e180f0a020f0a060e0d050c220b10050f0a02100c08010807060224070c05100204060e041a0907050f0403060c0807 69
    0x203106110503500d9454000040000032240c0414400030707074600d5002c005080101d0010340c01031412411400f1000ca100d8a000384c9031088040ca90400000c540101707004019441c1c0c40202a400e585030058950800c0c0c0f41c4903604441920302d141c10f0510350194401000c000784001c07842e80003050081d9484007000c0e11a10400401240071b0083da404140e5941c0c01c0c054a04001a00c419030a01c100100e96003c01c504001031058000c1d580c5441180c090306103071072030000240c01040400007081c3d8001a61201841c405840b03801071101c408141c581c041444a140d0b0305c20000061350740950b441c1001500400100182119424018580e462180940004903180300081003080100d1044590404d44143c0604a11158000e0500d404001d06807400f40d001c100180a03040a007211007c2c01a07a441c900030000d002c203800100e1191050f0b2804c4501142ca1081e022210b40c0c101c000c4490320b074141d6035401c050700d20340602c00d0020f800003c089800700c20040349500400110850361120100781d500e04604 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 228752122 1250 228750872 228750883
    0x509060f040618060f0f14010c0507141003020307020c120102040518090d050c03180109080d0c050d110307020411040e103308090f010c05091905011409040605060d0903030b0102 78
    0x42c0560461b0300c290810618a00c210a10400581450213410700140742d00c90038a070031115041480c2a2070021820300d068580404d01ea02c04080c241030a5045141c210300103506c0340d00840c0002d020f0b010100c03500480701020b40c1102c01521000f0110051f1008040000c14183c0045803200c20f01d20883c407111104600900c00c1d611800e607004003c40c0303008d008443c03807603100825a60f13071030501c5504a0302007003412052084d10b03807181035542c0342e590228a81c2456443c0200f4100c3c01424070904110b8562400b002104840c20240c0680e03010900109040b05880d840c491540304a4444010300184510448117441c04001c5801c0c0501c036040d4002400400d45001514100c6682c40c01e0100c1088185540548003090b401040c40b015500900b1707960383c0302400d407500d20008000090001036021400c1c940380c00200041d454013190310200c01d05040020384021400011710f52500804201c1407102e40d1143c21000140c0000791403552150700c03044001015100d1140b08a003c01c0c00d1070788201c03455200082 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 228753372 1250 228752122 228752129
    0x90f0b0a0803120703091e1a0601030b01090b071110020a0506311403180406080c0105040b03100f122a050105070314120403091d010509060f040618060f 67
    0x3d0110264403007400503002040464000c4034502410701c0901c000740f43d42c0c3e510720a098000c010b440504c418550910703000b61401403845052521300200124183d038031290070f5085c0c0f0b10120005030b82d1030140c18906000c2d090b0030403550b442000c1d950741011050340881c2c1035440c0346c0308100310b0300a511034045440c0c011007500c0159110807074031031440080f4402542d040704468083d030081072140e40d0354108a415a88416041d000c0890f090382840c00c44d0605100ea20014420607019041406402c03000905500c80e512a0151030680032010030f20030300d0802010780c028144140c0000360343c1c0e66007003164084500544150f031008511a030b1b00300260342c2d514460101c1c00600c114064810b04003001503840e900101300035020801c0c2004040307000500300c402810200c040c400d9058581c5001d190040004885410000c2649451200d0228102c1450071aa040d84d00440d003124403940d508010030203605100300056401800c0842c0041c40c266200d846441e8884550b50511103e0780f41c102c05640b03148540b2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 228754622 1250 228753372 228753397
    0x504080610150c0201030f0501140f0a0b1617130f0501182114101b02030904091103010f051b04081f09020306010b040806070809061303020304090f0b0a0803 69
    0x9601d1082d5200c2c40d00d804105105040000d20082c800c800f070302c200d410907000044030b00028400c01c0c480d03145c141040e64120100303c95110866082c42506c1c40503008030440d203c00c42101e034004804000005140e1403118007824040ea840c0c2d07120040111003500a032242c070302d10300d0400c0e80110b0030b544580d400d0150300050b0501041c3c281d241602421181d0035480030741010410084a80c0c0000e50b07202d40b1202c3d00d0241200814003030500701c01c0360084807003202c4401007030302d0040001c0003429004401d60313440c260101d400054403000da082c0b000320b030a95000d240742c5c0340d4680017100790007200982c04980070b0b103a140111003030407000d035540400701e1080c0e001d40b1070960b001020b010030300c1031303c4512050164030440340451b050445a003c20700d008401c1e088507280703010115041c0480103080103030b294007400c0c0d4545010941800041c007074452034041c000d204505400c4540405143c020801c403801450f190000b0403245100d88070300b00050505c1c1d40b08a11415222100185c041c1d000000c0ea091500101d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 228755872 1250 228754622 228754649
    0x3150d0b061002031902010914010501031a0606120a020a0807080705071103010b04090f0b07050f0403030f140c07050a08060c04060f031118040506220209120a030504080610 76
    0x1d108001030801a0092101107203c20030001c01750302e034803c90500a0380016000030039580d0040c90066005100146c484035940c2c58030004101040050340e0784202504621303c214144d450b030f2000714203140304000e042d8609482030000c0c021186495401071600c0300c1240e9480ba82c907110040304035204d40f026500900090811b000410124042d002030180c841801400003a0f140d4020021400b40c0d00c91500c1503800d84181c0a07684140002d500c5c842d035000c50185815490410412840300b654002c03800301900300403103c0b00d200b04460190a0009000740c14000543c1c407035190181d0103030364860078001d450003560ba08600007411040051451f01408a0010f0303d070402e801c00004591b00c0082c54a11420075840790350340301c5138010003001003410102007000c4821514194091109690707002c1c0245000d000304404c00d6406e032602c420091103c02000c80d01690b80c0815800240403071010801c4c0003100d01984010504140e0068010300c04c480b6500291555540d41b403070401110b0845100324942c89180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 228757122 1250 228755872 228755881
    0x7050315010305070534230a02060409020f07022805030c09160504030f05060a1a0f06030604091502250f0201050f041502160503071d090c060a0503150d0b 68
    0x42840709108001d0385040d080300c1d0701d84c01504020000c1e07081e000347e92090181080307000114226002002030300002004007040000d03940170483c2446103104060009074080780c3c1108803580c0c2002c50741d009030028140c14901113003520901a0071141c55001d175038450705403000501d80c00d0204103800d003414000c0800da07280d90751400c4058002c603041040000c1003020080800025400d00c08601114042e42c000d209519280c00040102e502040f03030800d200c0244a00341d480e6aa411005080303182050b03880b26180d4a400c00407a0140c001d000d0020b2411020080e003800760200c40e1701030310740c0e4100c05200c120688495100e4040040610030041d01c500f2182249002650180c00105186044140810304e0107a440c5581482105003210714401a00b10318040c140e8800083c0070000981003c9005c1c01d01e00785003c500c0d41607032500028000ba10303101000000d041002c00e01c07404600d440e025000650f60102c1d1a4010216801150724550175403943d40407104900300f04020701c000700d50180321100705031034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 228758372 1250 228757122 228757147
    0x60b0d0606140a0e0f1003080a03060e1803071410060311030106061103030f0403210c021507120e0703080a0512010e010302010503040f050a0507141f080415060905070503150103050705 81
    0x80180400d01e0b0007046d9800000155540c070040400c040255070015507281080c01d542c040308000b5000c05207052070400200f40c0031030b0200c04c56540b594090b4841040b807201881d407906001000000d0700300d07503160420010601031118141c07900504220020800310340c44100039240800c607480b10307441a9000380000b8450701c0c0f62105041e0001c0c001e041c110712001240f00b260480c1c49150145203022500c442c040d549998041000380000c0e80441d010008929026000501441c01c07181001e0f4a161a10720010f00c42100703028140107140c0104083d540c4849840b005402a1702003400040d01c41c0703400c0000512407402e0340300340341030f0b0754141c0d03590b0701d15141c58540c50b441d040c1c103040035203850040c08102c0307000560800c884c80c010a1610b18454800e400b05042100105a0810204411651003099120103070301004042c0e0140d030018018100b0701300784180d0802401903421040c000c1d442e010601400b190054055442480042210503440810301d00450a40f142503442002040062181d0b0340740c000e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 228759622 1250 228758372 228758401
    0x90f100f050f131203091b08010f0b100f050f04090b010908030703050a050f0d0e100b060301080705060310030b010f03020f06070c030602030603030c0102031806220f060b0d0606140a0e 81
    0x42e04d0328021030308031070f0340c2c917a20000448002d280544101c181c50411007010203004d07141d0744445521040150308181404140028280550f041c20004203482521035240030300161942003400468180d12542c840c44c2080050041d180340f280420000783c00099110700000440701c0040d4151346103814aa62a030083c2d9454000084110a28005011000e0681c0745c510448440f903c20344010300442d440c2c502460101c401001049000d050200010b01500344005410811150180c0300c86aa0355240070405e450115290802003c0704c1d001800010900c0314800a0f0054174021038100c42c45000201c1040110700c1540c0000b0a0070212410810100d020396010350b80c03110b0090706072841e00b01d01207402801c80e070084640e0f11404090004500c50b0768000c018542e44010504040340c2503c0702c140340700d607500e02d580310010b1055110070542c8003003111581010304114800340501e51a10781d0749c50100080c00260080343e4410030b94614a1031a031400c0341d10841100c070301c840801800d407946120071a00381c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 228760872 1250 228759622 228759653
    0x2150c1218030f060109150b0414030c031e0c01031b030b040213080a1109090312100f030f0303050f10140f03070b1b0102040501050f03090f100f050f13 67
    0x10200070305000d9582d00c2c203120200c280b101c0b00d4068240356060500c91400c0f2481c190520f54190b44501040c08018481011035081d0340c1050140901d00401100007842c0c80e2801001d070750140501c1001c6041d48003d101014240130303411059883c5480d08800450490700c86050b2524108800012240e8031070082c1c4c4003034035a200280000d40313806a038419038040695654000aa680d00c00b09100017030141d19480d150316844110f81c881c0460500d0b100442e81c074003903842405041410400400c00d80605130010800814030004161206580c0b41003002c0081e45079403058000c2800e04001071a80b80e20300466070300c01c440d5103034001442410008002e01c85101d9034641c0b074100b02c203003825803d00d03a8200b110070b004181c41c0306c0e40c039a28015450741c01500700f18000c0c404d50582c0103000900036a80c0000694010403400e01c0056103a9031220021032420069a00d9149540140d00840321440c82540000c0005c09004c1400e1040c0d07228004000041d00d011900a01d04444014140700041c18086100c80007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 228762122 1250 228760872 228760897
    0xb10030903020f0607050903070906030c0e0a0e1203061008040b1f03170c0d0203040815041e0303020c1e120f0417030a080109020a080406020313050a05010902150c12 73
    0x404030a105a80362480a40301c180101b000400c90a80a103020002c220250180800910540e40b80d07664901d1082e0560080c58103006034031f800907503050455441031041818078021940000f6a8002103c00381d881a030399507026a02d06e8503001c00c0140a4028a8000e550241c01c8000795038a100e8a00e40c0055500c413001c14100d83c1c040008041503407844007480307100d60920480e6030b951851380b00c03c1c13801c5a2842c07241c09541082c0410040baa60118400800c0c051070120400e40790344d9458400948100c03281e8043d43ca0107040d40c00303401e142d8540c1c00f808903d200c610071207078550404280c0300c900151070610360720b19622540d010070301c2040c404090305001a0140210382455191007a41400c8401710741e00c506258130201e07070800d40e40c1d40180002d00500c44070004601d0154010401480c0300f20081000e8402500040810b840c88410f6444400b040c0e04141034900c04d04462070302501800720000281d10810241c0c14500e103110b0707680c08541006d0007040040031100c001e20048942508000060f204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 228763372 1250 228762122 228762133
    0x6030d050906091306060905010206160f030b0d060b0406230f0d020a15120c0c0303111614060c0301060507030c050703080708070c0603020901021002090d060e030403050d030b1003090302 82
    0x5564a0b513040b40036060300503102c049000d40c140100141450072940c0540d0442d800344042c00360b2900048600d4a00304154507060501403464407007034002c1c1c6100d85000b0b80210754445a4824401c00340c0c00401c2d104c0c01151309206c590f0ba60a003a404003044035413051920340c80b02d0b6546007507181c81c4141140403200a0164002c8600d29000145040015445004081c4e5030302440840f10b5400144030078203405a010400802d0980031009000c0442d094004003415075841c04441c1500302d00050b07443e00301a07498541a10942c0d440c004000003c61160140c0034400d520114001814460650341610700300c0da40e850070071095031001c84d44526400d4055680d8005c83c0d1004c404610841d000308842c03401055004c2e500c000c0d6140916031001968002410148140300710100c0f40c5e07010644000c941415040944c60380215000200b008041c46130007440f031864500d403070280000200c00380c02180e00541c207407045400711076400d40030b9036100600b81c0c3d030008190b503090103800d0007603012996a078040d02c12280b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 228764622 1250 228763372 228763387
    0x81002090a08120d0b010503010608060607140105070f1403130215120c09090603010b090112051002030108011b0807210e100b120a02060301031221020901090e06030d050906 76
    0x1d04120004031406541400000c5110784d90016000e044c450000a180c480e10f1585000380042c04010060661403060b280018801d0a00c80c00300043c510381c0b40140000c000908100b480500300680e440210400314140d141c045200c16500001c0d02e00c00c0a0b003110f0310008110a6007045259010a04c940090f40801c0c0521001c81c529401305030b00c80d5541015255072400c46800700540d1040c000c203454440e078109007000b0b003143c69008019045031074003074820f602c0001918015042c90307101044a42502d00c0070000084480d01500311401c4240e6086981c0d83c10f01940000b12000c0320b007198540d010a20040f8400c0d034400002d00c522210303414003035000501e011100c294a00f042c514025000805440b103551381413918200380c84030600e0040200400409590b5404103400c1d0105100282040d003000748005802805a4244030310448802140d041304000202c00b8402174008150041c001059204086003402c0c0381200b035409078100900610b50030240c4da1048510f5400900d000380c202c81c1c10b00521 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 228765872 1250 228764622 228764639
    0x2070b0408010203060112200c0102160b04020a0e0708130f08070b0f0a060302030a021e0a0326090d1203241d0705040905040f0c031a0a0204081002090a 67
    0x100040c01c0010005641c03404c043c0c1c001010031006d0600482ca40f89800025400a90044022001c0c0c41c02c0c6040140c41c1c8a00260590090007090218402e03200f40b81c00000c10850800c000074440d510850f40311910750b448540320b4005107400c4a80703a001c5410000031481612090f64000c80142c8500d0004003800425075883c1d1a941009071b04031000414075080c0b1140f023410320843c1e43d12103034101040044d40d16540000e40c0e11052030070044c4c0100b02c6010340f690081d001b0510345120404c0504213950480d40ca11748090000500200e5040400701e515024140720301140c211031180d64001d000b0004001035440d42e01201301c0c09001d010605076203a281c0481034010182481c407220f040c510910400340b8201d203103110b200510b59802c90b145002410001e07078541000c284d07000c6d00c00c101400501d560781c81c9001840e84120b2007025003000a070030000030800640584480301600c441c01012031039196050301c24140d0055025410054120029254100402d03074003400310b01d44018140d001030341c0e550050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 228767122 1250 228765872 228765877
    0x3180b0a0309050c0f030d030f0b03010905100b0306010e0a051e1024080f090f030d06051f080a020a020c1002010903180e0f04060921020c0414011502070b 68
    0x466100d1a0b072400f40b000c00e00c8400000d40c2c081c0c848010500b00fa000203500c412442c64042c06055480c0c040302d416030f81640c09805040304c007034020072002201c1d0030050358400710b141e0074800081c101808203025080200343c03030303040300c0031280e038400e541c1c4490002d0b00c0a00001089848051481068000400001c5403503500034120600307201311060514031200804092007000074281c0c0c41c199507001c50b00d80e00407501c0303a1100d0740c0d4038030091070340b0b400200d241031400e4190500d0240c4000710b60140b05103540e901072401c441003202c1c641d0040d5514640130110210307852184010070143c000007490a00d003500140251002d51056070a001e0100307000482c0f100742401401e00507950740306000308042d0000100c005110b803441c41c0e860324624000c00c0aa9416005240b0780c407202e0300c400442d040280c59049001003951245079184182178400c44115800d2047c507400300188503491120206c0d0400c4c1c0318030000040b8080e503800c440c0c0e080c40d0f483d81500c141030708030004510902200240a6004101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 228768372 1250 228767122 228767137
    0xf1d09010b0306070f02071a0304110a0b180f040e06150301090b01080304060905150d111b0a0201020105280b03150703060509100e0403120b0d0b040b0f0405070303180b 74
    0xb50052042d80360f0170020300d8081c1e240c10400711029441c45041c100b1015400362944a40c1c0403410010440a910109154002991100a48032000b00e0034141001c9029040310350964140c0d01680006a80c20801041d1000091440d2082d00201e0110394816a072440710701445c80d020380003080c084059034403844904000d071303c8a9050380000c5010b03c030160740503500c40010726007220003803103802c030994242407135105008521100795900d0042500b142c82c0b44060b42d4240c02d00601038001d01c51045006610786084110403030041d4a040001920500440e060200781c61000a429080c000d4880c5c0c0c1d039000b4038074602e100768984030b022040c5810a09040515120b48900e40d40490340d1803820040c0f12032082c0c0981a404089010302b020f200d00005500541d501035003500e041d560401c0c03200c3ca600300400250a81d20703000001c00e0710075001c0c003101d403005a010700e1080c40804204c2e41d07810800d452009040d20300500300e030130440080003c00d204183c0c7d03581381d02e82c031440c40d01619035032100b00d030b03666001c070300b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 228769622 1250 228768372 228768377
    0xc0a030f060b0118090203100b0d0902030f1f0b03030409090c030507060c081c060314010204050a0902030103020a0b0706180b0411040608030301090c050d0903180f1d09010b030607 79
    0x980c940304010982c007412500901c207007031280134200500d901012940b010700034940080d80c04400141c80700c0403000080c0c0242143c506050751040c0491680c0013401c640341c0181c0c0a072007258800c00c042640065001d1150400f002607180e83d00d0102e035030740040c00101c480b0703982c184001e00c4049600240d91265602c89842a03009040c41860340c07901604001990b0701c02414010300c001e00ca004070b03011030b084401c0342e460301c1a21801040201121401401240c0002d40041405608082886e0055008000340c13541102c3e080c036469500c0600c2c0b4260f00c07090000070b4000d01c552400300300d200c3da250302410000c0e104030408550100d41c0030050340a01940c10301a5076000d5410140000e21030b0203c051201c190003a03c040c022075040500c103540d00d01c4184030700a025507035a0a1171454071322820549126120341c030300900c0040c00d982002009410044105520071070348180001d03030500440a41c43c101c41c128442e40041a1021000300b044080040c010480d95403a07041c130350b02581e0244842441510241c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 228770872 1250 228769622 228769643
    0x31f0b1305161106040201050901020f100c02011503110d0302030d020f070c0e060a170a0506040b06090121060525120b010306240c151a040b130e0c0a03 67
    0xb0602140144105106001480700700c040f003400d40440420400c0e405034081c00c0c103664035001400101d03d8141d4480d90040c079802540042c5028480342d400518988659074003c2c400941e109410408080e910712004210703002c01e01c055015401d2050036030300054040d0040c1e904100c410100401a43e00480c0840f00c408000107003182007060010428000c1d240c03194002182c0d140032004110016103a0054140081194802c0c941c0045c08004400c8019880400d880031410a89030514500070141d5046205035103031800468401e10408441e05078041480d0480702c1a440f0b0f031a035800410000e00141403078514807000700b448240521a103274200c05181d8403880c0c982d8070103400c8030884d08003040082c10142005400c11801e00a580040c40e0080040380340d69001d012902c0645001c003409000501e42c13644040c4008014070507500c0100640f40e03081c0015414240e40081104a98080c80003942c02004058007007110300f142d40c0010810007203401282d01c0c1c0400d001c00603040441541c0212001002d8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 228772122 1250 228770872 228770881
    0x507020405040816061e0506060d1a10200c0d08030a091e020a0b09060a031d070f0311040c0516060f05090102071b03080307051c060b040302041a031f0b1305 69
    0x83d4040c2c01c0d941b81e0105403c11050410702c000400e60b00c19020520301c0c0545819406000204100901100f10350051501c401d4034500400038010094600c0d01503412019420340000111010a030059a02c1c0024022070843c102540c680603e600040c00011100d40d03581c1295001404050b00103111584000c401c05126001348100300c42c10119030000310a2903000e000000e640e40b10707c8103450b4050301900303020400c8005210030308504660070f194028944650940080d020385e0210292050300e000e00d05551030104800103104c192010bd0700040005401080184c1e041000c8005182c0a540b0945001c034503c4083d032444001e07074409880703100090350f00040110401039003044494140789600040c503d81791030b51b1905841800700134208801e0002c00070300d403002050031103425180c00c44480d02c00c10503a40c480d13081401e0b075041800202e00440c034156110013194204101010203090041c01044c0c1b82c80c081044040b000f420b9200c0840c2c41e600c4031180c90a0f5502c0f0010500d0203a5040000900e62030b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 228773372 1250 228772122 228772151
    0x70e1005032202031f14040b010806010b0c03040302040c0c141606030e06010504020702220902100e030705010f050714010f1103040c05010e0d0b071e02010b01050702040504081606 79
    0x6880c1d16070801440384502c40006840110781d0891640103244051250001c5410040107030401250030490031400c1d808100410502e1941c01d1f0507900894202c074100d0380c07640c0c0112030500c2200d09080701a4803d100070001031806800000309401d96150010b00c1086641e1642000030b080d8070035030b0160300410b10781c1420411341c00b10a4002e00151a040c4a284030711482c0c207443c1c1106010745801a600054a1425911a203404c0000b46a2a40401c07041a0424800e84024880410128800d0340314024004107541b150075980c54840000300600102d61408005449495452001d0014060107101d1080855481c0344514500c4c0383e003200104207116100112404c0320181805400002018003d210205039041c211405854013801e10300306010306100050801c5080c46001042c10b007506d03003003000840c1d00548000c01c0102c00d00c030a9094650340c50090782690f20760503980d80050b20a00c2200058074254010300d8200d07014119440ca00a110b107012214090512002d030751305611203d17905032030b51 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 228774622 1250 228773372 228773401
    0x21030b03030a080103060c020705030703050a02010e12060f07020c040c08060f01050a02030d0f1104031a151c020d020409051501080102090d020f01110712060b0406030f0b070e100503 80
    0x110091031600280c654003818101d0f042c04080c101da9960982d080c2010b008100e29000b406004080350092580c03444c20540c2e807a1101030487c00074821000540003800c0c51404204101001005480039994072003880d00c1c1c0a0004052500314850811281c1e0207440300c2c8105144140702c1c2d40d07035071114a41001480503c0b4070080c4400c1c1004402c1011003103240c0d01206407500301c10112004100d00d18642003540c050140b280d404030304140300103400010400b1103001030742c0700340503a5082c00c0243c2e10180c49140310b5a41c00400390700102108440e01101d41c1c0a00d01c4c520840c070040c0b040355070300004d8000c10100c4513903085c211442d6000b00400c2e221544240c51003401006640001d40c50099244003082842200c520000d000c1c542d01082c1800ea680255411010030300400304980210b40e8881c55084e10032034107031082da8220320b003000c46511070811340240821340390403d100403400420b640d52280565402041d5000708029060155500d54401c50850a48030031030783d030b058903824204071031034505 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 228775872 1250 228774622 228774641
    0x6180e0604050712110603010605030106110f0d03021b070e01061205090d0e030a1a01090c020307080a0c05070e0a02030a0612050a062c070e1e0f060604032103 70
    0x591040c020040069000103400c0c05440740c01d03180e40c194141524100b0000d0040c0c5000d07650024000c40003084850b40440918100c41483d41e40100060300760754040d85a81494540c0607640d0004280c0e140c800303000c0d800502c440c00c2d19480e05810b8000c0040300300c1c205203007030304091070350744901e070040041903488840020311001c640410811420441d6140c1c0d506c0d40d1200f00d0000303028290a4903801036900f44540048a40c001000040d0750080e48040304900700240641401c80d45001d030380d181c00b1803000090f01c2000d42e00c41c4140e0301d452403c00741a100121889000c0351688070301c07400801c641c1c00e01d0388154000c49502c100907071030f42008010380098401c1074004241e40c1c0c2c41d0301c2c0f103000440d00004000b240755401040000308103111880380701c6030701894448940400039a203810f941507003001500c1c01c01c507030512580e003c2d40d440302c150070040801e048d0f40d06040b00b203000703000c1419002e400c025950000c000402e182c0c5003c1d031760b60f41e80107001d004622903500680901c41011243d80c26004000790b4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 228776978 1106 228775872 228775901
    0xe01170711100608071a1b01020a031803051e1e03040b0106030606230409090b0405070e01080d080a060308040314010e1b010e01120618 60
    0xa0700d44440e200149200340b1a22180c216924481d08094071440c0d00a89070492500c1300788102d00c2e440500f0076031380c2c003020400702a2006d5041200c3c0380780702074240050b071110722030354020b801c03039420084031ba40b400134060810340026841b000b1140d0320005400e2401529000261749242c0340502d01c103010040701d040e410f080d10240c5000145208900c64030468500e40c0e00d841d412401d6800c40e1240001040000140c1c1e26071401041c42c10f090030070588440c030306240da9260706206442c041301040d15200240401e002c2482801d02004014140101d040704881d494103000e40d65030120700350706c581040651030109420070601d40125001f590042080740d282c0c0d859003448102c80c128158000510f610301a002e0078800b8010900b000c206c022180f51290469403200103540541d842d1440c941000880051520207203140c1c441c01d0040c24800b030303140c0c2e4a00c608580100465401000300b820b03 = true := by decide +kernel

theorem cover : BRFrame.Cov 228597122 228776978 := by
  have h0 := BRFrame.cov_init 228597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 228597122 ≤ n) (h2 : n < 228776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
