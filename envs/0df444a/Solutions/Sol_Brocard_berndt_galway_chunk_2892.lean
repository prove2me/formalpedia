-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2892
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:03:02.195995+00:00
-- url     : https://prove2.me/submissions/4da56a6f-e129-4388-9325-87ec24993f76

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 519964028 ≤ n < 520143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 519965278 1250 519964028 519964037
    0x7030b13060b1c020405100e1f0806040c18030317090d0507020907021014090d050c100203070c050102181512040210020f15040327150c0210 62
    0x2094401030044149480014150152400004100c0011803000b0b03504682c0010018441c0345a50180c241c01034001d075080280c2c04020b403050740d90070366041446001e1820055824800c0d551020201401c00c0c0500324a80010803066030004800d403400740d000385504071007406e001081074101410201c6044403030b0003ca01260100d400f0641150314082c000341d2003241603009058a10800034000c00d54015100c3c006e0040000c1c40104104a00034000e12455010071003040002e035103610300813101c540f416a00e42d2b51398002c4d529190f2045100300112400810040001c02714001c00c000c1030303402540000d03c3c00081107100f82080d400a0020300040014000014a6a80003090b04041196602000402e90501c000422221080c3c11607402d003a584a601140c2e200503088164405074140742000c615401c19000b510000f9540d40c10144101d03014500030360300c1c0c404040482c19810242d00301c900c2c40003401003d001342042640c0c40c5406458641d5828607000b8003e00c03459002c542c5600c00e0303005110125 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 519966528 1250 519965278 519965291
    0xf0509030a020f030301120f020418030e0f030a051c0c0209070c03090e071709120c0703140c0307150e120f010c031e050c09090705040e0906040c2c0703 67
    0x2d82c10410f0411410b00400954a194034042c0c005000b200d490400415204208603040250741e501d80c4501680d4051055420501e404c5140040c04a5159541035206a81744424a9050f013400103070607000d0390303110000341500c0040b0040c40740c0340b5412020682c1000241a09180142c0754814054000c62140e00d0300c107140441803030080d000c0440e075000010340c80d06140811190300d50050156851210303001c18103205440e00494642054842d174041d02c10090f000403643c8485200107010011a401000245055400140c0d800d484da13098042196140d88030040c103010001c0c3d107114104644413103080c00031030b1600d940c0115103090b401340c0395901650054240d00038a42402c0c02100d05200c141d14041016111250350b0306915025500d6450300c02d40d480000800c9036010074115450000014904455440c185100078900e90081c0541c0b000400140003080c61554000340450255901c8050000c0d590f0900c24030303414090098007081c600004050041d00c3e039650900b409405030001c5e035000300f0003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 519967778 1250 519966528 519966547
    0xa0807020c010212030a09030e030609031c060302010503010522050703061410050a120f06080a02190b090f060d090c080c011701050603070c0c140103050112020109031101030f050903 80
    0x300101e41c0c6165055400c00070044807141c00c0b500480381e2120b120100055402e0860070304854200e10301481315014407606040c48100b4a00101901d140309820000c10f481001031009642a284288802808140e00b400180441c3c58100c070351007003420308241140f009901d030040300e0003034900c1035a080011035502c0e42e05008003c2e0100324500e9940080e10f4000c10701c03605042c0148188035280b00c440811041408c001100280d03500180c003010072503101030140640301e180c1192207815a01040781309045051010f0221088692036104841d03601c10214205107000003800000c80360110141e0340b00320200421722542d840c03485941c007260b0007900480ba003d814071020f2841c00c1d0400b0751a50511020302d80002d0384074611101c0c1030549405039050b43c0c5030b480702130042e10300b094030040040100c40e14200100c0d240d070b0f0000900e042003000741c0e024001c0d6640e820341c0303e0407410703c080e002e8001084c00c0002c2c8085454003040d00d20862043c9400180c4ea8610491101115015241003829420000700c444d01e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 519969028 1250 519967778 519967783
    0x6240212160b1510030e0c0a180b030f1005040309410630071107060306050d03031d0106170c060a090e0402040f0e06100b0405130b040906020a080702 66
    0x50040030f0702c41c0c8008152964002415062201c04442c4c10940c440d040030702158070600040442810140c002c02c64070341c1700c00b8031825144160b903100c07a40381c0c9800c0403003c0526001071545d660008503805007521840c1203038240080c210003031058040c01802800011000720401000041500351121070075500c400009503131012010028a54500c008402a07210716600c81c000c5070501c070000c12240d10400c521800004050500c1111240604680020010040e401045944210f082c40301520f5440f92212015412100d00d4010590003022a0481d000068020380c02403007991102c01c0c03603400c515240139203582075801d0350b0400210a0100103154a20020401101108070000c0b04c6a034140212088010318102c003903c04d8260010b820340c0443c00359110359000b1400708034100d000f8898009040c19195450320107a61080500100000005020108605580c159140200800d000c116500e06800141246030b024a900550320480170b800a007071403006254504003511241e549140c105406070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 519970278 1250 519969028 519969031
    0x90c0e0a0e0d0e0a14130509030d06060203130306150f09020703031d120f0705011401050f0301061401050c070b0c060708090d0f051b07080601081006240212160b 71
    0x1000c2c0f1940248808540e507902060700240d621007600000788440400000e004250301c1c580442049180c1010711079100350110050820b982091800e00c803841c1c3c0c60074120b07a40c1c425640c0001584200c100240000744c1c2c0c54009454070513840039013100007034039108107000c00fa00903440b0364040d80c2d0005000b410543c050194000c0c0200e900b09855028800c0d040784d0b522202c1728038901128003400603c0c64000100c000c241c41405805c40002c020165901440c4503003040c080c0103262155554410701903880c41c0500445040d0342d1803203828010208540019226a00039480d1f11000f802161400300300d030710321ba0b0041c0c69080400750007841d07542401d4201030445070b40038182d80e07429001508002d2501d9041542e442c0700c00103130300d0240d64648100681c00c00c450b03204007500e900c60145903400107150f1000141241a106410261a142104620360300200c03181c4e031045000b2525060f4403005555805000d038902c503071a41c01551581ea00d207190b401420b41c0034200c60304051407004049030500c525070b00d060303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 519971528 1250 519970278 519970303
    0x61f05040203060a142d0f04020a0c110609030f06010512070803040b030a02040e040501060510020706020606060310030c0b0a0207060912140708030703080f10120303090c0e0a0e 78
    0x11450340c03c00001251121046000d0407610b0700c801000c00005449003140144501c0e405502514800103000842401e0a400e5818901c04c0d20141c0307644d040c0e407401388201c5400f954280c1303905405462541d500b070068100b100150381e111005004004050f2024000081c1802110001c1c3c68958148010030082103400c02d201e880590201c2e40030311904400008840649810340f1714140c4036900c002401c0040d100710b80010616030613610600003086415044201515070480c0c801e4a82d640c0014126603484461244800681c0f0a60109186c2e08040300110303040310440c000d085651341c0b25118081200c803940d1140318030350300c0064802d80403681448244082c29551500d400759902d021b0624185074852100509252900d6907225981101080b40b03000801c0082d0940b03403144040e05001e00361101c107d505103103043c80030b40051010040e040c06c280035a2000702c41910350b5403c507101103000303103d8000100c4402035401d4010802e0308a90b403601e072080c03515070f02c0890034035410f00e4503900f44140c0c290038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 519972778 1250 519971528 519971531
    0x31401120803010e061c030807200a0201030e0124140103050c0a0f030e071d0109051e07020c1f02011505130e070e040c03170418090f0203061f0504 65
    0x550001d00031000300c81c1181d650070750b02c61994030340340001100c205a5848001d12010a0801d0408040c0c010f1a114807502107601c0d04550b00b000070b00c0c2e56806800b4008201c01c981c11004c007101c015802a40040214600c0d03000029002e162007003400310f0955180c0e4100010401e4080410020700300c290040b440368400c0c0790911550921901080c241c0c0601d4800f0304c140400c14a15801862003503010500525121044540150741e507200002501c0c85190240b041408030000816807161501805000d8061f00207100c2d00652100040580504007038202000c500803842a80426a9804030307140c003211001c007040540351485000a402c407440000d034805001c400500402083d900c2010b849010500000d011038002415401e00d0304144e92a0044000307070f201842030005000c4450ba00b4030590f842002001e144014000055100780680d10514040b0300b00c40c2c995502542298000040031031156a05000b40511b40d8002400c103042240e20b540e0803072000040b260b0903440f052600006020a540 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 519974028 1250 519972778 519972809
    0x103150e0601030209150a0906150507080f070c03080307021c030c0806101416030e06040b03070c08040b03041109070f050904020307051209010b040b09061c0201031b031401 76
    0x5039161030781440003901c20700860b00001e800c46545040c2c0c51034654010f02d04680710741c4a03288080106420701420040c05880141691120b0044084030701050f005469036041110403095460207038022042100c507840b85510002c000713103c01d405180038030043d8000d050030b095628452180360038002000010181002c83c0600143d800070340054000405642e441502c20199000f501c4461021510903c000c81c0020f504540010159000002e80d00c250346040d60503100304200032040c01207003d241c1e80e0010070400300d071151340100111034082c2d200d060903a0801c1e6451034240550b0300100c406942e00804610031070781c6403408410455100201e410074045d40d42d0280d0009007280508402a4041c03680040071038900340c040c0e4140c07103580643e1000b02c1550b1801d981c42c80d0180014045c02c034010790424000d0401f510740521645e10881019140d1910358056041d0700c060000103d90980c14140e841d07106d0100d200300c19010007048200c94401240c14503550320314284014050307221031250150405d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 519975278 1250 519974028 519974051
    0x2010c080f0a0c05160b060a090501150806041e05060103060b0f040608040c0f060210050a050606030703230a021b0a113a0b0604060b16050111030c03010315 69
    0x1608981020070403000043c0c0d2003103903206403040c2c030401c1c42e107484080c0351500700d008002c0303251002441942c003500d800035869a5030b0144029140d0a00480310244180c8004030603071340c42031107110741c0410007d00203c0c95244d04c92900045000c2c15020b800000d8840f01005000d5030140658402402d0315035070303549440040c1d011402a400746002d54001c21103d83d0108050100740d8140d10043c110302e810301c281c1c5a43d581000380d03441d10100880070005042000103000100e00b0b208051140d08050b0202d440c690390304030224000c01400c2c0020520484600410140c4440070026034411030b61868010782d2031101c0110090240301180c080e070f409502012100000800482440310440b0054440102a40c4941c910b4601c81c900d64403c1d501035102c44502000110042c11007085171401103050703128a403224420b02040c1c3d022401203103580001007044081042014001e40b02540c05900001549890042d42d041c2e2139109845080e59054040010700600c5030101002000b4010b40d0020000c80d00c145 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 519976528 1250 519975278 519975301
    0xb1801050105090a0e0c0304211704020402190f17060604090b0a1802090f011115070207230901082a0f030109030c05210d020903070b1204020102010c08 67
    0x1401003604004002c925640f00d82c40da00046800361442e1142402c0e02e107094074080328a80c00443d4207480d00390280b1300e81c40085440780c001014480c02175540c03104032040494400c41e41038000e44101d0300aa802c2002c0703042842d401d8103d10100815a031108209150054014401101d65200e0103643c2d02d1402844400d551f400111030407200c1465000c280da0715640000380500c2020746c0038040d0b10380b45400c1803c1c08580d036402410003010440d03848280342c1054004552030b05aa0b01000030715172110383e2404864061600e0164004c1892040790304541d01c034410310700420940c51960038403605510386c8038014075001d840107002d082408010002038004503480300c0c1c080c02ca8a0700c081c030f00b00c10549080094460160301d202d4610003034024031410341e00d440c3c001c14040d1100c1c3d05580f02e000e403000d81070355115150b4040d60311030710b140b82b01410103c2e06181600294404810f007030741807152100c000b0310031002030f000c2e025560300c0c500701001038a05400064203542080c00c214042081c000e00308843d4100e40c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 519977778 1250 519976528 519976531
    0x46030b0f01210c050906030f010e1b03071409120705040c020111160f0f0809040605030105091228020604050c15160c0b030907091107020603071407020a090c030b18 72
    0xc4107004180f00d00d1000c0b080d1002d00c03030201c80580080c000000c11184243d549000c6040703a9810709800329513601c0c0412042807400303a00c210001c948042010607a118403501c07805e5000c00e203401c1c8803860840c07007078002480030016000d000c103140c2281800700301d6458203116811400b203080c0003d010101130003c603103003503101c1e14100f0f0966521085004060041410711561115842151101c00e20340d1400c8c8034940340c0180c03030082c2c455800c100010545060600070b06020781d600f10300910740303000000e00403001741c0c004458403c103811015012460b10000070740180d1110116401420040c00c1c90300b000b9081901520b0007074040c0d041740d05056440d284d0038040b60700701c60300c01d4508507030f50205141101c9844a958030540d0715050200a01c441d10002045100c22a078007601c04000c0e0040802000c0d045011300b080203940850103100085501c0e01440100308450300c024921881c0408a81c00540c510106400c0001c00c1a618000140150342601c1004074a107401c85849000080c405c0c0c098204810 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 519979028 1250 519977778 519977837
    0x3050f13020d05030d021204050c121009020d050109032d050f1c06060504050a0914040f080d0f0f05153304230646030b0f01 55
    0x2c00e001c0c1400340030081c0309843c46420a008290741c3d0702e0313144400350000c40741500c0655240c0107140d00304c511403800c110803060042075100078040000d060f0021400421005400344c0e00800d842c045000012420701c5002142407194030307009200380c0d0301da41020058443c2c16000e403221100100c0f04819581000954142040660065503251000c0e61f448024000700f048078001c0030304104001c66080d401002510a42d401a64001200caa403200b40c101038640c144005001c0c6012040070401003044914014190750003000c1c420b2910103c100840308840d009014448643e90b500c1504030305800b00d004141d00318015080c1c1c608a506c1c0380001441c582201044444141138480388050381c540f000da01c030200b54a40580054070356a880b4020100100c008020320101000204001b0741490b080303042d1207150140c0b2400026410181ea84450702c5560000d5062600451104005a418044d041c030311355010a507601050707102c00b40c428480750070070080e080c07030502c61015100c0c001c45c0381000d84a0034680 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 519980278 1250 519979028 519979039
    0xc03011409040f0605040c030b0a0c0c080901020a02150c010b010e18090c06070f060b0d08070f110402030a0903020f123f10060201020901090e040c0e011503050f1302 73
    0x11034503d01088040e000360700080c1030724101003c00c42071100350101c0c441180e0003001886039550781c0242010803598042007202c08100508180d4001c2501c00b13000e80380c00603040c0100d4000441d180c00040c0c48200386d40c002c20000d4030015170299030340801c0c02000001c600a0a011901902120028020100c16074040340106c0c1100300103400c100d002c02c90640c441e0400b4106c2aa2034284c0d05103900320f01e0855109036181c1b810292490710905143c1d48a840d0203800081081c2801504c0c1d8941801c00c0791424140e03001c5e0841e4901505581d214030040d0b0258000030300000311040c0c0b52401a05080401582c00c520f034015465440d034041c075101c01c903054244e02302d0305614000c4100810140c40e80c0303004c84500d1101d07203a440a400b0b0101c064851030082c01883d52585c045552850100c1c240d22940800f58001100e140c8104078441d5131210264000e40320b00c108125403500c0c0c03000d07048404000d0303120403402c9001103240e00e9590f415204042d00526410003130005803030194001c000982241400030b0148 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 519981528 1250 519980278 519980281
    0x80702060903070b030112052103060d0c0503030412060f090201140906040905090625090b09030109060903020615060306031209061603030614010206070f0f030e0a0b0f0c03011409 79
    0x40c2d60030f00c002c1e0003402c0c4000c1025100e58503481e038110210180e0000f243e1038030540400d01e00400d10050030206070700d0012441c0c2d265076a01d6003445400058800200c48250302c1100c081900d0354140054000b80103a8a03184a840c0524101202510500c0c0068207410380341030b09140151764890403401c50b804444611a17030b00e043d1100461014882c40e4807110b50305203132909200e840e0002140c800d000c0c1d490200f0b2495071920303841c544c10300e20280c030b980040403039125501080505a40409081d0030240140001008031150320b802d41640d4008800b03c005800c00300400c00301c9221503c40040c1007200360f0f442c90551030008040b0b80d0ba0ba00f590031040e04400c000c201c012460342c4450446010307841046100300d0410152034058090f0003340111041d00620603400300c3c141d4800030b00940300c1c030b905a94a548400c490399064815041000c154002c154840601c101c0d01c0f181040029500340c13007869488014540203803108a150006002c400c02904100010829000c8030070000010240803030b00c4544030f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 519982778 1250 519981528 519981547
    0x2a171e030717030f0f0c09011d060c0a0c0f03030c0f050a1e02010e10200f0d05040e10030804150516230c03191b0b0408010e0a08070206 60
    0x214040c000340107241039841001c02030b0030314034807010f036000780c0e400d43c031850940e2a401c1e08103021003021241c070102d504061100701001c2d03100700e28940d14100c2101d0140141824203011449961014841c4203442d44070510480c1086868010700d40100251170b0040803090039690001d28909900380041c15104903240000b040c000c0130302c80e20010540c40300c0007403014910310040c1d00c00c40d12400810380c0030500451b100c0308142000403500450401d00d40c1d400190826102c044451841d114440f01e10920410500b404c1500e400c110032602da12083d1145a1194a06036004000030360046c10841c00899050b01000040c2ca40e100703603019180c20803071002101c0c1c14071404686074020541207d98001c3c513542500f09000f8088055461070003c0f12000d03c10280c8940360b01d44c2c4401d140340003901540900010380b81c0045102009054500c030b00142c48107c03040d21140320040341503400031012458009010060000c1c2407294510415419020780810b1295448034402c600440c0340c040d00070000003491106 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 519984028 1250 519982778 519982783
    0x12120c0225051f030b01030c0c02100e03032a03040807271401090506040912030e010b040c020d02150c16020d0f0507090f02090901060c02010203072a171e 68
    0x3400e0041c05080c0e10410044401103203040543e110360100349407030300340c0c6030381d500c00d010700c14042c150750b203548400594a030301707000410088072124400c1026892034012140d40500003000000c080303071820030807450501d03031500b81200001040445503008100802c291100441c4082c12203001c039803803248015007a146ea0350140380700a848d052040c50100820701c84401440810b06076240c0880c1084569104414001100c42c00034010b8110100d4445005125103c0d030450715055010400205036039500300f000c40c003604c08a881210150304500310320504103604220103d1003545901c10b1030503030b050886261000744220300c01a0303400302c0e01404c994155254554030300207996120342400742000c0745003003054940000e801041c0c4404d06140b5200e0a100c141d00a881c00d005c030003441e0300010b902e480c0e002d9518601d660030032415400203110b403070081400c0c103104001180e4081d0704000d0a035561844c00c060f1b056039401c80158241c5021400c1c0314182e002841022a10352100c1c16010846084026071 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 519985278 1250 519984028 519984103
    0x1b0503090a260708040314010903090315061e050306070c031e090513151409310501050a1407080609040c080f030903010b040504080f031e0412120c02 66
    0x100c141000480c0b40130495000000c1c41100e008207101010b041803450210b003601c5d9081005800500002c0741800031681e030b40d1102d400950381000000744107075545079950481c548240108010301e0200d004012170b0406000b0281c0c010b005251014000e170140d074014000098041440740701040804103160300394000c40402d0041c020003008441107220301c40c4400080c1506102c0c0c200201c0ca41e0301d0004000324803d0340460f09240c0140007241666a106d03d481d402c072036010030420a4003041c2e0341840c49110300d000010a850089002041c14940201c40d2b00c00c0e0b41054440101c17456001d02002106c0da400654590000000c844807149a100c0b03040065545000340c02c203201c01d01030800c44000d200c070000300070825024241e000748003048050007040121442140c02803c004020071041280c514030600035548030302c5201065030b041c841161181040441210101c400b01520302c1d03079504081c2c201035602126500c907007040c0a004106100251540111940b166400c0c041c03010822602c0705014616 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 519986528 1250 519985278 519985343
    0x70605160c0b060d08070b06030d0807021b151c1a0a06030c140a02210703020607110111030103150b031c030906060815061201060b09010e0616061b0503090a 69
    0x191b100c80b100c1c181040300c90801d42c0d00c04d00c00c0c810054031045c2580204102c91150400d50060001c842c0000c20400190fa08120f805038080d00e0b040e9441d410b14240405060a07400c11034016143c0c1c00461b5020b03080b0780228603010036005071801d600e4042d07078500303480c0c1081e00c2c0c06150204030888080c401362801c42c15132401c8100391201181031801164002782446c01c0d1003400c250903e00315202d2921103628441d043c4041c0068004400154400e40140346a0400110010000800b205034060520313041e0003c0c4c10481e610300340701c6184034514010340076040d8004000c034003034921b20034080044280d00d480386c2110000d0540303c640003000d100b00c650065000b0885a001c3c4c0c1d058905115135005641000c80c1d01510840710004442203054052013a1416101d01348600e501d8284040300641d5a400540125640030008021080d0003085801c0690300e150320030180807a00101240c84141080811052a000c0010901c01c010301c0b424000b1b140d0b1407094010701203010f80c0c00c40c010007900e07141c95007804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 519987778 1250 519986528 519986543
    0x1e0e1509060d0f1e09020a06080403231323010f0908060108010b011b240f140403120903020712080906160204061a030612070503010f02070605160c0b060d 68
    0x2903d0304800c542c100085596895030404c0303402c110f49620b1011121048006904000e000605200340780c000d040c21a0064000d044c044540c80300191121201031f8003090240c2202d0000c269241d4144078500030002401004403c0f40c00000c060b50308a04812100303680c0c50400018100d51101603005082c101c010380081010f0354403944c0c5401207280070346843c640480c00902079081e80101c5421020142212640c01003103801101c0c05004005400300e0000086806c10b9660444441940102c1c441d0040e0300300b004061320361524113400c0160903150800c20418099042c0072042c03000035400300e080000e4400586080c0300c1c0041504221a80e8003070f0702c02d59900300c000010039941c41c44425109101e210302c210b505003c200d4655110328200380c1018080d02c2e80741c1707040c008281a03103408202400b929064904070b852065948000074295112420880c07000c0c0e1340092704200340303c1c4900601e58448000820010400076410000740510f10054002d02904c400c600403038080d58440e8490034035182c01108 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 519989028 1250 519987778 519987791
    0x20312162418051209030a0303051504020301080a05070b0f0f030a020d0203010618050a0501090b16050d0c0b0a0501080601030206070507030b040b0a0e070b03060f1c031e0e1509060d 80
    0x29541c00d46140b200240d0b010302c03a8244241c0d40010746011201284006800703005403e24070740d800d80261901400440307002c078204261038030946451020314001d210740380082100c100d1130304020b030500f4540c0e0400180004100000e0401c8100d81003116800d041a850b02aa23030303070b11118568002d010344040701060358000800081e80035841074152034520051580c1007842c1c0da0760805c02004503580e100b4240403030b441002c05c115502510f0003600e064820310040610550090751254141044c41c40072001207204007558400707200701c07036884560001d4020010446d65043c40036856898005200003881404006442e004000003842040011513001400d0281d0b0300342842c01008082c800c451180b6000d2074590401241040020448221104030b10000d1444c2c0b924000c0c000142041081e43c6d801456501540300c0c290b02c0b00003503c60b0716000b540e0300700e80c0300c482d88550b05401310103040040401001c0400d54505580d00c40d082c0c1420642c4013862a81e4521032404900680107407038540e00b8140c5040e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 519990278 1250 519989028 519989051
    0x170304031106010609050d110105090a2301050705070e10030507090207150207020a090f0608030f03071b0b0708071707030c09050303160818030d020a0203121624 71
    0x1840c44904400c81c1995840e0383c81e01412580a0418842ca5a000c840d445101000c1101d0f1b66100b4500e0606260040c0703000d801c100850350081c815030188a510328100c00b0905115100304c0e00214052007482c2c84d6142031744688506641c1c0301076000e050316081101010560800b12001d503100107503400b6041c0c0314040da0b00c09070800290480b54040d6245413602d42d007000d0860241c03003113440c41c5600800c41d00388a41040c050000810700d01100c4840d081c0d4900e170101ea401c004001401c070305d40d03205010359900c0c6000c081c020010030703100962400400c0f400903a86c000404550b072482d03100034245403107407141d55101001c80300f0612810704604040100c501b0300642c598140c10074003801217a9101c070540107941e00b05040d034910070790080f0701c18400e04801d0440000c070703024010300b00c0324843c59250b00e45107145e00010f4207191152200c00c007d0fa21600c000b104500b03060100013280f019000d04e0b5800c00c1062900220800c110210082030803003040b010106559488890358840d11950804101004510 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 519991528 1250 519990278 519990287
    0xf06011b06090b010b0406120902040b060c010204030c08060405060a0203070c020a15110615040b043e070b070c02030a050d021506030a1a07170a0606230405010c17030403 75
    0x29202900c3e0003c0f41d200105540900c00110b40844150303680e03a00d52818012001b2005083c442c0c0200d0788161192603400503030b81c80c50b0181418201031000140c2d52481c61824240b400c41d6503001050f02d4121401b00000710b4030200c0c20a91181d8403034005030f501c0d915034030100d030140110303400254040101c3c2c40c0810100410740344003030060095164220b404070842e170314a980700021208000c0c40d603820f00c1c81c0700f0f503400c05070401481c15401800c003003080c408031250921902a94022000480900507211039008502010015810f5031800e00c2464400140c40390400d440e0700400f0b540600010460000441d1802c02802e40444c1c0c00c03205031860803190280003911902c3c101140203427484160301140d4146000310701600386a42c0842e049540d401644400c000c0280024112410300c00d07000b12441c400032600140ca881420985400501c450400901925003002010018404804040c0201422840703404440c10350385c090074002c4e0207109074030705501324140b2424518403000011046c0030426410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 519992778 1250 519991528 519991541
    0xc060536190504390c0f21110c1504030b0721020c03040e19050403050309010c1701060818030c0a150902130506060403051501080c010c0f0b07120213060206070509090f06011b06 78
    0x1500d030000307800c07d03400004a50701186030b0781c03044494100c0f092054051400100d03405c6880640080142070a40d80c0e154240d10880c115004004180594001c5251f840406003801c1503825625045040294019100d55280600e0191065000030170340814082c0c80c03020342d81c1440300c0060b80c06015514040c5401849904250f441400d1907003400081480c10b0700501c011200103c814004129680ca880300444400c000500036180c04d21040001d41c141c03180c00d200911b0808441001040d4030310305071501901107001c00420158082c6041d0407070006a6076046458804100c030a404602d98482c9400910705205070b0307000502a128040784689800895001541254601003d85100c4e550600042d1031030100900024484411000c00a001039200c0f04501d82084c494034152044560005c0c1c00001c03079001e0034140f20090071000d000c2100310341c100603596000c902490001d04140384200443c6105070080d102d03180c6203810030000b80040c0d01c140e1044d400210320100c20001c000c0c0a0900e036005100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 519994028 1250 519992778 519992813
    0xe0c060a081b0d0c0c021203160803042d030210060b16060605130b091501020a0f110d0807060507031a0105180a03080301030c060536190504390c0f 65
    0x1e9030044403890008415a03145c40803001e01d942c443c0004ad525100250300040081f039000502420040c000c0c0301d40d1a0080810403a100d100d01e11b40402e0802920341114200704007900c50070030300140100e0506400791607038080300e015200010005494444040c1c14140c100c0c0f5080852012544002042600f1412040b20705484c5902d040c0c9608031748401100c4612201030260384004072010002c0c0321101c0e04481580540300d0202607101842c0010341c0900b40c00010ba4281501042071800d0021901c0780c01d0308000dc2c1d0408002d80001c6900c00441180319007510350501074003013100d11030100038080260107030400810050003a900c80c038014480d80c100303004c00c1e504410a07a0000c00c055000d20116245014100b20180000900a1a520010405600588031104071140c8000903495002c01e41a41010703801c01c0018080c10308003407008880040441000e8000380c000e80d55905000901510782c9a140703c0180f4a0030301d0309103019180f003840341ca07000b02440c11070000e500521030030701e054000010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 519995278 1250 519994028 519994039
    0x90d1220012c0706260103031e0201090c1a04081903020f0a08030c0a020f1e16261603050105010501201b0f06030a0e0c060a081b0d0c0c02 61
    0x350b03000d400300482c55440242c1421a40310410602400e406862085c1080d5040b500816188809400e036a05107082a0b00c114086002c4004203000f0800e07180000d06a04040e1008000b072141d1034564103403010807446400301c4440c0d21200c001a8607000b0702124043c2c84602c0488000802d40700000c80800780e5102d0a500500980e02101048003003c69907407151a040078240341140c40b540c01080c600e500c00903d20040d44501c08000c05a840c050002c814886400d408443d110400c1050103403c013411880c100001c0041b10400b845480c0c02e509001101102300810004980c01d003c03030305071411808640c034000d14440104004100681504254140d640c20b81e82d070b03049542c0070145699250100418003480303400820401070300b00c410390158180f41b08014004450f9542c810040b541c25801601d580850036100c9240c0140818100304120b600207017070f0b07216444d02e05d441d1801041214042d06800b900300c03e10b500011420818820740700e010200750030400c02142d009401608030318114200300d010b103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 519996528 1250 519995278 519995321
    0x9051509070b0a0504050402160f1505060a0b19020708160630050406020d1a1e0a0e10030c0e060a061b06111605030705010b06090d122001 61
    0x30007502c19120f654807141c980c00d052500b0441004041e4000c08000b201240b10018a02d0108250b580802d4680303000d0042c0011104d01c0411303403026100c0c01058a4010744002504020016101088502d07066541c1ca800c2c424144202c3c04034240041d5510000d41e600c19088448056058002041c0441c3c800d40c41e0040c3d6007517034030300f1111411207028480308840000b8007a0340c8006000c0d00034561061103010300510380050030807028101c40320f80408804104203078200903120f06200201e42e2000540da1030920f000d446000c0021801c2c5042d0082ea02c08400000100f42d07904003648044002c0d41d07014520a00131500c0c1c60700040c507610102d422512a00c20a200080d41601401103162654050010400c8914250301c8600c043d00e204480c041d607001080096525080c04000c4c044040fa12403006555210280e041183c00e5030031070b5025511928080105400a0380c503580e0809865030700c4448100c60160043c01911040b902d200788011000e2084e5072001c0c03008042d400840d00040c0f041140051 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 519997778 1250 519996528 519996539
    0x1c0503180601031203090c09050a0609060e01030807080703020c04020a052a0d0e030708100501050306010b03130209070c0b01030b01150507110d02060c0a0501090c17060406020a030905150907 84
    0x86107800c1c44090201d0241024209843d8031903040a640b42d80030300642e00006546d020703440700326401280e000d010542d032a48207219070880c50003030000031300c0c10740340032042541151143c1c8c94610480303200a0655030002800b004042c0240403124010600403c00c6440707441c01c14015107107a0020010b0703c6001c402c00d660741e10100b5185201d25130b9001140041c0040140300d001a01e00580040300240c1c036101e51100061140010440be0000d41e905500220341549010107051074110107070041d103404201482000540301c0c000103107031020307034044541600a840b007010984003031900c0c0d10042c05420611002005210302100154102c80300c41c10141c001d08411402200c1c1c60190400091041d50505d07070a04481c50174400b043d51140c0000c001c1c500d085018842d513881c1208800d0115103a07519031b280c0900303001d00080c0b0000200001100d19048542812500707072100401031006240d940d01180120841c0d00ca43d000550059104046802030001c500442501104c11151005c0ea8031a02c10041403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 519999028 1250 519997778 519997783
    0xe040b0f07020c0118030506010306021e041d13021c050607030c080f15060d1b030b010e0108190c0507151b08060316120c0f0f030f051c050318 63
    0x100340081d901034800f01000c000111500601280010100c4080b10700210201d0814824070f40214131034880169031350b2070915425807201041c8041406a0801c1c030003049400341c03590342c191a81c01c04030140c0001e5902c00003d011681210341000c2d4100c00b80c640c0c0f407031000c1c5200c2d400c2501240100d086560a558043c800c40a0f0f030140303002c07403000860308004600034602c1150f030541c1001c103041c0a8544060f288012964a4000c801c1110a0729201c80700222000a81990440090310074074040c49408402d10000c0c0c290221000414104806d403000103c0c00400c1c0180003442e080000c9041c070101c0700540740113280360407146080e40e1445080900d103880d00000d01c5030300c5421012101d80641d03243d0b41c010071341d4030441c01044690180904102c4541c82041449441e01919009401d1302c14640c241c2000614591745402c4855412402030041c00300d00001c0d04040201c030390000c1c4c061f14072202450640d0918600401c241b2100a8040c80031001d9a0048081c503c510101c01101680542e0b0040865 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 520000278 1250 519999028 519999031
    0x41208010509071b0f14060403080f010518060f0a06031e1b110c03060f090616021908130801050f16120b030f060103050705011112041401090905010e040b0f 69
    0x1c0108504200401c0c140c614581c0307141c252805814188001200c0e40c42d88203100344500b01101054101008010030981c1100c0c0ac1900000010424003031036040070b01049083c1b40300c42d03004524441c03c100043d016603549404542c118006885030505668510380a405131121400c1282c4604011610f246148454400e070000840591181d0f0010301d4800c4003035a543c3d400740c6d0085058007500d004401c140c0c4080080310300400c559410003810340303030030b0103918181076020b844584c4a2038003c0d0702c540d0080d400500101e5981084409a00745d040d94503140e000d81c822594250742c5181c00020000b141e18066100501c51a018010a1010380d1001e42c0c896803038000d1180500421102c00b02e44c0c0f212000c5502249080c980901142c11032072001c0f0045240003001d80c03045503180c1c0301d060f0510195130710032048411b40485800030700c0c02d0340406400781810301031400f900714027841780b0752545a030340e11852001006101d10601041956150704030400a001c0031901910310280f100302080325401d0440489 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 520001528 1250 520000278 520000291
    0xc09030124152120031f050405070207030b060303040e0405010f062403020f04230f010203040e010308131503050714070201051204410c030703060509100203041208010509 75
    0x607010142c0c103003da80c020000d500102c960103080c00f1091850640070001903004140ea02c54404d0607070000c0ca6411080b01c100e81095009a05100034007440b40d07000034650742541c2d40551074184594030070b00401c0c0b560003142d02c8844071541010500c000d01806500403205104042400d20151707407100b00c6100840307038480060310105081c0142d0202e5500caa4041c14180300c1c1c1048261416940380840b00d030380118103001143e2220486440c540503e440740c0241d00440c0c0a00103182000d00e4821001060601444090200b1000013070318000480c0a141c04405010030262903103684120ba8001001000111501400701d0803120081000c054070500f502c0d4140e40c140d440c1e0386001d40c2c0f00710b0700780d40940190003100c002c80c030341d000410140c000181c00c200003104900d04410b10710400140c01031152030703c1600c15044d008034032400302944001c9906401e50b81c1141002c90701e170300ca007844245803416081c0314183c480d03c04401d00c810040d001c443c51503080155910300d484ea03601e401c00c04c403000710280c0300c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 520002778 1250 520001528 520001567
    0x5030a0c0603020901030f0c1e09050d0b130203070f0e010e151e03100b01180f1a0c070b0912070b0a1209080f190203120c0903012415 59
    0x401c2a20b1103034006088048041c0340104410f854030881000765585503014102281c0e44001d00c41442c480e003c1c0940422502d4a803d2800303c0c54040407c0c1041c002c0076000d019040c100340029203d400403558503c140d50302604a42c0c0555035009441c8031940340d4001c1c600303010080c500009403010307900f000701d00980c0c072065000f207a0103036142004603102446560705038080c0c00402d500f0740d958003808007001d08820310b41c01083e044060800180454140e20849005420001d400e2050102003000701040c1d0382c0c08030340d00c05080d0984940141d5030266020200151090700790201c0c0b40710010703025040303008003950a40c1d82209000034058a40300c00f8010850085810321044112902c141914150301142580005400400c0e03124406113901107025100601c9000031030300d02100e0304031002440b00070203201031414001c05030104081014050680741c05501c001c03501c40d0b1075507000e600c2441c688030448860440c1d030b100740d124002c0707024140c0700381204950700d2074281c440c0798001c00f07569040b0762082ca070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 520004028 1250 520002778 520002803
    0x1003090203100911030d050316021b1c05120405121903050a0908070e0106020c030a08090d0c15020c0405180c062104140d0f080411130911030705030a 66
    0xc0c060042400b000c0079031303e203c080a4411a543c80070b100122140440d039507500c0e52032500910505203017049008050465001d000d00041c1440e07040c0419490100c120f428080e00c1410030445a59106c00d07500282060092200b4500d110860740020b0089820a1301c0030317440921030914964451110610300e40d42402d05c5a45500064890001800a8841c0e0304121007400d032521300041c43d2240399000b0741e0030003090000621400e50100400611080100c008000e102c0381a9640c81144c0540781c00030740180070750384a00042007003c00c06030000e8489481e40120382c850100c4000d503510750444015000d20324000c00f00311039807541044140e940080718010100903020009101c5181d00c0b0110b6000d040c0c1001c1c83d07090000704420903060146018543d6081c000c060103c0c00c070b04006440e812841407010b000403003800d40d81c02c96603c0f0f500c581c00c901c1d074107110104c1101041e58078002883c240195480c0540d14810440340b0441c40c114081c00303400b19981c281d20b560a043d55401a0007029040b82d01901 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 520005278 1250 520004028 520004053
    0x503030f3412091d061201150e06040504150b0105090405072601060926010507080103030206010617010501030c110106121412070803091504030314060904030e040b01030225021003090203 82
    0x18032139401440141260b4048200d05850300c0c21199694a5101c0300d841e6000b04000c03802c0301404c4144c011008550800203410036645032040070b001916103e003015103036440f48070182c0c041c00982da07400f0b0010744140400d18142200402410f1107882c0001079a03115a0300d0150103c0420481b8140c1e07030709403100402c1506203e5205900418140701c140048090090085801d00a0255a002c1e807820740b244140342d4110700e0041d050100c141c002500b085840c4501a04030036040307007414111507080c20001481413100d4011500d032094052404190342c200781000070140c2000c1d003c3c2e1640c2c0d01a40e0350100c4603280c0c00a96880720b10070800070070f225400340001c07004a03040500a54108064000b1140443e4081d020b0302c0180d0011038041e40400d50701d141c1c1c5081c40a03007884441e482101111038203410b02e49990060a02b80380100e003140039955a00079212140d00030b60488540d0b81c0044040481c1d005501e81c0c1014481c0a06402c03030041444070984c0009902a000c2c02e00c010f54014080c051041d40344 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 520006528 1250 520005278 520005329
    0x180203091c121515050702100215060d080d0e100b01090503060105120f0601030305280207230901090207021c080409090f080a0206060111070503030f341209 69
    0x3c0354001c040001640081c0d400e00081c2e56205010140d1911615400c01e40101705404281d03030000740c00d540003c000b0840920121808603072000d41111742050850705401c0050f502d00503100d6803402186441c2450407040f6000a09045603d051134041c49048000c0c03004551100700c070b200351905071b480400140050700c0c10300080e200540a2008481082d90280c2030715180c1070007a071080d0301040c4009100c00100088c40d0700000c20005202507100c441101d254000d60f40d504a10071001030101c140c0036030121984414103503054410040100726907507183c0c1c0c2420700035031046000300d00c542c507000751516a60b00440180c4090a8000c0403981c03d19180000c00d0025102d003003011550000c8860803480080c9540b00901589035043d030080080e440c14030000340080c100d50054070116444040c04003e00e40d4004226100005400011929555415075541c1d00c4c0c5505415811051181188004601c034405141030489000e00143c3d100b004104d04251003c20316030140724200e800092800715a036584 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 520007778 1250 520006528 520006541
    0x1017010e07050c1009061505011b050709060e0906010e0603120702181503100216061a0d03020d091a090127080d121a1207180203091c12 60
    0x180c2c100245880c0860a000307040010320100e002406543c0e0704980140100e510801c1500740707a2807010300c89072381048000381c812281020003000d0003018070445400c02c102442100006c0101c00c034240000b41c2c8845003c3c04c401000c0b581c070241441101d0000520042035a00c09004480240117040d0000910340c030103040364800362007660020b200404550807010740800451007040d0711000220748008190401d410420341007004401180144060305900309004012040030340d1002c000510003501c00328031504c1c030392009a03050303000051720449003d2640100b407860000410360f0310070080b42d880d00360010312032aa06800c900b420030300707018a88071940a00010240100082510300e0450060102c1241e03542c40303500210056000314102c0c41f02d264104249405507000d181051105041000c050b5207548844076804d0301c02c03544215038400000f01846043c010745900011916484042150380f4040e5100741c640030018030510900040c440003107038001c00042c01980d03a02034070310003000c0c82034054046d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 520009028 1250 520007778 520007791
    0x150309010908120a0b0315060f0a0f1d010f03030203070f140d120609021c0b01090314010c0f0503090d23040f1e0f0b031b0a020c1017010e 61
    0x507641100340c007240418000c2c2804204407101215a46450445141554100741000b4000c0e802030407204081c009820115502000c2522040034600c030318000240c4c440601e5001c0170b134044401c0d0340454800010a2100407036500d003446501c0b2666510f0f0f0480c00d401c40d511025005030814010040001e00311703010390005501031040c80070110132000150307051480e841c4900c004100f03148011581c4011a000320700080507074a00460801c422100ca649500300001488403900d41d4550400b50309a00a00100001e16044484e442c12202440001d5000300029400d40c80030400e500d0303909528a00c104201c1388213041040143c0710800300325105541690484610343c115542c0c1010f9030034075140c603001820003810303240e0b6494095443e08401c8038503101c200300640d10948041c1e105100101011488a00300c450780c50304031750350382c6e2800ca101c02e0241c600021500580790004000c0d0b0000d0307001680385002e482c102c4081c40810101c42059070f42c40d0500700000d031000201c8004000d20144400000e601c800c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 520010278 1250 520009028 520009031
    0x3240907020f161415120c1c0902130509071a0d051f06050319060b0a02010606030e1b0307051810080106030b06060706090203031b120915030901 64
    0x1150100050041408640250040e80560800c400d004020403524400e40040340318000f05070300b803901e104c080d002d2600c0c400b03019210f600000303c08000c907101200d070203500000840c0102e05100d01408035950144401c2e40040a03661221900560f80d80703d000311403940102110a211803080700b82001d0600102141e00d9409140d01c000b441d9005d28490a501d8065524000e5451030144424811108085c1a81d0701d500e504010140315098848401c100303549480c1081600c0350750b4030b0723030b50451455100219060355051910004107a18004046c022130301161b002444025150102201184c40c544001d04107030b8041303c038542d2001c1101d001109103910207001c1e903192580f038202158940301000c0d0520401d9950004110201c1c8814202c0006000e50100a000c202d107541c403074101d81030024080c140304d804002030900801820341d203c150704a5014085e03d8a90000c440e140c6950040203102520a004030046000440d0703511701243c030001d81c0149031440b194283c500c486101d4000030a10241036 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 520011528 1250 520010278 520010341
    0xb0d0506120609010e0601080c0307230604031202010b0301051b0f0c1b1903020310021605070b030114062508070c0321020610051509120601061407050303 68
    0x1180074803242d44038050000000c55104681c411681c58079005920031407443d002180e1100ca15a400325800b42298100036a425004c0c0c56040b00c070a49044c8580010b0703000400190010802101004402404e03003160000c01002c4610001d06007030315012906070540b40828031b84210402c0440c0c0141ca44c4070904200703e400c0405003200640381c00000044100292041444900a481c00d0b110902c40411a409401c060f1461036003c2a600c140c070501504e0000d80118018241c10310340c10034084030036040f0049400e0703550388008019140d03000b07005101e002d401c28039070072116041080840310440001c0003c1d035001c8500302d031030281c1c484c661202150908010400c032004a51501c0001000e54040d84901e0800c00710800040701c0516070740001015908041e04111912207003448180031504242c65501c0e140b4030150502c0c019103d030701c14240d4042c0181d40c0e20041c2c0000000c00b94181e070f11a494501d0106040c01c42109980101c80780285103034002c00000c0c0c031052801c8107080203c00214a40c02c903030b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 520012778 1250 520011528 520011559
    0x110d020a1707021315061d0d11060a0906030c030608030d0c090b0705010f050a05060609040c1e02030309010507020309030307120c060c02010209090a18030c020a0e0106050a14040b0d0506 82
    0x40b241c1d0600c5450042d40700c43d0b000e26150350615002c0018041c074102000307440b804600c15414252015202423003100031400349802d000254450003d8a6030051101d603440700c085c2409442c0e1480790142c0d4000a1415445500c101d0003071248078141c4135031100540c10401c0310f02280010f0400d00010404201c0c40c010002a8194008040c0081a00c03c1d0000303d001f4521007000e904440300103040540e0311b801c101c140041512020200c0b04807183c1a40c0101d2034040c140000c0d180e003101c8000100038040c80101c4011116408800303103000d5940c4030028011516000401c070381d2409203021440c0d16410800c41d8000003104800c043c840403419003005800d05403e51290740c110380046070f01d000941d40004a107811031030102c680300c0d1b11918102042042c8036500c8141001e400710654010103001a102c0c18500f0f5660b0310104100900300f00380f00800c5580c460702c004115030403a071002c00214a0a00101c20702d40c04003015641aa025102500d06010a601c16407000c1d0001812032500003c960200004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 520014028 1250 520012778 520012789
    0x100e0106081914062d0105010804060f061505090a0b040302030304210606060c0302100603110d0614010603150f15051606090b190209060f1308060f07110d020a170702 73
    0x7140c0c42c6007845d030007250403038403061614105421450744041e00c07071401400960303001581030380c000307800c03500014044080102c107100400d8550000441580219014034409034440000c0201000c26140782c211140e4808580c12203016500000758541c0040c00284100d40c03541501c0125450203180f1039410041c0d546441c022203505801c050000b5440000c0841410b8040042842e4006109030401c407075442c40d1a5000c0da0182c100446104070710031081c0300240819a0003a105032100c00c0380004055940b5040a401861942c1c0e00b202100600b00b00003407021824484241211906100c0d00710099800c2800c6489520800e4a0711200900c0944140803c07040e208401610b440307481d13400c1080c28101144400d0140c80d00c2c101031010f004006803506c0303859140990703c5542e143d901d1252200040c2c90607032820200754211807118841c210401042e140e06840050040d00903484005010174007091907611100a07555450250b4000d100840016007103000c080e4034022402c484908151080e0300007074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 520015278 1250 520014028 520014031
    0x604230406020711010e180705040b16050d0f02060a11040e0a0b0102070504060812090f030d1205060d031b080c1504020f031f20040602100e010608191406 68
    0x2110141d0100f1000100703c5003004011080d4400d08040d04180602c100181e40000040c90001140890700007141c207043c0260240d4028201c0c1140481e21001c00d81c0041003043d0403840213561900ca41c01d008200240150f085008204a030b5016060300e5071860300e010054000346070360825171401000000380018491040501800801c08003181c10314009000a24000c220f420480c03080d4a4443c08000e040ba000448024105d00c8109440c1c4414032034001907220081c021905404d07000740889600300a92200c5920301044010604020300e4681a00340000b01070341403801000315050003500c1c050082c100498a00c0103200b540d80e40d2510300740d03100076801c00950010031801c00c107204040c44110701d401180807002800c10b1f03001304407081e941022051011046d074255500183d807500c5c10402d40c804c00d10044025420040710315569030f0b640b03100950b1004149031400307000d450841030381c17a289418010201101c441c00002c0101c20100703148002035007203070701085446c0c402803170b0003030107210302440b03d80e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 520016528 1250 520015278 520015283
    0xc0a0b0a020c0c09072a05120301060f09050907030504050f0d0e01090504020f190212130e090a0b07030218040513121704060b1309061a06040b0306042304 68
    0x350326040b880051600e4250003218251054080700c007001003003030b480140c81e41c103424648072000b81584401c0743c002e4500104103000d07203503020700d9103a000003401e1400154100c0340c1d29540c64941c1c1e060230100700d400099a000305d9078000080b00108450600c29006a40c010b4003d200380e4444418111015190035504482440890082a41001c1c45c1d03801c22201802000c00391829468031903480c0b03000d2510b22400040c0782c100c03600c520030704050074402c00c00c801032541c1c540103003a41c40001c2620741d044880039115000c00c00d0086030015090440c0491101c110a500000f402c00d1920b41c00c1083d0042d4003c551450040c9560449568642d51a4010603002d104108c660205002c0103003080030a02079416102014000c0030002032800042c000d101c4c035400350300510300080011700b5070b0008482c000702c4608944440d091500e80018029191b10141c0c004001d120b1014891408070300f4031900c7d00a500c00c64500590510004050b802c064201901c000100b0f03002119030140c00001c0c051204040c1d509 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 520017778 1250 520016528 520016531
    0x12011a1207022401050103180807030305280501171f02030a02090a0306020405040b01020d08070509040e030a11250915050d03080604050a0506030d14090607050f0706050a05030c0c0a0b0a 82
    0x4009030758162003030b900400308082c8c2c00400c03840540c881c104d051140003402401c065650340082c42141c2030810a08003108446045c84650540d100050003070304080c062808407030011520750071612400a1000ca010240c800818000020004180025003000f8112005281c003004075070701c160b450b1005c24010f103100d07240044c1c0b52400c0000707020480b120303580f04906540c0302c03134822203100380c004414640c02000d500d000d513522600e4001003400b0305249407008016200229440d81240d0b00249810b403901d001d80102d03440644a0014500400c1202008018032001010705016403c0c0f16000401100c200050f6241e410342d07101c0205070b800c080810141c00150f545000d2082034a000e00a00750460500071081c42181040000203440e141c840b0039103428000c5240c0d152045001c0c20090341c502810080001752104410b003000ca4889a600c0400c034000d014103040811818010703819211040482d986c3c881c11a80d8011806510380d0000c1e240f07804a100b1410200009030001b0001441412005e00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 520019028 1250 520017778 520017781
    0x1506042007150b0d0803190911030c1504061103042103030f02030403080a05130b10031403040819080d050403170609090d1d0a03060212011a12070224 66
    0xc04101d0245040461448681041c0103d0a5541d42d00410f11540c1d42042d040e96136525817204030a401424085010502410f000342d0400303105020841d40c207504010340030340b40b42d10503070700400100b003194102c10840740e01c040c00284062481104210f039075100c80c604617403525480b02e03040d54035a101142101203695642058404150b81800344103c20880e00e5025815814141c3e0b01400c0014000c03c5420801c0d0385000040e4400509441081291380055500d081d5040c40c4540b285041660300050300e0410f00200d0600061000100311003c4485150103018081020301480c8101d00c100141910540d4042c00340312410080762040e980500d12980300c07001c1191000c0c41420740200c008055612542d000c804100e9043e1010686144604192916124071400c0c01e0304101c40303410b06040fa541040840102200b089125030040c000d0050500c1941580da0b601e241394128405900a100c56044050000d9183e0800e1940c007250450954010b031020000d410031050b40c1703050101c10207091a40081c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 520020278 1250 520019028 520019033
    0xa120312111309020a021f150e070e0a050904080304020a090218040c030b10050f21040203210a0503041104050a06030311150c0d0605060310030308011202031506042007 74
    0x8074402c020701109109504010310f010001c1d446002c01a04c83c10790543e50f45041c00011040c0d4071060381190b47d0b4902e80406615050442030211084401c1c8020801d1018104040d2403c21807220880c0c200a1400815583e103036210f00741a0000340c03040b6004101c00201141c01115800a03149078142d5042c2020440e40c51400c1000303407001d213580c480c14180760a06030890381c1c6a9000b0108120030380c0c1010765482046e070050100314401c22070b212240b50040304820418511080c9aa40154022400c44103403000c60381802c0048012450686c608407810000c00350500d004502850b44180141e07a004641c54402c1c010905803081250340303840c0951744d0a818810150800304008120340c401e0002c00c10010390040c6800b0500c030240100c640b400c00410302d0003000d1010340090010702009021180c4a0600d01d4244e40c0c0e03000c031400200d022a6000c0c001041141e074146109500c5900140146080e6031584003d050f050b50280803203810545441c01c403000546800c031450a07e8100302c1c0702560b5400780c1d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 520021528 1250 520020278 520020307
    0x90a060c110406030b0f04171201030605090303010608070c1130070b0f090a030602040609090b1008040b1e0907031a040f030f0918020408100b0a12031211 68
    0xd0300c0c1c2070310651070402c3c24004540c40400b440d0740701402d0008502940c070ba03400d101c040c0e411040da000445010010300d0100c280340800392141224071900c000e106580f60314464030b489002c2400350100107070b1240c000840c954450802050800c3c02101d0190110400401144010003001c51480171000d4031550400765034841000300c80100b0b4480c01401006040818880a9210700c00c0d00303502500002c01d44081d03581c0d40300c0041008540c040000c659450340d404014101c02b080d40b00700c1ca403652400c00940101e0401c200c08041c4450f00b40d4517404240c0d81c0c0d6032041c070525000303441490368850301348450601d20000007120b030040155200611001d8030b1031a100030081c00e2020b94042e140d8101c420f020026116610400005505090000482c149510100c0d1005140e80c4001a542c500d481030260b41074081d4001e0040d00c5090054440446403c40c03103d059035202d00059810200341e680401400002c84c4e40d0762210741c030074906801c21401d11340300d620545980c0241501391010005e01d407249510b98 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 520022778 1250 520021528 520021553
    0x9130209061612030b01081501020304150806010906090506070f080712021b0102071520030a09030c0506090a0302090601120f020306040c08090a06020d061203090e0601171803090a060c 81
    0x503180c05c2c4818840000000d000c1c0401500480ca413106103039800c1a80c2c0e000317100303484c0a86100d40302c01101c0d070031341d03140140314500994586000c0b5594440c04502d144c495038020302612030142406250166550351180304138068101031f40e000d03d09006039000030308040f0244141c1d910680c0102105a900c420392440c0d02044a001c50540d0710900003040540c2d0081c8500d1400c808901f00400741495415000701c4141c40401041160700001034a129469004200103003540d000e003100ca2409621342080c8500c0c0d00c00c1c90b0380f899010b10300030020401481c002c0001c0d80d0042c811b2400301e1446050f48400000d4513a0020b1151b03005030040100452410309201b000101b4049241c10610383c01c00049254039481c00400181c031003600060f1500940d503858119900816804548440b014443d0400610000d05070052054103519480401d556610588155100c031601402100941c1c07650960050f00d80c0c1d2101d520301040c04140800801903071200382400090000791511000c800003840c20420b42c0c2e90 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 520024028 1250 520022778 520022813
    0x303070c1e030909050601030605030a0b190e1b0f03030d0504051606080c0703090f030b0403030b1207050402070c0902071a06100824031c18050303091302090616 71
    0x62105424000c60b0b0b001c5a00c0c0d0131a0403072180001c00b502e407140124064032440d00f29603003501c0740441400c100095580c11601c111a034000071451219078002d090140d800903c101c503829032250350181d03500d00c100d403c00c548004004281c03105c0c80d080ca10101e415034109098812905a45004000500809100ca000c40ea122801e40442050816101502c0c490300038240022208001c0b0340481014010702041003c5c1c18903620410800ba560714001c0030034401107508a00080c10514a0640350409000c04030030b90140902038440c8038148001d02c00290040d81c415102d0003103805d40007c4400892008016190140d038050301c2c0c2d103581440c00c90300998042c1c06d150042003405071008030310341e00007503c942129044845c0450079003807494800e2040010641d69905000d00c1c82064048107405040b110000615214040c54403840c81c04480400e0b800d00c140340c2c0540007005045d40e40e10b40405110085102200300500b0046042c002c60480d41041d000c402d201e100480d01c2ca02800003a1154148001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 520025278 1250 520024028 520024073
    0x20f0c0619140c0703140f0715030f06090603210513120201050c1f0c050c07270908090f060c0705010e2209120804031e110303070c 58
    0x100018641c01c2031500704403003141000041090030095016280455040b0140c6200f214207007500c80c10701007480c14032210a0506da20542e1409044400701082c00c804840903201507030384040704400c060300a4601140750304501640c1f107401080c0f0381160322900c0d01a42c018084405001107044252a20303610246107602031003024030004082c0c0c0050320200c01500c8146460081c110720078070042c0d8543c002c00040100901940203803103d2484824541e0311154840e26080c01841207401c81950944603445e40c03000c030741d08204801c1c03000500c0005074100c291540c0b405051180b41078400402110b40d10b400807a013000b00080e044c5490700c0d150800300c3c03244c00d08644041c0b5203c00e80a0060741c9044d40d204242c180010b0410006c020340d00c1d844580004241c0c0608001144074440d0304d20020b01c081d60b81142e521320390440c0c4415061040c2d903010b2140c2e80c991107405c401c0c0758181c440100345801c98040810000715412020b1010030601c09140600c580741c9a001e1a0111450b000c880e510065108100c0350703 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 520026528 1250 520025278 520025287
    0x30807140306010c02040e100e071505161106030702010f050109020405030c01030b0f060d1e0203090a03181502060a111603120b10050703024c0606020f0c06 69
    0x48500c404407078119100342000310b607254162011078064a80d4008625003801a0b106e542410070f001e400a40c0005002030650346820780350380e5404083d58003220040009a018811004440c00f00c81ca2921114080e501041d21000014001442d942c0116540f4005035155914956841c840e80507190140c000e983d420340c281428400440e80d0354a041c1000c504160319105c56041b103480b00e01000c0c01402002e4a640c1e41c170141c8010a00107007203410320303100801c10260399031010340b8028030a503400f45c020540a0101440c06480c2194003a621030325181c80d440c01680b000840400c401030354942e01d01e040c0c016081038a00400c610080354451000070103006410042e07542182440c410b44c500d070560504210710303c032808800701801400c1c0700e062150400d4040c0c0e084001d940e080304c0070f804218426400c44881e8140000442c815002440c45040780c4040d0701007204c6600141c1066a6a82249056010706510355414000c1541d883e50301400140c3c10040030720b41c11010600c881a580102038032001d140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 520027778 1250 520026528 520026557
    0xf0d06240e01170c03070306150e030c040605010507080703020f010903030501170a020102060115030e2b030e060c03040201050705010f05010515120615070b0c130815070305090109060612030807 85
    0x2403080100407828164000002541b003501983c4200d0143c8041c031200c20203c3c01c06600600142c114084c080c1c8284180c1d54409007601e0300340203d0f401c0c0d68040e900d443c24440a07548a28954001c0c06040301980140e400041c00074000b4400d04420a00a135400325940d4980800d05415a40088101e0016000348002d5409070f600040d40c00e0446000444044d00346d038a10f04100c0c01000a1090111980207000b041c0300301d03007840c0d5000007840128a030300e00d603c035617410001d4084451001c2c1a180c240c21000014509002c200301547e801030041c104a0f24265031a9149421a06c01060140358541d03510014000d13800c1250901420101342210545441c0d05103242e000041d4000b40080c6c42900c00b1185c2c40c05500e00076098a01c269030080340ea00329802c0c01a0001078a030052580a200307140c5030040082ca03647c0000c1c2106529480301100049600d80042c100d029000080c6a081d4079900e0308079540000e82c4900c1510300400c890300ba022038804451400910440d405401d07942040690441c1c1c040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 520029028 1250 520027778 520027817
    0x3110a081c060b1801050a031401030b0403021204080d0305070318060905120906030f1f18110a080406050424021c020712050903120c0a050d050408030f0d06240e01 72
    0xc1c04e4802d00b4800c0c0c03180d003040c008a000d4283e00d0b01c5040c846030400c00000401c45d20b0411705001d17a2080d0280c0c1d80420382e006031070020f40a01e00c1806d040707910000070118018002d0344000d41006061070302080c212001c502401c0410801034080b14016034543c4102c05200046c0420440841e0000344640b030100350000140c014000941007042c0c100c0ca6102080a45502c484401204294008a0396015a42d840c52100c0340d005040c5122205041003201040419014211811680306484020301c0e80c81d152501002000002c208440524082400100d85c00402880111205900d8005603807903e240000f44140000841000401801804041c0000b1042c81c2c10186902013450401d44a001803c002840c05034074610000c0c581c5800190045c003000d0128800440c0ca0052080304d0585818140c21102442144120390071038100748401c0b0000c400b1840104000344200b0070100d031140e01c401e1141c208000410103c4035225020b002c1c0181c032070b040200250500c0302420f00c0d519104580000e130343c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 520030278 1250 520029028 520029067
    0x6070204020904021612080105011e0f03091b1406040b03041e1b05190305060a09050f030408150a0b010203030a0221090d200a03110a081c060b 63
    0xd100360303008141c101031038840d9810355002c5040d00f107070090032103110300700703191805030310300410000901b0400041001e5029000c52030a1100c0342c8000044404029000c503040103080014104160b01c0707080d218003099007401c0214240d4000a01540c1031464500c500c01032105c582d040c5802a0400c1c08208450805001134907032003030700000f4414424030003207880211071621000040c070030402d0382400a104403040d100343d415204180e94041d0114480c8101964200302d40c4002001903000c000000e000410642000c01c219115200311a441700060305903e00390f402079041100554042d1040210300a007442c26030f40c1140506804016185140d00003d4030703072000900d10842180c00203294401002d10584d05020801d10054440c0d80d0704000190940364038010040100283e60340c0c800c0400600f00812507000d07080d483d00108880c400c0b43d5001d0300e42605446045409029089000c0003060300744d07000340603284071043d44544540050b5002401ca40c030356042410041c00c1409914101c7c140381440c038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 520031528 1250 520030278 520030283
    0x7060201090c0306050702100608010501030c120c0302010f09050d150b10050301060818030a020606010809010e0a0f022704030201060b0702010203121909060b03012003010902070606090c050a080a0203060607 91
    0x5c00c403540d542c68140e01d818010361172445010325105001415040c19440b40e4183c07032254604004d4159030f421040ea12801003840074103041c040700c8040005600508400b800e211a50420345142ca0752400010b04510840c0300650300b112414180e80d200c454240f00b41200c052084480100111003001c00401d1400140140700030b22200c0c1000c00c100031042d055a4580218910840307a44000b0035000940310601502e40501003010040400d1000c0d030306004504d0b450030418000c02090040d0380790214008071600040c0e8001e40034100c07025100c0510707440300c200d840888110310154240b5180007421a02c07181c0c040c40102c0380502c410300040c0e9001c1b00300d841020009402c030185e5190900c04040101034910103101c941d01c1c1c0f141c98004c100e1140c000c440c0e04c1c03038120020050340a0403611190031300c04454800c40350050410041c80169215409072508a000d2400010b20540310440407007150540702c901d1002c500081940d460065110f80c1150303100008103400d41c118100b010201d40c4a00503030200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 520032778 1250 520031528 520031531
    0x80c01021f0e070909060213050a234204060f030b04110c010624090501050708071a0603010e0f030d09080904090321020316051612030c0207060201090c0306 69
    0x110b155550801c000e4001d400c11450401140040f031401c0c0f4002d51011084030030015010310001041c2c80e1030003e250841d01901e40c0940c2030905048c0e041001008040c45607031203154001210413901000900d001d1031000184000c03ca80303560072200000482030075040d6240d001c01c02c02840b03403a900c6000341d002c0f5030300c60a02042c100b45080010303003e0218013a107a11181c501040c11440322205420070000c9440050340149014540d190030070781000020080e801088059500704225407044009000203401780d40c1e030324105407183c0c3d915000320030030111140c00022100f050041d00c2c40d080c450301c44551010b2009202d90a064074000351203000301203840d914259515501e00038000284200d480320040100704001008441c0b0700035102d010801080b15140c200ca881c1520704244900c22a405400324510500c113410388860215003e503c2400800f025034100313802040080c0130041e036180c1110180d140401d20071044140249010307002d5010f4011a0f0405d00e40c040400c69080787c41c025203030450070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 520034028 1250 520032778 520032791
    0xd050d05071b080405100e0906090c07050a050105011d0402100e0d0c12030306060906170c0702100e09101a0304051f02041401090b0d0e0c0303070c080c01021f 70
    0x2603400c101d03002c1e400d030302ca00041202031003005000300090040d17410440b08000d011803035107000c42c0c41d031100d006560740022041010500b01e29144907001e07445462172440c1c5152a40300c1d92958180002114101c507a03030344070340041c06a6002c10442102025000100c4107480ca0290000f40c0c503140e000c08108180036510b1404280c1e80c441008400c4142d41066003419980c2c0d41d595044904038244000b58000b80ca004408030741248030300303954000c035042075541062107800482c0d0390640000c0902407420000c2e0421a180040e02c07811400b681080290300c8200710009400300780240030304001c07c40c00b040000c8c8001403007903102d56505c1e003224090815040d51203980d0383c0b030690f28082c2c891070b108002c184440e800c09a190303c01d400800c1031751004021001a8400c41006652502c114041c80000700c9060181070f8031948540e122400c00310a100844050071001400700b420343e8819902501e041000240a000c2c03030f5002c00c20b01070800400e01c014420101c4c01d29460b1916400310803640e03481910b401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 520035278 1250 520034028 520034041
    0x2a11010c1b03030801031205070506070e040f110a08090c130b0307030204090f05120f09040903021c11071202090712090507090e060f011a07020d08030103050f0f0d050d05 75
    0xa8080d440c07110554500002c2c0c40b420b018190642c2444111034481d210695541c500b0310420685154076403120040c441e03900c40c2507045d0f51850345882c1c6281c000390f540f0003580c1d1929107801640140103844098903501d4000d031000402145006200385101c0d88041d8011440703848154804c4610007241100050b12505400061704000c1e00d50b1000e0340c42802d20300502c0c00e02c10200301c0091036a100d8811244040b08496000009004500100800500c1400941440d013029040901c43d144244107070703501d400c2e0070001000d080c40c01e090407400148000b4040e070400031080002c40050b1403103c0c810800340741c1c668002094031100500103800c01c0320268000641d501103401c401901070740801981e403c141c079451004028140c0c50b0346e09046100d400003041c82004496404e40c16110602c82c46106914010702c00400d617484080100d0f04a102202d808001c0784200024601075031145001c1c0080700d0fa07a00110f403501d81c0c00320712540c4a070001c0807558140c581000440d122903401109c08107007650b070030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 520036528 1250 520035278 520035293
    0xc031f092102010501150e0114090409120908010605010305040203031b0f060f041101113403080a110318040906110d05040506010803070c090e0a050d2a11010c 70
    0x30903030340900034101d240a190464040d0082c5042c0c507502c24a81500a001c008112085071640d06807034042080c401c01085501070b0080280701c0800082d0000c00da48000742d484500005104e40000000380052800b400000e2082c050000104400d10301400a8101600007a40380e10a04e410303202a190460b4420840381c20500019600e0480d860503581c1a00e40306509013009a000c07903003124900350210201840d0342c01484c5860000841e20003c00c0381e40001008109580c800c900c4001088003c8801041c01030343d03180341d01000e103206415140d1910007000024201403000e5000111300d42080c0300c1031a0704001d808981003040720403100450324020506164009092803010104900c130002030240895100e03401a90090784100100c80080c2c1e40c400b1010340f00d01032003400404000104504100c2407011741c01400160510302c0c1a2600401c0d03954540b0318100342ea10a0502261030b420714420f48803082d0403401104220701c40d100c5804030040d940c44080000c206250b5040c021042048024841807 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 520037778 1250 520036528 520036553
    0x30f12070e06030705030103060b04060806060904111207030204050711030d021804090b180d0c03051b031209070807180c020c22050603010207022b230c031f09 70
    0x350455a40c2c4c01d08090040403944240416609a8280341c404420390405115000c00c4503110b6010700840d440d00e50801c0103400c0080c0099450700811030a20040740e40310258441c0d0800000c2c02025807a03c1c610520050300c40040980d42445817501140c24582c070084112a4800d02d0200016561004d0400451040000008003900f251502042508002030304000d01e02a09020700782100c0c42440f2807207181d442e06060407000000d1981d601030300000b8082d4020f0107250340d81542058a13400e100050130301e990881038110310002002014001d000b070302800703408064011b01c0064500c5600b407260380d1801ca040d0008442e9915903465400c980c00c5e1081c441e4803407401e1300510344c070440c144800b110075104210850121419140501080c141d2038144200d5400381d40c05814004640001c80c4000d00c092a1503040c4550029510740d441c001a924490010300464002c4003982c4801c0407880c0549401d80b5610203078060b520a00038690400ca2000514034042e02e20301d80403030042039500d0880800b40e003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 520039028 1250 520037778 520037807
    0x280201080c0d0c090302040e01051506090a1d040312090201050901051c0606020c0307050a05130b0a0902030901151401020a0809030c150c010c090e070f1e0305060a0602030f1207 78
    0x90700410b41e54141d80a0010304c100c80c0215010701050340e440310755608881c2c003039891904000f505040f1500c203080200c06805450b00080c00f104159603689541ca800494420705184a040340720700f007004064109e0722b04407031050314041c20000c0000940c000380851003400c01a80c18840e0209601100d9441c1804040c0c4054002c6414421256244e402965503481c500d5602e1281c017400364045040d0034880002c00031039000921030328030f841e02200c85800400381d11340e40039044480c14101251201c0035000a5010342e04980c00050000c3c9400002d4048114641050380c0040c02412a241c25a0340000e2140e600789d04403940c207590b4002d43c0002494026100951a04911001d040002c052440780c06442a804200d000f03110507041400c1c11903a50416000d0b4842428110f0081040c2c90300c1083e807003450980a04010800400c1400180b107180c810a00200020b901c4800b006201e0400010000081042d80000c0d801c08262841d0540d01d0700600310007108041220000030001480b41c40320300340307080 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 520040278 1250 520039028 520039031
    0x26070507020409021c02030d0e060304060b0414101a1602130605031e07080606150706060504061707060206100e06031c0503010e01120f0201030c140a0e03280201080c0d 74
    0x1080d517004204c8112071440240d01c01d0245000312403060380100c1030b400d900100188030514590382c0f40e68002c020240315041540096940d0081c441c0d428601105074080ca10b6030403504580d910301105083c0d50311280094204402081c000e4040300619081c464001e183d04490310141540d8009440d402080c2650003140d0512903c441150f44901c18058100302e80601c0040d44c1909841d40c0e0190b5030784e4400d880700c0e600200701350001a00f010881c006000c05034440d00303010401603522800581690309581000007410403000804580e0841000340c1001001c041c0054031043c130b80705807509100300f0341e4850855800c6407400014540e43d13051041b059420b988009401d501885028010495002400341155800c0100300110303034010010081d4007581c0d07020640a55444035540110050420841040148000c40300300d0120b080c0340ca00503020061856035403411170f0741100c0415180c000c0c0002c0c0003014200090303078600060008080c06004c1303074080c01c1130400394a44d03c241603410300c03ea444040069 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 520041528 1250 520040278 520040299
    0xc07140102040909060b03150f0a06050405071e140f0a0504030f030206100b1603110a15050a0c080420060c0d1701061d100e0d06020702012607050702040902 69
    0x154207504c8103007807500800040141c0c9031345105143d910021281c00c9a46480c00700000f40220b4040c500483e4061b0056001092269403a0701003026a4010740340040420f40484038048114059000c940305500c003450509181d10085000348000c0c030640130f0a219040700010500e184500900440c1c00940d840f00301c682c9080040c0c1802911010705584c10a0466070320794001030307140303c0d81054809100d8001c03c0121541500e43c1e05071401722502d540c2c1c01960190303000003404502003c02e8103a030031240700c10105d035628219011400701c2e00080e2045040c00062002e00010450b21002a802c403142c5115a45050280c20300042442c0281045042c0038070030014201e07010f5030b10844c9202040980b246121403641c8484060341c582c88601140c4140300c503032400410041c07405000c40e582401c264100440b0f024a1440452900e1654241c1540c5460300010310302c0443d40d0001201c1ca9a0900072807072075800c2440d405040c404000500820200b00000c01d050b0290342d280e074040c00e0929401001c40204 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 520042778 1250 520041528 520041539
    0xe040b0a031a0610140306010305040c050306190e1605060304050a1506140f010e04050c0f0d02040e01051914060d0507080f0c0405150304261306050f030c0714010204 73
    0x3201c0c000c0c012034201800082544c0588171255101111031125411992401c00440040c40c001380181c3d482e0b681d0850014403038030140000c43c0144078640030400400d50040140083d14140554410300340d12040045041420303400b45642640c0d03040b9031f484c2c1d894503a400c15500c1c000d500000076046621951600d960981150300a43c1217a01404c42040001c218004000c4c91182080c5c0c007501003041601d0304400b2f0705d07140d03221552100d000340c41c5c1c9007041d4a40d01c00c13000300c0d0401408100c0443d030000d004e0040c0510010b400780100070480d9400d030741d034240a41500303080d0864400e054003e032903020b4140e070a07a110415609210f040740b00070001e40c41c08510041c184101a00c80485030070902d0b0100710030900e054111002c3d510003030300c490b00710b0851120701c50450784010b2040c0c8201140320100040203130000c0c0941c04915140c142c0a480e02c001607030178181c0c0d144c59800310003800002c00100100c00758001c1074950001041010700e4949850f81007801d03616143c0703070440d03849503c0054003056 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 520044028 1250 520042778 520042823
    0x1509031101020304030c050d0204110a02070f0509090706050c010b030a0f0b0a0b090114011205011518060e04090201050c01141806040203060105040209120703080304020108160e040b0a03 82
    0x2140e0080850314000c0500400582e10b91007140000340c0303002240803060146050a14811300b030284090000504088504140c1000b500403410260058000c00f20810901ca211a880b0024040c2240c0000980c200039000565a0a15205003018000d0120740d10012400a5001003855440035041d20b004e110185000c3d6070245000c1d01c101c2d10392180e04041001001d440c4559031008801400240d0f07141d003007000358107003284850801410007445100c002218105c0d402514000c0104c00c0381280510120174014216000721507d004103200200340420281c1e50000c0382e80f0542d03070203680000d0050303e6400102d91621804503481351943c01e19400941e500c05000307509110310820ba05030b035021034001d00001d444140a54000c0c0d03160788040014021450315900820b1813900040c0380314144007403588d0250038000c5652060700c942c400401004155604900105e5001000b08a603244070445080042d2400d19041800d81c007d9554406402c559219504440d002d5a0407441500000050300303114034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 520045278 1250 520044028 520044047
    0x8030901020406091e060813080d022119051e04141c05030609100f0806090c06030106080403140f0d02190503071b020409080f071a0c2215 61
    0x40c001130303d0340e00c0010b501c030001900c0010b451441c020301800520341001114039210151504502030940c40b02000042d0b030701002050000c0390031f0805620394290003085058490480d9045904c560700004014140a1201d81a05511011100000c10b5200c07000708071121081c2c0c01400b01141001d82c05c3c00300b4480034102010a106403042102c0c01940420071192019000815000200320280041890303461708070992a441189809181401d6079a503a102103810b845500c20f041c20b070415018005207020500144500c004244c07001499940752080c0240903c100800c0541040048001d000005041d00d04a800b0300d200d549007191035408a800c010029480310300c5400200c150b040c0e00da20154001c009480c40b0748000d071106011120250300451640301419812641b2035607071a0b803070780040c0a44000e490b90001078803086480d1403403840d140410b00d030742c2100d9032205203141c4100940308403410101c0d01314042003464607040c11041c44110005005640011403c0c0b285000c00f46d1007160b000c08900c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 520046528 1250 520045278 520045289
    0x11808090f030c060f0f2101030308011d01090e160f1701060803040509150a0608071206030c1806120b071d03030702010c0212060c0316031e0902030703080309010204 73
    0x508040100741007581c1d03000d01c410203640111003400252000304107180034240a0f800c1c400801c0c601001020340c244250384c4100c010360b0340c071000c1006105048d44030450a0240c0f401041034403c90041c02103080d1a50070500ca000c00c160707128461500000800d00004407200d110585004070b1030741760307882c84207150302d0341c01003014032075805151041e070500500454088a910b08007441c9001d080038103000603950300804011071541c03075810640395500c8521110f401000340c1d90702c4185606024400600c0b42842c50060002c0e641040350a102094890940c0c204481a000c0c2160340001100b0104001e014980d204164202e1314505140910100c0001703144698260354032440624807001240343d0031000d8031909505036209100da035005500855022920300d0000781201000d010b105019860814200c900741d8228101005012580400b500d51141d8490103007000c0c0b244c1c07210b8120006120003215541c01c95030745c8408c0100c043d92030500100d0080d43e0051081d83d0340313107094142a0b02035030091107007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 520047778 1250 520046528 520046539
    0x504020d091401020a0f03091101030b030f1f06141305100504051006180e070509011e02070f080a030e09150604060e0a170307030f021009060f0b0109051c0501180809 73
    0x6c0302c5148603200f0070b80d0340c1d68003582c56018074601400450080031011019501841241d050040e001c030100032120240741990b500380d84500e1041d00e000203a4007942c1c041c54a03200c0056510b8880d50355501d0042800002101c00151303a901e0a0021056200c1a0b200c80d030041c1c6441d0500c586203000401050568100f500e5582e001c0314503c004d500b4510f028812500e0308440300b0b002c00c3d6150321030f50080c4045201450104405400c269030750300c800482c0c1d50784801503400000704100381194048002e004149810140840c0740840c0c5000c1c0051780110f100d14031891a810014110100c04034461404081c081d01684d1641c0d141e2102a15648480c03c010f407180ca1000300c0080c101c0c0720b10036103025400c949006181090030b107a6007911202d5106031560158001c8424080150f500e610440405034040c6401259000c054038070502240c3c01c84036203a04000f00168144203030344800d4800c8200c0c5c84041d1107d140c0d030309242030150041c8041c6d81c050180220784601581842100c401030300000384212207 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 520049028 1250 520047778 520047797
    0x5040f02070b010b0c071701020f0a020d080c0a0f08100306020c0d11070303050f0304020a0905070c03030608010507081305070b0a090e0a06080c0d0215070b01030b0906010605040504020d091401020a 87
    0x413803c006000b442c0441006600c01d40e400d1010460001c112808491070701c00160506043e030380c2100a5402c5003c4080051340700c0c90f0b40f614003d92000c0803c0c0c101080019141c608844a500244030542291121080c42607071000308010303107100c1c011a401036070483c00c01c54032100c02800e41525000d040002c4000038644050320244a000440d41504030380c2c0c19202e1038948220001d42d9800d07900000c1040c0e900c428443e00009000900d401181c0c465403a80c1d58802283c551380c94013804036411500428074a0385003004000c002904292101d41281054211a138915901d182541c0741001c1d5400c03900c80f0036808900c010540f900301e02c1c01800d64040c0d06800c03240d80e485120040c116285403040f01003607805071201032030608020314034050590000d0008030402c409640d00581070350219070f040b200d0f0b00e5035600400c00d200650704000e07000740081c0090f01240d40b512100078520300440c0180da1007030b91700154901b0230003601e174800020590b10030360107003a102c500201203000350028110200030540025 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 520050278 1250 520049028 520049039
    0x150e100f1b05091e1c0311150411090402061b033606130509011203032406120b120a050c0a06081909150608070e04050a1b05040f02070b01 61
    0x14207403441d0400107008840200e04d401d01c0c101c030995032200f80680100e54641d420391102d0881e85c614080e64002d440e4a0303c0101001d00b058030348001c2c0e01207103101454103c103000c0041c8905a088200c0001100c02060580390f0340001407492242100d03504801080c040e4600c0341b040c000c0080c00319030300f14000c00d0140108010140e01b02040c4140b10902c1404a158500c0303d40c6005070283c95414030031580500c5c5a509c3c2d00104800035000e800c480c01a110303101340241015418090500300c44a80422100c0545203040d039040301001c1c0b4013950041c403030b4102e1910034010f00d03a80003a02c1600001c1400402254100b0310707d48400d030310b04044d82c250250740d180e885a4100708105000b01c0e10300f5034810089550300c80c145444041148950f41ca03c580741d60b41d0201107900302040200800031018002440352800d1106032416100e5032041d0140790990301003001040000c91011886508400e01801c0c0071581030741311002d0100f03a04015401362400420403104102540030f85209031080c42d08400f280d0f02c45 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 520051528 1250 520050278 520050287
    0xd061e0519020a120c1806020a061a0307032010120e0313120606030c0b04450e1609060902091c060b04090b060306070309150e100f1b 59
    0x30f40141d0218201d911106505800ca6001201102e060b1401a28092041500207800049075202d40c00580c404c21101c000d000491080300c41c0d14800000c604014072031400404d448aa0341e01c40a40034100c03404080707000340c1070400548088200104130014555903680c0203040034000005441d02103103070407010f0036003920010071500903042c0100c05001440c41c0c000ea03901c011000e080126546621140c0020014048000c0301024002e40d0b24a103846a040211007120507400c2e0f0451510410540254482d614806410004181d02c3c10b034610b120341c60600082c00a000c2c0e201c800c075100e209400c900285030306a00740e10340540c1d03600141881419a034603200001c2e409510b03812070b4420701682c42261051150444034042c64464a008034403400b1030000182100e20300c8000342e41c010b8000040003010302d0180036040d40b10440f8102042440c4071503e0302c4800d403000d642d10300982e96603072640c00700e8124200102c8000b02d081c1d80080c0000f5000d4030711000507141c107a0404070100f10041c42045445c1c002c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 520052778 1250 520051528 520051537
    0xf0c010203040311192004090c0b21040809060315030f010506031011160311010504200108131203062312030301030b0f10170601060801050d050a020d061e051902 71
    0x1101c050a41340306d43d4034500240112a0810075441303a55031041c03500103161201240001c1914080c05031703d030b0401c110340d4074040b1400b0b0050400104030101b0400000c1400d426190010015180b16485e40e40d031301041e4496820502c002d0741d06215100c8021851101500514410103056041e10008081c92030424165500b0038035601c02c1401c1440014400c0c2c180710003030b000e510f00070310b40a5405040080541e00b1038034207880540701d00f0f5003240d2888480c0c80300007000407030003028a0504040e190100030b0307080d4050743c0100102140341c6d528442031400c1c0300343c1208014090315010207458284549440c070b00c203000300a906004403080b0343c002d0802c0d00302006a038102c90300b1800d030007001d98900209141c000780c020b003808025107101d00c0210310300004900c800900c542c124000d00c101c3d4180380019100343d5050f88140e12034000c1062540026070b011038144004c540c141c5800d030b80e0b010a442c02c500a0103101d1010074018462030400c07030b640345142d081705010303242860500c2c40d4800c000314240c090384034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 520054028 1250 520052778 520052783
    0x32b020702011b0219060c23060a0903051306080103140105040b0408030403090b04080a0b0a0c020c010309080405220b0103110702091506040f0503010525050f0c01020304031119 78
    0x481954004818601c51405443c1407004101d021700107500750380d200c01d840140d005400000c265a15440421a40020090040c2d803048c0743da00f4a04060b1221a9441d403008000851007a01c070b2040004041c052420346150300d446601040380d807512528024840202480b040d1200c4034ad0b652b004940f46010700c552406950007004014140c0d540d43c4a10042e544090f03c210b0404c100c20b000004c543d078004006d00050b0424002426034819076080081002c01f020300b061980504d05500f09003030a80005000450b18401e003404030341c1101a0404600ca0f00803035004a401c200008000d80300c84c040c1e0100755040f071101d00c000304285aa10001101285c1001b131005e102140d0401442d8054070300410440c0d808074030340c1c1c01500c0c456441d101003580e0350081d038803503c00c034040c280040c8803502c4c082c02850340c00000c00885100300103410005019100c54082d0010500600003080e03046001d40504072510a2583d10007035681c0c3c24a441c1c0240729103c20500c20545001d1140b00c26081c0c0d0300c03420988401034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 520055278 1250 520054028 520054037
    0x603030e1e13090209090c090604091b0807060207080102041809020d0f060c022b0813060606260f010b0a0516050105011a0a080109020904020c032b02070201 69
    0x14200041c840040c11103040c07122898400880900c855407400e60521506901001c0459524803e1040c09500c40c4080c04010300b58001e482010b0590300d039240081c0d40003c04560202d4203003120b060000c0c000468030400030303101c1c0e86020003007401d5a0004407603044500e00d900b00d4181139030310380801e800c0340200e0240712512640d08110000707409050700140b0401e4001010200314050a81d40d207034040c00c50b40b8045603c203440321002910b4076010304c0000301e1100310a1a24805101e502d8002000149148221090000710310100703454482d801080444580c2c0030004000d0b00b600c0e8100500aa401280b851080525000040100340c5644221030b00581d896010300c2400d9090603c4580c0c1c07500064007100c200132040c40f0740d04134001c6031200e01070b51a0080000160039410160f008940d418205100b030f2080380700f000100402640626070a04655034200010784450000c00024013900c04d41683c1c0d0074500c000b19501194014904504072904480582040c20046807085101680507480000e030108 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 520056528 1250 520055278 520055297
    0xb01171209062503030603020f0406180507020a0b100e0c0c1b04020f12010e07050309030301030f030c0f0303020306041d0a021e041d0d020102190c1b080c030709060303 74
    0x41c1840c4001d050003101400300700303600c0342440a0b04020192a41e10544c0081d0f2940340c00c0055040040c191030074400c064405219013800c0140f08506000710082c000049a84c4a0020f020b60f0f1003408210403403603000c0c0141031a410200d41c81e210040703041c06201910703451040841c52238000f8408031850100414042d000300340c00044c0d10358407240c0034100b294100e50200310b4440800441c400400c0308006540100e50194180401e6480600005115070140701c401c0040c00110440001030b43d04683c2d018051907444625450700b21050f100001c0020030004803505440304158060300554407590068608021190340d480d91300e2001ea2020f42030b1100c0350040c03c4142c0250a151a09580c18052601252681072041000c10103d50001d241c03485440d0010507035581c0b4603c14003111403a1a407030700c000d40c1005107440c610303690501c61b408180107000905105004008d03403403401c820701001500304402000c5d0b66841654980c0c1c1007101683c440c0c02401c201060414a6210380303004d9a8040d6a0700121 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 520057778 1250 520056528 520056547
    0xe030a0c030f14070603020c01050c1303020603090114070504080105070206010e150103090c080705090c03011401110a060e07050a051f140c07090c03111905031e040b011712 76
    0xc0d0742d41c8220a5680e0b4400344010f42424504001e83c60081156503030041e07a0700845800c05003100c01c050803403100c40d1800c1004408505003e02c0c81e2080c0c03501200d85903031b2902e4142800e03004120003418141e018406e002000511070f01304010744201d503003202c0203008566800c00106c0e1122400d000b01d102c82c01c110000b10303043c1080030745a0203056006040009000442c0c0d180c8030320905090340a020742f6401a0424000b80c1003020b4071a80100b02c04200710308550404140c610780d8000c803a09541041016103c1c0c0580850070020003480540004082001502e010741aa46a146501070b0350300130740b15102c0000300c90411200c0b271100004001c2c8130004109404904540700d02c0044d0320304000310010f00011210b0001403080b01d00070000c440c03001480400c0108084c040c0d441520a00e40807030020b024003880180f80140131050403c00b460b10a07179139a10041c550042d480072001880240728844104070810081c214840c2c140c2c1d890f541d0903840005640d003120f035644059503c2e1040ba102c24443c0881 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 520059028 1250 520057778 520057793
    0xf170a020916030e1c020f030a05346e0114070507030c0b0c19020321090703080913020a030207140f031b0c100f0e030a0c03 55
    0x40401083c03070045000f41c041c8200d5441d04515a40c2020b02412015140383d0113601000002c1541e00001d000d18140340c0546000350903401000e0503840050000c4d110749449006540c2c0015202128280e800014006030a1000c2d08a8000c610f01200c05000820300d91020004810129070b0a10303a0451601e1801044000182419600341c1c0c4802030700480303c0c00d490300203d031010444007865800010f91a2125600981038160241480c0d050002c20800741c0003095000811001064004842d0000c68907a80045201c900c5070840001e41e0440d0061514070080e40803000341031104880c0c0c2d604104081060300c00414100c140c5a0202ca50300540013000014102c0024181d038810050a04480188181004060341d10006484000950000d4030908024541154004608811008101c0b038810105410380d640300d0490007000308101c90034520b80d94001000310032039104014061910711082900080c3c00300c050784840d0b2010554a0032903120501380002c90411164209050300c04051554440f8003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 520060278 1250 520059028 520059061
    0xb0a120807050a0f120306050607021e01140c0c031015050d06020706020d05010503101e0209040608122a0618150f0a0e0609340f170a0209 61
    0x1180350240510710000b007444018603001c554085d21241c040500506401001c8544942040384506828402d580158482c0016125a0070040e42462123440c0c5a000582d0710a17100094000b65a00010f141407a1100215000c05400d40a41c2111102801025424203072005200541038140302c0307400030025480c0a02e9525071180c0200001803a00340c0300d48480e41170781c0c04009213a0b074240d02c80300104044e040800c80854010381c0440c0c10080c50303851120301c1c50126100400d14560a8021603814100c0c2d49540c000390003001c0460896145a00d81c942450154010041801c4600e0710031100080c02c41b80c2603000600ba808120191804c1e6071354020200700c07100c1c10025405c40d44034070710008803818400c9104078042c039403980090241d031401e1040301068540c22204034942e600329509105140400280315031424a04132000a0640b51850300035000061401c080941200c0c21440024401000d125510699414581081d803200882041c0c2d590f445a07484020340010800001440c801e2050344070b103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 520061528 1250 520060278 520060283
    0x160b0f03072d0905030c10110c0d1b0f0317130803030f01090b0102160509070c05060703090501143306040b1b06160809031b010f0b0a120807 62
    0x10040302e2103030500c03001e00b4407a02c0301c80d00300d0195604403000400d80104081d0020603003100280b1384107100d2004506442034040c0c2440501080c800c0313001114800340041914034001500020b850720707050800c0d004149002c85e0a240614040e000800c09003010380c010030507a600603400904031a504444241c0da0340c490b290401400d8038401d400309000340309000850289081a0b520780b01035040c90408000c40d5404d005c0c550565000d82d540300071010714407603081c00f2158126600c43c100e555a00c410b90707030341458400080c01805120208020b00f038056106100c0240600000c2281610030441254070340d80a07280e070f81d1411050a84a0304114540400c00015408405030454840c240c2001c65801d8000e9041500e504d41c012030500011980141084102c00a140090a05003042c000103048138100041240401040c03000040401e0401c000b11007042d100400f6404010000f018224000d1144650302d6182c1400c20507a07508614241c03000f0419100c10810503142b0b034070300ba96505003561040408 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 520062778 1250 520061528 520061537
    0x30507270603050c01020c010e1003020304080904180311071d070c0b01090b0f04090c0308181903030305090f0d0c0303090f03090302090901140601080a0b0307030311160b0f0307 78
    0x201440003045008071002540720320010060301c803403d400a41012500d080c0036040140b40640544c4640c0c030075081840305043c5050040c0d90313440d242005c035132502c0740807089078000f400c2802c903c011050012600c2c96007802035450314646070080815546980c85841294800d070042c21004049200505242d50480c4076030915000b0304a050390358103542070f8240c2c0122411660303917084020f2418042c4070410341c03a0049800b0840211959210b503006580c030301002d890703540c01107100300c1d1130302142c00120ac41401c010b110950110844c40103140c43c001901007240000d04240110300c240e88001500c031000c2d10f0b140041c29040220080486a50901d0b480c01c0d0100350f180c02214004c218140c007500aa18000d0f55a8419a815030042c840180d00250120009030b02d03000d02a04034500d81c006440c2c204100b440d0030300b16500e0341d0545030054543c4a04c250780c1070107040c10010170503030003480701160015440107440000880c03014000070b000e014892420a90703c204038004650b59010015039201125080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 520064028 1250 520062778 520062839
    0x70311071e05010603081e090312250b060f100f080705040b030a0c0905030609030409110d020a0c0506180303040212011805070810051e07090b0a0c0c0f030507 70
    0x40303050135109194001d941c05403000809640090140c40d249001007429020207180000020200b60340e40c1ba210041c3c00900c002145420308c1e0700100d05509088030a0703e202410041c96030510080201c0250380492080d9071541d9a141c0d1803d040442e040c10350f010351038008024101d8a400d0713680f0a030040050042140400011540784d804001460140056000c0040c2100c40444060f00302800341d00482e1207030b8040170800c03d5418000049500341c03404090003040740f840c4c12030380c103d0500030610102c020a0020441103140c40d8003508a48a850184084403c1600c1c1d407603503110074034182c1d811000b60360010800203001d1304201080b0303400140240c0002a240810100358400c03d035000a085420380c01c80b06c000c001200d401c0200d0724880412000270001810304401d03e08822109441c81000c801e084d800007484a405508540c0042400b03aaa00d540c03205442c4000b0300087c40c0340c80484143c56049008600b071040502c1c3d11003a03036409001000001c5c18088505410340300d01e02c041e02c4160320b204 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 520065278 1250 520064028 520064033
    0x5031c03110c071701111605011806093806030f0106032405060609130f050c1e0301060e01050c1c0c050124140d1712070311071e 57
    0x8000c00c1001c80c0c08003e0701d4154288150240902e0300c54240c0c0b9056814503048512103c900412202040b003094403801600019240c0381c0d024080303201a1882e0401c600320315905010060700700d5050035200c1c41c0b80403800c00841541d0b428060100040d00c104a60000c0501da8800c0308034901908200020f00b25149100b0600702c4070300751100c940040301e80700c07090440c99178104c003941168006540319200034040d501c0c000c400306599019800c55039108140302541c03603502141a43c00344408100d488024003a503c2d15524000b0103502116511041d1681d6160f02140c422901c0d065a040e162a5502c421982d00b03110011102074001102c0b0403094042c60304104548000b280303140640034030a0f15000721400c1c59007000341c210703060034011031118280302c1e40000c14529440c5004040d5440d9010780500241d42e9000700e030b20b42003200001030001d1205200b00140070300d0040642019030440000b43d180c0e0703990080131810b0b210280900041500c2c244100800610700301d403240c0b0804049000c2c04042c64094 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 520066528 1250 520065278 520065311
    0x30112020f09040303020918010509040215070c08010506030d0806030d141b16090b0f0112020c0105090a060b03150a090314160b0106171503070503160f0504050105031c03 75
    0x1a68104d020a500059141060500380505d089950015407a602030750302d0080410320f042c5004000a1181c911803010700c0c49007600c603060751051600415940d8429441d02c030454004c15069482e18820302c01d07584000d80da10701c0780750010f1144101801a00c84181103c038192901c01c0c42c1540da030880f000a008114003103450b121500111040d81d4000c040f040040c920708800890703141c00100c10030b41000c102a03031640380e00d50b070381902c0042880e0003000d450300520080024011b81303100610799400d110902c0241000060040c62080c0100d0080092018ac80e08166545060180000302c031980c64000507159a0310f9400620818024249443d0704144100788140c20751000c000102c040a00c0c0b25040144500f40c40b215014000a0928454880d110f540d100803006000302078560943d210240c600740740c2c03000d01c5458000d040c080c0840c0d0803c0080c00242d1400c0f1018080c51445468204000400b45810f00869040f194094081c080c0118204009640b00841c0000c0e00285500e40e1400c3c482c881c0e01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 520067778 1250 520066528 520066531
    0x60c0a140f070822051e0d02010504080d110609060112060207020604030210030f0b0604121118090d021015090906060506160218092d010203040b060118030305030112020f09 76
    0x1c49103240c0c3da1130f5501032015003900340e500a18040d84906400d8814100c051034680b9070708504030f1300100441060702c0102d8141c46607811075841d0340a080c031050780042c1c02044000307a0151140c152003c80e070b50400c200d0380c0c98009104200700260b10401d9800400d07175a6005101042c006000c640c1340a80742d0300880c046500c441e0f2b41000080d5644800040c483c518454024807000854146240925208898801a0143d24058448005058501e082da5180850480442811000507046180c004180b03900d4002c3c0e100401c025000d201c20301c042c1c0f00707110322503100220801c440c1d03c1c2c2124101020303200101036240080b540d0f82e580f02c4000c00c3c50f50701d000c00f403c100c4130b0b004408488003c091040c40062110129451000345800e0188a0a4803001c50600c084080b14858170381000001c00030403080856003c3d0250700c0f0f510000500080c04250520345200300c200382c840411142c25907100840902141c84041c00144083c00103114420030081e05c0c3c1b1103140018100c02c00100000d0005403034020 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 520069028 1250 520067778 520067797
    0x60305010c05030a0f0b03100b0301062301020f06010f03080328062c010306020705120a031d0d0c03180b130602061e0f0c0d021b060c0a140f0708 64
    0x10702004000314540b044c0200c004500301c0c1038050003000e151b10003007961007080ba51250119900e83c0c25030149134409510110007404001d410340500540d090300700072041e4060b03400c01e005020b1110304224000001411504841403028082d0142e85561100403540e04064540e20112a03c80721b604500e0103200701004402903424000240c0901d041b110032510340366a180c0c0c180750140101d0000b9040951841d0904480d0010000b40c0c0d1100c05142c40760078030414032540a803000010542e0300c01203905a0005c9240d0070340042e80f8074402103a20781640e8900780c03000d40a000501905030340340080d201c0c0c00e41021004130915801c0d059620303502100320301c1c0c00036001c1e20308242c40385c4400c1001580c104487d64102070210b800200341c0044c12442d407070310100180070144000402c00400e6101a040d400c9610a1510510440d00c2e020503140d44c80c001c10711196031603045c0c031400020800d0300c0060f00840382140141c2d200d0032908030b0015211056600542504009071000744501303408200d0706001804040c6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 520070278 1250 520069028 520069037
    0xf09091a01020706090506041403070f0b0c0114010302130c030b030f100f0207030504061103120f060108011a070b090a240c021209192c09010c0906080a060305010c 72
    0x8521000a14040895200e44100017900c00100850340380d00781201c00307450310400b00c4490b20404c0d0000c02e2508110742e000e08444903103e40000740f100e8041d070140481c115000c000307100b0401c1b44024566418000c2c0006541319030003403c806000d0180e5880340c50400c586040200c0c0342c04846002a0604c0551a43c60100d6080040500760000c480d1180f9256410403010442c10135541d9280102140150b00441007070090b411586075554400704240c0b0714218034680d010307410340760600501c8440d02d42035541c0b50204031204008121928202810208658460f5a19042140f02d844c3c500304003030042c00c14a21805265101004110740761002402c150019000041c41d500c103051100131241e985103c08215000000800101742482c2c04840c01c10000b10380d68154010407261082d45003802c5d52041041c201c6e01411080c2d1500802e00c900c1050b10300103070401c81a901e00c4180b5090301d04900100d8006100c00f0410300c9024041c00c1801e81040851000003000c40e100d40e2840d0071a9010302031076000c038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 520071528 1250 520070278 520070321
    0x50405150106183813090221010311151c02091002060708190b13150b070f0209130c080a1e03020c040f0e01060b13051005030105010f0909 61
    0x343c44102c0c40303008120081e0407000b10105800030294010200ca4240880e683d030070030003030f01e1550310300c240c0b407080928800008441d5940c003c00c400030b5020010103803e104000401040810034000c6c5a41201c3d08645110b640550004c100704101c00e43e50140307024018103110300003507480100d42d0016003140d000c0340103035583c01010411808150580c07800e000c6501c000c0c2004003140c1c2c4190a40e1f0800105140000011602c40000e0003422904c02031036045000f88001500925091b000340002c08016008418100d0b103810030300d106482408400f07400603142802d03490040c20001c1000d0b901010402030310f060380400f6511110380d080c0d1030b4861480c50340700c2c00e01d101c280017100d1720116005507030624518200c145aa07019444070b03a1a10494400c6660743c504044400c244c1c0c00c4111910041c100030420681c643c20f4100c1c05800004040080600c51103022034542043c540d500d14441158480a055a10301801100c1d1008074040100800800e104000741e4a03280f2300615042c20080004070031003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 520072778 1250 520071528 520071557
    0xc030f0d0e0c0a0311040911060a0c0b100f0b0903030f040f051e0102153c1605071b09021602030d02030412020607060e1e0714090a050405150106 64
    0x102291003040b10320900c0300007030420005020342c910201078841500d001c200d0050900b007141c2c5072840d02c0e41c2c454020070005030f001c51441d408031100c1149842540030500c1900d0301050781d4440341d4036000e8000a00c10043e0103101300c02c800000780041200040c100d0785810081c0c418048c151700300741d00c2203410031121801484586031000300d0110075520040680b030700c2420207000035501c002559214144000d0a4040b0307a0b0f0345840c1281c0d141d01240c20070001c00c401c4140c404499000034403c01d01a00707000b075001145007c8a020701b40c2c00c201c1843c1d583c0b02d0405c0d9581d103849003040180c0c0e41c10827100b21500b400055071380103400a4020b000c488044c91034060114010b01d81031200c415456021034100b00400d200c1402c04072051850147c042e00c085840e00c01c0d03498100001d0103c503114030054132a032400142c03001d19031101e50040f840081c040c1c4805513134810b0074401080c094400300da44525201c0004034048aa5030281da44107000718215217515454450200c00342c0000e0b00b004000a0402180441 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 520074028 1250 520072778 520072783
    0x408060112030909230c0901110c030601231c02090711100c1106010906030510051e0403051e041e0b0f030408070605010b0d0507020f070504020c030f0d0e 68
    0x1001000030700301411070141d40c0200000014040c29010940d00c04c0710506103d020700d4510144644100b4129003030030400552546034104075031581c0003404007958803136080d00c04a50300714049006070003001941d00302002130048100048407203840e1454208010210307503d1520a424080c403404c0c1c0603c40803414018420310203402001c0a00344200400b00d0803000f0400604846000c800362400510400f03403050840c1e82c018400c0440040e4072941001042c25500c60344600112031003a0211000c5803405100c0006940d400c40c0c142c1c480c2d40802c80000361400d00300c003030790382c0c400d20a140440c40d01c445290720740720803003030100040f6013800c0c0402c080c070001c000e000507220708000c9180907210303252a145850a851040c59000c1144841c0800820308000480040c0ca404560058040c840d66071a00e46a0307441d50040030440c6422030a01022507035950010403a074000080c1c0e200645021401c10301408040d5000d41d081650f40c1c441007040048003c18034014040c4001c684501160801c2380001c0c40380b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 520075278 1250 520074028 520074031
    0x33a080703060b0a020709020a030f0e0c0102150c03070804080c150105010810030b15060c1203090115030b0708250206100807050a0612060b0c01090510050907030204110c0111040806 80
    0x225800f00400001d04500c0d00010403c00300c0c0c10311074000d6031322520050100c01501d4001e05084601e400c102601070082c4010482105584080c1c0c02c494480003000700d4100000030070f0301c0e817030081e01c004c00114103040d1181410a42c080d0003000c2880c5401d41ca051440d00e440d035146014036008000b500180b1196910a0a8030381104c0410040d030001c5003580c68224030f40601400f00200126400034502c001d4a17240240d80c0c0e46280182070b0b40c1a242e607000d0804043d401140c2414403035107049041e0280700080b0045c0401d403500010000d000343d50310742059490000184c035075010060b0904460340b0220341103700c0d000480e0554068100c42c00d1890105209100c203400804d40d640112400380555118040e06008032130309460074090300404018018002c00d629044885071610024031044110b00540150107924401d904403080860600c4404088500c04d80d800703002a00503000030809454283c2040311541038030240686441c48840000c0d00712042250034096003040401c2c00c1250a501740940d9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 520076528 1250 520075278 520075289
    0x9010203071d030709022d1c1104051309140d0206010e040b161103030c210106091203091e1d07120905011811030d020a02033a08070306 60
    0x90048140038800252111214040c42d0081540441d4003440c0c101f020401e80401c500194042020844031019042681e21041404041001025030b42440018501ca20a1100d50300740900703042505000402c1840d140a0b0b24998103e03450f280d640011484814040a01401c400010542d1083d4020040d0501e0340503030064000403904400c000114854050140e806581c401c41c140c88440a05400d441c1184401c1c40b10321140f1002c030422461607800c50082190002640741e221010b1a1205003440c400000d000d0361000030308101c420040e40e940c8490142106200741800048180c1700c1c003050165480122419071160f0b01d4010400503502400c40044407203800c040c00400a11700004003500380e00704150401342e00380c0d803a465941401820350001802e242c0504c1600044042401d0101413184401c1e41e46100e4045c6a1803040801d00004030708a529602a0141071812610006401c201c07010300080d5a0031114401e02440c090b100e50f142e202a03800d243c40b102d0340c500303000400800702d6141d80c111 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 520077778 1250 520076528 520076567
    0xc03011409090c0108040305070c0f0e060409020a0317040509090d080906070c0b1b0307021e0316020d021507140d03050103030e040c030e03040311190308070f05150901020307 77
    0x78003441c0c1c00e000c640b90007005005c3c01d00300313a2134450b40f408565602c50780754060400c0440303071b80214202c9040d000d20400c4880d49a55031405032580c108200451b008401d0095000c0c0da802001c1001480400f180c0141550383c40c140b80c20156148085042e042c2c3c04c860110568100007500b080f80ca42040419401103c0c9400815851400349805003410b0b000c244080d144150510010302d00c0c0f01d03401130b401100b545c00c54000384c0b00e04000324040e40d00c0c03100c80041451070f000503ca40c10a40d5000040d84c0d20710a00c0e00360204918041c0c1c0030702141401e06501660048210740100a804a0701c8004203000c901ca0032203800391800c031185082c01c14121a20200030942030200400100b94850350010042c0e03000c40b0001030b0401404019001829003601514130b50001107800014030440104d50b6920803401c0e030b880000c5c80100c45d0044115074940c040142800001e12901011402c09080086003900c500100c601c0880b030707000d0100c010f4074201e412030840d070b40020070081215407000f00035000e5001b05c01e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 520079028 1250 520077778 520077781
    0x30703030801032a14041b020c09010e070207091a060309060f0a021911010e0d050721050a0c1a0a0203090c01020109050d18050a06020d0206011e06030519050c03011409 74
    0x304401d28000620031101d4205c1c52138960745041e03846030b10151460042180c40c0890038a51440a0b40f1210314058441c81800c10400000d600420301142611401c0b0070b80c09807103001d0601c90f100004100d03d40401030300140b42c206031a803039143d020040d805030310717404001d0001d407815840c030403c2c803200203000c0c02c0703510700500402d4204d1258152044101000d400d20720a20714030481981d00600c070488008143c0d108002e070015200d5044070040c10014010106404030041030800d03900b50000b40701c2d20400103081003040e114094421149003e865108a101212104618540021514007580c20a440316030000a0100d2032400b01700035014684207000903c000c0005480e0305448084401e00c207420321110580c800b42e1503c5803850100907040c000c040418994452000950301c0c00402c014101600c211340002c6000d4010240720450050560801603480d814650b00700c014290190001c0600404801d040e0181c2c0142d000e051302c113401c40c00302c45c2d44940c5880c1440c540e100f0b952800d40c4c0152144030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 520080278 1250 520079028 520079093
    0x70605041505071103060c1c0e062703030c19020c22110d050618040c031209050904060b09060a0e04110604080a0b07031b021b030c03070303080103 65
    0x2124441d0080c400c0c00e0241e140c0b106400c040b40d0904070241102d5041c09010100582c459403100908110b004500d109000020414500e80845820748407022082c0e20100025644070480043c0000d0040c2c45c280e8400c6100000690700c0c0f0310341064500707000d8014041035a40c0620180c0e80d14070040c4405200811036400444045075001c4e022450720302301440b040181c032858040356080121011145854186c0e0f403003070122100d004010580f0110f100b085e47c1c80040c040c000c81400e10394069a00308551141c01481c55603039001210410040b04140922844005250303038442d861144268066900803807001303146010401103084c014206440f850f1400410b0109614070300049900a41c070511003008a8040c400080703550003543d0100d0440e01c00c4444903401c000c41d9018542c000e038059203051266242da031060b100d10760203120074600160721500c0e284040b81048039002c600480054107556041e40e003180480e00701140b030b800a40215081d03100400800c0100241c1c0ca008045401c01c02405d0300200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 520081528 1250 520080278 520080299
    0x7050102070b2505120f06040e12042102010807030f0f0603030c170c2a06040609080105074b020a05150408070f03050405090a0c0f020c0102061303090504061707060504 74
    0x25000b10081191b500c002111900c0d02e80c03029800d0b14801c001c43e134289401a4089410b94024094078414550300c020003d42c6410302c0e151014a80e60503110741110303941e0540b00324002e0a04400035401e0a803901e280203000f804a00c942e8000d0340c060380d51401d0000700d5040500c0204a091000e4180c0f510400c1040090800460200c1c803016141c0403006001141c500480110055003001030307400000010005911500020404d0490300000024401607480780740c240d5110459544481e1080208920030080c2e03900301c0020803c01900407250101c003032a42c03d2000c1022480d540907800750340640140d01c2800070030041c103842c4501030030b01100c062410340c0d96143c0301d000320040200306490f0070000904040c00344066501400000e88840094038060513050003422581c0440030208038000402450b061000c03895520101040e0024007180d22000d14292489240a00c243c04024100001040716510750103841c0061031403503819121f142c400703020300d0305003032596021f6130071f0110030041004036420070b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 520082778 1250 520081528 520081531
    0x70c0b060f06120a0516020a050c2b030216080c0a26030a020c0a150903080d020408010207050106090506010216140d33090b0c07050102070b250512 65
    0x25101044402401c0700401d074540283c01410060207107031010801e50586a50015201d24202c0240300014144080260f80780c2480c498080c1140e00302c07010143d09401d08240661501e641420b03524510891014480e142c801100812001600103503400205422541a00805499180060007061400200140b140812442080201e000701c1010302d00c038002c11070390002a020800d082e65984d44a0b884000d45850052454a01c2419000c80100303650854040c1844251026140d641201e420341c1c5490401da0800d0552056040c0c0801021554034403e0000d000224400c00000c034940b410302c1c982e0019510010300030ba0441d44002e895009100c0f68400c0d20003151020040313030000c031200d1804150740c0603070210090802c160800c4100307403207040880070807000c0d015001d0070b8070b0035841c00701840165104110050843c10101c4d0100d00d450814200426002d8480c40c0018544182a07a83c120301d64411180c0030039030000504141a401a0390010540b000004c0c904180750204181101070704150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 520084028 1250 520082778 520082791
    0xc1306050112050a06080a050d0306091a13020408100f05010501020109021e011806210b06180d1a0a060e04080403060b01121505010e040c0f0c0303110d14070c0b 71
    0x4603000030030302c0309404d548003101920400083d600c400d1307400d0800d0755a9590745401140000d181a1001910314594810000e555409140510154001008001900300501103800104c0e60030040003d64400800004901075142d140101e0300c5041400d1000c00c50703505900c068156410080301c10016998400c940309628100001c2c070f00d19a160300c0040300c10174040444c0341c100c01802c0c10007185140d00401d00307466401700402c40a502101d658004010b450641417035640001044c408903401200d6181c607161800409016024110502d4440d00c00d880114a80e01c40542c1d0380e4020700c90080b80c40d000300005090851005001403d095035801030f64407461201030311050b0344407000032140c1e1040060541000e20441b09100c60701c184001a004091188030b100e01103000d00002810354241030080004d4014140c5581010802c00907060301d06880001c400c6040655a846c58504540c10101510300701c00700040c005044840100e2805440402402c20310922450f01415000100c0c8041441d61201 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 520085278 1250 520084028 520084031
    0x10f060e2202130902090603011a0112150906180b0f10022529070b061f020303010609170607110f030301031b0e09030f07110405090c1306050112 64
    0x99280300744240614491000354822580105000101140d400a04c00d842c000c8070802031540301d4504042c02c031200c40f41e24040e558103001d02d9250a40c0510785880d0108101c100c00300d1404106042c4c041802281d8100c00c01d1075a5889040c08818004510a80340d20005041003090010180014201c0504100c1c04c1d8402c0484010b240c241da842484032a003603a149010031501052041c400d56140c0d6500e0203000880c1d481d41d07404455042e5910b2080401000c141d90300e620f4900151030710040300c0f8008001c03581100c800311001c0e07182a800c4032052038240d401d601558484d410300e4001072040180e035000c6180c2100c5541c0417030000300e012403100d401104501b003100c20803645204c03540c20b00340d20303007d080028040400000706014003040369001d482c1c1500004d221258891500d421401420b59440b00d0075813042c070241c58003e00c00401010494010304400d00350343c0c840342c00102900c20485203460190443c00c5d86d40913034207242ca1903603412004018144407041c2800002400b00c42d0001d901800303603 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 520086528 1250 520085278 520085311
    0x1d030f0703210b0f04020915030406320609010b0a1107170f0601080d0f0f140a020c01230a0302070c0f1205160e0402060901120606030b03010f060e 65
    0x14000e0040e446201804400014410a08141c440041541d03078180b40c05140f45003009413082c0f809100b00e48800e40700400c80a542c4488845003410340d040280304540a6941d1070f642018503c844089004500440e0589404200b185181c0d030b1175800040c1010380950011801401340c10b02c00c03010f5031601d603498038000007010300c3c3d980740c0e514004242e8880c008000890052121002003c103112020501c2e000c100e80e0071366a2062416075460207d01000001140d039444c8542e1144210807001c03801c0010300d823844541400d0800c3c010158041188840540c0c0800c040034510750300003c4030b08000441c3c00b0545046211800c00e04003c0c480d0510032410154006445402c1205c01003811000e040c4804141a01c0e0f502d50b41c4580e66180780d0071003903500384507044078040c1140764a5010400e440ca540c2120029489560900c2070b10b03045903460506004608184c0c4015414500c00c0100908650303030045004074002c010702d82103900ca4800720071118102030042c1f2840ca40008482c0c0c004050b9041c0382a40c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 520087778 1250 520086528 520086533
    0x60e06030415060b090301060506130e13021504050f0a06080718030804030812130c060c0501020c01050f101719021804030507020a0803071203020306060c01051602011d030f07 77
    0xb51554004101e4591910f00b0120301074640c0c001608002d20254020881e20751902c08100e40d60161020640340c0c07001840302445400d01900c0384d1900041d4040100d6041985540001c3c01e1664845202031a0480850704110038980b0b12901c204200095500440c11400c010008008800050261050118401c140d07501400140700340c00040d6000003d09485680700c0c580310100e035200e40b107015a000b03e41004980450300d10500360009a9000900261003846d04000303880f07501d8144030a8807195030a0026004c41c0c8000e00070035206a01c821003c000b00e1902090089000303482c0d8000b0540c00d40346a11403120141c0000340342c181c0306c08410145040c00001d1000030900e070710081d444a44804040180070405400070050811181300304c84e002c01721b58684061a03500e009000c40035042407d00d40500d030106010307500564100601505107850f0403174550003542940c1c0156004000344450389948540b0507420302c43c007040c000d0b0700c40c65008080700014955907039004031941000760000001c0c80a08 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 520089028 1250 520087778 520087793
    0x4140a0203060f01091103090c040f06051c141609051003050f0303090d0e03030706050406060801060602030306100512010b03070903061d1510030b040c08030313050c0406060e060304 80
    0x90480c0d005084039041e1904a2000a2464007131045001c420b00b407003000b0307500e11039120030b50744200c8001004108180c00320302004080d000347c4501072062591124042007030f84882022440e54010960712881c2c6008501d0011809409240d503012560010a0040329040c10045040300b110304d07040c000f04040c1c03200c0d401c15038048000d07440107180380b0500f0103005011201001075032040e041d490035070380b5807a20401e0070780c2d1491300100c9440d4160030400240c80001ea642d80403d800600032400000d40c1d52b2140340d02c130b027107035000d400242c050380c004410080c561030400e0562200881d03030301d0140c0c01c0034549100c56200940600030030344c407a1404400915654070a48002d4000c6030824428011104a41e8283c0d0307882c2000030002e0345900032024607a15940501c10958011041010201099451910fa40110b5035000e00110342140c015040011018010405140100241072141842d404180f81c0549003819000d0f040e800740d801c2c403004100098000085803411102075406540e240c1d11440c0454 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 520090278 1250 520089028 520089043
    0x2031e0d1410060212040e01261b1302070c05010c1401090f1a01150f09080307030215010e060d03030504050c030105010e100e0f1810020d0219080f0414 67
    0x4141c800408020200c02d00302e1081c8201c4240b90241c550350f2010943e01d40b803d124602441040950301c000410041211100c0d15028012804104c040b010801000f6400c2000c4428411090203842d030303080d0768901e4003a00c0c601500400d044c0c1180740548590366048540c400d07108d41410700051101e04030030700c0b41e40406643d0540704200200000e41c21032814015011070800243e5118142c00c00d091011081c041d0bc56051302c0c28141d20b0709a0403c060800c0b1703007140d1500041c1041014070f080c001071440042016112051098014090088041018940c2400168890142c2106040c140030450f02d502200d40318064051030082003681d681d0030424502455000790b2a01586003500006207903000c650b0b07503405129080401c5450607070b60300207002420382c1505d2120708101c00700d000c41c20b1034900700c00400810a200082c1d45030381c0c0380a0a0074049030040000c44940d02d03000203030611503034480d421195415029087c00005801c00078110018040010402030600b542c100385016070450401180 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 520091528 1250 520090278 520090301
    0xe0d1101120908070303050106020c031b0a030203100b010e060717180303030f0613090314070f05030f041e0b0a230c030d0c0f02060a051005150c06060102031e0d 71
    0x41c020800d0701d240c0407001da480744c00140d00103440c00001007400751000c22880c000c80d200a0044c0010031070041d00080c01078119003160751040e410007002005880c1401440d000d101924000240601c140c00050184028000d007244180000c01c5000d000614018904036003215200d82c0300e0f00c3d0200e00c2c00701941117000c00410360b410321022041000400340008060311816068590080b2074148448040983e03c0e80b001c014049009101503c1994400310003401c0190f008140d0b404010283e07441d0507055078081400225070100019040c002001081034207500102148006c1d02001d103403006000d198040c40c4140f504205034540b0b2510b0303401c001c05001c14070234048004c035541c0b0300c100d602c2d2564992080b4180d100d05405c00e41142511401220103200308d910341d8001e443d13242d5500810310018003004000e0380301c000310360101017110303180d12084a048103044840300740d0300c0d0402074009103001001000c00f811540100045013003043c60900481020350268680c648460031155560007410106626 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 520092778 1250 520091528 520091531
    0x711030309040f050a380315010f0e0601140301090e0a02040516120b180a0e0604110102100e0c060703020f0d09051503040b040f02010c021009060f0e0d110112 70
    0x104038801c2c2e0201e8005c00101804001c0e40f1502102c840b640c0003540c400240d00d8201d14291008a1840b4601d451196401001d42e1054880440320321a91002a0440341384040b03600010300051071141c182541003142402c18000000262140803014803050007192030f895125080c0c610328142c03c01207060b40f00e80c010b0050107a0701d4040e0400d042e0300b41c51b0350050002403058041442c000b185126500800c2c0c4060000d030010390501641103070443c0080c19000c8040c0d950003103100521340900c0480d008030b2140688554901c11480020301e070001c143d0003403003014545028520721807030000e00c410780e4060642c0c0680e158190741c1810b03824150107108008640c0200b41031010040da1001045084d1401100d20050114400d8045420b50004860080c00c0782c540d80040b801249850340591030b4103105160403446441c4a5000c00c000c01101e05a20020880b104402c1c030040d6002600c48561118a2910812a8202038002780c10621403400103085e401108008808a07441000103c0070350317414040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 520094028 1250 520092778 520092791
    0x1406010c08070b160f110330100603051f0312050435120301090f06091e05090c011b050c0d0812061c020907050c010c05030a150605071103030904 64
    0x410b0060700d1030284d5620010301e11024494406005070520002c46145000071400c2c00305403c0034481c3c00d000342d40d200c1c1d2a10310242600c00d00e04060054588150400015200300518150004e825554040c3c10b0611840900c1212400c24100020303a2040741d8101d01689014464003500f41c8441c46146c220103a0104012542a03811640c807030301141030a112560002c035000e84204150300c8030b40d4910034100765241007004026070421908004d080c1080c9407000640d090355550950201d03030303000315000b110441e901224110342001d4860780740e00c0341940d005440d0452000000901c007000101c41041031320011068042130010411915042210207411a0f005280506051065030408458503172440788400c0042c0c000e00300103440c20201d10002c045541160071660030070104207401001c1d00b0400c01e0a06c0301c140c03205003d015854660500782c0b200f941d80d0409200c14420b94240750320031118000c5c03048041250300d134424210380d29280c10040700048420030a0009040d4440c00422603030182c10000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 520095278 1250 520094028 520094041
    0x6090406140a082a010311071a090607020705130e070b0c070b040b0a050c120f0403050606030a0203030a080406060e0a020d0c0c021302070501090c0801051602011406010c08070b 78
    0x360010649242141c107110825070320300c04182e44180c40340d0f40001503160621070301020703071000c001341c4918401410042000c60b01031241190a0708108410340e18060420030191000c080786082070781206003074000e440c1501d000200a0765a4215120322409000701d101d40c468140025070040f50001c07510030a840b8581e5075900d580e6890340000d03080210314080c03010b00242030494a021130b812256040045c0b0704284900606441130342016203202543d000741001c58820410150042c00751598a00c0b4036070320359003175052951803c20000c1a5602036802101c030f50016039400000c2d00e980142900d024001aa2031389010000340031280c1c44140c10040000a2150b80c3d1860b0300901052401504d080000c6075140008403140111208065000140d148254010725950740040405a014030004a014500d9548204410110307502c40119a5910018007030b400408008031444203006200034016482d048041c022803820280105041c0030010594030f04100150042d9089150050f2910700180f0308030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 520096528 1250 520095278 520095299
    0x12090105120a021b06060f0112090501060e010f0503070e0a0b03150702030a080a092414010312080601050403030801140127060f0c050618010209030a030509090601030b030a1106090406 81
    0x3101c0313030043c0610b20107080c100403001409510424005000000341d04120005540075002e01c011b070a841030310340d4901000f00e034007406410000c1604c01d04080241d0b261000310503903c0300039000b451283d00828001c1042c2011602c20030f4010031002e20003e4040344c8140001e1030702c0000e520380903c4142442c100540c054005c4050080c8070240d03228501c41c0d40d0340c25031446c1101d0b990a0000d080c00c14448241c0b0b80e12128085403030148040c4040040e2800c1c0c0501e4031482d94100b40d0080351203030b5040d40c00044071603000010640020302820302c2d50a00d829a5809049800140145124410f19070080c3c2045e038072960782d1200c40a13440d07410001c03112800314921901021070083e0000701c0c00d81c081c8002e409103d1081511940e80040c064001c68940526a001c4402d120140c80c800d0340d0213008500d550b42d001e0111401ba544640c81d02070381d5400b6500bd20100c01802800c00341803520f001200701d00ea842c0803d5021113a64004001c9220004040c0029814002c0d050b01c50703042458500045515040c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 520097778 1250 520096528 520096537
    0xc2701230a090b030106021009082208070f0b041a190e0f0f01020d080a15120501060503010504030e0d0501060e0a0603230d26070e01081302010212090105120a02 71
    0x850b510303503000588951040109110078443c20f001a07001c1c0c0106d0a045407254819800c3c00d104108880c0b4004481011040c003040900c14510400403501c1d01b00710501702000f82c040200b15031091200700510300202d07211035008d28840c02c0443c00c00c2690044c96114044c01725902184500c1e00840f414209200081a00d0303110075009000764450f00101c2480e24280303121808642051340104071064000d40220b450a002900c80c0d0ba91503114560b40c042a0041c40c180801b0f400d80e40310f071443d100518149a07003528040c0d07000c14002e916000500004c030b54011403100c401c64043d00d280414000380c0c036101e03004050943c840c03d0381110070014894640000d4000c3e0702142d014007070344a206501c0030b41c40e91290b0282c81034404181d2000c500804020302603130070240680040114016840039506079403000e90800c56104001819000d001da04540e0400340c0c0340d400c0010080c0d01580e5610541c0042c2d503800c41e031784144145500105541c03030142e00c0350046031440a10744030f01e0141802d00001e440041d400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 520099028 1250 520097778 520097797
    0x1e03010305011a151b0304031217040f08030403022e060501020c0625050105070e1e0112050c070c08060f011a07080d09060e0705090c270123 62
    0x700300240f945007034070f061680e10039080100fa0700710902c40850325544661000a09888a83d4400c006441054092000e48001c6014121400c81a020701d00001e002001d080040f43c0e5814819082c40302141032020001c0603e903201e80682e689880e141800d910300740f030b915900e10040e00f00280c28034121241c0c24415041c600781010030321509840d0f5006a07107a81c0c15003000c5e40c0060782401482d45407003000303d2401b030006d6008040311681400e038680d01d00f541c4040319100003142501403910f0403805e04d00e4a51a034034060400780446c0860690000740b0301c07010340d42c0e441074041e155404121121000d0007100d000e180d000c50811440c541d00c994a07a15400300b1101010480000d00000a05a40c007005200200c0d00c41c00c090351500e0300d19600c1c843c2d00d0b0010b8103541c4403180c2d210342a000041c42482071140780404c42000704501490541000801c2030000c0c003108000e00280107000d500c1c464910b01c0e11110132142c8a6844200c070410040310098140390408400c0011606240c41820740c25006083c4a0b1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 520100278 1250 520099028 520099031
    0x201030209030a1b06090e06040f140f011d01030305030403081f06090807050301200307051e1c0b010c0b190606050a0306090c050a081308300106081b1e0301030501 72
    0x2617491074190388800452040114000b5010001600d52030240d010880d540c445540010b113421021034040d9052601300c695807804440c100041c085117103819002ca001800c40c8511030400d40c110366001384640400b070001018002c41f00c00ac81c680c581c14041405200c650b00941500340c1d40e4507080144000300d1350ac40d018007405090030200d000d04041c0503020942410500c91442c00e4600b40701e5001e0760784010450300800c0020712034400d0400441000c0c18040b5a080c0302c541d2a8800303c82810381007440c042110b09200d103041c1040c0d045d80d8010850020745500310701c3e0186295038403200809200780401181d42a603140c00d401081d03c0380c200d8060841c0c1c180e2541c1c20013171251200301c2d0f01c08882c2e042060001050040c00300441161268501d26031044bc0c030103080704441d400f036580e10b00070303001180390720b180071002d1300400d0b9450088407042a528000078a40740c565450b18901030180d90024100c803801000680599620100f00d1084490750085016501003d804c84d80404a00703420a01040300c865 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 520101528 1250 520100278 520100333
    0x6210b090a052a040b220b040525020606090a090f0602031305060c070c141c0303020d240317070c060f1116180906060e150901150c0201030209030a 65
    0x600b003c1c45000c5000c0c0c000751441c011b10380550515201a5079640e1404881611521440515210b600456000b0740c003080440c5161903403400211954080759440c7d40856203c1e0081180b590787d54003040b50805001580000d0042c92810460b100d9000054007815441c0000240020101665001c0441c1070252041e280c03135456202c081c04185c07044800191604004d90401d0041c603010b11042c0d050320600a040e4116602d02e98802022149248030940c0405ea01141c2010080030f28044d40c00000124040b4228080c542e901c2d4286030401c1c0e000103040360801c4110840e4851449048540e00c81d001105600340030b5483c3d0004058100e084c3ca49000607410705009980c90400280801d0500750724101c560320300d402c4c00c0c100580e05861149201150b500c400003000803414034802e801c0500a5100744400320310740124185010340402c21028003c3ca18040100544d1420125107241c1005514000d8030340101d45c00101c002e805030bc0d40303981c0d140c0030b4518060100721070201c4107525000c1d4034001200301c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 520102778 1250 520101528 520101613
    0x15070b0f0f071d0f120a050d0509061602030a020a03080c011a010c021212071a100305032b05011217030105030c121c080a06210b090a05 60
    0x941d60690300381021400b200795802a1104030354102d081004042d200b241e40c10543d4000038064914100d0301c130420303040740d13001d00140442400848846e0306541480e074540403d440c0410390600c00e450010820300d1180780c0c1c0711308568050110030071a40c2c000701404030341622410000710507817085c1000341944d072030180000c41d20800e000e480b00e000e41050311843c0c0b4564407034003400180f1421041c0d46915005444442034042c42c0f400244c65500d0180702404103031407141c000d171441240040e015511900422800b0000140000b080b25001c03070005a1070b60240708000c0d000f00c10f0440306008849240c1c1800004101c8100454080403528050200201e0042e21540c0d146140e00c030030b000765905034000100d804c6075420007003070b0407920803480c0d411110340603d102099076407030003046010400600510103121004481d03000d0000500000300700f6000150555001980c82d5440140040c4408001e00c001005400240003400d90b66420506490901100070408800307405400800d280640e01c01010706070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 520104028 1250 520102778 520102801
    0xb10050a08010909171c021b0106140a0b0d0e010c08240915011206030c05090703020a0207090e030706050709051216060e0613030f02040608160b0915070b0f 69
    0x1303041c3c0d00f120414181c1c501202c1e0301011648a510f0168000180348000017410205100030540c0c0e20b9410742c6c0d03406507940030b0020360959070389500c0011386841030035074090666601c54482d0129289051590391f03818030807080d400905124802c1c10f1046d4038000281070140c1d00100c00364841d4038150030200c3c45024200d0f842803117070060a040e64105000000080260b80c0703803103a08880075414104040041000d040e071710305072610b580085441c000242c00030461420400c4649400013a203050a41c14060022070007540c0b01c0040c46441880764840803113400c0c5110070f10442d2421500b000043c00300e072030907000203015482c41c0e101301c9000720f0401640054610020801d4145a03d100e001c0185503881d1440442d00e0800d401895548200100951b1808800b02c0510600031b6100b2041c5101c60f041a00401040b2030069004152581200580001c481c9081c4a60425141140003003901c5203100c00108610480c14955200c07030100005120003032207400248a8820130b007000f03451101e03903604d81d43d046 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 520105278 1250 520104028 520104041
    0x5070b04090612050d030b06070b09011a060c0a17071515051905150913090203190f030807033b0309030d26180d022107060b10050a080109 61
    0x91403504052803005c0c80314880c0c0c1200117414402081c031414104c0d6600c400b0300c00c080035590822181c0d59101082e20100c0c40100b10703d002c00c3c00322a640e082030310640143c0e4450f2008030004100012400885018188120a0300c40756900725034240303600d9118050610040c00c0a03026001001150706001072103141034401401e260a69094070a1402c0c0f0380002d01c43c0d6200c0d0310b070281c0d69001c024010703040e80341c03115441807065100900b000700b40c0c0790b05401850304011080c502c10306c0c4110301c80c01c80404122140c0400c01c0b584d078549040c041a0381ca6a0b811001030000704241040104804d500c18550701c161800ea000d007124500106c9400310b0428482580c0388115801070350503411004141c2d40340d60094076000c8080240d111103620804000e1824030122900300d41403044000090900d0140c1042000854001b280f940010181c0d084000c240711101e40c40006808461b8200090301c4081202d1504400304c40c040c040c10400d248140100d001d01660050141080060459000015112094003c0c0c3c2c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 520106528 1250 520105278 520105283
    0x30406330605030903160503031005090103120e0315012304090b070809030f04060906030e01060b04140f04090503030f0901020306010503010317090d03031505300a05070b04090612 79
    0x100400c03803401c801a2201c1e0070041042590340000e1110084080f507403156100703441e120b0303c041c603940d2030000007003842c400300c0c1e4001394029480c1c0c0e0010b000080c0b02c1010290744100307604090109240d806d0010340341984034004100c6241c500c40c000514400b0f02e0b50250340355810203203000240082c11044c1b1040b1281817030081c0c040354404000c520080d020f444510303040083c00d0240c070b10b0403480c21081400d40e070080e440040000d0248204208155241c4100c521f8551444001d00005107098070b964810f000c0c60140030500c0500c901c1d04000c0707642e50044204825006401806000c0f00e0b400d01d40c0c0c994004a81c40481000c201c0b001425001d41131007140d01c94581615928207503402d6440b1070181035490f11000030800300c20003092425990b6090290001e0f0300c2136402040c0310030f04021f9132103600c02c8d41c0e000c0c078000d940b0350b80a114141d809585200041c091080800f90300c0030b410344100d15280f18400082c0c4140142d60010603070845503c014000da495a41c0140030159a41140c041c1c4884a020003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 520107778 1250 520106528 520106621
    0x30e0102032a0c0102070c1403011806052e0302010212041a2110050103180b04080903120a03050603061303020309100e100302120c071509051002030406 67
    0x181855408800a00e41501c19801c2c1e50398100030f1105041822644405001c0e03855141890040095203c2c2040d40450b40009030b0080c4085501c410b44e1010080945000402240d181c000040c1d001006007034081000d0010042002078107048003d090040380c1d01d02003a4014042c032801402150360300000c507803c580324003510b0640b40102c0402c28070f2503081104a002800354080041503619000b6180600404898551030302076482e200004d01258682c40b20015178030300140d040d001060304030b413070700b58088d404c425015501c03404036001a040a00c0c0a17865040b81a0104444002e598913520151040a003076045600640300c0c882d503004000440c0800900503441000148228100703112811900c1c6c45905120040c03001000003e03280200d0a1010300019074042101d41006c484180580d03001019815294034180d215210b8040245910001d09165926001c5e541c082001c100f003070769078850318510115202d043ca450404080c0900075001901d031984030420504003849103074804407076a0910034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 520109028 1250 520107778 520107811
    0xb0316050d0906020721031b050d090204090c0e0a090b06040c0c021f03060b0a0905150706050f010815010b030a0914030c0d1805010903080c032206030e010203 70
    0x1254030340d01c28421498a2a110841540018540d001400c3d032a03104840c113014030051500f0790305046000344201c100b00b6052500304031440c1d0401a240d400c1090510708150340d003142031409000f400780600d000390000c3c50b180944092100d910003040c142e81c82d242240115031558803451044c0c4451401c0a81405090710224410f46031550140107000103074100326804d035190303400180842c450450301500c4010690340c1850b41a90611038030001d4000d050006043c000400c6009040c0d0040b8014140120040d8501c22240210f2809846035545c1c44481842075141000214021100071702c9139031054406d00070621000b044030302c00d881c16900120070107810740c2c2d1101e81c1c05d40a4280303c00140d541c1d10100c4810340040d00c1c02e200403c82d000407000100454990351a0003414410308115028607a82c00d15030a02590380d00100d0b5600b03c0303801a100c01d0700c940b50314080720300710300c80c14080d020740741d0074415802100380d8141c41c0380c811980b043d24100082d072060130f001d0b400d0348000c03660420400392480 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 520110278 1250 520109028 520109071
    0x60c0a09121e0804051009030b0103031107090203131202063702030f040b180a030309060e0303090106050319021c03170c0306040513080712140708130b03 68
    0x440c0c012039240124410401820242d60360700700c0181489003540c80100000e410300850a14080f0300340d8410261904200c0c007403840c0c070342e482900e106010003010096840c00d10b44903101c00700106409003080310011035590a003100e8410142c0303400703901110a0105040b281980900214032584a1040720a4038441c1200c502d0040307200c22000290741d44003400c00c2c07050580000c100c1c07001c2c5104649040c043d000e6401d0600b005460001c1c004e2282c030a0078040b01046440c580040f51b8175880982c90304010031590724034030341400a40001007050100d0305c804005c129100805410207000c5a00030350a4449054070300c581340c003003850691006500800f003040c580c001003000000d41841c0038000d04c0d1000864424051004003400d055130f28a904d20070110a000c00c5250034406c064000c002c0100da0003401d003241d9100c2d84940038010000e41034144c04180c080c24030780100b400141003a0403201e200c0c1e85902d60b2500403400d13085202d83c10b00e001c1c4034600c0803c508169070300312401070140d00d0315070140c4030095 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 520111528 1250 520110278 520110299
    0x405041b151e230c031305040501080d0f0f02030415230a0203090d0606152003120403050d1d031c0504111504050d15231f05090a0509060c0a09 63
    0x220b10f4044a40400550840e03120900241c07603107a00464001c4003540c0b8001c204000d40d01c040c0c00009039038000814410040d90030096041c0500c000f41404800401265000d0341036000e168404400c11812030054507101707501824440031440707941c1020561001d8040203170b0b032901655015030003681c0204101820703840c0030407045400a10a4030702194240c6c8600b04802500c002003800c401041908009800c22400002002c0002049500035414010055181c0029200250000d014003d000841c0350350741905400400340b4202058001100c0c03920900141d98991040800e4880c1507012501c585211041c6d000d800c0c0104d03004080300401c510588104442c902d0903801c00d030340444082000280d00e0f100c44049960450140c440e84520400d40c114010994100f20440070400d035010742c0c0b05110092900300c0765040400c0511444109048003801701c43c042c0e09400880c0e1100c0d44000700007540c14650401c6124015020598800d511218a000002d000313a20117000842e403100001d200c1c45824 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 520112778 1250 520111528 520111577
    0x3040602030910090f06080f100f21060c03090201020f0c0a060804060b030706050c01060501080c07140f010501120606080d0914010c080c030406020d09030812060604120b040606050d050303060405041b151e 90
    0x2462f41c01400704c559075034440031a400c2c14030441c04651100058001d43d038050120a80d04e402c0003000e4032000030b11400103103042201c1d015010138420a40082028000742c1c0d030003420029005001c480c803880d140e4101a00540240c00303550780710b600748040841c165210f0710700d641c000c41440080718285801e550312500b441e05215a49921889140c10700c203040c41c400d0040c1c074028240c41a07280382021042c180201518415000054a9407042c609180e1003507110303448008a0b480c09c800e6022000e60b00c070049450080c030180283c190794020810721041c140100051086603481d030215040304080300703401d80300118140f1000e0604001801802c801d6030040381c440303500810007020249026110303a010b64007140035072420b907540400201080100101d41c40303800d0140204a5048054090035912241e6070f00c401040e00d806180c032800807a040146200e0b80c8211301c04140102118181c40f801e01d80030402c1d100c000040060041270380d1880c0320100d02d02c4500910030343e603070311000801d1081903014800314 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 520114028 1250 520112778 520112819
    0xe070f0f081216020307031a0c0301051e360a060503030307082a030414060105130b0415080a050601062c1503010617010803040602030910090f06080f100f 68
    0xf501d8008401a5000d012000c0a0b44c80307408102c8029964070407058804e44000c010b07030480391040005011942e44c03401120903c81d070218994048001890110300c0b01c18050a51013424800e0f20020300c1079000000b03408403c0c941d041c10304003040e42d550314098181d61462003250340580040001c41c002920514585a01040c0c06168181020003000c059002c903140c009151000035000c424041000b003980d0034441c1c2d0000c10001082c0a505100014100607800042c170415181d0351540c2c0e90880d03c039908155008103698204401040d9255425511072411070011274040c0104000429254007920071220051180c004030044a020059088000c0700420100740d80207070f680e047c44a1080d004402140030709680c1e07076000c201da0240510000a1001a00488450380080c00700344001030340041541e11000702104d17681d1a4451004040d6100b4505e600301e400070035000354001c1540d94020100d64080c5c0c2c01e0b13040850b01c4e90b0740c010140490080c0c6001d581c0c041006003404219241c00601944a80f92 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 520115278 1250 520114028 520114057
    0x21503090304030c090f150b031f0506031e010e07050d0b041b111504050a0602090a09060b04051e0a0509090f151b0307050405010f090503010e070f0f0812 68
    0x25125114061300003080c1c1e0251001684500040501e03040d02d0060b810004820303503440e004d581c200012010240401071000c0c40c50700e81c412620082c0e0000701d0010703005100c040c01c5542d803410b0a078614200ca00104e180350105044101c00040c8468915400394851103540d5295410001e000590201030300c00000041c1d80b054942c1c0c902101c07020140c001b012018102d403110300d6001c1032003c00e603050032080180189400c480340d0030040841d201280c9413a003154865001a80c07041080c001070140c0c3c80b0341c0c005020360741c541040881d020081000400c1918401c84403034221246a11950410518a92542c2d03080394046c0d00411650400441003500702c0119415582100d0310181e4070351400007003d10341070240e0443c0051085400088460728007507580e00c0f084900d9440d0441024110341300b980f05060410840c10f06020000f4458424640500350044c02840031161281640e5a10080b40c040d0410502e001d10f4002001ea000b110030700200d030094005400404401c0304161269002502000e5050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 520116528 1250 520115278 520115287
    0x140d020103060b0a0c051e03070204091703010f06090f05060d0c02101e0f23041712060907050c072102191502010204061713060f0f180215030903 64
    0x40d11500588481c141e00da464448a000c0c0f41041b919101a580030440440c110740500305460384080210381115805070b60102e2001c0a52a09848102119004000850020001242c00303050318032010212070155070381001d001d0b2079040512400702d0758412583c1c0038008001c200310f100c0558204a03441a8140150748a10026184200507101e190030100c03c0900f0303038002ca80c10700d400343c03041c22007548030f004003000840700c0911900340c3c604440b42d1010455180e00001010811018194070b11490460541500d9034071020308425680c600f13594403441285500e00050001d4450001c0c3da0403029810000c0041901c1c01e5210f00c0c803c0c4450a000965109107054040580c46100a80c500c0805c400c05140049180c1127402c032440b6420a150011a40104010004194010003030310b100c40c01800c5d16000d948650114155040c0414002014141400f059003400c11107903000001410340f010b0140b11401a1141c081c103502d202c0100254442c1d03681007540c0501c80c021002d16404040c0e00300b2246003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 520117778 1250 520116528 520116539
    0x60406081b1809010e0c0426150604050601020f0607110a06110a02100911040e1005010e01060906140412080409090605060a170d05130e2707140d02010306 68
    0x290340c04406a525026400700b01d005080c2003600c1554010010b0031640121402c0644010046201c1c600c1015408190f0100c1c403107040b05039071252410040040d0031107600c441504225190071104848580c8643d1514001441550010810402018900e400341c040e80e039516400341c031808003100c1c15846520410502d440013506c2842070805003001502040d031100301048009141220603108c480c131490410444000040e044240301000800403a80030500c010400c103d1441c0065240d4100c00050904e0300006070019004c41990503501b080c0d88113030590340c03581c00030b4a0031510041b00d03484070703c000c200030403900081c0c4140c44846403007420303034602c1c00daa598010400d54a040f20142d50311542d40d810b1003010b10700012120004c040100c1241c085940243c5d00d11b444001c01c42c0b000051010011f404610700500c004842c010b40046213030310700c00b070034400380c8500c000b810480200b0b12001c030a043c1c1c402c03030240000e00314201c88942e10060000e9201c0400d1000e40890100d007241416241e00380402c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 520119028 1250 520117778 520117831
    0x4021002070b0d0e19200411192307060b030a020303030103050c03010c17070e01050405150705010b06071211030d0204060e030d0503160305060609120307031205010506040608 77
    0x5000885042c0400c0a41d207442d012824a144c1c17202c3c07480008103104592001502c2800c09420b035541d800c54401100540b007012170080d0241310010000b01c40001114490400c044582c03085501c3c69a841200c440715164843d59410700484819003009000c0c0300e11400541d0315000100340000103402d5a820981d01d9011034a180c00a800c2100c41d070700021640c002c81d0800f4032510000312120320b425003010601c854600308010024100c1c07810003424030300703003801640110f0454000780b002030594808038a5000c4140e0468002800841c0c0950800744869014170303080c0107030756207280c210b030f49400140c07451442611450940007001402c0d000903c02114035001c2172001c0c1c4000d15842e02c820140e20b011a04142c02c0c280903042d110f0500c14140b0a02042c052101c08a40201d032032800c0c0051583c0703454000444d24040d00761615840300002046800000020000d003414500c00d450b10300440d9034003441041903607024006d040e0030040501c03007049440e22404040e038104d45081c00284040311800303800d82 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 520120278 1250 520119028 520119037
    0x308030606040b03190e070e010303050307111b010905180606070f060216050c0904110d080903030708122503050402010c0501061e0608190b010908060a1a0906030604021002070b 78
    0x8643d1036040304a651400070706d0088000020100001c6c040c464142203d406100c14180006804c0002c0131000400c8140a0020040d200036031070b04443c424062008041c525a822079181400507901000000780350805002e404014140b00c1d4414600343d40b44d400b8844c881d00610400d481c11001e102111010a4040c07004095906500314007102e80c89031800d22600e409a40701c883c50003a00303101c0811002c24520713100c03204139050455400071b440c441414142c03078038000d030500503905002c0040c3c500c4c208642c24008225103400d4400361102a51150800d607401c01c285400000c0050002025070110b520940c411588688141400c05221950740c0f2824215112900072800205a440c040c0403025050f8000500078045840c24820768a0203007040e0821403507084aa902280c3c42c1e40c0b808030980c0c016074040010f0000c0ba02110418a001d00f00030000e40680301000d1078007401501005180d00781b458507240b00d88000b03030090407561982d9091045078011054180f003180204080400c10500c0b5a0041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 520121528 1250 520120278 520120291
    0x70c080c03090405062706010504170c0906011d0108061f020109050f030a0215040c0e0708250e13061805060306060d0b0103060207050c0904030215070503060a0308030606040b03 78
    0xc0da2680c0c0000c0922046403c0502005d2184801c02c2c0340c0000126461606403000348001d01051290300c9031f00043c1d42c07034016074103c50403214a2500c1c1580f08000004c122501440840f1683c0c1c0544840b0b0054031180391500b07440d040343c580c0c6114100707554021a000798000c0e0014080c4d407083c20340108c0600c001d800703107409280141d458071014800d1003020803000c07081104400186103070558070700300a503540b881c6010880c901504480000d05108400520301c0c0200000d01090886d40341914004254041c01c0300c0710011b01e62058842c000200355030000d81c0014165841300e415004a070420040b12406000b00504a60348071030004c110711000c4591440740c0c1c44801c6001c142400c2030420103081c0040142040d003e40303060074644011661603054030b41103c2c1c00050041c0d995203681441414030b0682c6001c42d0f04612540c05000030594001124041c104003c20004c031151030b102d5080711244800e4540c183d006000c0d00040c00414540002513800103001841e0360301e060f6580b1481d044076082110700 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 520122778 1250 520121528 520121533
    0xa05070812040b100f17030f03040f050d03140601031e1a0a090c08160c05070e090d2f161212020f0a0326092a0d0209070c080c 56
    0x348030803c26020030040c3c1002d80c401c02070381c14030b061240b007034510806482002c0c800c0c0541c14911655070010b10850f90260710f44105a0b5881c0341a040038566460380b42c4045032184036540104984502c03900c507001e102c4100007154030090b101c103001140941281021281040301c440040c01080d00707a4400c444141154001103c0154410804c100240d0300c15403210b22031030704202c2e00c50401d83d070240c1c032079601602440d03004000a54403440cc4842c0118010300420300e00c65503202080443c000d03080d85100b905130004903036403840c22150480b6801c1848500b404007498403601c0707100d0041442c6400780301400c600103c0300c661350207419101081c1d00e507520070140782e0264080c00007400740300380c0358400048160004161540079060259074400c041b80c0c014080001c40301120740110100c48065011404000503803155050284840c1d0700c075507480169036131042e00c081d07065a9901440c80344462a1900a01e0242403500e2602440078441d001489101004614003002001920480240c04400c00c10b100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 520124028 1250 520122778 520122781
    0x61201090b22020906100903050a0b2d0c0913060902030a060f1a09060c0109060516111207050f0a03020c04231f12060f051302030303010306020a05070812 68
    0x1068a001d8036414140b4050002c503542d55030168883e031040350b0b0082415161900b01d0750403000708070b03031981c01508000c0c0b203409000d440c0018484508001030194019429007200308008040410041682c008034a01120234a00002d20603c0507201400e10528058a000c1074031881001070012039101d0340007005015404400d0001e0540e1500c221006805081100c200182c00c2401b4000c2040d0070400d40c2c04070362400190000180c40311025200b0b10b840ca60001e01404005152010103810300300c4030515407a09110700274010a10503c412030903420014050300e1803036008055404c0c1640003c0301030b0b8580c812001a102c400c0e02c10032030140f032140030768058614030f084d00b8204800d0322081442e100102d4890848011702c4154080072640290007201504011072165000b0f00c3c440c03c1a5022031458149050084203110b5150400c8091010003c0201311555407416040d04180c13180e04040c0d05a032040c0b005200094603640200122030182c245982059001c2e501c0d292113501441849905030b10030340 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 520125278 1250 520124028 520124041
    0xf040807080d090e0c0705101404020f0307060c0f020406080717070b180f12071412030a0e0634140f0c010e0409060207050102070c0e0708010905061201090b 69
    0x3030000403419503c0d20b0030b500b070302d45a100c2c04160005030040c00a0500045e0020400104015406040000000038001000e07ca0381c1100c0b40401110164083d0303c44505044145c60040381ea54203468558680ca243c0003a03e03140d0a40d0240c03000d8040f03811036520580424006000c2040074010701042d0f00704001e16154881d400e0a0003030503844030540d084244912220700410031001504a00e0550b190400005040d00260200714800c4000d0500c1c0200c08021444004014601c20071003010380b51450030183c80001d803540c03845031915400c0058011500f404492070044000c01c1782040e00c40e079402c008650340c00c0d441c01d01e030805640041c04c0284024030508104409000c4900004264013606128203007060460302ca40c544110320b4100702488801500ea41da0f5940803415140d04901c00310349903c06d51410314000d501c00d180560300c4c2c84021200065000001584510030301c00c540e180b04499203814140300280c20007405459100303041c0031961105800034450480568040c14601e1098140380 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 520126528 1250 520125278 520125283
    0xb0a0f062007050d02031509010203070f02030f09010e1503070815090411060c0f0105041101090e190b01031404210c230109150618050103022101020f04080708 70
    0x142860710082190110a28a050703000c14424100c0740140e4040c001c4020510001e0304141520188144d81c0c11141d0612401700c41c15805035115050f50b465050340518004800e036501e00440c02209403003001006215004d500c90040c0409008003d0802c402c2210742400c1c030440f0740c108070b580e40c0010b0718070700030800b401d80c170030060350780a49041d10810380604168403280d41103004000b5550080f00c0028203001c1988040000d036000c044450000c00050a043c0742022030002840005800581c243c031f0081180904007003118042c41021030095250580d6400c1c10b405000240490b0381450b9455802c0e00c004d00003100407e100b58820a42c0311042901c0000389204a02c441d070310300d001c111800b180c1400064201c880882d0b52054030301204014059054018050106014014040b001c441c14903000c4902c16001b150a480005031030450b160309094128084410074031010b0740c0940500341e40c0303001d0750564540b08607890748007001510f42805952103040036409075200c010307240d118800811406409 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 520127778 1250 520126528 520126547
    0x70513141512060108160c060c023a110d030b0604030b07080a0609060b160f080c030307030605040510091a060c0a0311030c06061005090306010303121503020310020d0b0a0f06 77
    0x40d20b01e0040240002d000109500e8903180c0c02040c0550352034034980c181c5d008000e145402d410f4060000d008a44c80100010308102f031500300c03c1c17044105504620524090000c03009604012002031083c01030441040340036150221071144c0040c4100004008220301c202803921a241d552504012410011012800c070348181d030103040c24500e4928103106840300d400844180c4007504056082a42d405d0074202021440c0501c02448844001580da0100c180400603510590480c6c800f00f100641c2c1c1e00511003540c00840701e0701c0c50081d4446051040a840f640704121103e2050201e40d070204143c2c0101381d03194007080c80c82d075050b03011012003020154400e50030f07c0c0c1d860150300503508164483e40303140c2c0c2e1401c025040c240304010841241d02ca851180082e01c25504008040700e0b16545d40341006810400d02260a59a250500d22032110b08002c014030328080700d9000d40181440c1b408455400025040108660381264a812a4582c507584072402100030300280c00c1e03502e00044ca003a07006001c007041c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 520129028 1250 520127778 520127791
    0x8070b012409081207060b030303010e040516080d1d0301050a1d03090a031e1205031605070f14030d14070f180308031b0a030504020108070513141512060108 69
    0x112902c09004111001c106860001c52441459888001a14151000c0d241c3e007201141c040c8404000061141000540f4a0045000c4c0003580c60700d070100d0160220141041c0144251a40b154004445452084450190f402d849036010002c010711040007070f0964100303441c01400350741c03030346820300d40b00400f4016100940c6001d00114903207180038001c200c8540c42848060206801540003404406c0e090241d084c0d6140e000c0f98540642540000c05000c0d9042a2440103075200c0703084025090b14000c00840c0c01203500101c1c90384403800c281e5a040100400301c0805c0a540c002440039218000305802181d0600d0b184800d000800d1411540051540e45126a0f130001c0000c0c6241a40111710801481c00582c2e030007411041d0344ea500c1942c00c100528580040b8901c0301f400080c40100b0750f9056100d5070007103200342d071011501e8a0322081210342c1e00130020300d10803100c40c0c090b00704034040c6c00300811801034501a12288401030884042c00c0a6007296030100c01e0050040304001d181d41c0c0c40038100b640800d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 520130278 1250 520129028 520129037
    0x1a09100c151e090c0f0b1312030516060e03040902072a0303111905010203070f0302090604170c060c070f09110d050622060503150403081308070b0124 66
    0x18044910b5000784180240c240c00710303641d55501c64043c08240080c480c00703000030101840d0036a5803400194082e500141e120089030000d00d0303000c034043c49400428004650140d5070700d410809201e00700003002c031945d68225822651303880080000070050003d0001000c250300300503142d69040c10400404c6012080c260001611048a0034103480304010a0702541c0d01443d0840a028080700880d10340401266221102d1400020701d100700032054004500c1112941d440004480320b09400760144e0043e80c69180d400807040c04184403280c0d501020105400c52941158005100d00e00415a20349c8140f01c60420b5402c03c1405028104a00c403005c80203003042c000400c941c2d0606040d0901d540943c0300d2100b1180c1c0c0340e0340815038039903421401c40b4001741c44e050b100f074202001070060001007a15120340e50280c06000000111024480501441103401d80c984624582c0c44448003010b07184400801c55a0400900160011401c501c00130382c0a8180700200c201994080e81d02a41c040d8500f444035810070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 520131528 1250 520130278 520130291
    0x90e0f070609030b0a060b04140111010606080c0a02073c0e0c1b0d1211070f0206031905040303091a071413031713170303011a09100c15 60
    0x1590215104080f2508009240314075100d400060002e49529031003120301c95404100410111550104888401d40c03d0b251a0481d80b11b546e1781609940b0035200b03010200c5e4041e4001040398184030001c1240c6a502c1c03054a51b039948580014980c45035036640c3d44000c1c9505001901c8030700c10380750f58066110451840313040a0b85010005e41a03160010046071060070302060150080c0041683d105514803501d081d54039200354864010250800c5031483c01c1004d050482c11018a001caa044580b000c1d0001c01c0c080090181c0d0b020310203c0e601c080c003118020780d001c030802c0b00104800d10405010318400c0d03a0126078419642082c0c900d85201c85101c3c801e211400c1d0074006070b540c000002010518403500203a859004004052141014a900c0902020f8401280010b000349100003810100050500344482c5a103c2050149000e0f801070a2040d66000300014005866181e4803001034800c280300c070a1804070002c002c58412004054101b0104103c3c00b0180d0400034481886032001081074402c1060 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 520132778 1250 520131528 520131539
    0x32212050c0105160b04140607090303050d2309010207030206070e0102060f09100f0209190506070b04020a0504021b1507021504020307241202040506090603060a050a090e0f07 77
    0x240c1d03101407480e0703050000c0000c0f6a6070300f40200c0c90b40d610090f0055810390807803406061512038000d1f407059600003401214009003401d400340c02000c05036505981e4050a01d01c1201d5240002d140c4040c0102141d1800302506038419031031500d0b5032044030030380000742c0c481c3c0d80c4d0f10300030380360400251281c400c0c40404c00704011580d9001801070b40c000b407010781060141e02e80800c07050070213055842c09813100e820529240d21040098004000512069442e686807090001c0c410031a00154080c1c540e2040040003110701080d10100c5403a00203000400e4079039003654130340000e01240d10034815401d0000e1300b002055019202801b400c184094000241c440c03614284100940b02c194180c188003a03104c4032404a03081d501c081007564003402805d1084e15402c66201005101c0d03200c940864000190b5080d5510b01c005414000d4404660300a00f000781020040010000e80d604010030f080d8200040c0100000e043d40d038480d085006082d0b403000000c0e425500903000e410301d0840c1100300306030303401074104004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 520134028 1250 520132778 520132783
    0xc090321050319091202150c0412140321011503110d0e0c100324030b0109050603010902090709060e0307030b1602030d0e0c010306060314011703070503221205 70
    0x50103c200380b551207004401c8003d900041800d940d010f8280201e1003880f188140e000140c01e01e0042c1b81292100300c5668803800300781c061107240100007880c510381c4c0b05007000801100000064030815000c3c1c2c2d08100f50362140317150008a03c0034141848a140d00100f19a101d04048262450b84030301c2e05100b0707030f10820075018079842080681c29000b40d8503081c2e0252701400b03005404082030020003220109070040e4005026140075080314054108485e044130b06004203001400440b80e110490211b5603180c10050402080300611207034155480e071070030f06c0c0166100850140306a090f61501c00010f402d08800902070520a600103000e40c0c00744c01c092003c80c40d41d4445a0f84942d907800596002841c07654224154003400b001e000011b0300f0f100c887c2f00685408240281c951748282c1c1c0030400655074800890031fa9100d200c500c405417241400611204400c0424a90500c205004170b0340b40ca10643d0354540303180e12014600088039107120881400c003200c0f032121801400803040408212000d529002e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 520135278 1250 520134028 520134031
    0x10201051608130206040f0905090a050705010f170a14010909020102100c0302160503121303170c1b0c0a090e030a0c02030c0409120216120204020f0c010c0903210503 73
    0x41c01c0c0712801c00002c41c1c0e0710420105008550f80540b1030382d2aa40e40e17100088907a9464000c000400c3e0903c3d0001340810b00021303606000ca07810100030140685018010344d85074a080003010200708600d0340c80030b081e51494504d280196109200001c40007140d07115080550410b03007080c45e80700d08100c00b11025070b9002880580003001d4000000f60100c01240503002031090000c0440104110720712841400740200180041310000e5056880594909405180c05a421000100860080b4145a0f414501485200d0380300840e103105502d0080f4881f01000c5000d000d180b0508240c0c40311185400508210859200600c400c0106100a240f83e201c2a0384034068032540c40f0400032802d0070340d015075804001c52181c0d4007002d04208501c21480c1040440044502d4454015101ba0300c0036066003001243d06008454001c10b02404540c15035003000041c0d8001c0c1c61445e424a030a2100300a201020701c68204141c0384c61700c0e82641d0926524013820312030039a0ba50310141514000150f0b41a0fa04001100d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 520136528 1250 520135278 520135321
    0x20f09100902030916080708070b12041217010f1e0b12071e032705190206070507081e0606090103080c0a05100f06050904050a2306070f0e01020105 65
    0x96100d42d14440c0151400640141707000364040004000a0417a00120b4410b080d0b59421090f00d0751192240d4814080c1e20816405942070402e1000040c04907900801d4200c80d805a45842042510103680300c000482013a04a000100e82d100703800c200d5040420110088501d10b440c040328281d00c0d107050800741d80038030490321101403514800104103521641250080c80c1594800e942c03c01300d40342005001300003000c07003041e11910002401040c0421030000c0b12803668800c0080544440c0300c0c0005040b8042204100c0e08082e091003540f000400074002c50000c2d040c001d00030440c803200041ea10100007000c0760a007003507410034400d0003c0d54490f200c9850560380c00180982d0341d0b080c1c002c010792401101c910050081e0003000050305c03840d80c690704403030052a4400e4080c00003039212404c010041a05a9004050381e00000c0703c0000103011607280180b0107142610b00c0e100048200300c45040400403141340000175400841c0e014003035000360110404840a100030800340c902046900e20174081410715 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 520137778 1250 520136528 520136531
    0xa1b060e1c020c1c0212100204091a0a060f09051206041b081203060a03200f03010c0e0d021813052a220c05070b01060302211510020a020f091009 64
    0x7113810b42d2a40c0100c03840c000054001c1714100014144508001d401038041e0010142c00d11800c0c00340460540c11007801841c00900c0079142d540752510654040607450208003c1c0621740ca00040c0c2652044200c0050340307101400b508041c6004c2c40c0080e60a4041d0b941d0038044030044009000c0d0304000603208c00341d102c80c031300d142d0303526120640080c0c0b04c041d0680c4018003018840b100740c01d542140b1407011080724000d503151100103000c0760825003070310b0045015000040e8460420710581c50441312a0424034006405017118a134110401c17094880c04907090f0650240000d00001041020009a155401a0b0141000b5021b21540d1825820300c44c20700180b24451090100c00300c082c80e01e0726040c0c401d0101204100c0e600513004040c105410900c070581d00f061101000290317441c000d00850b012a50340b034110560040c5080400117486001401c90f002030416140005102d46070101d099540d10155002094244d91920412103c043c2c2e400210740950051020b002810101d0304100041d00c100340c6c030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 520139028 1250 520137778 520137829
    0x30c040308091f021b041e050604060b0301030305070309290d0e01231806071409090106050d0f0920010c15020307020f010c050a1b060e1c020c 63
    0x1a846020a098181000303000840141d03c0a40001d908072940701300c6040e500b4111000c000708001c50300c117540450a40350202c0415401c0f44556440260710080003000003403040d40781d450300b02980c0c10980048010800020301c0303000341138000910000910004504040d151841c142030700c90307020024409040d0303c0c03000c6080b205154650b00414200300543c0005c0080d038032500341d030740c809180d2594034000d244004d0740403030b40c1c40d074842e00800002c8000800800d41903d62001c1190301040c088800364080c4010b01c4541c1c4255131301e00e0460300800056039a5a221351040324850f0844d42200080d02c41c2c145010b00c0c40001590007045001400350420100007850f410b02e00503182c190483d02c0082049a13081d00800c0f078180036030702a50140034039500300d4407100e40c8a541030742201c00025100c8046442801122001c0b445001c10541104030740060000440b0982d0301c1000b44c46c011110410325422019140c044180300381880081e0000a02c0106458030210003c00c00711900c0c0d01c9900041c02d0b1642 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 520140278 1250 520139028 520139047
    0xf04030b0c07050f030912030301051e0d2f1002070306020d020705011d01051303170a0b0d060615020a031d0303070f030804050105062e0e04060f030611030c040308 72
    0x500351030301c41c0c2d0010161200f04c490300440603201d40c0134036240c80c400c59409041c145007920002c00d0341d05079000640908803104105a031401c0910403a281c00e644140700d130415100003481c1d140c071501c151400600d040d402d1200d0415011148c0b011000740b60090209180070040b10b940081c0a20459801500050341c9103a28030342c0038080c0c0725011011344158281000d103117038040142500a031600d0740100030004c1c2e40342e44128840120001c900035000076480e030540c082815070b640d0b08a41090254400185003003a960208100c40700e07484054400302c0da070b0380e030402c01d550256805040c012400c1c401f50041c0607250b5805007140d0180305846e250344c54040c03a180303200d4800700100c035861504851203240400030362400800400d01110101c5055007400040b07070240c20000c250003a5041c96000c02400345039496041c0c00c803d802e0100c0307403003000f10f0800a25403541301d520071540941102070102c0c2c485825828070030b00792517030f545244041080400400c800c090200e002c1d94152544003081598811051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 520141528 1250 520140278 520140301
    0xe0d0618051501050a030803010b2107080a150503031b010f02031f06021b01050a0c021215060307030c0302060c0109021908060f040503030a23070f11030f04030b 71
    0x10300d88040148030000e00d8080c880700050a10030400c104211100503030b222024020a0001440001c145034010320060001412841c054000e244071038265070b01303402880210242c80c179420355114000c1a1510300703222003664039002d218040c00c11460b107002e0051030240881c1e62441841d81200c000d01010951412008007900101c0d104011170710155102d00f01100b40100504845105120aa8288500140542c0003186220081403464001c40e006085c0400644d02d541c840490403007000a180103000040c0d0300c0080036013080c040d803401006020040c0d03006400541c07016210b28841d40c0041030800024201079a50000d599041e02c2b106d0f1504290a0b07400e0142c000550006d5001c880f9030088503041111946400483c1c03249000c89440f40c0b5601c1c07508541e000196000762080c1c0040000070f401c2c0e02c01e50881007001004801d0250307a1410b5840c0304040c101d080d40d070032001440300344100300e049521541c0303440c1100c0150050b610380304022021503070710b1255110050140c3c3c6101c000a0003021003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 520142778 1250 520141528 520141541
    0xf03020c030d020a020709050c04091a0904110f0315130c0f03060c080705120610050c0a0b041b0602061504112101060c050303040b060d05151012030e0d06 68
    0x1400210381c0c40c1c180840502c0081c0d0044405180180300c0c40310001551040c50066038014403080b41c0742441d05040420071009015000c986840c107024603818140355403100e0760700e2845207009800d280704002c17402c42044414210a0300291283d0b0000d004652400d40c0340040302d81005c540c1d80340c4c1c40c66032401c1ca850704040c0002e5021004001c024103001081c1310017508201d50b580c14a07034031481603a459001c1641c1c14010001c4c0351140e54410b20000b11380342001c810480955040d4200740342401c8480040603c0c1000844048844109010900c4204034558954a05490002030010200c0742043d8000b5655000208403c1c1e440c070343c1507402651500d50307910070b400480840701c10980d180c507484403220303038111110724120154440d01e0000800743c3c81180211001035100000c2c528640b80e685030703007075248400f0300748690102401140300002503041040712200e0b072900a8400c3e480c50070740010070042400754401e10305031240325203100c0081c0c2e0002d00c10b0300d4050101d03149020740d1002d04215004000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 520143884 1106 520142778 520142797
    0xf0b0726010e07030e011808070b0702010c050319060b04080105070801060f02070303030b0a05180406050601080402010f030e0709020d06080f15060d14011401082b0f0302 75
    0x1080c0c01c85d10110200d00e0001c0b490201c2e801c419680202c00000072103d641000554504202054800e181d00244c42d0000300a60140180050b007a072000818050815a020b2480c41003580b03a5030103000505020301d5101d4031540c0f11402d680c002c140a840342c80c0420b95201c00021f080b03104000740c403003030310942d8080d001e16840c42d41c1c00d4026001c00031043da0300003144100030405844040314101c2c10400c000d443c603403c0c10641091402c881d0302800c041d042000050030031016036001400d80d0340200c1d5034130380010810040820300c0d040c00c5d00c54106405a500008243c40c000d43c4d44c1e088802074404030400d442150900c3c046040c1d0310b08038000104051007a0720005105c80c03030100d0349070310814044d183c0c002c64007a43e141d9003821a007040d880b192000031080010b00941e0820400c242690b803441c130301c40040240c0c05400140748407107054540100302c8101516161580310f42c040e01c14040 = true := by decide +kernel

theorem cover : BRFrame.Cov 519964028 520143884 := by
  have h0 := BRFrame.cov_init 519964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 519964028 ≤ n) (h2 : n < 520143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
